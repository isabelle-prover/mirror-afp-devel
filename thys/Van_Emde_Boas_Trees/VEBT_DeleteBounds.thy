(*by Ammer*)
theory VEBT_DeleteBounds imports VEBT_Bounds VEBT_Delete  VEBT_DeleteCorrectness
begin

subsection \<open>Running Time Bounds for Deletion\<close>

context begin
interpretation VEBT_internal .

fun T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) 0 = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) (Suc 0) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Leaf a b) (Suc (Suc n)) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node None deg treeList summary) _ = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) 0 treeList summary) x = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) (Suc 0) treeList summary) x =1 "|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3 + ( 
              if (x < mi \<or> x > ma) then 1 
              else 3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )))"

end

context VEBT_internal begin                       
                       
lemma tdeletemimi:"deg \<ge> 2 \<Longrightarrow> T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, mi)) deg treeList summary) x \<le> 9"
  using T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi mi "deg-2" treeList summary x]
  apply(cases "x \<noteq> mi") 
  apply (smt (z3) One_nat_def Suc_1 add_Suc_shift div_le_dividend le_add_diff_inverse not_less_iff_gr_or_eq numeral_3_eq_3 numeral_Bit0 numeral_Bit1_div_2 plus_1_eq_Suc)
  apply (smt (z3) Suc3_eq_add_3 Suc_eq_plus1 Suc_nat_number_of_add add_2_eq_Suc dual_order.eq_iff le_add_diff_inverse nat_less_le numeral_Bit1 semiring_norm(2) semiring_norm(8))
  done

lemma minNull_delete_time_bound: "invar_vebt t n \<Longrightarrow> minNull (vebt_delete t x) \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e t x \<le> 9" 
proof(induction  t n rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    apply(cases x)
    apply simp
    apply(cases "x=1") 
    apply simp 
    by (smt (z3) One_nat_def Suc_diff_le Suc_leI T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(3) diff_Suc_Suc le_add_diff_inverse one_le_numeral order.not_eq_order_implies_strict plus_1_eq_Suc zero_less_Suc)
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "4.prems" \<open>2 \<le> deg\<close> delt_out_of_range by force
  next
    case False
    hence "x \<le> ma \<and> x \<ge> mi" by simp
    then show ?thesis
    proof(cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>2 \<le> deg\<close> tdeletemimi by blast
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then show ?thesis
      proof(cases "x = mi")
        case True
        hence "x = mi" by simp
        let  ?xn = "the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary)))" 
        let  ?l = "low ?xn (deg div 2)"
        let  ?h = "high ?xn (deg div 2)" 
        have "\<exists> y. both_member_options summary y" 
          using "4.hyps"(4) "4.hyps"(5) "4.hyps"(8) "4.hyps"(9) False True high_bound_aux by blast
        then obtain i where aa:" (vebt_mint summary) = Some i" 
          by (metis "4.hyps"(1) Collect_empty_eq mint_corr_help_empty not_Some_eq set_vebt'_def valid_member_both_member_options)
        hence "\<exists> y. both_member_options (treeList ! i ) y"
          by (meson "4.hyps"(1) "4.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        hence "\<exists> y. both_member_options (treeList !  the (vebt_mint summary) ) y" 
          using \<open>vebt_mint summary = Some i\<close> by auto
        hence "invar_vebt (treeList ! the (vebt_mint summary)) n" 
          by (metis "4.IH"(1) "4.hyps"(1) "4.hyps"(2) \<open>vebt_mint summary = Some i\<close> option.sel member_bound mint_member nth_mem)
        then obtain y where "(vebt_mint (treeList ! the (vebt_mint summary)))  = Some y" 
          by (metis Collect_empty_eq \<open>\<exists>y. both_member_options (treeList ! the (vebt_mint summary)) y\<close> mint_corr_help_empty option.exhaust set_vebt'_def valid_member_both_member_options)
        have "y < 2^n \<and> i < 2^m" 
          using "4.hyps"(1) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>invar_vebt (treeList ! the (vebt_mint summary)) n\<close> aa member_bound mint_member by blast
        hence "?h \<le> 2^m" using aa 
          using "4.hyps"(3) "4.hyps"(4) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> high_inv by force 
        have  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
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
          using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l] "4.hyps"(2) "4.hyps"(3) 
                  "4.hyps"(4) "4.hyps"(7) False True \<open>2 \<le> deg\<close> \<open>vebt_mint (treeList ! the (vebt_mint summary)) = 
                  Some y\<close> \<open>y < 2 ^ n \<and> i < 2 ^ m\<close> aa high_inv
          by fastforce
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        show ?thesis
        proof(cases "minNull ?newnode")
          case True
          then show ?thesis 
            by (smt (z3) "0" "4.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            by (smt (z3) "0" "4.prems" minNull.simps(5))
        qed
      next
        case False
        hence "x > mi" 
          using \<open>x \<le> ma \<and> mi \<le> x\<close> nat_less_le by blast
        let  ?l = "low x (deg div 2)"
        let  ?h = "high x (deg div 2)" 
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        have "?h < length treeList" 
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>x \<le> ma \<and> mi \<le> x\<close> high_bound_aux by auto
        hence  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  if minNull ?newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg ?newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)))
                                 deg ?newlist summary ))"
          using del_x_not_mi[of mi x ma deg ?h ?l ?newnode ?newlist treeList summary]
          by (metis \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close> del_x_not_mi leD)
        then show ?thesis
        proof(cases " minNull ?newnode ")
          case True
          then show ?thesis 
            by (metis "0" "4.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            using "0" "4.prems" by fastforce
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "5.prems" \<open>2 \<le> deg\<close> delt_out_of_range by force
  next
    case False
    hence "x \<le> ma \<and> x \<ge> mi" by simp
    then show ?thesis
    proof(cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>2 \<le> deg\<close> tdeletemimi by blast
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then show ?thesis
      proof(cases "x = mi")
        case True
        hence "x = mi" by simp
        let  ?xn = "the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary)))" 
        let  ?l = "low ?xn (deg div 2)"
        let  ?h = "high ?xn (deg div 2)" 
        have "\<exists> y. both_member_options summary y" 
          using "5.hyps"(4) "5.hyps"(5) "5.hyps"(8) "5.hyps"(9) False True high_bound_aux by blast
        then obtain i where aa:" (vebt_mint summary) = Some i" 
          by (metis "5.hyps"(1) Collect_empty_eq mint_corr_help_empty not_Some_eq set_vebt'_def valid_member_both_member_options)
        hence "\<exists> y. both_member_options (treeList ! i ) y"
          by (meson "5.hyps"(1) "5.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        hence "\<exists> y. both_member_options (treeList !  the (vebt_mint summary) ) y" 
          using \<open>vebt_mint summary = Some i\<close> by auto
        hence "invar_vebt (treeList ! the (vebt_mint summary)) n" 
          by (metis "5.IH"(1) "5.hyps"(1) "5.hyps"(2) \<open>vebt_mint summary = Some i\<close> option.sel member_bound mint_member nth_mem)
        then obtain y where "(vebt_mint (treeList ! the (vebt_mint summary)))  = Some y" 
          by (metis Collect_empty_eq \<open>\<exists>y. both_member_options (treeList ! the (vebt_mint summary)) y\<close> mint_corr_help_empty option.exhaust set_vebt'_def valid_member_both_member_options)
        have "y < 2^n \<and> i < 2^m" 
          using "5.hyps"(1) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>invar_vebt (treeList ! the (vebt_mint summary)) n\<close> aa member_bound mint_member by blast
        hence "?h \<le> 2^m" using aa 
          using "5.hyps"(3) "5.hyps"(4) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> high_inv by force 
        have  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
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
                                 deg newlist summary )) "
          using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l] "5.hyps"(2) "5.hyps"(3)
                "5.hyps"(4) "5.hyps"(7) False True \<open>2 \<le> deg\<close> \<open>vebt_mint (treeList ! the (vebt_mint summary
                )) = Some y\<close> \<open>y < 2 ^ n \<and> i < 2 ^ m\<close> aa high_inv 
          by fastforce
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        show ?thesis
        proof(cases "minNull ?newnode")
          case True
          then show ?thesis 
            by (smt (z3) "0" "5.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            by (smt (z3) "0" "5.prems" minNull.simps(5))
        qed
      next
        case False
        hence "x > mi" 
          using \<open>x \<le> ma \<and> mi \<le> x\<close> nat_less_le by blast
        let  ?l = "low x (deg div 2)"
        let  ?h = "high x (deg div 2)" 
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        have "x <2^deg"
          using "5.hyps"(8) \<open>x \<le> ma \<and> mi \<le> x\<close> dual_order.strict_trans2 by blast
        hence "?h < 2^m" using  "5.prems" \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close>
            del_in_range minNull.simps(5) verit_comp_simplify1(3) apply simp
          by (smt (z3) minNull.simps(5))
        hence  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  if minNull ?newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg ?newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)))
                                 deg ?newlist summary ))" using del_x_not_mi[of mi x ma deg ?h ?l ?newnode ?newlist treeList summary]
          by (metis "5.hyps"(2) \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close> del_x_not_mi leD)
        then show ?thesis
        proof(cases " minNull ?newnode ")
          case True
          then show ?thesis 
            by (metis "0" "5.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            using "0" "5.prems" by fastforce
        qed
      qed
    qed
  qed
qed 

lemma delete_bound_height: "invar_vebt t n \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e t x \<le> (1+ height t)*70"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    apply(cases x) 
     apply simp 
    apply(cases "x = 1") 
     apply simp 
    apply (metis One_nat_def Suc_eq_plus1_left Suc_le_mono T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(3) comm_monoid_mult_class.mult_1 dual_order.trans height.simps(1) le_SucE lessI less_Suc_eq_le less_imp_Suc_add one_le_numeral zero_less_Suc)
    done
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case by simp
next
  case (4 treeList n summary m deg mi ma)
  hence deggy: "deg \<ge> 2" 
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case
  proof(cases " (x < mi \<or> x > ma)")
    case True
    hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 4" using
        T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] 
      by (smt (z3) Suc3_eq_add_3 Suc_1 \<open>2 \<le> deg\<close> add_2_eq_Suc' le_add_diff_inverse2 numeral_code(2))
    then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] by auto
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence 0: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  ))" using T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] deggy 
      by (smt (z3) False add.commute add_2_eq_Suc' add_numeral_left le_add_diff_inverse numeral_plus_numeral)    
    then show ?thesis 
    proof(cases " (x = mi \<and> x = ma)")
      case True
      hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 9" using 0 by simp
      then show ?thesis by simp
    next
      case False
      hence 1: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+
                (if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                 (if x = mi then 1 else 1)  +
                  (let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 0 
        by (simp add: False) 
      then show ?thesis 
      proof(cases "x = mi")
        case True
        let ?xn = " the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                   (let  l = low ?xn (deg div 2);
                   h = high ?xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1 by (smt (z3) True add.assoc)
        let ?l = "low ?xn (deg div 2)"
        let ?h = "high ?xn (deg div 2)"
        have 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                    (if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          using  2  by meson
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "4.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          have 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 37 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                              if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       ))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by simp
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1)        
                       ))"  
            by (smt (z3) Suc_eq_plus1 add.commute add_Suc numeral_plus_one semiring_norm(5) semiring_norm(8))        
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]   by presburger
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"] 
              using \<open>invar_vebt (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) n\<close> by blast       
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" by simp
            then show ?thesis 
            proof(cases "?xn =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" using 10 
                by (smt (z3) add.assoc trans_le_add1)
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" using maxt_bound[of ?sn] by force
              then show ?thesis
              proof(cases " vebt_maxt ?sn")
                case None
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h" using 11 by simp
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 + (1+height summary)*70" using "4.IH"(2)[of ?l]
                  by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              next
                case (Some a)
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                         1+ 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))" 
                  using "11" by fastforce
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                  using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  (1+ height summary)*70"
                  by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  (height  (Node (Some (mi, ma)) deg treeList summary) )*70"
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              qed
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 +  (1+ height summary)*70"
                by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                52 +  (height (Node (Some (mi, ma)) deg treeList summary) )*70" using height_compose_summary[of summary "Some (mi, ma)" deg treeList ] 
                by (meson add_mono_thms_linordered_semiring(2) le_refl mult_le_mono order_trans)
              then show ?thesis by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n" 
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) (low (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   43 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "?xn = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                55 + (1 + height (treeList ! ?h))*70" 
              by (meson "4.IH"(1) True le_trans nat_add_left_cancel_le nth_mem)
            moreover have "treeList ! ?h \<in> set treeList"
              using True nth_mem by blast
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                55 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary] by presburger
            then show ?thesis by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 34" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      next
        case False
        let ?l = "low x (deg div 2)"
        let ?h = "high x (deg div 2)"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+1 +1 +
                   (let  l = low x (deg div 2);
                   h = high x (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1  False by simp
        hence 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+(
                    if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          apply auto by metis
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "4.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          hence 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+ 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  
                      + 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                             if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by (smt (z3) True add.assoc)
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + 
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" by force
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]  by force
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"]
              using \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> by blast
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "x =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using 10  by (smt (z3) add.assoc trans_le_add1)
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by force
              then show ?thesis
              proof(cases " vebt_maxt ?sn")
                case None
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h" using 11 by simp
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 + (1+height summary)*70" using "4.IH"(2)[of ?l]
                  by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              next
                case (Some a)
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                         1+ 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))" 
                  using "11" by fastforce
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                  using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  (1+ height summary)*70"
                  by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  (height  (Node (Some (mi, ma)) deg treeList summary) )*70"
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              qed
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  (1+ height summary)*70"
                by (meson "4.IH"(2) le_trans nat_add_left_cancel_le)
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                42 +  (height (Node (Some (mi, ma)) deg treeList summary) )*70" using height_compose_summary[of summary "Some (mi, ma)" deg treeList ] 
                by (meson add_mono_thms_linordered_semiring(2) le_refl mult_le_mono order_trans)
              then show ?thesis by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n"
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high x (deg div 2)) (low x (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "x = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                           38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                38 + (1 + height (treeList ! ?h))*70" 
              by (meson "4.IH"(1) True le_trans nat_add_left_cancel_le nth_mem)
            moreover have "treeList ! ?h \<in> set treeList"
              using True nth_mem by blast
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                38 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary] by presburger
            then show ?thesis by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 22" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence deggy: "deg \<ge> 2" 
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case
  proof(cases " (x < mi \<or> x > ma)")
    case True
    hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 4" using
        T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] 
      by (smt (z3) Suc3_eq_add_3 Suc_1 \<open>2 \<le> deg\<close> add_2_eq_Suc' le_add_diff_inverse2 numeral_code(2))
    then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] by auto
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence 0: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 + (if (x = mi \<and> x = ma) then 3
              else 13 + ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  ))" using T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e.simps(7)[of mi ma "deg-2" treeList summary x] deggy 
      by (smt (z3) False add.commute add_2_eq_Suc' add_numeral_left le_add_diff_inverse numeral_plus_numeral)    
    then show ?thesis 
    proof(cases " (x = mi \<and> x = ma)")
      case True
      hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 9" using 0 by simp
      then show ?thesis by simp
    next
      case False
      hence 1: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+
                ( if x = mi then T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7 else 1 )+
                        (if x = mi then 1 else 1)  +
                  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) )
                                                              else 1)        
                             ))else 
                              2 + (if xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 0 
        by (simp add: False) 
      then show ?thesis 
      proof(cases "x = mi")
        case True
        let ?xn = " the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                   (let  l = low ?xn (deg div 2);
                   h = high ?xn (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" 
          using 1 by (smt (z3) True add.assoc)
        let ?l = "low ?xn (deg div 2)"
        let ?h = "high ?xn (deg div 2)"
        have 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +
                    (if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" 
          using  2  by meson
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "5.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          have 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 37 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                              if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       ))" 
            using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] mint_bound[of "summary"] 
            by simp
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1)        
                       ))"  
            by (smt (z3) Suc_eq_plus1 add.commute add_Suc numeral_plus_one semiring_norm(5) semiring_norm(8))        
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" using 5 minNull_bound[of ?newnode]   by presburger
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"] 
              using \<open>invar_vebt (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) n\<close> by blast       
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 39 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)"
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if ?xn  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "?xn =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 51 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using 10  by (smt (z3) add.assoc trans_le_add1)
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by force
              then show ?thesis
              proof(cases " vebt_maxt ?sn")
                case None
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h" using 11 by simp
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 + (1+height summary)*70" using "5.IH"(2)[of ?l]
                  by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              next
                case (Some a)
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                         1+ 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))" 
                  using "11" by fastforce
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                  using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  (1+ height summary)*70"
                  by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 67 +  (height  (Node (Some (mi, ma)) deg treeList summary) )*70"
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              qed
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 52 +  (1+ height summary)*70"
                by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                52 +  (height (Node (Some (mi, ma)) deg treeList summary) )*70" using height_compose_summary[of summary "Some (mi, ma)" deg treeList ] 
                by (meson add_mono_thms_linordered_semiring(2) le_refl mult_le_mono order_trans)
              then show ?thesis by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n" 
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2)) (low (the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   43 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if ?xn = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "?xn = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 55 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                55 + (1 + height (treeList ! ?h))*70" 
              by (meson "5.IH"(1) True le_trans nat_add_left_cancel_le nth_mem)
            moreover have "treeList ! ?h \<in> set treeList"
              using True nth_mem by blast
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                55 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary] by presburger
            then show ?thesis by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 3+3 +13+ T\<^sub>m\<^sub>i\<^sub>n\<^sub>t summary + 
                      T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the (vebt_mint summary))+ 7+1 +1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 34" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      next
        case False
        let ?l = "low x (deg div 2)"
        let ?h = "high x (deg div 2)"
        have 2: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x =3+3 +13+1 +1 +
                   (let  l = low x (deg div 2);
                   h = high x (deg div 2) in
                    if h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary h + (
                                let sn = vebt_delete summary h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! h)   else  1)        
                       )))else  1  )" using 1  False by simp
        hence 3: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+(
                    if ?h < length treeList 
                       then( 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l newnode + (
                             if minNull newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (newlist ! ?h)   else  1)        
                       )))else  1  )" apply auto by metis
        then show ?thesis 
        proof(cases "?h < length treeList")
          case True
          hence "?h < length treeList" by simp
          let  ?newnode = "vebt_delete (treeList ! ?h) ?l"
          let ?newlist = "treeList[?h:= ?newnode]"
          have "invar_vebt  (treeList ! ?h) n" 
            using "5.IH"(1) True nth_mem by blast 
          hence "invar_vebt ?newnode n" 
            using delete_pres_valid by blast
          hence 4: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+ 4 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  
                      + 1 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                             if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" using 3   mint_bound[of "treeList ! the (vebt_mint summary)"] 
            mint_bound[of "summary"] by (smt (z3) True add.assoc)
          hence 5: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + 
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode + (
                              if minNull ?newnode 
                             then(  1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)  ))else 
                              2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)   else  1))" by force
          then show ?thesis 
          proof(cases "minNull ?newnode ")
            case True
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                                let sn = vebt_delete summary ?h in
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t sn + (let maxs = vebt_maxt sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              using 5 minNull_bound[of ?newnode]  by force
            have 7: " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l \<le> 9" using True
                minNull_delete_time_bound[of "treeList ! ?h"]
              using \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> by blast
            let  ?sn = "vebt_delete summary ?h" 
            have 8: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l 
                            + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + (
                              2+ (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1))" 
              by (meson "6")
            hence 9:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 29 + 9 + 1 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h + 2+
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              using 6 7 by force
            hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (if x  = ma then 1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                       ) ) else 1)" 
              by simp
            then show ?thesis 
            proof(cases "x =  ma")
              case True
              hence 10:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 41 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            1 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t ?sn + (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))"
                using 10 by (smt (z3) add.assoc trans_le_add1)
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                            (let maxs = vebt_maxt ?sn in 
                                                                      1 + (if maxs = None 
                                                                         then 1
                                                                         else 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the maxs)
                                                                      ))" 
                using maxt_bound[of ?sn] by force
              then show ?thesis
              proof(cases " vebt_maxt ?sn")
                case None
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h" using 11 by simp
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 + (1+height summary)*70" using "5.IH"(2)[of ?l]
                  by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 47 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              next
                case (Some a)
                hence 12:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 45 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h +
                                         1+ 8+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! the (vebt_maxt ?sn))" 
                  using "11" by fastforce
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h "
                  using maxt_bound[of "?newlist ! the (vebt_maxt ?sn)"] by linarith
                hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  (1+ height summary)*70"
                  by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
                hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 57 +  (height  (Node (Some (mi, ma)) deg treeList summary) )*70"
                  using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
                then show ?thesis by simp
              qed
            next
              case False
              hence 11:  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e summary ?h " 
                using 10 by simp
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 42 +  (1+ height summary)*70"
                by (meson "5.IH"(2) le_trans nat_add_left_cancel_le)
              hence  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                42 +  (height (Node (Some (mi, ma)) deg treeList summary) )*70" 
                using height_compose_summary[of summary "Some (mi, ma)" deg treeList ] 
                by (meson add_mono_thms_linordered_semiring(2) le_refl mult_le_mono order_trans)
              then show ?thesis by simp
            qed
          next
            case False
            hence 6: "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 26 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l  +(
                           T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l ?newnode +  2 + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1))" using 5 by simp
            moreover have "invar_vebt (?newlist ! ?h) n"
              by (simp add: True \<open>invar_vebt (vebt_delete (treeList ! high x (deg div 2)) (low x (deg div 2))) n\<close>)
            ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                   29 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l + (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1)"
              using minNull_bound[of ?newnode] by linarith
            moreover have " (if x = ma then 6+  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (?newlist ! ?h)  else 1) \<le> 9" 
              apply(cases "x = ma") using maxt_bound[of " (?newlist ! ?h) "] by simp+
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                                 38 + T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (treeList ! ?h) ?l" by force
            hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                38 + (1 + height (treeList ! ?h))*70" 
              by (meson "5.IH"(1) True le_trans nat_add_left_cancel_le nth_mem)
            moreover have "treeList ! ?h \<in> set treeList"
              using True nth_mem by blast
            ultimately have  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x \<le>
                                38 + (height  (Node (Some (mi, ma)) deg treeList summary))*70" 
              using height_compose_child[of "treeList ! ?h"  treeList "Some (mi, ma)" deg summary]
              by presburger
            then show ?thesis by simp
          qed
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x = 21+1" using 3 by simp
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e (Node (Some (mi, ma)) deg treeList summary) x  \<le> 22" using 
              mint_bound[of "treeList ! the (vebt_mint summary)"] 
              mint_bound[of "summary"] by simp
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed

theorem delete_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e  t x \<le> 140 + 70 * lb (lb u)"
  using delete_bound_height[of t n x] height_double_log_univ_size[of u n t] by simp

fun T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) 0 = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) (Suc 0) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Leaf a b) (Suc (Suc n)) = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node None deg treeList summary) _ = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) 0 treeList summary) x = 1"|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) (Suc 0) treeList summary) x =1 "|
  "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x =  ( 
              if (x < mi \<or> x > ma) then 1 
              else if (x = mi \<and> x = ma) then 1
              else  (  let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! h) l  +(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary h        
                             else 1      
                       ))else  1  ))"


lemma tdeletemimi':"deg \<ge> 2 \<Longrightarrow> T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, mi)) deg treeList summary) x \<le> 1"
  using T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi mi "deg-2" treeList summary x]
  apply(cases "x \<noteq> mi") 
  apply (metis add_2_eq_Suc' le_add_diff_inverse2 le_eq_less_or_eq linorder_neqE_nat) 
  by (metis add_2_eq_Suc' eq_imp_le le_add_diff_inverse2)

lemma minNull_delete_time_bound': "invar_vebt t n \<Longrightarrow> minNull (vebt_delete t x) \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' t x \<le> 1" 
proof(induction t n rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    by (metis T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(1) T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(2) T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3) vebt_buildup.cases order_refl)
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "4.prems" \<open>2 \<le> deg\<close> delt_out_of_range by force
  next
    case False
    hence "x \<le> ma \<and> x \<ge> mi" by simp
    then show ?thesis
    proof(cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>2 \<le> deg\<close> tdeletemimi' by blast
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then show ?thesis
      proof(cases "x = mi")
        case True
        hence "x = mi" by simp
        let  ?xn = "the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary)))" 
        let  ?l = "low ?xn (deg div 2)"
        let  ?h = "high ?xn (deg div 2)" 
        have "\<exists> y. both_member_options summary y" 
          using "4.hyps"(4) "4.hyps"(5) "4.hyps"(8) "4.hyps"(9) False True high_bound_aux by blast
        then obtain i where aa:" (vebt_mint summary) = Some i" 
          by (metis "4.hyps"(1) Collect_empty_eq mint_corr_help_empty not_Some_eq set_vebt'_def valid_member_both_member_options)
        hence "\<exists> y. both_member_options (treeList ! i ) y"
          by (meson "4.hyps"(1) "4.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        hence "\<exists> y. both_member_options (treeList !  the (vebt_mint summary) ) y" 
          using \<open>vebt_mint summary = Some i\<close> by auto
        hence "invar_vebt (treeList ! the (vebt_mint summary)) n" 
          by (metis "4.IH"(1) "4.hyps"(1) "4.hyps"(2) \<open>vebt_mint summary = Some i\<close> option.sel member_bound mint_member nth_mem)
        then obtain y where "(vebt_mint (treeList ! the (vebt_mint summary)))  = Some y" 
          by (metis Collect_empty_eq \<open>\<exists>y. both_member_options (treeList ! the (vebt_mint summary)) y\<close> mint_corr_help_empty option.exhaust set_vebt'_def valid_member_both_member_options)
        have "y < 2^n \<and> i < 2^m" 
          using "4.hyps"(1) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>invar_vebt (treeList ! the (vebt_mint summary)) n\<close> aa member_bound mint_member by blast
        hence "?h \<le> 2^m" using aa 
          using "4.hyps"(3) "4.hyps"(4) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> high_inv by force 
        have  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (?xn, if ?xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       ) )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (?xn, (if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (newlist ! ?h))
                                                            else ma)))
                                 deg newlist summary ))
          " using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l]
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(7) False True \<open>2 \<le> deg\<close> \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>y < 2 ^ n \<and> i < 2 ^ m\<close> aa high_inv by fastforce
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        show ?thesis
        proof(cases "minNull ?newnode")
          case True
          then show ?thesis 
            by (smt (z3) "0" "4.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            by (smt (z3) "0" "4.prems" minNull.simps(5))
        qed
      next
        case False
        hence "x > mi" 
          using \<open>x \<le> ma \<and> mi \<le> x\<close> nat_less_le by blast
        let  ?l = "low x (deg div 2)"
        let  ?h = "high x (deg div 2)" 
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        have "?h < length treeList" 
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>x \<le> ma \<and> mi \<le> x\<close> high_bound_aux by auto
        hence  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  if minNull ?newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg ?newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)))
                                 deg ?newlist summary ))" using del_x_not_mi[of mi x ma deg ?h ?l ?newnode ?newlist treeList summary]
          by (metis \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close> del_x_not_mi leD)

        then show ?thesis
        proof(cases " minNull ?newnode ")
          case True
          then show ?thesis 
            by (metis "0" "4.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            using "0" "4.prems" by fastforce
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      using "5.prems" \<open>2 \<le> deg\<close> delt_out_of_range by force
  next
    case False
    hence "x \<le> ma \<and> x \<ge> mi" by simp
    then show ?thesis
    proof(cases "(x = mi \<and> x = ma)")
      case True
      then show ?thesis
        using \<open>2 \<le> deg\<close> tdeletemimi' by blast
    next
      case False
      hence "\<not> (x = mi \<and> x = ma)" by simp
      then show ?thesis
      proof(cases "x = mi")
        case True
        hence "x = mi" by simp
        let  ?xn = "the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary)))" 
        let  ?l = "low ?xn (deg div 2)"
        let  ?h = "high ?xn (deg div 2)" 
        have "\<exists> y. both_member_options summary y" 
          using "5.hyps"(4) "5.hyps"(5) "5.hyps"(8) "5.hyps"(9) False True high_bound_aux by blast
        then obtain i where aa:" (vebt_mint summary) = Some i" 
          by (metis "5.hyps"(1) Collect_empty_eq mint_corr_help_empty not_Some_eq set_vebt'_def valid_member_both_member_options)
        hence "\<exists> y. both_member_options (treeList ! i ) y"
          by (meson "5.hyps"(1) "5.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        hence "\<exists> y. both_member_options (treeList !  the (vebt_mint summary) ) y" 
          using \<open>vebt_mint summary = Some i\<close> by auto
        hence "invar_vebt (treeList ! the (vebt_mint summary)) n" 
          by (metis "5.IH"(1) "5.hyps"(1) "5.hyps"(2) \<open>vebt_mint summary = Some i\<close> option.sel member_bound mint_member nth_mem)
        then obtain y where "(vebt_mint (treeList ! the (vebt_mint summary)))  = Some y" 
          by (metis Collect_empty_eq \<open>\<exists>y. both_member_options (treeList ! the (vebt_mint summary)) y\<close> mint_corr_help_empty option.exhaust set_vebt'_def valid_member_both_member_options)
        have "y < 2^n \<and> i < 2^m" 
          using "5.hyps"(1) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>invar_vebt (treeList ! the (vebt_mint summary)) n\<close> aa member_bound mint_member by blast
        hence "?h \<le> 2^m" using aa 
          using "5.hyps"(3) "5.hyps"(4) \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> high_inv by force 
        have  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
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
                                 deg newlist summary ))
          " using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l]
          using "5.hyps"(2) "5.hyps"(3) "5.hyps"(4) "5.hyps"(7) False True \<open>2 \<le> deg\<close> \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some y\<close> \<open>y < 2 ^ n \<and> i < 2 ^ m\<close> aa high_inv by fastforce
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        show ?thesis
        proof(cases "minNull ?newnode")
          case True
          then show ?thesis 
            by (smt (z3) "0" "5.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            by (smt (z3) "0" "5.prems" minNull.simps(5))
        qed
      next
        case False
        hence "x > mi" 
          using \<open>x \<le> ma \<and> mi \<le> x\<close> nat_less_le by blast
        let  ?l = "low x (deg div 2)"
        let  ?h = "high x (deg div 2)" 
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]" 
        have "x <2^deg"
          using "5.hyps"(8) \<open>x \<le> ma \<and> mi \<le> x\<close> dual_order.strict_trans2 by blast
        hence "?h < 2^m" using  "5.prems" \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close>
            del_in_range minNull.simps(5) verit_comp_simplify1(3) apply simp
          by (smt (z3) minNull.simps(5))
        hence  0:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  if minNull ?newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg ?newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)))
                                 deg ?newlist summary ))" using del_x_not_mi[of mi x ma deg ?h ?l ?newnode ?newlist treeList summary]
          by (metis "5.hyps"(2) \<open>2 \<le> deg\<close> \<open>mi < x\<close> \<open>x \<le> ma \<and> mi \<le> x\<close> del_x_not_mi leD)
        then show ?thesis
        proof(cases " minNull ?newnode ")
          case True
          then show ?thesis 
            by (metis "0" "5.prems" minNull.simps(5))
        next
          case False
          then show ?thesis
            using "0" "5.prems" by fastforce
        qed
      qed
    qed
  qed
qed simp+


lemma delete_bound_height': "invar_vebt t n \<Longrightarrow>  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' t x \<le> 1+ height t"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    apply(cases "x \<le> 0")
    apply simp
    apply(cases "x = 1") 
    apply simp 
    using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3)[of a b "x-2"] height.simps(1)[of a b]
    by (metis One_nat_def T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(3) vebt_buildup.cases lessI less_Suc_eq_le plus_1_eq_Suc)
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge>2" 
    by (metis Suc_leI add_2_eq_Suc' add_Suc_shift add_le_mono deg_not_0 numeral_2_eq_2)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      by (metis One_nat_def Suc_1 T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7) \<open>2 \<le> deg\<close> add_leD2 vebt_buildup.cases le_add1 lessI not_less plus_1_eq_Suc)
  next
    case False
    hence miama:"mi \<le> x \<and> x \<le> ma" by simp
    then show ?thesis
    proof(cases "x = mi \<and> x = ma")
      case True
      then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi ma "deg-2" treeList summary x] \<open>2 \<le> deg\<close>  tdeletemimi' trans_le_add1 by blast
    next
      case False  
      let ?xn = "(if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)"
      let ?minn = "(if x = mi then ?xn else mi)"
      let ?l = "low ?xn (deg div 2)"
      let ?h = "high ?xn (deg div 2)"
      have 0:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = (if ?h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1      
                       ))else  1)" 
        using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi ma "deg-2" treeList summary x] \<open>2 \<le> deg\<close> False miama 
        by (smt (z3) add_2_eq_Suc le_add_diff_inverse not_less)
      then show ?thesis 
      proof(cases "?h< length treeList")
        case True
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]"
        have 1:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                               T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                             if minNull ?newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1  )" using 0 True by simp
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l \<le> 1" 
            by (metis "0" "1" "4.IH"(1) minNull_delete_time_bound' nat_le_iff_add nth_mem)
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1+ T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h" using 1 True by auto 
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1+1+ height summary" using 4(2)[of ?h] by simp
          then show ?thesis
            using order_trans by fastforce
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                              1+  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l   " using 1 by simp
          moreover have 2:" (treeList ! ?h) \<in>set treeList" 
            by (meson True nth_mem)
          ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height (treeList ! ?h)" 
            using 4(1) by simp
          then show ?thesis 
            by (smt (z3) "2" Suc_eq_plus1_left Suc_le_mono add_2_eq_Suc dual_order.trans height_compose_child nat_1_add_1)
        qed
      qed (simp add : 0)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge>2" 
    by (metis Suc_1 Suc_eq_plus1 add_mono_thms_linordered_semiring(1) le_add2 set_n_deg_not_0)
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    then show ?thesis 
      by (metis One_nat_def Suc_1 T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7) \<open>2 \<le> deg\<close> add_leD2 vebt_buildup.cases le_add1 lessI not_less plus_1_eq_Suc)
  next
    case False
    hence miama:"mi \<le> x \<and> x \<le> ma" by simp
    then show ?thesis
    proof(cases "x = mi \<and> x = ma")
      case True
      then show ?thesis using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi ma "deg-2" treeList summary x] \<open>2 \<le> deg\<close>  tdeletemimi' trans_le_add1 by blast
    next
      case False  
      let ?xn = "(if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)"
      let ?minn = "(if x = mi then ?xn else mi)"
      let ?l = "low ?xn (deg div 2)"
      let ?h = "high ?xn (deg div 2)"
      have 0:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = (if ?h < length treeList 
                       then(  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= newnode]in
                             if minNull newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1      
                       ))else  1)" 
        using  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'.simps(7)[of mi ma "deg-2" treeList summary x] \<open>2 \<le> deg\<close> False miama 
        by (smt (z3) add_2_eq_Suc le_add_diff_inverse not_less)
      then show ?thesis 
      proof(cases "?h< length treeList")
        case True
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        let ?newlist = "treeList[?h:= ?newnode]"
        have 1:"T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                               T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l  +(
                             if minNull ?newnode 
                             then  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h        
                             else 1  )" using 0 True by simp
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence " T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l \<le> 1" 
            by (metis "0" "1" "5.IH"(1) minNull_delete_time_bound' nat_le_iff_add nth_mem)
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1+ T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' summary ?h" using 1 True by auto 
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1+1+ height summary" using 5(2)[of ?h] by simp
          then show ?thesis
            using order_trans by fastforce
        next
          case False
          hence "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x = 
                              1+  T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (treeList ! ?h) ?l   " using 1 by simp
          moreover have 2:" (treeList ! ?h) \<in>set treeList" 
            by (meson True nth_mem)
          ultimately have "T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height (treeList ! ?h)" 
            using 5(1) by simp
          then show ?thesis 
            by (smt (z3) "2" Suc_eq_plus1_left Suc_le_mono add_2_eq_Suc dual_order.trans height_compose_child nat_1_add_1)
        qed
      qed (simp add : 0)
    qed
  qed
qed simp+

theorem delete_bound_size_univ': "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e'  t x \<le> 2 +  lb (lb u)"
  using delete_bound_height'[of t n x] height_double_log_univ_size[of u n t] by simp

end
end
