(*by Ammer*)
theory VEBT_DeleteCorrectness imports VEBT_Delete
begin

context VEBT_internal begin

subsection \<open>Validness Preservation\<close>

theorem delete_pres_valid: "invar_vebt t n \<Longrightarrow> invar_vebt (vebt_delete t x) n"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
  proof(cases x)
    case 0
    then show ?thesis 
      by (simp add: invar_vebt.intros(1))
  next
    case (Suc prex)
    hence "x = Suc prex" by simp
    then show ?thesis 
    proof(cases prex)
      case 0
      then show ?thesis
        by (simp add: Suc invar_vebt.intros(1))
    next
      case (Suc preprex)
      then show ?thesis 
        by (simp add: \<open>x = Suc prex\<close> invar_vebt.intros(1))
    qed
  qed
next
  case (2 treeList n summary m deg)
  then show ?case 
    using invar_vebt.intros(2) by force
next
  case (3 treeList n summary m deg)
  then show ?case
    using invar_vebt.intros(3) by auto
next
  case (4 treeList n summary m deg mi ma)
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary m" and 2:"length treeList = 2^m" and 3:" deg = n+m" and 
    4: "(\<forall> i < 2^m. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    and 8: "n = m" and 9: "deg div 2 = n" using "4" add_self_div_2 by auto
  hence 10: "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using invar_vebt.intros(4)[of treeList n summary m deg mi ma] by blast
  hence 11:"n \<ge> 1 " and 12: " deg \<ge> 2" 
    by (metis "1" "8" "9" One_nat_def Suc_leI deg_not_0 div_greater_zero_iff)+
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node (Some (mi, ma)) deg treeList summary)"
      using delt_out_of_range[of x mi ma deg treeList summary]
      using "1" "4.hyps"(3) "9" deg_not_0 div_greater_zero_iff by blast
    then show ?thesis
      by (simp add: "10")
  next
    case False
    hence inrg: "mi\<le> x \<and> x \<le> ma" by simp
    then show ?thesis  
    proof(cases "x = mi \<and> x = ma")
      case True
      hence" (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y)" 
        using "5" by blast
      moreover have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x  = (Node None deg treeList summary)"
        using del_single_cont[of x mi ma deg treeList summary] "1" "8" "9" True deg_not_0 div_greater_zero_iff by blast
      moreover have  " (\<nexists> i. both_member_options summary i)"
        using "10" True mi_eq_ma_no_ch by blast
      ultimately  show ?thesis
        using "0" "1" "2" "3" "4.hyps"(3) invar_vebt.intros(2) by force
    next
      case False
      hence "x \<noteq> mi \<or> x \<noteq> ma" by simp
      hence "mi \<noteq> ma \<and> x < 2^deg" 
        by (metis "6" inrg le_antisym le_less_trans)
      hence "7b": "(\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
               (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma))"
        using "7" by fastforce 
      hence "both_member_options (treeList ! (high ma n)) (low ma n)"
        using "1" "3" "6" "8" deg_not_0 exp_split_high_low(1) by blast
      hence yhelper:"both_member_options (treeList ! (high y n)) (low y n) 
                  \<Longrightarrow> high y n < 2^m \<Longrightarrow> mi < y \<and> y \<le> ma \<and> low y n < 2^n" for y 
        by (simp add: "7b" low_def) 
      then show ?thesis  
      proof(cases "x \<noteq> mi")
        case True
        hence xnotmi: "x \<noteq> mi" by simp
        let ?h = "high x n" 
        let ?l = "low x n"
        have hlbound:"?h < 2^m \<and> ?l < 2^n" 
          using "1" "3" "8" \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> deg_not_0 exp_split_high_low(1) exp_split_high_low(2) by blast
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        have "treeList ! ?h \<in> set treeList " 
          by (metis "2" hlbound in_set_member inthall)
        hence nnvalid: "invar_vebt ?newnode n" 
          by (simp add: "4.IH"(1))
        let ?newlist = "treeList[?h:= ?newnode]"
        have hlist:"?newlist ! ?h = ?newnode" 
          by (simp add: "2" hlbound)
        have nothlist:"i \<noteq> ?h \<Longrightarrow> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        have allvalidinlist:"\<forall> t \<in> set ?newlist. invar_vebt t n"
        proof
          fix t 
          assume "t \<in> set ?newlist"
          then obtain i where "i< 2^m \<and> ?newlist ! i = t" 
            by (metis "2" in_set_conv_nth length_list_update)
          show "invar_vebt t n" 
            by (metis "0" "2" \<open>i < 2 ^ m \<and> treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! i = t\<close> hlist nnvalid nth_list_update_neq nth_mem)
        qed
        have newlistlength: "length ?newlist = 2^m" using 2 by auto
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence ninNullc: "minNull ?newnode" by simp
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
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_not_mi_new_node_nil[of mi x ma deg ?h ?l ?newnode treeList ?sn summary ?newlist]
              hlbound 9 11 12 True 2 inrg xnotmi by simp
          have newsummvalid: "invar_vebt ?sn m"
            by (simp add: "4.IH"(2))
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options ?sn i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hlist by blast
                hence  1001:"\<nexists> x. vebt_member (?newlist ! i) x" 
                  by (simp add: min_Null_member ninNullc)
                hence 1002: "\<nexists> x. both_member_options (?newlist ! i) x"
                  using "1000" nnvalid valid_member_both_member_options by auto
                have 1003: "\<not> both_member_options ?sn i" 
                  using "1" True dele_bmo_cont_corr by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothlist by blast
                hence "both_member_options (?newlist ! i) y \<Longrightarrow> both_member_options ?sn i" for y
                proof-
                  assume "both_member_options (?newlist ! i) y"
                  hence "both_member_options summary i" 
                    using "1000" "4" \<open>i < 2 ^ m\<close> by auto
                  thus "both_member_options ?sn i" 
                    using "1" False dele_bmo_cont_corr by blast
                qed
                moreover have "both_member_options ?sn i \<Longrightarrow> \<exists> y. both_member_options (?newlist ! i) y" 
                proof-
                  assume "both_member_options ?sn i "
                  hence "both_member_options summary i"
                    using "1" dele_bmo_cont_corr by auto
                  thus " \<exists> y. both_member_options (?newlist ! i) y"
                    using "1000" "4" \<open>i < 2 ^ m\<close> by presburger
                qed
                then show ?thesis 
                  using calculation by blast
              qed
            qed
          qed
          have 112:" (mi = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"mi = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "x = ma")
              case True
              let ?maxs = "vebt_maxt ?sn" 
              show ?thesis
              proof(cases "?maxs = None")
                case True
                hence aa:"\<nexists> y. vebt_member ?sn y" 
                  using maxt_corr_help_empty newsummvalid set_vebt'_def by auto
                hence "\<nexists> y. both_member_options ?sn y"
                  using newsummvalid valid_member_both_member_options by blast
                hence "t \<in> set ?newlist \<Longrightarrow> \<nexists>y. both_member_options t y" for t 
                proof-
                  assume "t \<in> set ?newlist"
                  then obtain i where "?newlist ! i = t \<and> i< 2^m" 
                    by (metis in_set_conv_nth newlistlength)
                  thus " \<nexists>y. both_member_options t y" 
                    using "111" \<open>\<nexists>y. both_member_options (vebt_delete summary (high x n)) y\<close> by blast
                qed
                then show ?thesis by blast
              next
                case False
                then obtain maxs where "Some maxs = ?maxs"
                  by fastforce
                hence "both_member_options summary maxs" 
                  by (metis "1" dele_bmo_cont_corr maxbmo)
                have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                  by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                hence "invar_vebt (?newlist ! maxs) n"using 0  "2" by auto
                hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                  using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" using 
                    \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close>
                    empty_Collect_eq option.sel maxt_corr_help_empty set_vebt'_def valid_member_both_member_options by fastforce
                hence "maxs = high mi n \<and> both_member_options (?newlist ! maxs) (low mi n)" 
                  by (smt (z3) "9" True \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> aampt option.sel high_inv low_inv maxbmo member_bound mult.commute option.distinct(1) valid_member_both_member_options) 
                hence False 
                  by (metis bb nat_less_le nothlist yhelper)
                then show ?thesis by simp
              qed
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed
          have 114: "?newma < 2^deg \<and> mi \<le> ?newma" 
          proof(cases "x = ma")
            case True
            hence "x = ma" by simp
            let ?maxs = "vebt_maxt ?sn"
            show ?thesis 
            proof(cases "?maxs = None")
              case True
              then show ?thesis 
                using "6" by fastforce
            next
              case False
              then obtain maxs where "Some maxs = ?maxs"
                by fastforce
              hence "both_member_options summary maxs" 
                by (metis "1" dele_bmo_cont_corr maxbmo)
              have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
              hence "invar_vebt (?newlist ! maxs) n"using 0  "2" by auto
              hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
              then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"
                by (metis \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> empty_Collect_eq maxt_corr_help_empty option_shift.elims set_vebt'_def valid_member_both_member_options)
              then show ?thesis 
                by (smt (verit, best) "6" "9" \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> bb option.sel high_inv less_le_trans low_inv maxbmo maxt_member member_bound mult.commute not_less_iff_gr_or_eq nothlist verit_comp_simplify1(3) yhelper)
            qed
          next
            case False
            then show ?thesis 
              using "6" by auto
          qed 
          have 115: "mi \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
          proof
            assume "mi \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "x = ma" )
                      case True
                      let ?maxs = "vebt_maxt ?sn"
                      show ?thesis
                      proof(cases "?maxs = None")
                        case True
                        then show ?thesis
                          by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>mi \<noteq> (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma)\<close> \<open>treeList ! high x n \<in> set treeList\<close> bit_split_inv dele_bmo_cont_corr hlist newmaassm nth_list_update_neq)
                      next
                        case False
                        then obtain maxs where "Some maxs = ?maxs"
                          by fastforce
                        hence "both_member_options summary maxs" 
                          by (metis "1" dele_bmo_cont_corr maxbmo)
                        have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                          by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                        hence "invar_vebt (?newlist ! maxs) n"using 0 2 by auto
                        hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                          using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                        then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" using 
                            \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close>
                            empty_Collect_eq  maxt_corr_help_empty set_vebt'_def valid_member_both_member_options 
                          by (smt (z3) VEBT_Member.vebt_member.simps(2) \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> vebt_maxt.elims minNull.simps(1) min_Null_member valid_member_both_member_options)
                        then show ?thesis 
                          by (smt (z3) "9" False True \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> option.sel high_inv low_inv maxbmo maxt_member member_bound mult.commute newmaassm)
                      qed
                    next
                      case False
                      then show  ?thesis 
                        by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>treeList ! high x n \<in> set treeList\<close> assumption bit_split_inv dele_bmo_cont_corr hlist newmaassm nothlist)
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "mi < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)" 
                          using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr hlist yassm by auto
                        then show ?thesis 
                          by (simp add: assumption yassm yhelper)
                      next
                        case False
                        then show ?thesis 
                          using assumption nothlist yassm yhelper by presburger
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "x = ma")
                        case True
                        hence "x= ma" by simp
                        let ?maxs = "vebt_maxt ?sn"
                        show ?thesis 
                        proof(cases "?maxs = None")
                          case True
                          then show ?thesis 
                            using \<open>mi \<noteq> ?newma\<close> \<open>x = ma\<close> by presburger
                        next
                          case False
                          then obtain maxs where "Some maxs = ?maxs"
                            by fastforce
                          hence "both_member_options summary maxs" 
                            by (metis "1" dele_bmo_cont_corr maxbmo)
                          have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                            by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                          hence "invar_vebt (?newlist ! maxs) n"using 0 2 by auto
                          hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                            using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                          then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"
                            by (metis "2" "4.IH"(1) Collect_empty_eq bb both_member_options_equiv_member maxt_corr_help_empty nth_list_update_neq nth_mem option.exhaust set_vebt'_def)
                          hence "maxs < 2^m \<and> maxi < 2^n" 
                            by (metis \<open>invar_vebt (?newlist ! maxs) n\<close> bb maxt_member member_bound)
                          hence "?newma = 2^n* maxs + maxi" 
                            by (smt (z3) "9" False True \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> option.sel)
                          hence "low ?newma n = maxi \<and> high  ?newma n = maxs"
                            by (simp add: \<open>maxs < 2 ^ m \<and> maxi < 2 ^ n\<close> high_inv low_inv mult.commute)
                          hence "both_member_options (treeList ! (high y n)) (low y n)" 
                            by (metis "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm)
                          hence hleqdraft:"high y n > maxs \<Longrightarrow> False" 
                          proof-
                            assume "high y n > maxs"
                            have "both_member_options summary (high y n)" 
                              using "1" "111" assumption dele_bmo_cont_corr yassm by blast
                            moreover have "both_member_options ?sn (high y n)" 
                              using "111" assumption yassm by blast
                            ultimately show False 
                              by (metis \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>maxs < high y n\<close> leD maxt_corr_help newsummvalid valid_member_both_member_options)
                          qed
                          hence hleqmaxs: "high y n \<le> maxs" by presburger
                          then show ?thesis
                          proof(cases "high y n = maxs")
                            case True
                            hence "low y n \<le> maxi" 
                              by (metis \<open>Some maxi = vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs)\<close> \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> maxt_corr_help valid_member_both_member_options yassm)
                            then show ?thesis 
                              by (smt (z3) True \<open>(if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt ((?newlist) ! the maxs)) else ma) = 2 ^ n * maxs + maxi\<close> add_le_cancel_left bit_concat_def bit_split_inv mult.commute)
                          next
                            case False
                            then show ?thesis
                              by (metis \<open>low (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt ((?newlist) ! the maxs)) else ma) n = maxi \<and> high (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt ((?newlist) ! the maxs)) else ma) n = maxs\<close> div_le_mono high_def hleqdraft le_neq_implies_less nat_le_linear)
                          qed
                        qed
                      next
                        case False
                        then show ?thesis 
                          by (smt (z3) "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm yhelper)
                      qed
                      ultimately show " mi < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "mi \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (mi, ?newma)) deg ?newlist ?sn) deg"
            using invar_vebt.intros(4)[of ?newlist n ?sn m deg mi ?newma] 
            using 3 allvalidinlist newlistlength newsummvalid  "4.hyps"(3) 111 112 118 117 115 by fastforce
          show ?thesis
            using "116" dsimp by presburger
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist summary)" 
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp"
            using del_x_not_mi_newnode_not_nil[of mi x ma deg ?h ?l ?newnode treeList ?newlist summary]
            by (metis "12" "2" "9" False dual_order.eq_iff hlbound inrg order.not_eq_order_implies_strict xnotmi)
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options summary i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hlist by blast
                hence  1001:"\<exists> x. vebt_member (?newlist ! i) x" 
                  using nnvalid notemp valid_member_both_member_options by auto
                hence 1002: "\<exists> x. both_member_options (?newlist ! i) x" 
                  using "1000" notemp by presburger
                have 1003: "both_member_options summary i"
                  using "0" "1000" "1002" "4" True \<open>i < 2 ^ m\<close> \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by fastforce
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothlist by blast              
                then show ?thesis
                  using "4" \<open>i < 2 ^ m\<close> by presburger
              qed
            qed
          qed
          have 112:" (mi = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"mi = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "x = ma")
              case True 
              obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
                by (metis False VEBT_Member.vebt_member.simps(2) hlist vebt_maxt.elims minNull.simps(1) nnvalid notemp valid_member_both_member_options)
              hence "both_member_options ?newnode maxi" 
                using hlist maxbmo by auto
              hence "both_member_options (treeList ! ?h) maxi" 
                using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by blast
              hence False 
                by (metis "9" True \<open>both_member_options ?newnode maxi\<close> \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> aampt option.sel high_inv hlbound low_inv member_bound nnvalid not_less_iff_gr_or_eq valid_member_both_member_options yhelper)       
              then show ?thesis by blast
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed   
          have 114: "?newma < 2^deg \<and> mi \<le> ?newma" 
          proof(cases "x = ma")
            case True
            hence "x = ma" by simp
            obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
              by (metis empty_Collect_eq hlist maxt_corr_help_empty nnvalid notemp option.exhaust set_vebt'_def valid_member_both_member_options)
            hence "both_member_options ?newnode maxi" 
              using hlist maxbmo by auto
            hence "both_member_options (treeList ! ?h) maxi" 
              using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by blast
            hence "maxi < 2^n"
              using \<open>both_member_options?newnode maxi\<close> member_bound nnvalid valid_member_both_member_options by blast
            show ?thesis
              by (smt (z3) "3" "9" div_eq_0_iff True \<open>both_member_options (treeList ! high x n) maxi\<close> \<open>maxi < 2 ^ n\<close> \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> add.right_neutral div_exp_eq div_mult_self3 option.sel high_inv hlbound le_0_eq less_imp_le_nat low_inv power_not_zero rel_simps(28) yhelper)
          next
            case False
            then show ?thesis 
              using "6" by auto
          qed 
          have 115: "mi \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
          proof
            assume "mi \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "x = ma")
                      case True
                      obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                        by (metis Collect_empty_eq both_member_options_equiv_member hlist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                      hence "both_member_options (?newlist ! ?h) maxi" 
                        using maxbmo by blast
                      then show ?thesis
                        by (smt (z3) "9" True \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> option.sel high_inv hlist low_inv maxt_member member_bound newmaassm nnvalid)
                    next
                      case False
                      then show ?thesis 
                        by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>treeList ! high x n \<in> set treeList\<close> assumption bit_split_inv dele_bmo_cont_corr hlist newmaassm nothlist)
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "mi < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)" 
                          using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr hlist yassm by auto
                        then show ?thesis 
                          by (simp add: assumption yassm yhelper)
                      next
                        case False
                        then show ?thesis 
                          using assumption nothlist yassm yhelper by presburger
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "x = ma")
                        case True
                        hence "x= ma" by simp
                        obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                          by (metis Collect_empty_eq both_member_options_equiv_member hlist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                        hence "both_member_options (?newlist ! ?h) maxi" 
                          using maxbmo by blast
                        have "high y n \<le> ?h" 
                          by (metis "7b" True assumption div_le_mono high_def nothlist yassm)
                        then show ?thesis
                        proof(cases "high y n = ?h")
                          case True
                          have "low y n > maxi \<Longrightarrow> False" 
                            by (metis True \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> hlist leD maxt_corr_help nnvalid valid_member_both_member_options yassm) 
                          then show ?thesis 
                            by (smt (z3) "9" True \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> \<open>x = ma\<close> add_le_cancel_left div_mult_mod_eq option.sel high_def low_def nat_le_linear nat_less_le)
                        next
                          case False
                          then show ?thesis 
                            by (smt (z3) "9" True \<open>both_member_options (?newlist ! high x n) maxi\<close> \<open>high y n \<le> high x n\<close> \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> div_le_mono option.sel high_def high_inv hlist le_antisym member_bound nat_le_linear nnvalid valid_member_both_member_options)
                        qed                     
                      next
                        case False
                        then show ?thesis 
                          by (smt (z3) "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm yhelper)
                      qed
                      ultimately show " mi < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "mi \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (mi, ?newma)) deg ?newlist summary) deg"
            using invar_vebt.intros(4)[of ?newlist n summary m deg mi ?newma] allvalidinlist 
              1 newlistlength  8 3 111 112 117 118 115 by fastforce
          then show ?thesis
            using dsimp by presburger
        qed
      next
        case False
        hence xmi:"x = mi" by simp
        have "both_member_options summary (high ma n)" 
          using "1" "3" "4" "4.hyps"(3) "6" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> deg_not_0 exp_split_high_low(1) by blast
        hence "vebt_member summary (high ma n)" 
          using "4.hyps"(1) valid_member_both_member_options by blast
        obtain summin where "Some summin = vebt_mint summary" 
          by (metis "4.hyps"(1) \<open>vebt_member summary (high ma n)\<close> empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def)
        hence "\<exists> z . both_member_options (treeList ! summin) z"
          by (metis "4.hyps"(1) "4.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        moreover have "invar_vebt (treeList ! summin) n" 
          by (metis "0" "1" "2" \<open>Some summin = vebt_mint summary\<close> member_bound mint_member nth_mem)
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
          by (metis "12" "2" "9" \<open>invar_vebt (treeList ! summin) n\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree high_inv low_inv member_bound numeral_2_eq_2 plus_1_eq_Suc)
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
          by (meson \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> nth_list_update_eq)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        have hlbound:"?h < 2^m \<and> ?l < 2^n"
          using "1" "2" "3" "8" \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>summin * 2 ^ n + lx < 2 ^ deg\<close> deg_not_0 exp_split_high_low(2) by presburger
        hence nnvalid: "invar_vebt ?newnode n"
          by (metis "4.IH"(1) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> inthall member_def)
        have allvalidinlist:"\<forall> t \<in> set ?newlist. invar_vebt t n"
        proof
          fix t 
          assume "t \<in> set ?newlist"
          then obtain i where "i < 2^m \<and> ?newlist ! i = t"
            by (metis "2" \<open>length treeList = length (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)])\<close> in_set_conv_nth)
          then show "invar_vebt t n" 
            by (metis "0" "2" hprolist nnvalid nth_list_update_neq nth_mem)
        qed
        have newlistlength: "length ?newlist = 2^m" 
          by (simp add: "2") 
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence ninNullc: "minNull ?newnode" by simp
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if ?xn  = ma then (let maxs = vebt_maxt ?sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist ?sn)" 
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_mi_lets_in_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist ?sn] 
            by (metis "12" "9" \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x = mi\<close> \<open>x \<noteq> mi \<or> x \<noteq> ma\<close> inrg nat_less_le ninNullc)
          have newsummvalid: "invar_vebt ?sn m"
            by (simp add: "4.IH"(2))
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options ?sn i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hprolist by fastforce
                hence  1001:"\<nexists> x. vebt_member (?newlist ! i) x" 
                  by (simp add: min_Null_member ninNullc)
                hence 1002: "\<nexists> x. both_member_options (?newlist ! i) x"
                  using "1000" nnvalid valid_member_both_member_options by auto
                have 1003: "\<not> both_member_options ?sn i" 
                  using "1" True dele_bmo_cont_corr by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i" 
                  using \<open>i < 2 ^ m\<close> nothprolist by blast
                hence "both_member_options (?newlist ! i) y \<Longrightarrow> both_member_options ?sn i" for y
                proof-
                  assume "both_member_options (?newlist ! i) y"
                  hence "both_member_options summary i" 
                    using "1000" "4" \<open>i < 2 ^ m\<close> by auto
                  thus "both_member_options ?sn i" 
                    using "1" False dele_bmo_cont_corr by blast
                qed
                moreover have "both_member_options ?sn i \<Longrightarrow> \<exists> y. both_member_options (?newlist ! i) y" 
                proof-
                  assume "both_member_options ?sn i "
                  hence "both_member_options summary i"
                    using "1" dele_bmo_cont_corr by auto
                  thus " \<exists> y. both_member_options (?newlist ! i) y"
                    using "1000" "4" \<open>i < 2 ^ m\<close> by presburger
                qed
                then show ?thesis 
                  using calculation by blast
              qed
            qed
          qed
          have 112:" (?xn = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"?xn = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)" 
            proof(cases "?xn = ma")
              case True
              let ?maxs = "vebt_maxt ?sn" 
              show ?thesis
              proof(cases "?maxs = None")
                case True
                hence aa:"\<nexists> y. vebt_member ?sn y" 
                  using maxt_corr_help_empty newsummvalid set_vebt'_def by auto
                hence "\<nexists> y. both_member_options ?sn y"
                  using newsummvalid valid_member_both_member_options by blast
                hence "t \<in> set ?newlist \<Longrightarrow> \<nexists>y. both_member_options t y" for t 
                proof-
                  assume "t \<in> set ?newlist"
                  then obtain i where "?newlist ! i = t \<and> i< 2^m"
                    by (metis "2" \<open>length treeList = length (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)])\<close> in_set_conv_nth)
                  thus " \<nexists>y. both_member_options t y" 
                    using "111" \<open>\<nexists>y. both_member_options (vebt_delete summary (high (summin * 2 ^ n + lx) n)) y\<close> by blast
                qed
                then show ?thesis by blast
              next
                case False
                then obtain maxs where "Some maxs = ?maxs"
                  by fastforce
                hence "both_member_options summary maxs" 
                  by (metis "1" dele_bmo_cont_corr maxbmo)
                have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                  by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                hence "invar_vebt (?newlist ! maxs) n"using 0 
                  by (simp add: "2" allvalidinlist)
                hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                  using "4" bb \<open>both_member_options summary maxs\<close> nothprolist by presburger
                then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"
                  using \<open>invar_vebt (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs) n\<close> maxt_corr_help_empty set_vebt'_def valid_member_both_member_options by fastforce
                hence "maxs = high ?xn n \<and> both_member_options (?newlist ! maxs) (low ?xn n)"
                  by (smt (z3) "9" False True \<open>Some maxs = vebt_maxt (vebt_delete summary ?h)\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> aampt option.sel high_inv low_inv maxbmo maxt_member member_bound mult.commute)
                hence False 
                  using bb by blast
                then show ?thesis by simp
              qed
            next
              case False
              hence "?xn \<noteq> ?newma" by simp
              hence False using aampt by simp
              then show ?thesis by blast
            qed
          qed
          have 114: "?newma < 2^deg \<and> ?xn \<le> ?newma" 
          proof(cases "?xn = ma")
            case True
            hence "?xn = ma" by simp
            let ?maxs = "vebt_maxt ?sn"
            show ?thesis 
            proof(cases "?maxs = None")
              case True
              then show ?thesis 
                using "4.hyps"(8) \<open>?xn = ma\<close> by force
            next
              case False
              then obtain maxs where "Some maxs = ?maxs"
                by fastforce
              hence "both_member_options summary maxs" 
                by (metis "1" dele_bmo_cont_corr maxbmo)
              have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
              hence "invar_vebt (?newlist ! maxs) n"using 0  by (simp add: "2" allvalidinlist)
              hence "\<exists> y. both_member_options (?newlist ! maxs) y" 
                using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
              then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                using \<open>invar_vebt (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs) n\<close> empty_Collect_eq maxt_corr_help_empty not_Some_eq set_vebt'_def valid_member_both_member_options by fastforce
              hence abc:"?newma = 2^n * maxs + maxi" 
                by (smt (z3) "9" True \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> option.sel not_None_eq)
              have abd:"maxi < 2^n" 
                by (metis \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> maxt_member member_bound)
              have "high ?xn n \<le> maxs"
                using "1" \<open>Some summin = vebt_mint summary\<close> \<open>both_member_options summary maxs\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound mint_corr_help valid_member_both_member_options by force
              then show ?thesis 
              proof(cases "high ?xn n = maxs")
                case True
                then show ?thesis
                  using bb by fastforce
              next
                case False
                hence "high ?xn n < maxs" 
                  by (simp add: \<open>high (summin * 2 ^ n + lx) n \<le> maxs\<close> order.not_eq_order_implies_strict)
                hence "?newma < 2^deg"using
                    "1" "10" "9" True \<open>both_member_options summary maxs\<close> \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> 
                    equals0D  leD maxt_corr_help maxt_corr_help_empty mem_Collect_eq summaxma set_vebt'_def
                    valid_member_both_member_options
                  by (metis option.exhaust_sel)
                moreover have "high ?xn n < high ?newma n"
                  by (smt (z3) "9" True \<open>Some maxi = vebt_maxt (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> \<open>high (summin * 2 ^ n + lx) n < maxs\<close> abd option.sel high_inv mult.commute option.discI)
                ultimately show ?thesis
                  by (metis div_le_mono high_def linear not_less)
              qed
            qed
          next
            case False
            then show ?thesis 
              by (smt (z3) "12" "4.hyps"(7) "4.hyps"(8) "9" both_member_options_from_complete_tree_to_child dual_order.trans hlbound one_le_numeral xnin yhelper)
          qed 
          have 115: "?xn \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
          proof
            assume assumption0:"?xn \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "?xn = ma" )
                      case True
                      hence bb:"?xn = ma" by simp
                      let ?maxs = "vebt_maxt ?sn"
                      show ?thesis
                      proof(cases "?maxs = None")
                        case True
                        hence "?newma = ?xn"  using assumption Let_def bb by simp
                        hence False using assumption0 by simp
                        then show ?thesis by simp
                      next
                        case False
                        then obtain maxs where "Some maxs = ?maxs"
                          by fastforce
                        hence "both_member_options summary maxs" 
                          by (metis "1" dele_bmo_cont_corr maxbmo)
                        have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                          by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                        hence "invar_vebt (?newlist ! maxs) n"using 0    by (simp add: "2" allvalidinlist)
                        hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                          using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
                        then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" using
                            \<open>invar_vebt (treeList [high (summin * 2 ^ n + lx) n :=
                             vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs) n\<close>
                             equals0D  maxt_corr_help_empty mem_Collect_eq set_vebt'_def 
                             valid_member_both_member_options 
                          by (metis option.collapse)
                        then show ?thesis using  "1" "10" "9" True \<open>Some summin = vebt_mint summary\<close>
                            \<open>both_member_options summary maxs\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> 
                            \<open>invar_vebt (treeList ! summin) n\<close> bb equals0D  high_inv maxt_corr_help maxt_corr_help_empty
                            mem_Collect_eq member_bound mint_corr_help nat_less_le summaxma set_vebt'_def
                            valid_member_both_member_options verit_comp_simplify1(3)
                          by (metis option.collapse)
                      qed
                    next
                      case False
                      hence ccc:"?newma = ma" by simp
                      then show  ?thesis
                      proof(cases "?xn = ma")
                        case True
                        hence "?xn = ?newma"
                          using False by blast
                        hence False
                          using False by auto
                        then show ?thesis by simp
                      next
                        case False
                        hence "both_member_options (?newlist ! high ma n) (low ma n)" 
                          by (metis "1" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>vebt_member summary (high ma n)\<close> \<open>invar_vebt (treeList ! summin) n\<close> bit_split_inv dele_bmo_cont_corr high_inv hprolist member_bound nothprolist)
                        moreover have "high ma n = i \<and> low ma n = low ?newma n" using ccc newmaassm by simp
                        ultimately show ?thesis by simp
                      qed
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "?xn < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)"
                          using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by auto
                        then show ?thesis 
                          using True hprolist min_Null_member ninNullc nnvalid valid_member_both_member_options yassm by fastforce
                      next
                        case False
                        hence "i \<le> ?h \<Longrightarrow> False"
                          by (metis "1" "111" \<open>Some summin = vebt_mint summary\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption dele_bmo_cont_corr high_inv le_antisym member_bound mint_corr_help valid_member_both_member_options yassm)
                        hence "i > ?h" 
                          using leI by blast
                        then show ?thesis
                          by (metis div_le_mono high_def not_less yassm)
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "?xn = ma")
                        case True
                        hence "?xn= ma" by simp
                        let ?maxs = "vebt_maxt ?sn"
                        show ?thesis 
                        proof(cases "?maxs = None")
                          case True
                          then show ?thesis
                            using "1" "111" assumption dele_bmo_cont_corr nothprolist yassm yhelper by auto
                        next
                          case False
                          then obtain maxs where "Some maxs = ?maxs"
                            by fastforce
                          hence "both_member_options summary maxs" 
                            by (metis "1" dele_bmo_cont_corr maxbmo)
                          have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                            by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                          hence "invar_vebt (?newlist ! maxs) n"using 0 
                            by (simp add: "2" allvalidinlist)
                          hence "\<exists> y. both_member_options (?newlist ! maxs) y" 
                            using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
                          then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                            by (metis True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption calculation dele_bmo_cont_corr high_inv hprolist leD member_bound nth_list_update_neq yassm yhelper)
                          hence "maxs < 2^m \<and> maxi < 2^n" 
                            by (metis \<open>invar_vebt (?newlist ! maxs) n\<close> bb maxt_member member_bound)
                          hence "?newma = 2^n* maxs + maxi" 
                            by (smt (z3) "9" False True \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high ?xn n))\<close> option.sel)
                          hence "low ?newma n = maxi \<and> high  ?newma n = maxs"
                            by (simp add: \<open>maxs < 2 ^ m \<and> maxi < 2 ^ n\<close> high_inv low_inv mult.commute)
                          hence "both_member_options (treeList ! (high y n)) (low y n)" 
                            by (metis "1" "111" assumption dele_bmo_cont_corr nothprolist yassm)
                          hence hleqdraft:"high y n > maxs \<Longrightarrow> False" 
                          proof-
                            assume "high y n > maxs"
                            have "both_member_options summary (high y n)" 
                              using "1" "111" assumption dele_bmo_cont_corr yassm by blast
                            moreover have "both_member_options ?sn (high y n)" 
                              using "111" assumption yassm by blast
                            ultimately show False
                              using True \<open>both_member_options (treeList ! high y n) (low y n)\<close> \<open>summin * 2 ^ n + lx < y\<close> assumption leD yassm yhelper by blast
                          qed
                          hence hleqmaxs: "high y n \<le> maxs" by presburger                     
                          then show ?thesis 
                            using \<open>both_member_options (treeList ! high y n) (low y n)\<close> assumption calculation dual_order.strict_trans1 yassm yhelper by auto
                        qed
                      next
                        case False
                        then show ?thesis
                          by (smt (z3) \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption dele_bmo_cont_corr high_inv hprolist member_bound nothprolist yassm yhelper)
                      qed
                      ultimately show " ?xn < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "?xn \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (?xn, ?newma)) deg ?newlist ?sn) deg"
            using invar_vebt.intros(4)[of ?newlist n ?sn m deg ?xn ?newma] 
            using 3 allvalidinlist newlistlength newsummvalid  "4.hyps"(3) 111 112 118 117 115 by fastforce
          show ?thesis
            using "116" dsimp by presburger
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist summary)" 
          have dsimp:"vebt_delete (Node (Some (x, ma)) deg treeList summary) x = ?delsimp" 
            using del_x_mi_lets_in_not_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist] 
              "12" "2" "9" False dual_order.eq_iff hlbound inrg order.not_eq_order_implies_strict xmi 
            by (metis \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x \<noteq> mi \<or> x \<noteq> ma\<close>)
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options summary i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode" 
                  using hprolist by blast
                hence  1001:"\<exists> x. vebt_member (?newlist ! i) x" 
                  using nnvalid notemp valid_member_both_member_options by auto
                hence 1002: "\<exists> x. both_member_options (?newlist ! i) x" 
                  using "1000" notemp by presburger
                have 1003: "both_member_options summary i" 
                  using "4" True \<open>\<exists>z. both_member_options (treeList ! summin) z\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothprolist by blast              
                then show ?thesis
                  using "4" \<open>i < 2 ^ m\<close> by presburger
              qed
            qed
          qed
          have 112:" (?xn = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"?xn = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "?xn = ma")
              case True 
              obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
                by (metis Collect_empty_eq False hprolist maxt_corr_help_empty nnvalid not_None_eq not_min_Null_member set_vebt'_def valid_member_both_member_options)
              hence "both_member_options ?newnode maxi" 
                using hprolist maxbmo by auto
              hence "both_member_options (treeList ! ?h) maxi"
                using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv member_bound by force
              hence False 
                by (metis "9" \<open>both_member_options (vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)) maxi\<close> \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> aampt add_diff_cancel_left' dele_bmo_cont_corr option.sel high_inv low_inv member_bound)
              then show ?thesis by blast
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed   
          have 114: "?newma < 2^deg \<and> ?xn \<le> ?newma" 
          proof(cases "?xn = ma")
            case True
            hence "?xn = ma" by simp
            obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
              by (metis "111" "2" "4" Collect_empty_eq True \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> hprolist maxt_corr_help_empty nnvalid not_None_eq set_vebt'_def valid_member_both_member_options)
            hence "both_member_options ?newnode maxi" 
              using hprolist maxbmo by auto
            hence "both_member_options (treeList ! ?h) maxi" 
              using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv member_bound by force
            hence "maxi < 2^n"
              using \<open>both_member_options?newnode maxi\<close> member_bound nnvalid valid_member_both_member_options by blast
            show ?thesis 
              by (smt (verit, ccfv_threshold) "3" "9" div_eq_0_iff True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>both_member_options (treeList ! high (summin * 2 ^ n + lx) n) maxi\<close> \<open>vebt_maxt (?newlist ! high (summin * 2 ^ n + lx) n) = Some maxi\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> add.right_neutral add_left_mono div_mult2_eq div_mult_self3 option.sel high_inv hlbound le_0_eq member_bound mint_corr_help power_add power_not_zero rel_simps(28) valid_member_both_member_options)
          next
            case False
            then show ?thesis 
              using "10" "4.hyps"(8) maxt_corr_help valid_member_both_member_options xnin by force

          qed 
          have 115: "?xn \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
          proof
            assume xnmassm:"?xn \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)" 
                    proof(cases "?xn = ma")
                      case True
                      obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                        by (metis Collect_empty_eq both_member_options_equiv_member hprolist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                      hence "both_member_options (?newlist ! ?h) maxi" 
                        using maxbmo by blast
                      then show ?thesis 
                        by (smt (z3) "2" "9" True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> add_left_mono dele_bmo_cont_corr eq_iff high_inv hprolist low_inv member_bound mint_corr_help valid_member_both_member_options yhelper)
                    next
                      case False
                      hence abcd:"?newma = ma" by simp
                      then show ?thesis 
                      proof(cases "high ma n = ?h")
                        case True
                        hence "?newlist ! high ma n = ?newnode"
                          using hprolist by presburger
                        then show ?thesis  
                          by (smt (z3) False True \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> bit_split_inv dele_bmo_cont_corr high_inv member_bound newmaassm)                      
                      next
                        case False
                        hence "?newlist ! high ma n = treeList ! high ma n" 
                          using "1" \<open>vebt_member summary (high ma n)\<close> member_bound nothprolist by blast
                        moreover hence "both_member_options (treeList ! high ma n) (low ma n)" 
                          using \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> by blast
                        ultimately  show ?thesis using abcd newmaassm by simp
                      qed
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "?xn < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)"
                          using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by force
                        moreover have "vebt_mint (treeList  ! i) = Some (low ?xn n)" 
                          using True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv low_inv member_bound by presburger
                        moreover hence "low y n \<ge> low ?xn n" 
                          using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> calculation(1) high_inv member_bound mint_corr_help valid_member_both_member_options by auto
                        moreover have "low y n \<noteq> low ?xn n"
                          using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by auto
                        ultimately have "low y n > low ?xn n" by simp
                        show ?thesis 
                          by (metis True \<open>low (summin * 2 ^ n + lx) n \<le> low y n\<close> \<open>low y n \<noteq> low (summin * 2 ^ n + lx) n\<close> bit_concat_def bit_split_inv leD linorder_neqE_nat nat_add_left_cancel_less yassm)
                      next
                        case False
                        have "Some (high ?xn n) = vebt_mint summary" 
                          using \<open>Some summin = vebt_mint summary\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                        moreover hence "high y n \<ge> high ?xn n" 
                          by (metis "1" "111" assumption mint_corr_help valid_member_both_member_options yassm)
                        ultimately show ?thesis
                          by (metis False div_le_mono high_def leI le_antisym yassm)
                      qed
                      moreover have "y \<le> ?newma" 
                        by (smt (z3) \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption calculation dele_bmo_cont_corr high_inv hprolist leD member_bound nothprolist yassm yhelper)                 
                      ultimately show " ?xn < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "?xn \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (?xn, ?newma)) deg ?newlist summary) deg"
            using invar_vebt.intros(4)[of ?newlist n summary m deg ?xn ?newma] allvalidinlist 
              1 newlistlength  8 3 111 112 117 118 115 by fastforce
          hence "invar_vebt (?delsimp) deg" by simp
          moreover  obtain delsimp where 118:"delsimp = ?delsimp" by simp
          ultimately have 119:"invar_vebt delsimp deg" by simp 
          have "vebt_delete (Node (Some (x, ma)) deg treeList summary) x = delsimp" using dsimp 118 by simp
          hence "delsimp = vebt_delete (Node (Some (x, ma)) deg treeList summary) x" by simp
          then show ?thesis using 119 
            using xmi by auto
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary m" and 2:"length treeList = 2^m" and 3:" deg = n+m" and 
    4: "(\<forall> i < 2^m. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    and 8: "Suc n = m" and 9: "deg div 2 = n" using "5" add_self_div_2 by auto
  hence 10: "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using invar_vebt.intros(5)[of treeList n summary m deg mi ma] by blast
  hence 11:"n \<ge> 1 " and 12: " deg \<ge> 2" 
    by (metis "0" "2" "9" One_nat_def deg_not_0 div_greater_zero_iff le_0_eq numeral_2_eq_2 set_n_deg_not_0)+
  then show ?case 
  proof(cases "(x < mi \<or> x > ma)")
    case True
    hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node (Some (mi, ma)) deg treeList summary)"
      using delt_out_of_range[of x mi ma deg treeList summary] 
      using "12" by fastforce
    then show ?thesis
      by (simp add: "10")
  next
    case False
    hence inrg: "mi\<le> x \<and> x \<le> ma" by simp
    then show ?thesis  
    proof(cases "x = mi \<and> x = ma")
      case True
      hence" (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y)" 
        using "5" by blast
      moreover have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x  = (Node None deg treeList summary)"
        using del_single_cont[of x mi ma deg treeList summary] "1" "8" "9" True deg_not_0 div_greater_zero_iff "12" by fastforce
      moreover have  " (\<nexists> i. both_member_options summary i)"
        using "10" True mi_eq_ma_no_ch by blast
      ultimately  show ?thesis 
        using "0" "1" "2" "3" "8" invar_vebt.intros(3) by force
    next
      case False
      hence "x \<noteq> mi \<or> x \<noteq> ma" by simp
      hence "mi \<noteq> ma \<and> x < 2^deg" 
        by (metis "6" inrg le_antisym le_less_trans)
      hence "7b": "(\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
               (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma))"
        using "7" by fastforce 
      hence "both_member_options (treeList ! (high ma n)) (low ma n)" 
        by (metis "1" "12" "3" "6" "9" deg_not_0 div_greater_zero_iff exp_split_high_low(1) zero_less_numeral)
      hence yhelper:"both_member_options (treeList ! (high y n)) (low y n) 
                  \<Longrightarrow> high y n < 2^m \<Longrightarrow> mi < y \<and> y \<le> ma \<and> low y n < 2^n" for y 
        by (simp add: "7b" low_def) 
      then show ?thesis  
      proof(cases "x \<noteq> mi")
        case True
        hence xnotmi: "x \<noteq> mi" by simp
        let ?h = "high x n" 
        let ?l = "low x n"
        have hlbound:"?h < 2^m \<and> ?l < 2^n"
          by (metis "1" "11" "3" One_nat_def \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> deg_not_0 dual_order.strict_trans1 exp_split_high_low(1) exp_split_high_low(2) zero_less_Suc)
        let ?newnode = "vebt_delete (treeList ! ?h) ?l"
        have "treeList ! ?h \<in> set treeList " 
          by (metis "2" hlbound in_set_member inthall)
        hence nnvalid: "invar_vebt ?newnode n" 
          by (simp add: "5.IH"(1))
        let ?newlist = "treeList[?h:= ?newnode]"
        have hlist:"?newlist ! ?h = ?newnode" 
          by (simp add: "2" hlbound)
        have nothlist:"i \<noteq> ?h \<Longrightarrow> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        have allvalidinlist:"\<forall> t \<in> set ?newlist. invar_vebt t n"
        proof
          fix t 
          assume "t \<in> set ?newlist"
          then obtain i where "i< 2^m \<and> ?newlist ! i = t" 
            by (metis "2" in_set_conv_nth length_list_update)
          then  show "invar_vebt t n" 
            by (metis "0" "2" hlist nnvalid nth_list_update_neq nth_mem)
        qed
        have newlistlength: "length ?newlist = 2^m" 
          by (simp add: "2")
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence ninNullc: "minNull ?newnode" by simp
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
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_not_mi_new_node_nil[of mi x ma deg ?h ?l ?newnode treeList ?sn summary ?newlist]
              hlbound 9 11 12 True 2 inrg xnotmi by simp
          have newsummvalid: "invar_vebt ?sn m"
            by (simp add: "5.IH"(2))
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options ?sn i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hlist by blast
                hence  1001:"\<nexists> x. vebt_member (?newlist ! i) x" 
                  by (simp add: min_Null_member ninNullc)
                hence 1002: "\<nexists> x. both_member_options (?newlist ! i) x"
                  using "1000" nnvalid valid_member_both_member_options by auto
                have 1003: "\<not> both_member_options ?sn i" 
                  using "1" True dele_bmo_cont_corr by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothlist by blast
                hence "both_member_options (?newlist ! i) y \<Longrightarrow> both_member_options ?sn i" for y 
                  by (metis "1" "4" False \<open>i < 2 ^ m\<close> dele_bmo_cont_corr)
                moreover have "both_member_options ?sn i \<Longrightarrow> \<exists> y. both_member_options (?newlist ! i) y" 
                  using "1" "4" \<open>i < 2 ^ m\<close> dele_bmo_cont_corr by force               
                then show ?thesis 
                  using calculation by blast
              qed
            qed
          qed
          have 112:" (mi = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"mi = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "x = ma")
              case True
              let ?maxs = "vebt_maxt ?sn" 
              show ?thesis
              proof(cases "?maxs = None")
                case True
                hence aa:"\<nexists> y. vebt_member ?sn y" 
                  using maxt_corr_help_empty newsummvalid set_vebt'_def by auto
                hence "\<nexists> y. both_member_options ?sn y"
                  using newsummvalid valid_member_both_member_options by blast
                hence "t \<in> set ?newlist \<Longrightarrow> \<nexists>y. both_member_options t y" for t 
                proof-
                  assume "t \<in> set ?newlist"
                  then obtain i where "?newlist ! i = t \<and> i< 2^m" 
                    by (metis in_set_conv_nth newlistlength)
                  thus " \<nexists>y. both_member_options t y"
                    using "111" \<open>\<nexists>y. both_member_options (vebt_delete summary (high x n)) y\<close> by blast
                qed
                then show ?thesis by blast
              next
                case False
                then obtain maxs where "Some maxs = ?maxs"
                  by fastforce
                hence "both_member_options summary maxs" 
                  by (metis "1" dele_bmo_cont_corr maxbmo)
                have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                  by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                hence "invar_vebt (?newlist ! maxs) n"using 0
                  by (metis allvalidinlist newlistlength nth_mem)
                hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                  using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"  
                  by (metis Collect_empty_eq_bot \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> bb bot_empty_eq equals0D maxt_corr_help_empty nth_list_update_neq option_shift.elims set_vebt'_def valid_member_both_member_options)
                hence "maxs = high mi n \<and> both_member_options (?newlist ! maxs) (low mi n)"
                  by (smt (z3) "9" False True \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> aampt option.sel high_inv low_inv maxbmo maxt_member member_bound mult.commute)
                hence False 
                  by (metis bb nat_less_le nothlist yhelper)
                then show ?thesis by simp
              qed
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed
          have 114: "?newma < 2^deg \<and> mi \<le> ?newma" 
          proof(cases "x = ma")
            case True
            hence "x = ma" by simp
            let ?maxs = "vebt_maxt ?sn"
            show ?thesis 
            proof(cases "?maxs = None")
              case True
              then show ?thesis 
                using "6" by fastforce
            next
              case False
              then obtain maxs where "Some maxs = ?maxs"
                by fastforce
              hence "both_member_options summary maxs" 
                by (metis "1" dele_bmo_cont_corr maxbmo)
              have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
              hence "invar_vebt (?newlist ! maxs) n"using 0 
                by (metis allvalidinlist newlistlength nth_mem)
              hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
              then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                by (smt (z3) VEBT_Member.vebt_member.simps(2) \<open>invar_vebt (?newlist ! maxs) n\<close> vebt_maxt.elims minNull.simps(1) min_Null_member valid_member_both_member_options)
              then show ?thesis 
                by (smt (verit, best) "6" "9" \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> bb option.sel high_inv less_le_trans low_inv maxbmo maxt_member member_bound mult.commute not_less_iff_gr_or_eq nothlist verit_comp_simplify1(3) yhelper)
            qed
          next
            case False
            then show ?thesis 
              using "6" by auto
          qed 
          have 115: "mi \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
          proof
            assume "mi \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "x = ma" )
                      case True
                      let ?maxs = "vebt_maxt ?sn"
                      show ?thesis
                      proof(cases "?maxs = None")
                        case True
                        then show ?thesis
                          by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>mi \<noteq> (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (?newlist ! the maxs)) else ma)\<close> \<open>treeList ! high x n \<in> set treeList\<close> assumption bit_split_inv dele_bmo_cont_corr hlist newmaassm nothlist)
                      next
                        case False
                        then obtain maxs where "Some maxs = ?maxs"
                          by fastforce
                        hence "both_member_options summary maxs" 
                          by (metis "1" dele_bmo_cont_corr maxbmo)
                        have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                          by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                        hence "invar_vebt (?newlist ! maxs) n"using 0 "2" by auto
                        hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                          using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                        then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                          by (smt (z3) VEBT_Member.vebt_member.simps(2) \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> vebt_maxt.elims minNull.simps(1) min_Null_member valid_member_both_member_options)
                        then show ?thesis 
                          by (smt (z3) "9" True \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> option.sel high_inv low_inv maxbmo maxt_member member_bound mult.commute newmaassm option.distinct(1))
                      qed
                    next
                      case False
                      then show  ?thesis 
                        by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>treeList ! high x n \<in> set treeList\<close> assumption bit_split_inv dele_bmo_cont_corr hlist newmaassm nothlist)
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "mi < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)" 
                          using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr hlist yassm by auto
                        then show ?thesis 
                          by (simp add: assumption yassm yhelper)
                      next
                        case False
                        then show ?thesis 
                          using assumption nothlist yassm yhelper by presburger
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "x = ma")
                        case True
                        hence "x= ma" by simp
                        let ?maxs = "vebt_maxt ?sn"
                        show ?thesis 
                        proof(cases "?maxs = None")
                          case True
                          then show ?thesis 
                            using \<open>mi \<noteq> ?newma\<close> \<open>x = ma\<close> by presburger
                        next
                          case False
                          then obtain maxs where "Some maxs = ?maxs"
                            by fastforce
                          hence "both_member_options summary maxs" 
                            by (metis "1" dele_bmo_cont_corr maxbmo)
                          have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                            by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                          hence "invar_vebt (?newlist ! maxs) n"using 0  "2" by fastforce
                          hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                            using "4" bb \<open>both_member_options summary maxs\<close> nothlist by presburger
                          then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                            by (metis \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> equals0D maxt_corr_help_empty mem_Collect_eq option_shift.elims set_vebt'_def valid_member_both_member_options)
                          hence "maxs < 2^m \<and> maxi < 2^n" 
                            by (metis \<open>invar_vebt (?newlist ! maxs) n\<close> bb maxt_member member_bound)
                          hence "?newma = 2^n* maxs + maxi" 
                            by (smt (z3) "9" False True \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> option.sel)
                          hence "low ?newma n = maxi \<and> high  ?newma n = maxs"
                            by (simp add: \<open>maxs < 2 ^ m \<and> maxi < 2 ^ n\<close> high_inv low_inv mult.commute)
                          hence "both_member_options (treeList ! (high y n)) (low y n)" 
                            by (metis "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm)
                          hence hleqdraft:"high y n > maxs \<Longrightarrow> False" 
                          proof-
                            assume "high y n > maxs"
                            have "both_member_options summary (high y n)" 
                              using "1" "111" assumption dele_bmo_cont_corr yassm by blast
                            moreover have "both_member_options ?sn (high y n)" 
                              using "111" assumption yassm by blast
                            ultimately show False 
                              by (metis \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>maxs < high y n\<close> leD maxt_corr_help newsummvalid valid_member_both_member_options)
                          qed
                          hence hleqmaxs: "high y n \<le> maxs" by presburger
                          then show ?thesis
                          proof(cases "high y n = maxs")
                            case True
                            hence "low y n \<le> maxi" 
                              by (metis \<open>Some maxi = vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs)\<close> \<open>invar_vebt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! maxs) n\<close> maxt_corr_help valid_member_both_member_options yassm)
                            then show ?thesis 
                              by (smt (z3) True \<open>(if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma) = 2 ^ n * maxs + maxi\<close> add_le_cancel_left bit_concat_def bit_split_inv mult.commute)
                          next
                            case False
                            then show ?thesis
                              by (smt (z3) \<open>low (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma) n = maxi \<and> high (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma) n = maxs\<close> div_le_mono high_def hleqmaxs le_antisym nat_le_linear)
                          qed
                        qed
                      next
                        case False
                        then show ?thesis 
                          by (smt (z3) "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm yhelper)
                      qed
                      ultimately show " mi < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "mi \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (mi, ?newma)) deg ?newlist ?sn) deg"
            using invar_vebt.intros(5)[of ?newlist n ?sn m deg mi ?newma] 
            using 3 allvalidinlist newlistlength newsummvalid  "5.hyps"(3) 111 112 118 117 115 by fastforce
          show ?thesis
            using "116" dsimp by presburger
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist summary)" 
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp"
            using del_x_not_mi_newnode_not_nil[of mi x ma deg ?h ?l ?newnode treeList ?newlist summary]
            by (metis "12" "2" "9" False dual_order.eq_iff hlbound inrg order.not_eq_order_implies_strict xnotmi)
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options summary i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hlist by blast
                hence  1001:"\<exists> x. vebt_member (?newlist ! i) x" 
                  using nnvalid notemp valid_member_both_member_options by auto
                hence 1002: "\<exists> x. both_member_options (?newlist ! i) x" 
                  using "1000" notemp by presburger
                have 1003: "both_member_options summary i"
                  using "0" "1000" "1002" "4" True \<open>i < 2 ^ m\<close> \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by fastforce
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothlist by blast              
                then show ?thesis
                  using "4" \<open>i < 2 ^ m\<close> by presburger
              qed
            qed
          qed
          have 112:" (mi = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"mi = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "x = ma")
              case True 
              obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
                by (metis False VEBT_Member.vebt_member.simps(2) hlist vebt_maxt.elims minNull.simps(1) nnvalid notemp valid_member_both_member_options)
              hence "both_member_options ?newnode maxi" 
                using hlist maxbmo by auto
              hence "both_member_options (treeList ! ?h) maxi" 
                using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by blast
              hence False 
                by (metis "9" True \<open>both_member_options ?newnode maxi\<close> \<open>vebt_maxt ( ?newlist ! high x n) = Some maxi\<close> aampt option.sel high_inv hlbound low_inv member_bound nnvalid not_less_iff_gr_or_eq valid_member_both_member_options yhelper)       
              then show ?thesis by blast
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed   
          have 114: "?newma < 2^deg \<and> mi \<le> ?newma" 
          proof(cases "x = ma")
            case True
            hence "x = ma" by simp
            obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
              by (metis False VEBT_Member.vebt_member.simps(2) hlist vebt_maxt.elims minNull.simps(1) nnvalid notemp valid_member_both_member_options)
            hence "both_member_options ?newnode maxi" 
              using hlist maxbmo by auto
            hence "both_member_options (treeList ! ?h) maxi" 
              using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr by blast
            hence "maxi < 2^n"
              using \<open>both_member_options?newnode maxi\<close> member_bound nnvalid valid_member_both_member_options by blast
            show ?thesis
              by (smt (z3) "3" "9" div_eq_0_iff True \<open>both_member_options (treeList ! high x n) maxi\<close> \<open>maxi < 2 ^ n\<close> \<open>vebt_maxt ( ?newlist ! high x n) = Some maxi\<close> add.right_neutral div_exp_eq div_mult_self3 option.sel high_inv hlbound le_0_eq less_imp_le_nat low_inv power_not_zero rel_simps(28) yhelper)
          next
            case False
            then show ?thesis 
              using "6" by auto
          qed 
          have 115: "mi \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
          proof
            assume "mi \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "x = ma")
                      case True
                      obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                        by (metis Collect_empty_eq both_member_options_equiv_member hlist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                      hence "both_member_options (?newlist ! ?h) maxi" 
                        using maxbmo by blast
                      then show ?thesis
                        by (smt (z3) "9" True \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> option.sel high_inv hlist low_inv maxt_member member_bound newmaassm nnvalid)
                    next
                      case False
                      then show ?thesis 
                        by (smt (z3) "0" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>treeList ! high x n \<in> set treeList\<close> assumption bit_split_inv dele_bmo_cont_corr hlist newmaassm nothlist)
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "mi < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)" 
                          using "0" \<open>treeList ! high x n \<in> set treeList\<close> dele_bmo_cont_corr hlist yassm by auto
                        then show ?thesis 
                          by (simp add: assumption yassm yhelper)
                      next
                        case False
                        then show ?thesis 
                          using assumption nothlist yassm yhelper by presburger
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "x = ma")
                        case True
                        hence "x= ma" by simp
                        obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                          by (metis Collect_empty_eq both_member_options_equiv_member hlist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                        hence "both_member_options (?newlist ! ?h) maxi" 
                          using maxbmo by blast
                        have "high y n \<le> ?h" 
                          by (metis "7b" True assumption div_le_mono high_def nothlist yassm)
                        then show ?thesis
                        proof(cases "high y n = ?h")
                          case True
                          have "low y n > maxi \<Longrightarrow> False" 
                            by (metis True \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> hlist leD maxt_corr_help nnvalid valid_member_both_member_options yassm) 
                          then show ?thesis 
                            by (smt (z3) "9" True \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> \<open>x = ma\<close> add_le_cancel_left div_mult_mod_eq option.sel high_def low_def nat_le_linear nat_less_le)
                        next
                          case False
                          then show ?thesis 
                            by (smt (z3) "9" True \<open>both_member_options (?newlist ! high x n) maxi\<close> \<open>high y n \<le> high x n\<close> \<open>vebt_maxt (?newlist ! high x n) = Some maxi\<close> div_le_mono option.sel high_def high_inv hlist le_antisym member_bound nat_le_linear nnvalid valid_member_both_member_options)
                        qed                     
                      next
                        case False
                        then show ?thesis 
                          by (smt (z3) "0" \<open>treeList ! high x n \<in> set treeList\<close> assumption dele_bmo_cont_corr hlist nothlist yassm yhelper)
                      qed
                      ultimately show " mi < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "mi \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (mi, ?newma)) deg ?newlist summary) deg"
            using invar_vebt.intros(5)[of ?newlist n summary m deg mi ?newma] allvalidinlist 
              1 newlistlength  8 3 111 112 117 118 115 by fastforce
          then show ?thesis
            using dsimp by presburger
        qed
      next
        case False
        hence xmi:"x = mi" by simp
        have "both_member_options summary (high ma n)" 
          by (metis "1" "11" "3" "4" "6" One_nat_def Suc_le_eq \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> deg_not_0 exp_split_high_low(1))
        hence "vebt_member summary (high ma n)" 
          using "5.hyps"(1) valid_member_both_member_options by blast
        obtain summin where "Some summin = vebt_mint summary" 
          by (metis "5.hyps"(1) \<open>vebt_member summary (high ma n)\<close> empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def)
        hence "\<exists> z . both_member_options (treeList ! summin) z"
          by (metis "5.hyps"(1) "5.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        moreover have "invar_vebt (treeList ! summin) n" 
          by (metis "0" "1" "2" \<open>Some summin = vebt_mint summary\<close> member_bound mint_member nth_mem)
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
          by (metis "12" "2" "9" \<open>invar_vebt (treeList ! summin) n\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree high_inv low_inv member_bound numeral_2_eq_2 plus_1_eq_Suc)
        let ?h ="high ?xn n"
        let ?l = "low ?xn n"
        have "?xn < 2^deg"
          by (smt (verit, ccfv_SIG) "5.hyps"(1) "5.hyps"(4) div_eq_0_iff \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>invar_vebt (treeList ! summin) n\<close> div_exp_eq high_def high_inv le_0_eq member_bound mint_member not_numeral_le_zero power_not_zero)
        hence "?h < length treeList" 
          using "2" \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
        let ?newnode = "vebt_delete (treeList ! ?h) ?l" 
        let ?newlist = "treeList[?h:= ?newnode]"
        have "length treeList = length ?newlist" by auto
        hence hprolist: "?newlist ! ?h = ?newnode"
          by (meson \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> nth_list_update_eq)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by auto
        have hlbound:"?h < 2^m \<and> ?l < 2^n" 
          using "2" \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> low_inv member_bound by presburger
        hence nnvalid: "invar_vebt ?newnode n"
          by (metis "5.IH"(1) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> inthall member_def)
        have allvalidinlist:"\<forall> t \<in> set ?newlist. invar_vebt t n"
        proof
          fix t 
          assume "t \<in> set ?newlist"
          then obtain i where "i < 2^m \<and> ?newlist ! i = t" 
            by (metis "2" in_set_conv_nth length_list_update)
          then  show "invar_vebt t n" 
            by (metis "0" "2" hprolist nnvalid nth_list_update_neq nth_mem)
        qed
        have newlistlength: "length ?newlist = 2^m"
          by (simp add: "2")
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          hence ninNullc: "minNull ?newnode" by simp
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if ?xn  = ma then (let maxs = vebt_maxt ?sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist ?sn)" 
          have dsimp:"vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_mi_lets_in_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist ?sn] 
            by (metis "12" "9" \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x = mi\<close> \<open>x \<noteq> mi \<or> x \<noteq> ma\<close> inrg nat_less_le ninNullc)
          have newsummvalid: "invar_vebt ?sn m"
            by (simp add: "5.IH"(2))
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options ?sn i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options ?sn i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode"
                  using hprolist by fastforce
                hence  1001:"\<nexists> x. vebt_member (?newlist ! i) x" 
                  by (simp add: min_Null_member ninNullc)
                hence 1002: "\<nexists> x. both_member_options (?newlist ! i) x"
                  using "1000" nnvalid valid_member_both_member_options by auto
                have 1003: "\<not> both_member_options ?sn i" 
                  using "1" True dele_bmo_cont_corr by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i" 
                  using \<open>i < 2 ^ m\<close> nothprolist by blast
                hence "both_member_options (?newlist ! i) y \<Longrightarrow> both_member_options ?sn i" for y 
                  using "1" "4" False \<open>i < 2 ^ m\<close> dele_bmo_cont_corr by auto              
                moreover have "both_member_options ?sn i \<Longrightarrow> \<exists> y. both_member_options (?newlist ! i) y" 
                proof-
                  assume "both_member_options ?sn i "
                  hence "both_member_options summary i"
                    using "1" dele_bmo_cont_corr by auto
                  thus " \<exists> y. both_member_options (?newlist ! i) y"
                    using "1000" "4" \<open>i < 2 ^ m\<close> by presburger
                qed
                then show ?thesis 
                  using calculation by blast
              qed
            qed
          qed
          have 112:" (?xn = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"?xn = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)" 
            proof(cases "?xn = ma")
              case True
              let ?maxs = "vebt_maxt ?sn" 
              show ?thesis
              proof(cases "?maxs = None")
                case True
                hence aa:"\<nexists> y. vebt_member ?sn y" 
                  using maxt_corr_help_empty newsummvalid set_vebt'_def by auto
                hence "\<nexists> y. both_member_options ?sn y"
                  using newsummvalid valid_member_both_member_options by blast
                hence "t \<in> set ?newlist \<Longrightarrow> \<nexists>y. both_member_options t y" for t 
                proof-
                  assume "t \<in> set ?newlist"
                  then obtain i where "?newlist ! i = t \<and> i< 2^m" 
                    by (metis "2" \<open>length treeList = length (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)])\<close> in_set_conv_nth)
                  thus " \<nexists>y. both_member_options t y" 
                    using "111" \<open>\<nexists>y. both_member_options (vebt_delete summary (high (summin * 2 ^ n + lx) n)) y\<close> by blast
                qed
                then show ?thesis by blast
              next
                case False
                then obtain maxs where "Some maxs = ?maxs"
                  by fastforce
                hence "both_member_options summary maxs" 
                  by (metis "1" dele_bmo_cont_corr maxbmo)
                have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                  by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                hence "invar_vebt (?newlist ! maxs) n"using 0
                  by (simp add: "2" allvalidinlist)
                hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                  using "4" bb \<open>both_member_options summary maxs\<close> nothprolist by presburger
                then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                  by (smt (z3) VEBT_Member.vebt_member.simps(2) \<open>invar_vebt (?newlist ! maxs) n\<close> vebt_maxt.elims minNull.simps(1) min_Null_member valid_member_both_member_options)
                hence "maxs = high ?xn n \<and> both_member_options (?newlist ! maxs) (low ?xn n)"
                  by (smt (z3) "9" False True \<open>Some maxs = vebt_maxt (vebt_delete summary ?h)\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> aampt option.sel high_inv low_inv maxbmo maxt_member member_bound mult.commute)
                hence False 
                  using bb by blast
                then show ?thesis by simp
              qed
            next
              case False
              hence "?xn \<noteq> ?newma" by simp
              hence False using aampt by simp
              then show ?thesis by blast
            qed
          qed
          have 114: "?newma < 2^deg \<and> ?xn \<le> ?newma" 
          proof(cases "?xn = ma")
            case True
            hence "?xn = ma" by simp
            let ?maxs = "vebt_maxt ?sn"
            show ?thesis 
            proof(cases "?maxs = None")
              case True
              then show ?thesis 
                using "5.hyps"(8) \<open>?xn = ma\<close> by force
            next
              case False
              then obtain maxs where "Some maxs = ?maxs"
                by fastforce
              hence "both_member_options summary maxs" 
                by (metis "1" dele_bmo_cont_corr maxbmo)
              have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
              hence "invar_vebt (?newlist ! maxs) n"using 0   by (simp add: "2" allvalidinlist)
              hence "\<exists> y. both_member_options (?newlist ! maxs) y" 
                using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
              then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"
                using \<open>invar_vebt (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs) n\<close> maxt_corr_help_empty set_vebt'_def valid_member_both_member_options by fastforce
              hence abc:"?newma = 2^n * maxs + maxi" 
                by (smt (z3) "9" True \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> option.sel not_None_eq)
              have abd:"maxi < 2^n" 
                by (metis \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> maxt_member member_bound)
              have "high ?xn n \<le> maxs"
                using "1" \<open>Some summin = vebt_mint summary\<close> \<open>both_member_options summary maxs\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound mint_corr_help valid_member_both_member_options by force
              then show ?thesis 
              proof(cases "high ?xn n = maxs")
                case True
                then show ?thesis
                  using bb by fastforce
              next
                case False
                hence "high ?xn n < maxs" 
                  by (simp add: \<open>high (summin * 2 ^ n + lx) n \<le> maxs\<close> order.not_eq_order_implies_strict)
                hence "?newma < 2^deg" 
                  by (smt (z3) "5.hyps"(8) "9" \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> \<open>invar_vebt (?newlist ! maxs) n\<close> abd bb both_member_options_equiv_member option.sel high_inv less_le_trans low_inv maxt_member mult.commute nothprolist verit_comp_simplify1(3) yhelper)
                moreover have "high ?xn n < high ?newma n" 
                  by (smt (z3) "9" True \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> \<open>high (summin * 2 ^ n + lx) n < maxs\<close> abd option.sel high_inv mult.commute option.discI)
                ultimately show ?thesis
                  by (metis div_le_mono high_def linear not_less)
              qed
            qed
          next
            case False
            then show ?thesis 
              by (smt (z3) "12" "5.hyps"(7) "5.hyps"(8) "9" both_member_options_from_complete_tree_to_child dual_order.trans hlbound one_le_numeral xnin yhelper)
          qed 
          have 115: "?xn \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
          proof
            assume assumption0:"?xn \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "?xn = ma" )
                      case True
                      hence bb:"?xn = ma" by simp
                      let ?maxs = "vebt_maxt ?sn"
                      show ?thesis
                      proof(cases "?maxs = None")
                        case True
                        hence "?newma = ?xn"  using assumption Let_def bb by simp
                        hence False using assumption0 by simp
                        then show ?thesis by simp
                      next
                        case False
                        then obtain maxs where "Some maxs = ?maxs"
                          by fastforce
                        hence "both_member_options summary maxs" 
                          by (metis "1" dele_bmo_cont_corr maxbmo)
                        have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                          by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                        hence "invar_vebt (?newlist ! maxs) n"using 0 by (simp add: "2" allvalidinlist)
                        hence "\<exists> y. both_member_options (?newlist ! maxs) y"
                          using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
                        then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)" 
                          using \<open>invar_vebt (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! maxs) n\<close> maxt_corr_help_empty set_vebt'_def valid_member_both_member_options by fastforce
                        then show ?thesis 
                          by (metis "1" "10" "9" True \<open>Some summin = vebt_mint summary\<close> \<open>both_member_options summary maxs\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> \<open>invar_vebt (treeList ! summin) n\<close> bb equals0D high_inv le_antisym maxt_corr_help maxt_corr_help_empty mem_Collect_eq member_bound mint_corr_help option.collapse summaxma set_vebt'_def valid_member_both_member_options)

                      qed
                    next
                      case False
                      hence ccc:"?newma = ma" by simp
                      then show  ?thesis
                      proof(cases "?xn = ma")
                        case True
                        hence "?xn = ?newma"
                          using False by blast
                        hence False
                          using False by auto
                        then show ?thesis by simp
                      next
                        case False
                        hence "both_member_options (?newlist ! high ma n) (low ma n)" 
                          by (metis "1" \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>vebt_member summary (high ma n)\<close> \<open>invar_vebt (treeList ! summin) n\<close> bit_split_inv dele_bmo_cont_corr high_inv hprolist member_bound nothprolist)
                        moreover have "high ma n = i \<and> low ma n = low ?newma n" using ccc newmaassm by simp
                        ultimately show ?thesis by simp
                      qed
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)" 
                  proof
                    fix y 
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "?xn < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)"
                          using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by auto
                        then show ?thesis 
                          using True hprolist min_Null_member ninNullc nnvalid valid_member_both_member_options yassm by fastforce
                      next
                        case False
                        hence "i \<le> ?h \<Longrightarrow> False"
                          by (metis "1" "111" \<open>Some summin = vebt_mint summary\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption dele_bmo_cont_corr high_inv le_antisym member_bound mint_corr_help valid_member_both_member_options yassm)
                        hence "i > ?h" 
                          using leI by blast
                        then show ?thesis
                          by (metis div_le_mono high_def not_less yassm)
                      qed
                      moreover have "y \<le> ?newma"
                      proof(cases "?xn = ma")
                        case True
                        hence "?xn= ma" by simp
                        let ?maxs = "vebt_maxt ?sn"
                        show ?thesis 
                        proof(cases "?maxs = None")
                          case True
                          then show ?thesis
                            using "1" "111" assumption dele_bmo_cont_corr nothprolist yassm yhelper by auto
                        next
                          case False
                          then obtain maxs where "Some maxs = ?maxs"
                            by fastforce
                          hence "both_member_options summary maxs" 
                            by (metis "1" dele_bmo_cont_corr maxbmo)
                          have bb:"maxs \<noteq> ?h \<and> maxs < 2^m" 
                            by (metis "1" \<open>Some maxs = vebt_maxt ?sn\<close> dele_bmo_cont_corr maxbmo member_bound valid_member_both_member_options) 
                          hence "invar_vebt (?newlist ! maxs) n"using 0  by (simp add: "2" allvalidinlist)
                          hence "\<exists> y. both_member_options (?newlist ! maxs) y" 
                            using "4" \<open>both_member_options summary maxs\<close> bb nothprolist by presburger
                          then obtain maxi where "Some maxi = vebt_maxt (?newlist ! maxs)"
                            by (metis True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption calculation dele_bmo_cont_corr high_inv hprolist leD member_bound nth_list_update_neq yassm yhelper)
                          hence "maxs < 2^m \<and> maxi < 2^n" 
                            by (metis \<open>invar_vebt (?newlist ! maxs) n\<close> bb maxt_member member_bound)
                          hence "?newma = 2^n* maxs + maxi" 
                            by (smt (z3) "9" False True \<open>Some maxi = vebt_maxt (?newlist ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high ?xn n))\<close> option.sel)
                          hence "low ?newma n = maxi \<and> high  ?newma n = maxs"
                            by (simp add: \<open>maxs < 2 ^ m \<and> maxi < 2 ^ n\<close> high_inv low_inv mult.commute)
                          hence "both_member_options (treeList ! (high y n)) (low y n)" 
                            by (metis "1" "111" assumption dele_bmo_cont_corr nothprolist yassm)
                          hence hleqdraft:"high y n > maxs \<Longrightarrow> False" 
                          proof-
                            assume "high y n > maxs"
                            have "both_member_options summary (high y n)" 
                              using "1" "111" assumption dele_bmo_cont_corr yassm by blast
                            moreover have "both_member_options ?sn (high y n)" 
                              using "111" assumption yassm by blast
                            ultimately show False
                              using True \<open>both_member_options (treeList ! high y n) (low y n)\<close> \<open>summin * 2 ^ n + lx < y\<close> assumption leD yassm yhelper by blast
                          qed
                          hence hleqmaxs: "high y n \<le> maxs" by presburger                     
                          then show ?thesis 
                            using \<open>both_member_options (treeList ! high y n) (low y n)\<close> assumption calculation dual_order.strict_trans1 yassm yhelper by auto
                        qed
                      next
                        case False
                        then show ?thesis
                          by (smt (z3) \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption dele_bmo_cont_corr high_inv hprolist member_bound nothprolist yassm yhelper)
                      qed
                      ultimately show " ?xn < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "?xn \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (?xn, ?newma)) deg ?newlist ?sn) deg"
            using invar_vebt.intros(5)[of ?newlist n ?sn m deg ?xn ?newma] 
            using 3 allvalidinlist newlistlength newsummvalid  "5.hyps"(3) 111 112 118 117 115 by fastforce
          show ?thesis
            using "116" dsimp by presburger
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist summary)" 
          have dsimp:"vebt_delete (Node (Some (x, ma)) deg treeList summary) x = ?delsimp" 
            using del_x_mi_lets_in_not_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist] 
              "12" "2" "9" False dual_order.eq_iff hlbound inrg order.not_eq_order_implies_strict xmi 
            by (metis \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x \<noteq> mi \<or> x \<noteq> ma\<close>)
          have 111: "(\<forall> i < 2^m. (\<exists> x. both_member_options (?newlist ! i) x) \<longleftrightarrow> ( both_member_options summary i))" 
          proof
            fix i
            show " i < 2^m \<longrightarrow> ((\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i))" 
            proof
              assume "i < 2^m" 
              show "(\<exists> x. both_member_options (?newlist ! i) x) = ( both_member_options summary i)"
              proof(cases "i = ?h")
                case True
                hence 1000:"?newlist ! i = ?newnode" 
                  using hprolist by blast
                hence  1001:"\<exists> x. vebt_member (?newlist ! i) x" 
                  using nnvalid notemp valid_member_both_member_options by auto
                hence 1002: "\<exists> x. both_member_options (?newlist ! i) x" 
                  using "1000" notemp by presburger
                have 1003: "both_member_options summary i" 
                  using "4" True \<open>\<exists>z. both_member_options (treeList ! summin) z\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by auto
                then show ?thesis 
                  using "1002" by blast
              next
                case False
                hence 1000:"?newlist ! i = treeList ! i"
                  using \<open>i < 2 ^ m\<close> nothprolist by blast              
                then show ?thesis
                  using "4" \<open>i < 2 ^ m\<close> by presburger
              qed
            qed
          qed
          have 112:" (?xn = ?newma \<longrightarrow> (\<forall> t \<in> set ?newlist. \<nexists> x. both_member_options t x))" 
          proof
            assume aampt:"?xn = ?newma"
            show "(\<forall> t \<in> set ?newlist. \<nexists> y. both_member_options t y)"
            proof(cases "?xn = ma")
              case True 
              obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
                by (metis Collect_empty_eq False hprolist maxt_corr_help_empty nnvalid not_None_eq not_min_Null_member set_vebt'_def valid_member_both_member_options)
              hence "both_member_options ?newnode maxi" 
                using hprolist maxbmo by auto
              hence "both_member_options (treeList ! ?h) maxi"
                using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv member_bound by force
              hence False 
                by (metis "9" \<open>both_member_options (vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)) maxi\<close> \<open>vebt_maxt (?newlist ! ?h) = Some maxi\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> aampt add_diff_cancel_left' dele_bmo_cont_corr option.sel high_inv low_inv member_bound)
              then show ?thesis by blast
            next
              case False
              then show ?thesis 
                using \<open>mi \<noteq> ma \<and> x < 2 ^ deg\<close> aampt by presburger
            qed
          qed   
          have 114: "?newma < 2^deg \<and> ?xn \<le> ?newma" 
          proof(cases "?xn = ma")
            case True
            hence "?xn = ma" by simp
            obtain maxi where " vebt_maxt (?newlist ! ?h) = Some maxi" 
              by (metis "111" "2" "4" Collect_empty_eq True \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> hprolist maxt_corr_help_empty nnvalid not_None_eq set_vebt'_def valid_member_both_member_options)
            hence "both_member_options ?newnode maxi" 
              using hprolist maxbmo by auto
            hence "both_member_options (treeList ! ?h) maxi" 
              using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv member_bound by force
            hence "maxi < 2^n"
              using \<open>both_member_options?newnode maxi\<close> member_bound nnvalid valid_member_both_member_options by blast
            show ?thesis
              by (smt (verit, ccfv_threshold) "3" "9" div_eq_0_iff True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>both_member_options (treeList ! high (summin * 2 ^ n + lx) n) maxi\<close> \<open>vebt_maxt (?newlist ! high (summin * 2 ^ n + lx) n) = Some maxi\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> add.right_neutral add_left_mono div_mult2_eq div_mult_self3 option.sel high_inv hlbound le_0_eq member_bound mint_corr_help power_add power_not_zero rel_simps(28) valid_member_both_member_options)
          next
            case False
            then show ?thesis 
              using "10" "5.hyps"(8) maxt_corr_help valid_member_both_member_options xnin by force

          qed 
          have 115: "?xn \<noteq> ?newma \<longrightarrow> 
                    (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
          proof
            assume xnmassm:"?xn \<noteq> ?newma"
            show " (\<forall> i < 2^m.  
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma))"
            proof
              fix i
              show "i < 2^m \<longrightarrow> 
                    (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
              proof
                assume assumption:"i < 2^m"
                show " (high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n)) \<and>
                    (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)"
                proof-
                  have "(high ?newma n = i \<longrightarrow> both_member_options (?newlist ! i) (low ?newma n))"
                  proof
                    assume newmaassm: "high ?newma n = i"
                    thus " both_member_options (?newlist ! i) (low ?newma n)"
                    proof(cases "?xn = ma")
                      case True
                      obtain maxi where "vebt_maxt (?newlist ! ?h) = Some maxi"
                        by (metis Collect_empty_eq both_member_options_equiv_member hprolist maxt_corr_help_empty nnvalid not_Some_eq notemp set_vebt'_def) 
                      hence "both_member_options (?newlist ! ?h) maxi" 
                        using maxbmo by blast
                      then show ?thesis 
                        by (smt (z3) "2" "9" True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> add_left_mono dele_bmo_cont_corr eq_iff high_inv hprolist low_inv member_bound mint_corr_help valid_member_both_member_options yhelper)
                    next
                      case False
                      hence abcd:"?newma = ma" by simp
                      then show ?thesis 
                      proof(cases "high ma n = ?h")
                        case True
                        hence "?newlist ! high ma n = ?newnode"
                          using hprolist by presburger
                        then show ?thesis 
                        proof(cases "low ma n = ?l")
                          case True
                          hence "?newma = ?xn" 
                            by (metis "1" False \<open>?newlist ! high ma n = vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)\<close> \<open>both_member_options (treeList ! high ma n) (low ma n)\<close>
                                \<open>vebt_member (treeList ! summin) lx\<close> \<open>vebt_member summary (high ma n)\<close> \<open>invar_vebt (treeList ! summin) n\<close> bit_split_inv dele_bmo_cont_corr high_inv member_bound nothprolist)
                          hence False 
                            using False by presburger
                          then show ?thesis by simp
                        next
                          case False
                          have "both_member_options (treeList ! high ma n) (low ma n)" 
                            by (simp add: \<open>both_member_options (treeList ! high ma n) (low ma n)\<close>)
                          hence "both_member_options ?newnode (low ma n)" 
                            using False True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv member_bound by force
                          hence "both_member_options (?newlist ! high ma n) (low ma n)"
                            using True hprolist by presburger
                          then show ?thesis using abcd newmaassm by simp
                        qed
                      next
                        case False
                        hence "?newlist ! high ma n = treeList ! high ma n" 
                          using "1" \<open>vebt_member summary (high ma n)\<close> member_bound nothprolist by blast
                        moreover hence "both_member_options (treeList ! high ma n) (low ma n)" 
                          using \<open>both_member_options (treeList ! high ma n) (low ma n)\<close> by blast
                        ultimately  show ?thesis using abcd newmaassm by simp
                      qed
                    qed
                  qed
                  moreover have " (\<forall> y. (high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma)" 
                  proof
                    fix y
                    show "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  ) \<longrightarrow> ?xn < y \<and> y \<le> ?newma"
                    proof
                      assume yassm: "(high y n = i \<and> both_member_options (?newlist ! i) (low y n)  )"
                      hence "?xn < y"
                      proof(cases "i = ?h")
                        case True
                        hence "both_member_options (treeList ! i) (low y n)"
                          using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by force
                        moreover have "vebt_mint (treeList  ! i) = Some (low ?xn n)" 
                          using True \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv low_inv member_bound by presburger
                        moreover hence "low y n \<ge> low ?xn n" 
                          using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> calculation(1) high_inv member_bound mint_corr_help valid_member_both_member_options by auto
                        moreover have "low y n \<noteq> low ?xn n"
                          using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> dele_bmo_cont_corr high_inv hprolist member_bound yassm by auto
                        ultimately have "low y n > low ?xn n" by simp
                        show ?thesis 
                          by (metis True \<open>low (summin * 2 ^ n + lx) n \<le> low y n\<close> \<open>low y n \<noteq> low (summin * 2 ^ n + lx) n\<close> bit_concat_def bit_split_inv leD linorder_neqE_nat nat_add_left_cancel_less yassm)
                      next
                        case False
                        have "Some (high ?xn n) = vebt_mint summary" 
                          using \<open>Some summin = vebt_mint summary\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                        moreover hence "high y n \<ge> high ?xn n" 
                          by (metis "1" "111" assumption mint_corr_help valid_member_both_member_options yassm)
                        ultimately show ?thesis
                          by (metis False div_le_mono high_def leI le_antisym yassm)
                      qed
                      moreover have "y \<le> ?newma" 
                        by (smt (z3) \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> assumption calculation dele_bmo_cont_corr high_inv hprolist leD member_bound nothprolist yassm yhelper)                 
                      ultimately show " ?xn < y \<and> y \<le> ?newma" by simp
                    qed
                  qed            
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          hence 117: "?newma < 2^deg" and 118: "?xn \<le> ?newma" using 114 by auto
          have 116: "  invar_vebt (Node (Some (?xn, ?newma)) deg ?newlist summary) deg"
            using invar_vebt.intros(5)[of ?newlist n summary m deg ?xn ?newma] allvalidinlist 
              1 newlistlength  8 3 111 112 117 118 115 by fastforce
          hence "invar_vebt (?delsimp) deg" by simp
          moreover  obtain delsimp where 118:"delsimp = ?delsimp" by simp
          ultimately have 119:"invar_vebt delsimp deg" by simp 
          have "vebt_delete (Node (Some (x, ma)) deg treeList summary) x = delsimp" using dsimp 118 by simp
          hence "delsimp = vebt_delete (Node (Some (x, ma)) deg treeList summary) x" by simp
          then show ?thesis using 119 
            using xmi by auto
        qed
      qed
    qed
  qed
qed

corollary dele_member_cont_corr:"invar_vebt t n \<Longrightarrow> (vebt_member (vebt_delete t x) y \<longleftrightarrow> x \<noteq> y \<and> vebt_member t y)"
  by (meson both_member_options_equiv_member dele_bmo_cont_corr delete_pres_valid)

subsection \<open>Correctness with Respect to Set Interpretation\<close>
theorem delete_correct': assumes "invar_vebt t n"
  shows "set_vebt' (vebt_delete t x) = set_vebt' t - {x}" 
  using assms by(auto simp add: set_vebt'_def dele_member_cont_corr)


corollary delete_correct: assumes "invar_vebt t n"
  shows "set_vebt' (vebt_delete t x) = set_vebt t - {x}" 
  using assms delete_correct' set_vebt_set_vebt'_valid by auto

end
end
