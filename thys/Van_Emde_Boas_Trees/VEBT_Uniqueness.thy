(*by Ammer*)
theory VEBT_Uniqueness imports VEBT_InsertCorrectness VEBT_Succ VEBT_Pred VEBT_DeleteCorrectness
begin

context VEBT_internal begin

section \<open>Uniqueness Property of valid Trees\<close>
text \<open>Two valid van Emde Boas trees having equal degree number and representing the same integer set are equal.\<close>

theorem uniquetree: "invar_vebt t n \<Longrightarrow> invar_vebt s n \<Longrightarrow> set_vebt' t = set_vebt' s \<Longrightarrow> s = t"
proof(induction t n arbitrary: s rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    apply(cases "vebt_member t 0")
     apply(cases "vebt_member t 1")
      apply(cases "vebt_member t 1") 
       apply (smt (z3) "1.prems"(1) "1.prems"(2) VEBT_Member.vebt_member.simps(1) One_nat_def deg_1_Leafy deg_not_0 less_not_refl mem_Collect_eq set_vebt'_def) +
    done
next
  case (2 treeList n summary m deg)
  from 2(9) obtain treeList' summary' where sprop:"s = Node None deg treeList' summary' \<and> deg = n+m 
                \<and> length treeList' =2^m \<and> invar_vebt summary' m \<and> (\<forall> t \<in> set treeList'. invar_vebt t n) \<and>
               (\<nexists>i. both_member_options summary' i)"
    apply(cases) 
    using "2.hyps"(3) "2.hyps"(4) one_is_add apply force 
    apply (metis "2.hyps"(3) "2.hyps"(4) add_self_div_2)
    apply (metis "2.hyps"(3) "2.hyps"(4) One_nat_def add_self_div_2 div_greater_zero_iff even_Suc_div_two not_numeral_le_zero odd_add order.not_eq_order_implies_strict plus_1_eq_Suc zero_le_one zero_neq_one)
    apply (metis "2.prems"(1) "2.prems"(2) VEBT_Member.vebt_member.simps(2) Suc_1 add_leD1 add_self_div_2 both_member_options_def deg_not_0 div_greater_zero_iff empty_Collect_eq membermima.simps(4) nat_le_iff_add plus_1_eq_Suc set_vebt'_def valid_member_both_member_options)
    apply (metis "2.hyps"(3) "2.hyps"(4) add_self_div_2 div2_Suc_Suc even_Suc_div_two odd_add one_is_add plus_1_eq_Suc zero_neq_one)
    done
  from 2(9) have aa:"\<forall> t \<in> set treeList'. invar_vebt t n"   using sprop by simp
  have ac:"deg \<ge> 2" 
    by (metis "2.hyps"(3) add_self_div_2 deg_not_0 div_greater_zero_iff sprop)
  hence ab:"\<forall> t \<in> set treeList. set_vebt' t = {}" 
    by (metis "2.hyps"(6) empty_Collect_eq min_Null_member not_min_Null_member set_vebt'_def)
  hence ac:"length treeList' =length treeList"
    by (simp add: "2.hyps"(2) sprop)
  hence membercongy:"i < 2^m \<Longrightarrow> vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x" for i x 
  proof-
    assume "i < 2^m"
    show "vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x"
    proof
      show "vebt_member (treeList ! i) x \<Longrightarrow> vebt_member (treeList' ! i) x" 
        by (metis "2.hyps"(6) \<open>i < 2 ^ m\<close> ac min_Null_member not_min_Null_member nth_mem sprop)
      show "vebt_member (treeList' ! i) x \<Longrightarrow> vebt_member (treeList ! i) x" 
      proof-
        assume "vebt_member (treeList' ! i) x"
        hence "both_member_options (treeList' ! i) x" 
          by (metis \<open>i < 2 ^ m\<close> both_member_options_equiv_member nth_mem sprop)
        hence "membermima (treeList' ! i) x \<or> naive_member (treeList' ! i) x" unfolding both_member_options_def by auto
        moreover have "membermima (treeList' ! i) x \<Longrightarrow> membermima s (2^m*i+x)" 
          using membermima.simps(5)[of "deg-1" treeList' summary' "(2^m*i+x)"] sprop ac 
          apply auto
          apply (metis One_nat_def Suc_diff_1 \<open>membermima (Node None (Suc (deg - 1)) treeList' summary') (2 ^ m * i + x) = (let pos = high (2 ^ m * i + x) (Suc (deg - 1) div 2) in if pos < length treeList' then membermima (treeList' ! pos) (low (2 ^ m * i + x) (Suc (deg - 1) div 2)) else False)\<close> add.commute deg_not_0 neq0_conv not_add_less1)
          by (smt (z3) "2.hyps"(3) Nat.add_0_right Suc_pred \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> add_gr_0 add_self_div_2 deg_not_0 div_less div_mult_self4 high_def low_inv member_bound mult.commute nth_mem power_not_zero zero_neq_numeral)
        moreover have "naive_member (treeList' ! i) x \<Longrightarrow> naive_member s (2^m*i+x)" 
          using naive_member.simps(3)[of None "deg-1" treeList' summary' "(2^m*i+x)" ] sprop ac
          apply auto 
          apply (metis One_nat_def Suc_pred' \<open>naive_member (Node None (Suc (deg - 1)) treeList' summary') (2 ^ m * i + x) = (let pos = high (2 ^ m * i + x) (Suc (deg - 1) div 2) in if pos < length treeList' then naive_member (treeList' ! pos) (low (2 ^ m * i + x) (Suc (deg - 1) div 2)) else False)\<close> add_gr_0 deg_not_0)
          by (smt (z3) "2.hyps"(3) Nat.add_0_right Suc_pred \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> add_gr_0 add_self_div_2 deg_not_0 div_less div_mult_self4 high_def low_inv member_bound mult.commute nth_mem power_not_zero zero_neq_numeral)
        ultimately have "both_member_options s (2^m*i +x)" unfolding both_member_options_def by auto
        hence False 
          using "2.prems"(1) VEBT_Member.vebt_member.simps(2) sprop valid_member_both_member_options by blast
        then show ?thesis by simp
      qed
    qed
  qed
  hence ad:"i<2^m \<Longrightarrow> set_vebt' (treeList' ! i ) = {}" for i 
  proof-
    assume assm:"i < 2^m"
    show "set_vebt' (treeList' ! i ) = {}"
    proof(rule ccontr)
      assume "set_vebt' (treeList' ! i ) \<noteq> {}"
      then obtain y where "vebt_member (treeList' ! i) y" 
        using set_vebt'_def by fastforce
      thus False 
        using ab ac assm membercongy sprop set_vebt'_def by force
    qed
  qed
  hence ae:"i< 2^m \<Longrightarrow> treeList' ! i = treeList ! i"  for i 
    by (simp add: "2.IH"(1) "2.hyps"(2) ab sprop)
  then show ?case
    by (metis "2.IH"(2) "2.hyps"(1) "2.hyps"(5) ac both_member_options_equiv_member empty_Collect_eq list_eq_iff_nth_eq sprop set_vebt'_def)
next
  case (3 treeList n summary m deg)
  from 3(9) obtain treeList' summary' where sprop:"s = Node None deg treeList' summary' \<and> deg = n+m 
                        \<and> length treeList' =2^m \<and> invar_vebt summary' m \<and> (\<forall> t \<in> set treeList'. invar_vebt t n) \<and>
                       (\<nexists>i. both_member_options summary' i)"
    apply(cases) 
    apply (metis "3.IH"(1) "3.hyps"(2) "3.hyps"(3) "3.hyps"(4) One_nat_def Suc_1 not_one_le_zero one_is_add set_n_deg_not_0 zero_neq_numeral)
    apply (metis "3.hyps"(3) "3.hyps"(4) add_self_div_2 div2_Suc_Suc even_Suc_div_two odd_add plus_1_eq_Suc)
    apply (metis "3.hyps"(3) "3.hyps"(4) Suc_inject add_Suc_right add_self_div_2)
    apply (metis "3.hyps"(3) "3.hyps"(4) add_Suc_right add_self_div_2 even_Suc_div_two le_add2 le_less_Suc_eq odd_add order.strict_iff_order plus_1_eq_Suc)
    apply (metis "3.prems"(1) "3.prems"(2) VEBT_Member.vebt_member.simps(2) Suc_pred' both_member_options_def deg_not_0 mem_Collect_eq membermima.simps(4) set_vebt'_def valid_member_both_member_options)
    done
  have ac:"deg \<ge> 2"
    by (metis "3.hyps"(3) One_nat_def add_le_mono le_add1 numeral_2_eq_2 plus_1_eq_Suc set_n_deg_not_0 sprop)
  hence ab:"\<forall> t \<in> set treeList. set_vebt' t = {}" 
    by (metis "3.hyps"(6) empty_Collect_eq min_Null_member not_min_Null_member set_vebt'_def)
  hence ac:"length treeList' =length treeList"
    by (simp add: "3.hyps"(2) sprop)
  hence membercongy:"i < 2^m \<Longrightarrow> vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x" for i x 
  proof-
    assume "i < 2^m"
    show "vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x"
    proof
      show "vebt_member (treeList ! i) x \<Longrightarrow> vebt_member (treeList' ! i) x" 
        by (metis "3.hyps"(6) \<open>i < 2 ^ m\<close> ac min_Null_member not_min_Null_member nth_mem sprop)
      show "vebt_member (treeList' ! i) x \<Longrightarrow> vebt_member (treeList ! i) x" 
      proof-
        assume "vebt_member (treeList' ! i) x"
        hence "both_member_options (treeList' ! i) x" 
          by (metis \<open>i < 2 ^ m\<close> both_member_options_equiv_member nth_mem sprop)
        hence "membermima (treeList' ! i) x \<or> naive_member (treeList' ! i) x"
          unfolding both_member_options_def by auto
        moreover have "membermima (treeList' ! i) x \<Longrightarrow> membermima s (2^n*i+x)" 
          using membermima.simps(5)[of "deg-1" treeList' summary' "(2^n*i+x)"] sprop ac
          by (smt (z3) "3.hyps"(3) "3.prems"(1) Nat.add_diff_assoc Suc_pred \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> add_diff_cancel_left' add_self_div_2 deg_not_0 even_Suc high_inv le_add1 low_inv member_bound mult.commute mult_2 nth_mem odd_two_times_div_two_nat plus_1_eq_Suc)
        moreover have "naive_member (treeList' ! i) x \<Longrightarrow> naive_member s (2^n*i+x)" 
          using naive_member.simps(3)[of None "deg-1" treeList' summary' "(2^n*i+x)" ] sprop ac 
          by (smt (z3) "3.hyps"(3) "3.prems"(1) Nat.add_0_right Nat.add_diff_assoc Suc_pred \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> add_self_div_2 deg_not_0 div_less div_mult_self4 even_Suc_div_two high_def le_add1 low_inv member_bound mult.commute nth_mem odd_add plus_1_eq_Suc power_not_zero zero_neq_numeral)
        ultimately have "both_member_options s (2^n*i +x)" unfolding both_member_options_def 
          by auto
        hence False 
          using "3.prems"(1) VEBT_Member.vebt_member.simps(2) sprop valid_member_both_member_options 
          by blast
        then show ?thesis by simp
      qed
    qed
  qed
  hence ad:"i<2^m \<Longrightarrow> set_vebt' (treeList' ! i ) = {}" for i 
  proof-
    assume assm:"i < 2^m"
    show "set_vebt' (treeList' ! i ) = {}"
    proof(rule ccontr)
      assume "set_vebt' (treeList' ! i ) \<noteq> {}"
      then obtain y where "vebt_member (treeList' ! i) y" 
        using set_vebt'_def by fastforce
      thus False 
        using ab ac assm membercongy sprop set_vebt'_def by force
    qed
  qed
  hence ae:"i< 2^m \<Longrightarrow> treeList' ! i = treeList ! i"  for i 
    by (simp add: "3.IH"(1) "3.hyps"(2) ab sprop)
  then show ?case 
    by (metis "3.IH"(2) "3.hyps"(1) "3.hyps"(5) Collect_empty_eq ac both_member_options_equiv_member list_eq_iff_nth_eq sprop set_vebt'_def)
next
  case (4 treeList n summary m deg mi ma)
  note case4= this
  hence "set_vebt' (Node (Some (mi, ma)) deg treeList summary) = set_vebt' s" by simp
  hence a0:"deg \<ge> 2" using 4
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  hence aa:"{mi, ma} \<subseteq> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" 
    apply auto using vebt_member.simps(5)[of mi ma "deg -2" treeList summary mi]
    apply (metis add_2_eq_Suc' le_add_diff_inverse2 mem_Collect_eq set_vebt'_def)
    using vebt_member.simps(5)[of mi ma "deg -2" treeList summary ma]
    apply (metis add_2_eq_Suc' le_add_diff_inverse2 mem_Collect_eq set_vebt'_def)
    done
  from 4(12) obtain treeList' summary' info where sprop1:"s = Node info deg treeList' summary' \<and> deg = n+m 
                       \<and> length treeList' =2^m \<and> invar_vebt summary' m \<and> (\<forall> t \<in> set treeList'. invar_vebt t n) " 
    apply cases
    using "4.hyps"(3) "4.hyps"(4) one_is_add apply force
    apply (metis "4.hyps"(3) "4.hyps"(4) add_self_div_2)
    apply (metis "4.hyps"(3) "4.hyps"(4) even_Suc odd_add)
    apply (metis "4.hyps"(3) "4.hyps"(4) add_self_div_2)
    apply (metis "4.hyps"(3) "4.hyps"(4) even_Suc odd_add)
    done
  have  ac:"invar_vebt t h \<Longrightarrow> invar_vebt k h \<Longrightarrow> set_vebt' t = set_vebt' k \<Longrightarrow> vebt_mint t = vebt_mint k" for t k h 
  proof-
    assume assms: "invar_vebt t h" "invar_vebt k h" "set_vebt' t = set_vebt' k"
    have "\<not> vebt_mint t = vebt_mint k \<Longrightarrow> False"
    proof-
      assume "vebt_mint t \<noteq> vebt_mint k"
      then obtain a b where abdef:"vebt_mint t = None \<and> vebt_mint k = Some b \<or>
                            vebt_mint t = Some a \<and> vebt_mint k = None \<or>
                            a < b \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k \<or>
                            b < a \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k"
        by (metis linorder_neqE_nat option.exhaust)
      show False
        apply(cases "vebt_mint t = None \<and> vebt_mint k = Some b")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        apply(cases "   vebt_mint t = Some a \<and> vebt_mint k = None")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        apply (cases "a < b \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> abdef assms(1) assms(2) assms(3) mint_corr mint_sound)
        done
    qed
    thus "vebt_mint t = vebt_mint k" by auto
  qed   
  have  ad:"invar_vebt t h \<Longrightarrow> invar_vebt k h \<Longrightarrow> set_vebt' t = set_vebt' k \<Longrightarrow> vebt_maxt t = vebt_maxt k" for t k h 
  proof-
    assume assms: "invar_vebt t h" "invar_vebt k h" "set_vebt' t = set_vebt' k"
    have "\<not> vebt_maxt t = vebt_maxt k \<Longrightarrow> False"
    proof-
      assume "vebt_maxt t \<noteq> vebt_maxt k"
      then obtain a b where abdef:"vebt_maxt t = None \<and> vebt_maxt k = Some b \<or>
                            vebt_maxt t = Some a \<and> vebt_maxt k = None \<or>
                            a < b \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k \<or>
                            b < a \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k"
        by (metis linorder_neqE_nat option.exhaust)
      show False apply(cases "vebt_maxt t = None \<and> vebt_maxt k = Some b") 
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        apply(cases "   vebt_maxt t = Some a \<and> vebt_maxt k = None")
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        apply (cases "a < b \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k")
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        by (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> abdef assms(1) assms(2) assms(3) maxt_corr maxt_sound)
    qed
    thus "vebt_maxt t = vebt_maxt k" by auto
  qed
  have infsplit: "info = Some (mi ,ma)" using 4(12) 
  proof cases
    case (1 a b)
    then show ?thesis 
      using sprop1 by blast
  next
    case (2 treeList n summary m)
    then show ?thesis 
      by (metis "4.prems"(2) Collect_empty_eq VEBT_Member.vebt_member.simps(2) aa empty_iff insert_subset set_vebt'_def)
  next
    case (3 treeList n summary m)
    then show ?thesis 
      by (metis "4.prems"(2) Collect_empty_eq VEBT_Member.vebt_member.simps(2) aa empty_iff insert_subset set_vebt'_def)
  next
    case (4 treeList' n' summary' m' mi' ma')
    have "vebt_mint s = Some mi'"  
      by (simp add: "4"(1))
    hence "mi' = mi" 
      by (smt (verit, ccfv_threshold) "4.hyps"(7) "4.prems"(1) "4.prems"(2) VEBT_Member.vebt_member.simps(5) One_nat_def a0 aa add.assoc eq_iff insert_subset leI le_add_diff_inverse less_imp_le_nat mem_Collect_eq min_in_set_def mint_sound numeral_2_eq_2 option.sel order.not_eq_order_implies_strict plus_1_eq_Suc set_vebt'_def)
    have "vebt_maxt s = Some ma'"
      by (simp add: "4"(1))
    hence "ma' < ma \<Longrightarrow> ma\<notin> set_vebt' s"
      by (meson "4.prems"(1) leD max_in_set_def maxt_corr)  
    moreover have "ma < ma' \<Longrightarrow> ma' \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" using case4 
      by (metis dual_order.strict_trans2 mem_Collect_eq member_inv not_less_iff_gr_or_eq set_vebt'_def)
    ultimately have "ma'=ma" 
      by (metis \<open>vebt_maxt s = Some ma'\<close> aa case4(12) case4(13) insert_subset max_in_set_def maxt_corr not_less_iff_gr_or_eq)
    then show ?thesis 
      using "4"(1) \<open>mi' = mi\<close> sprop1 by force
  next
    case (5 treeList n summary m mi' ma')
    have "vebt_mint s = Some mi'"  
      by (simp add: "5"(1))
    hence "mi' = mi" 
      by (smt (verit, ccfv_threshold) "4.hyps"(7) "4.prems"(1) "4.prems"(2) VEBT_Member.vebt_member.simps(5) One_nat_def a0 aa add.assoc eq_iff insert_subset leI le_add_diff_inverse less_imp_le_nat mem_Collect_eq min_in_set_def mint_sound numeral_2_eq_2 option.sel order.not_eq_order_implies_strict plus_1_eq_Suc set_vebt'_def)
    have "vebt_maxt s = Some ma'"
      by (simp add: "5"(1))
    hence "ma' < ma \<Longrightarrow> ma\<notin> set_vebt' s"
      by (meson "4.prems"(1) leD max_in_set_def maxt_corr)  
    moreover have "ma < ma' \<Longrightarrow> ma' \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" using case4 
      by (metis dual_order.strict_trans2 mem_Collect_eq member_inv not_less_iff_gr_or_eq set_vebt'_def)
    ultimately have "ma'=ma" 
      by (metis "5"(5) "5"(6) case4(5) case4(6) even_Suc odd_add)
    then show ?thesis 
      using "5"(1) \<open>mi' = mi\<close> sprop1 by force
  qed 
  from 4(12) have acd:"mi \<noteq> ma \<longrightarrow>
    (\<forall>i<2 ^ m.
        (high ma n = i \<longrightarrow> both_member_options (treeList' ! i) (low ma n)) \<and>
        (\<forall>x. high x n = i \<and> both_member_options (treeList' ! i) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma))"
    apply cases using sprop1 apply simp
    using sprop1 infsplit apply simp
    using sprop1 infsplit apply simp 
    apply (metis VEBT.inject(1) add_self_div_2 case4(5) infsplit option.inject prod.inject sprop1)
    by (metis case4(5) case4(6) even_Suc odd_add)
  hence "length treeList' = 2^m" 
    using sprop1 by fastforce
  hence aca:"length treeList' =length treeList" using "4.hyps"(2) 
    by (simp add: "4.hyps"(2) sprop1)
  from 4(12) have sumtreelistcong: " \<forall>i<2 ^ m. (\<exists>x. both_member_options (treeList' ! i) x) = both_member_options summary' i"
    apply cases 
    using a0 apply linarith 
    apply (metis VEBT.inject(1) nth_mem sprop1)
    using infsplit sprop1 apply force 
    apply (metis VEBT.inject(1) sprop1)
    using sprop1 by auto
  hence membercongy:"i < 2^m \<Longrightarrow> vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x" for i x 
  proof-
    assume "i < 2^m"
    show "vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x"
    proof
      show "vebt_member (treeList ! i) x \<Longrightarrow> vebt_member (treeList' ! i) x"  
      proof-
        assume "vebt_member (treeList ! i) x"
        hence aaa:"both_member_options (treeList ! i) x"  
          by (metis \<open>i < 2 ^ m\<close> both_member_options_equiv_member case4(1) case4(4) nth_mem)
        have "x < 2^n"
          by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) x\<close> case4(1) case4(4) member_bound nth_mem)
        hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) (2^n*i+x)" 
          using both_member_options_from_chilf_to_complete_tree
            [of " (2^n*i+x)" deg treeList mi ma summary] aaa high_inv[of x n i] 
          by (smt (z3) VEBT_Member.vebt_member.simps(5) Suc_diff_Suc Suc_leD \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) x\<close> a0 add_self_div_2 case4(11) case4(4) case4(5) case4(8) le_add_diff_inverse le_less_Suc_eq le_neq_implies_less low_inv mult.commute nat_1_add_1 not_less_iff_gr_or_eq nth_mem plus_1_eq_Suc sprop1)
        have "mi <  (2^n*i+x) \<and>  (2^n*i+x) \<le> ma" using vebt_mint.simps(3)[of mi ma deg treeList summary] 
          by (metis \<open>i < 2 ^ m\<close> \<open>x < 2 ^ n\<close> aaa case4(11) case4(4) case4(8) high_inv low_inv mult.commute nth_mem)
        moreover have "both_member_options s (2^m*i +x)" 
          using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * i + x)\<close> both_member_options_equiv_member case4(12) case4(13) case4(5) set_vebt'_def by auto
        hence "both_member_options (treeList' ! i) x"  
          by (smt (z3) \<open>i < 2 ^ m\<close>  acd \<open>x < 2 ^ n\<close> a0 add_leD1 add_self_div_2 both_member_options_from_complete_tree_to_child calculation case4(5) high_inv infsplit low_inv mult.commute nat_neq_iff numeral_2_eq_2 plus_1_eq_Suc sprop1)
        then show ?thesis 
          by (metis \<open>i < 2 ^ m\<close> nth_mem sprop1 valid_member_both_member_options)
      qed
      show "vebt_member (treeList' ! i) x \<Longrightarrow> vebt_member (treeList ! i) x" 
      proof-
        assume "vebt_member (treeList' ! i) x"
        hence "vebt_member s (2^n*i +x)" using sprop1 both_member_options_from_chilf_to_complete_tree
            [of "(2^n*i +x)" deg treeList' mi ma summary'] 
          by (smt (z3) Nat.add_0_right \<open>i < 2 ^ m\<close> a0 add_leD1 add_self_div_2 both_member_options_equiv_member case4(12) case4(5) div_less div_mult_self4 high_def infsplit low_inv member_bound mult.commute nat_1_add_1 nth_mem power_not_zero zero_neq_numeral)
        hence "mi < (2^n*i +x) \<and> (2^n*i +x) \<le> ma " 
          using vebt_mint.simps(3)[of mi ma deg treeList' summary'] vebt_maxt.simps(3)[of mi ma deg treeList' summary'] 
          by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> acd both_member_options_equiv_member case4(12) high_inv infsplit low_inv member_bound mi_eq_ma_no_ch mult.commute nth_mem sprop1)
        moreover have "both_member_options (Node (Some (mi, ma)) deg treeList summary) (2^m*i +x)" 
          by (metis \<open>vebt_member s (2 ^ n * i + x)\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree calculation case4(1) case4(13) case4(5) maxbmo vebt_maxt.simps(3) mem_Collect_eq member_inv nat_neq_iff nth_mem one_add_one set_vebt'_def) 
        hence "both_member_options (treeList ! i) x"
          using both_member_options_from_complete_tree_to_child[of deg mi ma treeList summary "(2^n*i +x)"]
          by (smt (z3) Nat.add_0_right Suc_leD \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> a0 add_self_div_2 calculation case4(11) case4(5) div_less div_mult_self4 high_def low_inv member_bound mult.commute nat_1_add_1 nat_neq_iff nth_mem plus_1_eq_Suc power_not_zero sprop1 zero_neq_numeral)
        then show ?thesis 
          by (metis \<open>i < 2 ^ m\<close> aca case4(1) nth_mem sprop1 valid_member_both_member_options)
      qed
    qed
  qed
  hence setcongy: "i < 2^m \<Longrightarrow> set_vebt' (treeList ! i) = set_vebt' (treeList' ! i)" for i unfolding set_vebt'_def by presburger
  hence treecongy: "i < 2^m \<Longrightarrow> treeList ! i = treeList' ! i" for i 
    by (metis case4(1) case4(4) nth_mem sprop1)
  hence "treeList = treeList'" 
    by (metis aca case4(4) nth_equalityI)
  have "vebt_member summary x \<longleftrightarrow> vebt_member summary' x" for x 
    by (metis \<open>treeList = treeList'\<close> both_member_options_equiv_member case4(3) case4(7) member_bound sprop1 sumtreelistcong)
  hence "set_vebt' summary = set_vebt' summary'" unfolding set_vebt'_def by auto
  hence "summary = summary'" 
    using case4(2) sprop1 by blast
  then show ?case 
    using \<open>treeList = treeList'\<close> infsplit sprop1 by fastforce
next
  case (5 treeList n summary m deg mi ma)
  note case4= this
  hence "set_vebt' (Node (Some (mi, ma)) deg treeList summary) = set_vebt' s" by simp
  hence a0:"deg \<ge> 2" using 5 
    by (metis Suc_leI add_le_mono diff_Suc_1 less_add_same_cancel1 not_add_less1 not_less_iff_gr_or_eq numeral_2_eq_2 plus_1_eq_Suc set_n_deg_not_0)
  hence aa:"{mi, ma} \<subseteq> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" 
    apply auto using vebt_member.simps(5)[of mi ma "deg -2" treeList summary mi]
    apply (metis add_2_eq_Suc' le_add_diff_inverse2 mem_Collect_eq set_vebt'_def)
    using vebt_member.simps(5)[of mi ma "deg -2" treeList summary ma]
    apply (metis add_2_eq_Suc' le_add_diff_inverse2 mem_Collect_eq set_vebt'_def)
    done
  from 5(12) obtain treeList' summary' info where sprop1:"s = Node info deg treeList' summary' \<and> deg = n+m 
                  \<and> length treeList' =2^m \<and> invar_vebt summary' m \<and> (\<forall> t \<in> set treeList'. invar_vebt t n) " 
    apply cases 
    using a0 apply linarith 
    apply (metis case4(5) case4(6) even_Suc odd_add add_self_div_2)
    apply (metis Suc_inject add_Suc_right add_self_div_2 case4(5) case4(6))
    apply (metis case4(5) case4(6) even_Suc odd_add)
    apply (metis Suc_inject add_Suc_right add_self_div_2 case4(5) case4(6))
    done
  have  ac:"invar_vebt t h \<Longrightarrow> invar_vebt k h \<Longrightarrow> set_vebt' t = set_vebt' k \<Longrightarrow> vebt_mint t = vebt_mint k" for t k h 
  proof-
    assume assms: "invar_vebt t h" "invar_vebt k h" "set_vebt' t = set_vebt' k"
    have "\<not> vebt_mint t = vebt_mint k \<Longrightarrow> False"
    proof-
      assume "vebt_mint t \<noteq> vebt_mint k"
      then obtain a b where abdef:"vebt_mint t = None \<and> vebt_mint k = Some b \<or>
                            vebt_mint t = Some a \<and> vebt_mint k = None \<or>
                            a < b \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k \<or>
                            b < a \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k"
        by (metis linorder_neqE_nat option.exhaust)
      show False apply(cases "vebt_mint t = None \<and> vebt_mint k = Some b")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        apply(cases "   vebt_mint t = Some a \<and> vebt_mint k = None")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        apply (cases "a < b \<and> Some a = vebt_mint t \<and> Some b = vebt_mint k")
        apply (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> assms(1) assms(2) assms(3) mint_corr mint_sound)
        by (metis \<open>vebt_mint t \<noteq> vebt_mint k\<close> abdef assms(1) assms(2) assms(3) mint_corr mint_sound)
    qed
    thus "vebt_mint t = vebt_mint k" by auto
  qed   
  have  ad:"invar_vebt t h \<Longrightarrow> invar_vebt k h \<Longrightarrow> set_vebt' t = set_vebt' k \<Longrightarrow> vebt_maxt t = vebt_maxt k" for t k h 
  proof-
    assume assms: "invar_vebt t h" "invar_vebt k h" "set_vebt' t = set_vebt' k"
    have "\<not> vebt_maxt t = vebt_maxt k \<Longrightarrow> False"
    proof-
      assume "vebt_maxt t \<noteq> vebt_maxt k"
      then obtain a b where abdef:"vebt_maxt t = None \<and> vebt_maxt k = Some b \<or>
                            vebt_maxt t = Some a \<and> vebt_maxt k = None \<or>
                            a < b \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k \<or>
                            b < a \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k"
        by (metis linorder_neqE_nat option.exhaust)
      show False 
        apply(cases "vebt_maxt t = None \<and> vebt_maxt k = Some b") 
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        apply(cases "   vebt_maxt t = Some a \<and> vebt_maxt k = None")
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        apply (cases "a < b \<and> Some a = vebt_maxt t \<and> Some b = vebt_maxt k")
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        apply (metis \<open>vebt_maxt t \<noteq> vebt_maxt k\<close> abdef assms(1) assms(2) assms(3) maxt_corr maxt_sound)
        done
    qed
    thus "vebt_maxt t = vebt_maxt k" by auto
  qed
  have infsplit: "info = Some (mi ,ma)" using 5(12) 
  proof cases
    case (1 a b)
    then show ?thesis 
      using sprop1 by blast
  next
    case (2 treeList n summary m)
    then show ?thesis 
      by (metis "5.prems"(2) Collect_empty_eq VEBT_Member.vebt_member.simps(2) aa empty_iff insert_subset set_vebt'_def)
  next
    case (3 treeList n summary m)
    then show ?thesis 
      by (metis "5.prems"(2) Collect_empty_eq VEBT_Member.vebt_member.simps(2) aa empty_iff insert_subset set_vebt'_def)
  next
    case (4 treeList' n' summary' m' mi' ma')
    have "vebt_mint s = Some mi'"  
      by (simp add: "4"(1))
    hence "mi' = mi" 
      by (smt (verit, ccfv_threshold) "5.hyps"(7) "5.prems"(1) "5.prems"(2) VEBT_Member.vebt_member.simps(5) One_nat_def a0 aa add.assoc eq_iff insert_subset leI le_add_diff_inverse less_imp_le_nat mem_Collect_eq min_in_set_def mint_sound numeral_2_eq_2 option.sel order.not_eq_order_implies_strict plus_1_eq_Suc set_vebt'_def)
    have "vebt_maxt s = Some ma'"
      by (simp add: "4"(1))
    hence "ma' < ma \<Longrightarrow> ma\<notin> set_vebt' s"
      by (meson "5.prems"(1) leD max_in_set_def maxt_corr)  
    moreover have "ma < ma' \<Longrightarrow> ma' \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" using case4 
      by (metis dual_order.strict_trans2 mem_Collect_eq member_inv not_less_iff_gr_or_eq set_vebt'_def)
    ultimately have "ma'=ma" 
      by (metis \<open>vebt_maxt s = Some ma'\<close> aa case4(12) case4(13) insert_subset max_in_set_def maxt_corr not_less_iff_gr_or_eq)
    then show ?thesis 
      using "4"(1) \<open>mi' = mi\<close> sprop1 by force
  next
    case (5 treeList' n' summary' m' mi' ma')
    have "vebt_mint s = Some mi'"  
      by (simp add: "5"(1))
    hence "mi' = mi" 
      by (smt (verit, ccfv_threshold) "5.hyps"(7) "5.prems"(1) "5.prems"(2) VEBT_Member.vebt_member.simps(5) One_nat_def a0 aa add.assoc eq_iff insert_subset leI le_add_diff_inverse less_imp_le_nat mem_Collect_eq min_in_set_def mint_sound numeral_2_eq_2 option.sel order.not_eq_order_implies_strict plus_1_eq_Suc set_vebt'_def)
    have "vebt_maxt s = Some ma'"
      by (simp add: "5"(1))
    hence "ma' < ma \<Longrightarrow> ma\<notin> set_vebt' s"
      by (meson "5.prems"(1) leD max_in_set_def maxt_corr)  
    moreover have "ma < ma' \<Longrightarrow> ma' \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)" using case4 
      by (metis dual_order.strict_trans2 mem_Collect_eq member_inv not_less_iff_gr_or_eq set_vebt'_def)
    ultimately have "ma'=ma" using case4(13) 5
      by (metis \<open>vebt_maxt s = Some ma'\<close> aa both_member_options_equiv_member case4(12) insert_subset maxbmo mem_Collect_eq not_less_iff_gr_or_eq set_vebt'_def)
    then show ?thesis 
      using "5"(1) \<open>mi' = mi\<close> sprop1 by force
  qed 
  from 5(12) have acd:"mi \<noteq> ma \<longrightarrow>
    (\<forall>i<2 ^ m.
        (high ma n = i \<longrightarrow> both_member_options (treeList' ! i) (low ma n)) \<and>
        (\<forall>x. high x n = i \<and> both_member_options (treeList' ! i) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma))"
    apply cases using sprop1 apply simp
    using sprop1 infsplit apply simp
    using sprop1 infsplit apply simp 
    apply (metis case4(5) even_Suc odd_add sprop1)
    apply (smt (z3) Suc_inject VEBT.inject(1) add_Suc_right add_self_div_2 case4(5) infsplit option.inject prod.inject sprop1)
    done
  hence "length treeList' = 2^m"
    using sprop1 by fastforce
  hence aca:"length treeList' =length treeList" using "5.hyps"(2) 
    by (simp add: "5.hyps"(2) sprop1)
  from 5(12) have sumtreelistcong: " \<forall>i<2 ^ m. (\<exists>x. both_member_options (treeList' ! i) x) = both_member_options summary' i"
    apply cases 
    using a0 apply linarith 
    apply (metis VEBT.inject(1) nth_mem sprop1)
    using infsplit sprop1 apply force 
    apply (metis VEBT.inject(1) sprop1)
    using sprop1 apply auto
    done
  hence membercongy:"i < 2^m \<Longrightarrow> vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x" for i x
  proof-
    assume "i < 2^m"
    show "vebt_member (treeList! i) x \<longleftrightarrow> vebt_member (treeList' ! i) x"
    proof
      show "vebt_member (treeList ! i) x \<Longrightarrow> vebt_member (treeList' ! i) x"  
      proof-
        assume "vebt_member (treeList ! i) x"
        hence aaa:"both_member_options (treeList ! i) x"  
          by (metis \<open>i < 2 ^ m\<close> both_member_options_equiv_member case4(1) case4(4) nth_mem)
        have "x < 2^n"
          by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) x\<close> case4(1) case4(4) member_bound nth_mem)
        hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) (2^n*i+x)" 
          using both_member_options_from_chilf_to_complete_tree
            [of " (2^n*i+x)" deg treeList mi ma summary] aaa high_inv[of x n i]
            \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) x\<close> low_inv[of x n i]
          by (simp add: case4(4) case4(5) mult.commute sprop1)
        hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) (2^n*i+x)" using 
            valid_member_both_member_options[of "(Node (Some (mi, ma)) deg treeList summary)" deg "2^n*i+x"]
            invar_vebt.intros(5)[of treeList n summary m deg mi ma]  case4 by fastforce
        hence "mi <  (2^n*i+x) \<and>  (2^n*i+x) \<le> ma" using vebt_mint.simps(3)[of mi ma deg treeList summary] 
          by (metis \<open>i < 2 ^ m\<close> \<open>x < 2 ^ n\<close> aaa case4(11) case4(4) case4(8) high_inv low_inv mult.commute nth_mem)
        moreover have "both_member_options s (2^n*i +x)" 
          using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * i + x)\<close> both_member_options_equiv_member case4(12) case4(13) case4(5) set_vebt'_def by auto
        have acffs:"both_member_options (treeList' ! (high ma n)) (low ma n)" 
          using acd calculation case4(10) high_bound_aux sprop1 verit_comp_simplify1(3) by blast
        hence "both_member_options (treeList' ! i) x"
          using both_member_options_from_complete_tree_to_child[of deg mi ma treeList' summary' "2^n*i+x"]
            low_inv[of x n i] high_inv[of x n i] 
          by (smt (z3) Nat.add_0_right \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * i + x)\<close> \<open>x < 2 ^ n\<close> a0 add_Suc_right add_leD1 both_member_options_equiv_member calculation case4(12) case4(13) case4(5) diff_Suc_1 div_less div_mult_self4 infsplit le_add_diff_inverse2 mem_Collect_eq mult.commute mult_2 nat_1_add_1 nat_neq_iff one_less_numeral_iff semiring_norm(76) sprop1 set_vebt'_def zero_neq_numeral)
        then show "vebt_member (treeList' ! i) x" 
          by (metis \<open>i < 2 ^ m\<close> nth_mem sprop1 valid_member_both_member_options)
      qed
      show "vebt_member (treeList' ! i) x \<Longrightarrow> vebt_member (treeList ! i) x" 
      proof-
        assume "vebt_member (treeList' ! i) x"
        hence "vebt_member s (2^n*i +x)" using sprop1 both_member_options_from_chilf_to_complete_tree
            [of "(2^n*i +x)" deg treeList' mi ma summary'] 
          by (smt (z3) Nat.add_0_right Suc_leD \<open>i < 2 ^ m\<close> a0 add_Suc_right both_member_options_equiv_member case4(12) case4(5) diff_Suc_1 div_less div_mult_self4 even_Suc high_def infsplit low_inv member_bound mult.commute mult_2_right nat_1_add_1 nth_mem odd_add odd_two_times_div_two_nat plus_1_eq_Suc power_not_zero zero_neq_numeral)
        hence "mi < (2^n*i +x) \<and> (2^n*i +x) \<le> ma " 
          using vebt_mint.simps(3)[of mi ma deg treeList' summary'] vebt_maxt.simps(3)[of mi ma deg treeList' summary'] 
          by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList' ! i) x\<close> acd both_member_options_equiv_member case4(12) high_inv infsplit low_inv member_bound mi_eq_ma_no_ch mult.commute nth_mem sprop1)
        moreover have "both_member_options (Node (Some (mi, ma)) deg treeList summary) (2^n*i +x)"
          by (metis \<open>vebt_member s (2 ^ n * i + x)\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree calculation case4(1) case4(13) case4(5) maxbmo vebt_maxt.simps(3) mem_Collect_eq member_inv nat_neq_iff nth_mem one_add_one set_vebt'_def) 
        have "invar_vebt (treeList' ! i) n"
          by (simp add: \<open>i < 2 ^ m\<close> sprop1)
        hence "x < 2^n" 
          using \<open>vebt_member (treeList' ! i) x\<close> member_bound by auto
        hence "both_member_options (treeList ! i) x"
          using both_member_options_from_complete_tree_to_child[of deg mi ma treeList summary "(2^n*i +x)"]
            low_inv[of x n i] high_inv[of x n i] 
          by (smt (z3) Nat.add_0_right Suc_leD \<open>both_member_options (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * i + x)\<close> \<open>i < 2 ^ m\<close> a0 add_Suc_right calculation case4(11) case4(5) div_less div_mult_self4 mult.commute mult_2 nat_1_add_1 nat_neq_iff one_less_numeral_iff plus_1_eq_Suc semiring_norm(76) sprop1 zero_neq_numeral)
        then show ?thesis 
          by (metis \<open>i < 2 ^ m\<close> aca case4(1) nth_mem sprop1 valid_member_both_member_options)
      qed
    qed
  qed
  hence setcongy: "i < 2^m \<Longrightarrow> set_vebt' (treeList ! i) = set_vebt' (treeList' ! i)" for i unfolding set_vebt'_def by presburger
  hence treecongy: "i < 2^m \<Longrightarrow> treeList ! i = treeList' ! i" for i 
    by (metis case4(1) case4(4) nth_mem sprop1)
  hence "treeList = treeList'" 
    by (metis aca case4(4) nth_equalityI)
  have "vebt_member summary x \<longleftrightarrow> vebt_member summary' x" for x 
    by (metis \<open>treeList = treeList'\<close> both_member_options_equiv_member case4(3) case4(7) member_bound sprop1 sumtreelistcong)
  hence "set_vebt' summary = set_vebt' summary'" unfolding set_vebt'_def by auto
  hence "summary = summary'" 
    using case4(2) sprop1 by blast
  then show ?case 
    using \<open>treeList = treeList'\<close> infsplit sprop1 by fastforce
qed

corollary "invar_vebt t n \<Longrightarrow> set_vebt' t = {} \<Longrightarrow> t = vebt_buildup n" 
  by (metis buildup_gives_empty buildup_gives_valid deg_not_0 uniquetree)

corollary unique_tree: "invar_vebt t n \<Longrightarrow> invar_vebt s n \<Longrightarrow> set_vebt t = set_vebt s \<Longrightarrow> s = t"
  by (simp add: set_vebt_set_vebt'_valid uniquetree)

corollary "invar_vebt t n \<Longrightarrow> set_vebt t = {} \<Longrightarrow> t = vebt_buildup n" 
  by (metis buildup_gives_empty buildup_gives_valid deg_not_0 uniquetree  set_vebt_set_vebt'_valid)

text \<open>All valid trees can be generated by $vebt-insertion$ chains on an empty tree with same degree parameter:\<close>

inductive perInsTrans::"VEBT \<Rightarrow> VEBT \<Rightarrow> bool" where
  "perInsTrans t t"|
  "(t = vebt_insert s x) \<Longrightarrow> perInsTrans t u \<Longrightarrow> perInsTrans s u"

lemma perIT_concat:" perInsTrans s t \<Longrightarrow> perInsTrans t u \<Longrightarrow> perInsTrans s u"
  by (induction s t rule: perInsTrans.induct) (simp add: perInsTrans.intros)+

lemma assumes "invar_vebt t n " shows
  "perInsTrans (vebt_buildup n) t"
proof-
  have "finite A \<Longrightarrow>invar_vebt s n \<Longrightarrow>set_vebt' s = B \<Longrightarrow> B\<subseteq> A \<Longrightarrow> perInsTrans (vebt_buildup n) s" for s A B
  proof (induction "card B" arbitrary: s B)
    case 0
    then show ?case 
      by (metis buildup_gives_empty buildup_gives_valid card_eq_0_iff deg_not_0 perInsTrans.intros(1) set_vebt_finite uniquetree)
  next
    case (Suc car)
    hence "finite B"
      by (meson rev_finite_subset)
    obtain x b where "B = insert x b \<and> x \<notin> b" 
      by (metis Suc.hyps(2) card_Suc_eq)
    have "set_vebt' (vebt_delete s x) = b" 
      using Suc.prems(2) Suc.prems(3) \<open>B = insert x b \<and> x \<notin> b\<close> delete_correct' by auto  
    moreover hence "perInsTrans (vebt_buildup n) (vebt_delete s x)"
      by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc.prems(4) \<open>B = insert x b \<and> x \<notin> b\<close> \<open>finite B\<close> card_insert_disjoint delete_pres_valid finite_insert nat.inject subset_insertI subset_trans)
    hence "set_vebt' (vebt_insert (vebt_delete s x) x) = set_vebt' s" 
      by (metis Diff_insert_absorb Suc.prems(2) Suc.prems(3) Un_insert_right \<open>B = insert x b \<and> x \<notin> b\<close> boolean_algebra_cancel.sup0 delete_pres_valid delete_correct' insertI1 insert_corr mem_Collect_eq member_bound set_vebt'_def)
    have "invar_vebt (vebt_insert (vebt_delete s x) x) n"  
      by (metis Suc.prems(2) Suc.prems(3) \<open>B = insert x b \<and> x \<notin> b\<close> delete_pres_valid insertI1 mem_Collect_eq member_bound set_vebt'_def valid_pres_insert)
    moreover hence "vebt_insert (vebt_delete s x) x = s" 
      using Suc.prems(2) \<open>set_vebt' (VEBT_Insert.vebt_insert (vebt_delete s x) x) = set_vebt' s\<close> uniquetree by force
    ultimately show ?case 
      by (metis \<open>perInsTrans (vebt_buildup n) (vebt_delete s x)\<close> perIT_concat perInsTrans.intros(1) perInsTrans.intros(2))
  qed
  then show ?thesis 
    by (meson assms equalityD1 set_vebt_finite)
qed
  
end
end
