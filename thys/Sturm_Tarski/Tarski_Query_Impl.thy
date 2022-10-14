(*
  File:    Pseudo_Remainder_Sequence.thy
  Author:  Wenda Li
*)

section \<open>TaQ for polynomials with rational coefficients\<close>

theory Tarski_Query_Impl imports
  Pseudo_Remainder_Sequence Sturm_Tarski
begin

global_interpretation rat_int:hom_pseudo_smods rat_of_int real_of_int real_of_rat
  defines 
    ri_changes_itv_spmods = rat_int.changes_itv_spmods and
    ri_changes_gt_spmods = rat_int.changes_gt_spmods and
    ri_changes_le_spmods = rat_int.changes_le_spmods and
    ri_changes_R_spmods = rat_int.changes_R_spmods
  apply unfold_locales
  by (simp_all add: of_rat_less of_rat_less_eq)

definition TaQ_R_rats::"rat poly \<Rightarrow> rat poly \<Rightarrow> int" where
  "TaQ_R_rats p q = taq {x. poly (map_poly real_of_rat p) x = (0::real)} 
                                      (map_poly real_of_rat q)"

definition TaQ_itv_rats::"rat \<Rightarrow> rat \<Rightarrow> rat poly \<Rightarrow> rat poly \<Rightarrow> int" where
  "TaQ_itv_rats a b p q = taq {x. poly (map_poly real_of_rat p) x = (0::real) 
        \<and> of_rat a < x \<and> x < of_rat b} (map_poly real_of_rat q)"

definition TaQ_gt_rats::" rat \<Rightarrow> rat poly \<Rightarrow> rat poly \<Rightarrow> int" where
  "TaQ_gt_rats a p q = taq {x. poly (map_poly real_of_rat p) x = (0::real) 
        \<and> of_rat a < x } (map_poly real_of_rat q)"

definition TaQ_le_rats::"rat \<Rightarrow> rat poly \<Rightarrow> rat poly \<Rightarrow> int" where
  "TaQ_le_rats b p q = taq {x. poly (map_poly real_of_rat p) x = (0::real) 
        \<and> x < of_rat b} (map_poly real_of_rat q)"

lemma taq_smult_pos:
  assumes "a>0"
  shows "taq s (smult a p) = taq s p"
  unfolding taq_def by (simp add: assms sign_times)

lemma taq_proots_R_code[code]:
  "TaQ_R_rats p q = (let 
    ip = clear_de p; 
    iq = clear_de q
    in ri_changes_R_spmods ip (pderiv ip * iq))"
proof -
  define ip iq where "ip = clear_de p" and "iq = clear_de q"
  define dp dq where "dp = rat_of_int (de_lcm p)" and "dq = rat_of_int (de_lcm q)"

  have "dp > 0" "dq>0"
    unfolding dp_def dq_def by simp_all
  have ip:"of_int_poly ip = smult dp p" and iq:"of_int_poly iq = smult dq q"
    using clear_de unfolding ip_def iq_def dp_def dq_def by auto
    
  have "TaQ_R_rats p q = taq {x. poly (map_poly real_of_rat (of_int_poly ip)) x = 0} 
        (map_poly real_of_rat (of_int_poly iq))"
    unfolding TaQ_R_rats_def ip iq  using \<open>dp > 0\<close> \<open>dq >0\<close>
    by (simp add:of_rat_hom.map_poly_hom_smult taq_smult_pos)
  also have "... = taq {x. poly (of_int_poly ip) x = (0::real)} (of_int_poly iq)"
    by (simp add:map_poly_map_poly comp_def)
  also have "... = changes_R_smods (of_int_poly ip) (pderiv (of_int_poly ip) * of_int_poly iq)"
    using sturm_tarski_R by simp
  also have "... = changes_R_smods (of_int_poly ip) (of_int_poly (pderiv ip * iq))"
    by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
  also have "... = ri_changes_R_spmods ip (pderiv ip * iq)"
    using rat_int.changes_spmods_smods by simp
  finally have "TaQ_R_rats p q = ri_changes_R_spmods ip (pderiv ip * iq) " .
  then show ?thesis unfolding Let_def ip_def iq_def .
qed

lemma taq_proots_itv_code[code]:
  "TaQ_itv_rats a b p q = (if a\<ge>b then 
      0
    else if poly p a \<noteq> 0 \<and> poly p b \<noteq>0 then
      (let
      ip = clear_de p; 
      iq = clear_de q
      in ri_changes_itv_spmods a b ip (pderiv ip * iq))
    else 
       Code.abort (STR ''Roots at border yet to be supported'') 
                              (\<lambda>_. TaQ_itv_rats a b p q)
    )"
proof (cases "a\<ge>b \<or> poly p a = 0 \<or> poly p b = 0")
  case True
  moreover have ?thesis if "a\<ge>b"
  proof -
    have "{x. poly (map_poly of_rat p) x = 0 \<and> real_of_rat a < x \<and> x < real_of_rat b} 
            = {}"
      using that rat_int.r2.hom_less_eq by fastforce
    then have "TaQ_itv_rats a b p q  = taq {} (map_poly real_of_rat q)"
      unfolding TaQ_itv_rats_def by metis
    also have "... = 0" 
      unfolding taq_def by simp
    finally show ?thesis using that by auto
  qed
  moreover have ?thesis if "\<not> a\<ge>b" "poly p a = 0 \<or> poly p b = 0"
    using that by auto
  ultimately show ?thesis by auto
next
  case False

  define ip iq where "ip = clear_de p" and "iq = clear_de q"
  define dp dq where "dp = rat_of_int (de_lcm p)" and "dq = rat_of_int (de_lcm q)"
  define aa bb where "aa = real_of_rat a" and "bb = real_of_rat b"

  have "dp > 0" "dq>0"
    unfolding dp_def dq_def by simp_all
  have ip:"of_int_poly ip = smult dp p" and iq:"of_int_poly iq = smult dq q"
    using clear_de unfolding ip_def iq_def dp_def dq_def by auto
    
  have "TaQ_itv_rats a b p q = taq {x. poly (map_poly real_of_rat (of_int_poly ip)) x = 0
        \<and> aa < x \<and> x < bb} 
        (map_poly real_of_rat (of_int_poly iq))"
    unfolding TaQ_itv_rats_def ip iq aa_def bb_def  using \<open>dp > 0\<close> \<open>dq >0\<close>
    by (simp add:of_rat_hom.map_poly_hom_smult taq_smult_pos)
  also have "... = taq {x. poly (of_int_poly ip) x = (0::real) 
        \<and> aa < x \<and> x < bb} (of_int_poly iq)"
    by (simp add:map_poly_map_poly comp_def)
  also have "... = changes_itv_smods aa bb (of_int_poly ip) 
      (pderiv (of_int_poly ip) * of_int_poly iq)"
  proof -
    have "aa < bb" "poly (map_poly of_int ip) aa \<noteq> 0" 
        "poly (map_poly of_int ip) bb \<noteq> 0"
      unfolding aa_def bb_def
      subgoal by (meson False not_less of_rat_less)
      subgoal using False \<open>0 < dp\<close> ip rat_int.map_poly_R_hom_commute by force
      subgoal using False \<open>0 < dp\<close> ip rat_int.map_poly_R_hom_commute by force
      done
    from sturm_tarski_interval[OF this] 
    show ?thesis by auto
  qed
  also have "... = changes_itv_smods aa bb (of_int_poly ip) (of_int_poly (pderiv ip * iq))"
    by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
  also have "... = ri_changes_itv_spmods a b ip (pderiv ip * iq)"
    using rat_int.changes_spmods_smods unfolding aa_def bb_def by simp
  finally have "TaQ_itv_rats a b p q = ri_changes_itv_spmods a b ip (pderiv ip * iq) " .
  then show ?thesis unfolding Let_def ip_def iq_def using False by presburger
qed

lemma taq_proots_gt_code[code]:
  "TaQ_gt_rats a p q = (
    if poly p a \<noteq> 0 then
      (let
      ip = clear_de p; 
      iq = clear_de q
      in ri_changes_gt_spmods a ip (pderiv ip * iq))
    else 
       Code.abort (STR ''Roots at border yet to be supported'') 
                              (\<lambda>_. TaQ_gt_rats a p q)
    )"
proof (cases "poly p a = 0")
  case True
  then show ?thesis by auto
next
  case False

  define ip iq where "ip = clear_de p" and "iq = clear_de q"
  define dp dq where "dp = rat_of_int (de_lcm p)" and "dq = rat_of_int (de_lcm q)"
  define aa where "aa = real_of_rat a" 

  have "dp > 0" "dq>0"
    unfolding dp_def dq_def by simp_all
  have ip:"of_int_poly ip = smult dp p" and iq:"of_int_poly iq = smult dq q"
    using clear_de unfolding ip_def iq_def dp_def dq_def by auto
    
  have "TaQ_gt_rats a p q = taq {x. poly (map_poly real_of_rat (of_int_poly ip)) x = 0
        \<and> aa < x} 
        (map_poly real_of_rat (of_int_poly iq))"
    unfolding TaQ_gt_rats_def ip iq aa_def  using \<open>dp > 0\<close> \<open>dq >0\<close>
    by (simp add:of_rat_hom.map_poly_hom_smult taq_smult_pos)
  also have "... = taq {x. poly (of_int_poly ip) x = (0::real) 
        \<and> aa < x } (of_int_poly iq)"
    by (simp add:map_poly_map_poly comp_def)
  also have "... = changes_gt_smods aa (of_int_poly ip) 
      (pderiv (of_int_poly ip) * of_int_poly iq)"
  proof -
    have "poly (map_poly of_int ip) aa \<noteq> 0" 
      unfolding aa_def using False \<open>0 < dp\<close> ip rat_int.map_poly_R_hom_commute by force
    from sturm_tarski_above[OF this] 
    show ?thesis by auto
  qed
  also have "... = changes_gt_smods aa (of_int_poly ip) (of_int_poly (pderiv ip * iq))"
    by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
  also have "... = ri_changes_gt_spmods a ip (pderiv ip * iq)"
    using rat_int.changes_spmods_smods unfolding aa_def by simp
  finally have "TaQ_gt_rats a p q = ri_changes_gt_spmods a ip (pderiv ip * iq) " .
  then show ?thesis unfolding Let_def ip_def iq_def using False by presburger
qed

lemma taq_proots_le_code[code]:
  "TaQ_le_rats b p q = (
    if poly p b \<noteq>0 then
      (let
      ip = clear_de p; 
      iq = clear_de q
      in ri_changes_le_spmods b ip (pderiv ip * iq))
    else 
       Code.abort (STR ''Roots at border yet to be supported'') 
                              (\<lambda>_. TaQ_le_rats b p q)
    )"
proof (cases "poly p b = 0")
  case True
  then show ?thesis by auto
next
  case False

  define ip iq where "ip = clear_de p" and "iq = clear_de q"
  define dp dq where "dp = rat_of_int (de_lcm p)" and "dq = rat_of_int (de_lcm q)"
  define bb where "bb = real_of_rat b"

  have "dp > 0" "dq>0"
    unfolding dp_def dq_def by simp_all
  have ip:"of_int_poly ip = smult dp p" and iq:"of_int_poly iq = smult dq q"
    using clear_de unfolding ip_def iq_def dp_def dq_def by auto
    
  have "TaQ_le_rats b p q = taq {x. poly (map_poly real_of_rat (of_int_poly ip)) x = 0
        \<and> x < bb} 
        (map_poly real_of_rat (of_int_poly iq))"
    unfolding TaQ_le_rats_def ip iq bb_def  using \<open>dp > 0\<close> \<open>dq >0\<close>
    by (simp add:of_rat_hom.map_poly_hom_smult taq_smult_pos)
  also have "... = taq {x. poly (of_int_poly ip) x = (0::real) 
        \<and> x < bb} (of_int_poly iq)"
    by (simp add:map_poly_map_poly comp_def)
  also have "... = changes_le_smods bb (of_int_poly ip) 
      (pderiv (of_int_poly ip) * of_int_poly iq)"
  proof -
    have "poly (map_poly of_int ip) bb \<noteq> 0"
      unfolding bb_def using False \<open>0 < dp\<close> ip rat_int.map_poly_R_hom_commute by force
    from sturm_tarski_below[OF this] 
    show ?thesis by auto
  qed
  also have "... = changes_le_smods bb (of_int_poly ip) (of_int_poly (pderiv ip * iq))"
    by (simp add: of_int_hom.map_poly_pderiv of_int_poly_hom.hom_mult)
  also have "... = ri_changes_le_spmods b ip (pderiv ip * iq)"
    using rat_int.changes_spmods_smods unfolding bb_def by simp
  finally have "TaQ_le_rats b p q = ri_changes_le_spmods b ip (pderiv ip * iq) " .
  then show ?thesis unfolding Let_def ip_def iq_def using False by presburger
qed

end