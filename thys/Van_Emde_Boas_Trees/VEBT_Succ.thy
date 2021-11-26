(*by Ammer*)
theory VEBT_Succ imports VEBT_Insert VEBT_MinMax
begin

section \<open>The Successor Operation\<close>

definition is_succ_in_set :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_succ_in_set xs x y =  (y \<in> xs \<and> y > x \<and> (\<forall> z \<in> xs. (z > x \<longrightarrow> z \<ge> y)))"

context VEBT_internal begin  
  
corollary succ_member: "is_succ_in_set (set_vebt' t) x y = (vebt_member t y \<and> y > x \<and> (\<forall> z. vebt_member t z \<and> z > x \<longrightarrow> z \<ge> y))" 
  using is_succ_in_set_def set_vebt'_def by auto

subsection \<open>Auxiliary Lemmas on Sets and Successorship\<close>

lemma "finite (A:: nat set) \<Longrightarrow> A \<noteq> {}\<Longrightarrow> Min A \<in> A"
  by(induction A rule: finite.induct)(blast | meson Min_in finite_insert)+

lemma obtain_set_succ: assumes "(x::nat) < z " and "max_in_set A z" and "finite B" and "A=B"  shows "\<exists> y. is_succ_in_set A x y"
proof-
  have "{y \<in> A. y > x} \<noteq> {}"
    using assms(1) assms(2) max_in_set_def by auto 
  have "Min {y \<in> A. y > x} \<in> {y \<in> A. y > x}" 
    by (metis (full_types) Collect_mem_eq \<open>{y \<in> A. x < y} \<noteq> {}\<close> assms(3) assms(4) eq_Min_iff finite_Collect_conjI)
  have "i \<in> A\<Longrightarrow> i > x \<Longrightarrow> i \<ge> Min {y \<in> A. y > x} " for i 
    by (simp add: assms(3) assms(4))
  have "is_succ_in_set A x (Min {y \<in> A. y > x})" 
    using is_succ_in_set_def \<open>Min {y \<in> A. x < y} \<in> {y \<in> A. x < y}\<close> \<open>\<And>i. \<lbrakk>i \<in> A; x < i\<rbrakk> \<Longrightarrow> Min {y \<in> A. x < y} \<le> i\<close> by blast
  then show?thesis by auto
qed

lemma succ_none_empty: assumes "(\<nexists> x. is_succ_in_set (xs) a x)"  and "finite xs"shows "\<not> (\<exists> x \<in> xs. ord_class.greater x a)"
proof-
  have "\<exists> x \<in> xs. ord_class.greater x a \<Longrightarrow> False"
  proof-
    assume "\<exists> x \<in> xs. ord_class.greater x a"
    hence "{x \<in> xs. ord_class.greater x  a} \<noteq> {}" by auto
    have "Min {y \<in> xs. y > a} \<in> {y \<in> xs. y > a}"  
      by (metis (full_types) Collect_mem_eq Min_in \<open>{x \<in> xs. a < x} \<noteq> {}\<close> assms(2) finite_Collect_conjI)
    have "i \<in> xs \<Longrightarrow>  ord_class.greater i  a\<Longrightarrow> 
             ord_class.greater_eq i (Min {y \<in> xs. ord_class.greater y  a}) " for i 
      by (simp add: assms(2))
    have "is_succ_in_set xs a (Min {y \<in> xs. y > a})" 
      using is_succ_in_set_def \<open>Min {y \<in> xs. a < y} \<in> {y \<in> xs. a < y}\<close> \<open>\<And>i. \<lbrakk>i \<in> xs; a < i\<rbrakk> \<Longrightarrow> Min {y \<in> xs. a < y} \<le> i\<close> by blast
    then show False 
      using assms(1) by blast
  qed
  then show ?thesis by blast
qed

end

subsection \<open>The actual Function\<close>

context begin
  interpretation VEBT_internal .

fun vebt_succ :: "VEBT \<Rightarrow> nat \<Rightarrow> nat option" where
  "vebt_succ (Leaf _ b) 0 = (if b then Some 1 else None)"|
  "vebt_succ (Leaf _ _) (Suc n) = None"|
  "vebt_succ (Node None _ _ _) _ = None"|
  "vebt_succ (Node _ 0 _ _) _ = None"|
  "vebt_succ (Node _ (Suc 0) _ _) _ = None"|
  "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = (
        if x < mi then (Some mi) 
        else (let l = low x (deg div 2); h = high x (deg div 2) in 
             if h < length treeList then  
                let maxlow = vebt_maxt (treeList ! h) in (
                    if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                        Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_succ (treeList ! h) l
                    else let sc = vebt_succ summary h in
                         if sc = None then None
                         else Some (2^(deg div 2)) *\<^sub>o sc +\<^sub>o vebt_mint (treeList ! the sc) )
              else None))"

end              

subsection \<open>Lemmas for Term Decomposition\<close>
context VEBT_internal begin

lemma succ_min: assumes "deg \<ge> 2" and "(x::nat) < mi" shows 
  "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some mi" 
  by (metis add_2_eq_Suc assms(1) assms(2) le_add_diff_inverse vebt_succ.simps(6))

lemma succ_greatereq_min: assumes "deg \<ge> 2" and "(x::nat) \<ge> mi" shows 
  "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = (let l = low x (deg div 2); h = high x (deg div 2) in 
                    if h < length treeList then  
  
                            let maxlow = vebt_maxt (treeList ! h) in 
                            (if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_succ (treeList ! h) l
                             else let sc = vebt_succ summary h in
                             if sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o sc +\<^sub>o vebt_mint (treeList ! the sc) )

                     else None)"
  by (smt add_numeral_left arith_simps(1) assms(1) assms(2) le_add_diff_inverse not_less numerals(1) plus_1_eq_Suc vebt_succ.simps(6))

lemma succ_list_to_short: assumes "deg \<ge> 2" and "x \<ge> mi" and " high x (deg div 2) \<ge> length treeList" shows
  "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = None"
  using assms(1) assms(2) assms(3) succ_greatereq_min by auto

lemma succ_less_length_list: assumes "deg \<ge> 2" and "x \<ge> mi" and " high x (deg div 2) < length treeList" shows
  "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = 
               (let l = low x (deg div 2); h = high x (deg div 2) ; maxlow = vebt_maxt (treeList ! h) in 
                            (if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_succ (treeList ! h) l
                             else let sc = vebt_succ summary h in
                             if sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o sc +\<^sub>o vebt_mint (treeList !the sc)))"
  by (simp add: assms(1) assms(2) assms(3) succ_greatereq_min)

subsection \<open>Correctness Proof\<close>

theorem succ_corr: "invar_vebt t n \<Longrightarrow> vebt_succ t x = Some sx == is_succ_in_set (set_vebt' t) x sx" 
proof(induction t n arbitrary: x sx rule: invar_vebt.induct)
  case (1 a b)
  then show ?case proof(cases x)
    case 0
    then show ?thesis
      by (simp add: succ_member)
  next
    case (Suc nat)
    then show ?thesis proof(cases nat)
      case 0
      then show ?thesis
        by (simp add: Suc succ_member)
    next
      case (Suc nat)
      then show ?thesis by (metis (no_types) VEBT_Member.vebt_member.simps(1) Suc_eq_plus1 add_cancel_right_left le_add2 le_imp_less_Suc not_add_less2 not_less0 old.nat.exhaust option.distinct(1) option.simps(1) vebt_succ.simps(1) vebt_succ.simps(2) succ_member)  
    qed
  qed
next
  case (2 treeList n summary m deg)
  then show ?case
    by (simp add: succ_member)
next
  case (3 treeList n summary m deg)
  then show ?case 
    by (simp add: succ_member)
next
  case (4 treeList n summary m deg mi ma)
  hence "n = m" and "n \<ge> 1" and "deg \<ge> 2" and "deg = n + m"
       apply blast+ 
    using "4.hyps"(2) "4.hyps"(5) Suc_le_eq deg_not_0 apply auto[1]
    using "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) deg_not_0 apply fastforce
    by (simp add: "4.hyps"(6))
  hence "deg div 2 =n" and "length treeList = 2^n" 
    using add_self_div_2 apply blast by (simp add: "4.hyps"(4) "4.hyps"(5))
  then show ?case proof(cases "x < mi")
    case True
    hence 0: "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some mi"
      by (simp add: \<open>2 \<le> deg\<close> succ_min)
    have 1:"mi = the (vebt_mint (Node (Some (mi, ma)) deg treeList summary))" by simp
    hence "mi \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
      by (metis VEBT_Member.vebt_member.simps(5) \<open>2 \<le> deg\<close> add_numeral_left arith_simps(1) le_add_diff_inverse mem_Collect_eq numerals(1) plus_1_eq_Suc set_vebt'_def)
    hence 2:"y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> y \<ge> x" for y
      using "4.hyps"(9) True member_inv set_vebt'_def by fastforce
    hence 3: "y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> (y > mi \<Longrightarrow> y \<ge> x)" for y by blast
    hence 4: "\<forall> y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary). y > mi \<longrightarrow> y \<ge> x" by blast
    hence "is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x mi"
      by (metis (mono_tags, lifting) "4.hyps"(9) True \<open>mi \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)\<close> eq_iff less_imp_le_nat mem_Collect_eq member_inv succ_member set_vebt'_def)
    then show ?thesis using 0
      by (metis is_succ_in_set_def antisym_conv option.inject)
  next 
    case False
    hence "x \<ge> mi"by simp  
    then show ?thesis 
    proof(cases "high x (deg div 2)< length treeList ")
      case True
      hence "high x n < 2^n \<and> low x n < 2^n"
        by (simp add: \<open>deg div 2 = n\<close> \<open>length treeList = 2 ^ n\<close> low_def)
      let ?l = "low x (deg div 2)" 
      let ?h = "high x (deg div 2)"
      let ?maxlow = "vebt_maxt (treeList ! ?h)"
      let ?sc = "vebt_succ summary ?h"
      have 1:"vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = 
                            (if ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some ?h +\<^sub>o vebt_succ (treeList ! ?h) ?l
                             else if ?sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc))"
        by (smt True \<open>2 \<le> deg\<close> \<open>mi \<le> x\<close> succ_less_length_list)
      then show ?thesis 
      proof(cases "?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow)")
        case True
        then obtain maxl where 00:"Some maxl = ?maxlow \<and> ?l < maxl" by auto
        have 01:"invar_vebt ((treeList ! ?h)) n \<and> (treeList ! ?h) \<in> set treeList "
          by (simp add: "4.hyps"(1) \<open>deg div 2 = n\<close> \<open>high x n < 2 ^ n \<and> low x n < 2 ^ n\<close> \<open>length treeList = 2 ^ n\<close>)
        have  02:"vebt_member ((treeList ! ?h)) maxl" 
          using "00" "01" maxt_member by auto
        hence 03: "\<exists> y. y > ?l \<and> vebt_member ((treeList ! ?h)) y"
          using "00" by blast 
        hence afinite: "finite (set_vebt' (treeList ! ?h)) " 
          using "01" set_vebt_finite by blast
        then obtain succy where 04:"is_succ_in_set (set_vebt' (treeList ! ?h)) ?l succy"
          using "00" "01" maxt_corr obtain_set_succ by fastforce
        hence 05:"Some succy =  vebt_succ (treeList ! ?h) ?l"  using 4(1) 01 by force
        hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x  =  Some (2^(deg div 2)*  ?h + succy) "
          by (metis "1" True add_def mul_def option_shift.simps(3))
        hence 06: "succy \<in> set_vebt' (treeList ! ?h)" 
          using "04" is_succ_in_set_def by blast
        hence 07: "succy < 2^(deg div 2) \<and> ?h < 2^(deg div 2) \<and> deg div 2 + deg div 2 = deg" 
          using "01" "04" "4.hyps"(5) "4.hyps"(6) \<open>high x n < 2 ^ n \<and> low x n < 2 ^ n\<close> member_bound succ_member by auto
        let ?y = "2^(deg div 2)*  ?h + succy"
        have 08: "vebt_member (treeList ! ?h) succy"
          using "06" set_vebt'_def by auto
        hence 09: "both_member_options (treeList ! ?h) succy"
          using "01" both_member_options_equiv_member by blast
        have 10: "high ?y (deg div 2) = ?h \<and> low ?y (deg div 2) = succy"
          by (simp add: "07" high_inv low_inv mult.commute)
        hence 11: "naive_member (treeList ! ?h) succy 
                \<Longrightarrow> naive_member (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary ?y] 
          by (metis "07" "4.hyps"(4) "4.hyps"(5) One_nat_def Suc_pred \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> add_gr_0 div_greater_zero_iff zero_less_numeral)
        have 12: "?y \<ge> mi \<and> ?y \<le> ma" 
          by (metis "01" "07" "09" "10" "4.hyps"(11) "4.hyps"(5) "4.hyps"(8) \<open>deg div 2 = n\<close> less_imp_le_nat)    
        hence 13: "membermima (treeList ! ?h) succy
                \<Longrightarrow> membermima (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using membermima.simps(4)[of mi ma "deg -1" treeList summary ?y] 
          apply(cases "?y = mi \<or> ?y = ma")
           apply (metis "07" One_nat_def Suc_pred \<open>2 \<le> deg\<close> add_gr_0 div_greater_zero_iff zero_less_numeral)
          by (metis "07" "10" "4.hyps"(4) "4.hyps"(5) One_nat_def Suc_pred \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> add_gr_0 div_greater_zero_iff zero_less_numeral)
        hence 14:"both_member_options (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using "09" "11" both_member_options_def by blast
        have 15: "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?y" 
          by (smt "07" "08" "10" "12" "4.hyps"(4) "4.hyps"(5) VEBT_Member.vebt_member.simps(5) One_nat_def Suc_1 Suc_le_eq Suc_pred \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> add_gr_0 div_greater_zero_iff not_less zero_less_numeral)
        have 16: "Some ?y = vebt_succ (Node (Some (mi, ma)) deg treeList summary) x" 
          by (simp add: \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2) * high x (deg div 2) + succy)\<close>)
        have 17: "x = ?h * 2^(deg div 2) + ?l"
          using bit_concat_def bit_split_inv by auto 
        have 18: "?y - x = ?h * 2^(deg div 2) + succy - ?h * 2^(deg div 2) - ?l " 
          by (metis "17" diff_diff_add mult.commute)
        hence "?y -x > 0"
          using "04" is_succ_in_set_def by auto
        hence 19: "?y > x" 
          using zero_less_diff by blast
        have 20: "z > x \<Longrightarrow> vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<Longrightarrow> z\<ge> ?y " for z 
        proof-
          assume "z > x" and "vebt_member (Node (Some (mi, ma)) deg treeList summary) z"
          hence "high z (deg div 2) \<ge> high x (deg div 2)" 
            by (simp add: div_le_mono high_def)
          then show ?thesis proof(cases "high z (deg div 2) = high x (deg div 2)")
            case True
            hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
              using vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              by (metis "01" "07" "4.hyps"(11) "4.hyps"(5) False \<open>deg div 2 = n\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z\<close> \<open>x < z\<close> both_member_options_equiv_member member_inv)
            hence "succy \<le> low z (deg div 2)" using 04 unfolding is_succ_in_set_def 
              by (metis True \<open>x < z\<close> add_diff_cancel_left' bit_concat_def bit_split_inv diff_diff_left mem_Collect_eq set_vebt'_def zero_less_diff)
            hence "?y \<le> z"
              by (smt True bit_concat_def bit_split_inv diff_add_inverse diff_diff_add diff_is_0_eq mult.commute)
            then show ?thesis by blast
          next
            case False
            hence "high z (deg div 2) > high ?y (deg div 2)"
              using "10" \<open>high x (deg div 2) \<le> high z (deg div 2)\<close> by linarith
            then show ?thesis 
              by (metis div_le_mono high_def nat_le_linear not_le)
          qed
        qed
        hence "is_succ_in_set (set_vebt'  (Node (Some (mi, ma)) deg treeList summary)) x ?y" 
          by (simp add: "15" "19" succ_member)
        then show ?thesis using 16 
          by (metis eq_iff option.inject succ_member)
      next
        case False
        hence i1:"?maxlow =  None \<or> \<not> (Some ?l <\<^sub>o  ?maxlow)" by simp
        hence 2: "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x =  (if ?sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc))" 
          using "1" by auto
        have " invar_vebt (treeList ! ?h) n"
          by (metis "4"(1) True inthall member_def)
        hence 33:"\<nexists> u. vebt_member (treeList ! ?h) u \<and> u > ?l" 
        proof(cases "?maxlow = None")
          case True
          then show ?thesis using maxt_corr_help_empty[of "treeList ! ?h" n] 
            by (simp add: \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> set_vebt'_def)
        next
          case False
          obtain maxilow where "?maxlow =Some maxilow" 
            using False by blast
          hence "maxilow \<le> ?l" 
            using "i1" by auto
          then show ?thesis
            by (meson \<open>vebt_maxt (treeList ! high x (deg div 2)) = Some maxilow\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> le_imp_less_Suc le_less_trans maxt_corr_help not_less_eq)
        qed
        then show ?thesis 
        proof(cases " ?sc = None")
          case True
          hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x =   None" 
            by (simp add: "2")
          hence "\<nexists> i. is_succ_in_set (set_vebt' summary) ?h i"
            using "4.hyps"(3) True by force
          hence "\<nexists> i. i > ?h \<and> vebt_member summary i " using succ_none_empty[of "set_vebt' summary" ?h]
          proof -
            { fix nn :: nat
              have "\<forall>n. ((is_succ_in_set (Collect (vebt_member summary)) (high x (deg div 2)) esk1_0 \<or> infinite (Collect (vebt_member summary))) \<or> n \<notin> Collect (vebt_member summary)) \<or> \<not> high x (deg div 2) < n" 
                using \<open>\<nexists>i. is_succ_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> succ_none_empty set_vebt'_def by auto
              then have "\<not> high x (deg div 2) < nn \<or> \<not> vebt_member summary nn"
                using "4.hyps"(2) \<open>\<nexists>i. is_succ_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> set_vebt'_def set_vebt_finite by auto }
            then show ?thesis
              by blast
          qed
          hence "(i > x \<and>  vebt_member (Node (Some (mi, ma)) deg treeList summary) i) \<Longrightarrow> False" for i
          proof-
            fix i
            assume "i > x \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i"
            hence 20: "i = mi \<or> i = ma \<or> (high i (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high i (deg div 2))) (low i (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary i] 
              using member_inv by blast
            have "i \<noteq> mi" 
              using \<open>mi \<le> x\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> not_le by blast
            hence "mi \<noteq> ma" 
              using \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> member_inv not_less_iff_gr_or_eq by blast
            hence "i < 2^deg"
              using "4.hyps"(10) \<open>i \<noteq> mi\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> member_inv by fastforce
            hence aa:"i = ma  \<Longrightarrow> both_member_options( treeList ! (high i (deg div 2))) (low i (deg div 2))" 
              using "4.hyps"(11) "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) \<open>mi \<noteq> ma\<close> deg_not_0 exp_split_high_low(1) by auto
            hence abc:"invar_vebt (treeList ! (high i (deg div 2))) n" 
              by (metis "4.hyps"(1) "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) \<open>deg div 2 = n\<close> \<open>i < 2 ^ deg\<close> \<open>length treeList = 2 ^ n\<close> deg_not_0 exp_split_high_low(1) in_set_member inthall)
            hence  abd:"i = ma  \<Longrightarrow> vebt_member( treeList ! (high i (deg div 2))) (low i (deg div 2))" 
              using aa valid_member_both_member_options by blast
            hence abe:"vebt_member( treeList ! (high i (deg div 2))) (low i (deg div 2))" 
              using "20" \<open>i \<noteq> mi\<close> by blast
            hence abf:"both_member_options( treeList ! (high i (deg div 2))) (low i (deg div 2))"
              using \<open>invar_vebt (treeList ! high i (deg div 2)) n\<close> both_member_options_equiv_member by blast
            hence abg:"both_member_options summary (high i (deg div 2))"
              by (metis "20" "4.hyps"(10) "4.hyps"(2) "4.hyps"(4) "4.hyps"(6) "4.hyps"(7) \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> \<open>i \<noteq> mi\<close> deg_not_0 div_greater_zero_iff exp_split_high_low(1) zero_less_numeral)
            hence abh:"vebt_member summary (high i (deg div 2))" 
              using "4.hyps"(2) valid_member_both_member_options by blast
            have aaa:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low i (deg div 2))"
              using \<open>vebt_member (treeList ! high i (deg div 2)) (low i (deg div 2))\<close> by auto
            have abi:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> low i (deg div 2) > ?l" 
              by (metis \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> add_le_cancel_left bit_concat_def bit_split_inv le_neq_implies_less less_imp_le_nat nat_neq_iff) 
            hence abj:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> False" using 33 aaa by blast
            hence abk:" (high i (deg div 2)) \<in> (set_vebt' summary) \<and>  (high i (deg div 2)) >  (high x (deg div 2)) " 
              by (metis (full_types) \<open>vebt_member summary (high i (deg div 2))\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> div_le_mono high_def le_less mem_Collect_eq set_vebt'_def)       
            then show ?thesis 
              using \<open>\<not> (\<exists>i>high x (deg div 2). vebt_member summary i)\<close> abh by blast
          qed
          then show ?thesis 
            using \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = None\<close> succ_member by auto
        next
          case False
          hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = 
                           Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc)"
            by (simp add: False "2")
          obtain sc where "?sc = Some sc" 
            using False by blast
          hence "is_succ_in_set (set_vebt' summary) ?h sc"
            using "4.hyps"(3) by blast
          hence "vebt_member summary sc"
            using succ_member by blast
          hence "both_member_options summary sc" 
            using "4.hyps"(2) both_member_options_equiv_member by auto
          hence "sc < 2^m" 
            using "4.hyps"(2) \<open>vebt_member summary sc\<close> member_bound by blast
          hence "\<exists> miny. both_member_options (treeList ! sc) miny" 
            using "4.hyps"(7) \<open>both_member_options summary sc\<close> by blast
          hence fgh:"set_vebt' (treeList ! sc) \<noteq> {}" 
            by (metis "4.hyps"(1) "4.hyps"(4) "4.hyps"(5) Collect_empty_eq_bot \<open>deg div 2 = n\<close> \<open>sc < 2 ^ m\<close> bot_empty_eq empty_iff nth_mem set_vebt'_def valid_member_both_member_options)
          hence "invar_vebt (treeList ! the ?sc) n" 
            by (simp add: "4.hyps"(1) "4.hyps"(4) \<open>sc < 2 ^ m\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close>)
          then obtain miny where "Some miny = vebt_mint (treeList ! sc)"
            by (metis fgh Collect_empty_eq VEBT_Member.vebt_member.simps(2) vebt_buildup.simps(2) buildup_gives_empty vebt_mint.elims set_vebt'_def)
          hence "Some miny = vebt_mint (treeList ! the ?sc)"
            by (simp add: \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close>)
          hence "min_in_set (set_vebt' (treeList ! the ?sc)) miny" 
            using \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> mint_corr by auto
          hence scmem:"vebt_member (treeList ! the ?sc) miny" 
            using \<open>Some miny = vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2))))\<close> \<open>invar_vebt (treeList ! the(vebt_succ summary (high x (deg div 2)))) n\<close> mint_member by auto
          let ?res =  "Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList !the ?sc)"
          obtain res where "res = the ?res" by blast
          hence "res = 2^(deg div 2) * sc + miny"
            by (metis \<open>Some miny = vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2))))\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> add_def mul_def option.sel option_shift.simps(3))
          have "high res (deg div 2) = sc" 
            by (metis \<open>deg div 2 = n\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>invar_vebt (treeList ! the ?sc) n\<close> high_inv member_bound mult.commute scmem)
          hence "res > x" 
            by (metis is_succ_in_set_def \<open>is_succ_in_set (set_vebt' summary) (high x (deg div 2)) sc\<close> div_le_mono high_def not_le) 
          hence "res > mi"
            using \<open>mi \<le> x\<close> le_less_trans by blast
          hence "res \<le> ma" 
          proof(cases "high res n < high ma n")
            case True
            then show ?thesis 
              by (metis div_le_mono high_def leD nat_le_linear)
          next
            case False
            hence "mi \<noteq> ma" 
              by (metis "4.hyps"(5) "4.hyps"(8) \<open>\<exists>miny. both_member_options (treeList ! sc) miny\<close> \<open>length treeList = 2 ^ n\<close> \<open>sc < 2 ^ m\<close> nth_mem)
            have "high res n < 2^m" 
              using \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>sc < 2 ^ m\<close> by blast
            hence " (\<forall>x. high x n = high res n \<and> both_member_options (treeList ! (high res n)) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma)" using 4(11)
              using \<open>mi \<noteq> ma\<close> by blast
            have "high res n = high res n \<and> both_member_options (treeList ! (high res n)) (low res n)" 
              by (metis \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> both_member_options_equiv_member low_inv member_bound mult.commute option.sel scmem)
            then show ?thesis 
              using \<open>\<forall>x. high x n = high res n \<and> both_member_options (treeList ! high res n) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma\<close> by blast
          qed
          hence "vebt_member  (Node (Some (mi, ma)) deg treeList summary) (the ?res)" using vebt_member.simps(5)[of mi ma "deg-2" treeList summary res] 
            by (metis "4.hyps"(4) \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>mi < res\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>res = the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary (high x (deg div 2)) +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2)))))\<close> \<open>sc < 2 ^ m\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> add_2_eq_Suc leD le_add_diff_inverse low_inv member_bound mult.commute not_less_iff_gr_or_eq option.sel scmem)
          have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z > x) \<Longrightarrow> z \<ge> res" for z
          proof-
            fix z
            assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z > x"
            hence 20: "z = mi \<or> z = ma \<or> (high z (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              using member_inv by blast
            have "z \<noteq> mi"
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> \<open>mi \<le> x\<close> not_le by blast
            hence "mi \<noteq> ma"
              using \<open>mi < res\<close> \<open>res \<le> ma\<close> not_le by blast
            hence "z < 2^deg" 
              using "4.hyps"(10) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> \<open>z \<noteq> mi\<close> member_inv by fastforce
            hence aa:"z = ma  \<Longrightarrow> both_member_options( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
              using "4.hyps"(11) "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) \<open>mi \<noteq> ma\<close> deg_not_0 exp_split_high_low(1) by auto
            hence abc:"invar_vebt (treeList ! (high z (deg div 2))) n" 
              by (metis "4.hyps"(1) "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) \<open>deg div 2 = n\<close> \<open>z < 2 ^ deg\<close> \<open>length treeList = 2 ^ n\<close> deg_not_0 exp_split_high_low(1) in_set_member inthall)
            hence  abd:"z = ma  \<Longrightarrow> vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
              using aa valid_member_both_member_options by blast
            hence abe:"vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
              using "20" \<open>z \<noteq> mi\<close> by blast
            hence abf:"both_member_options( treeList ! (high z (deg div 2))) (low z (deg div 2))"
              using \<open>invar_vebt (treeList ! high z (deg div 2)) n\<close> both_member_options_equiv_member by blast
            hence abg:"both_member_options summary (high z (deg div 2))" 
              by (metis (full_types) "4.hyps"(5) "4.hyps"(6) "4.hyps"(7) \<open>deg div 2 = n\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> \<open>z < 2 ^ deg\<close> deg_not_0 exp_split_high_low(1))
            hence abh:"vebt_member summary (high z (deg div 2))" 
              using "4.hyps"(2) valid_member_both_member_options by blast
            have aaa:"(high z (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low z (deg div 2))"
              using abe by auto
            have "high z(deg div 2)< sc \<Longrightarrow> False" 
            proof-
              assume "high z(deg div 2)< sc"
              hence "vebt_member summary (high z(deg div 2))" 
                using abh by blast
              have aaaa:"?h \<le> high z(deg div 2)" 
                by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> div_le_mono high_def less_imp_le_nat)
              have bbbb:"?h \<ge> high z(deg div 2)"   
                using \<open>is_succ_in_set (set_vebt' summary) (high x (deg div 2)) sc\<close> \<open>high z (deg div 2) < sc\<close> abh leD succ_member by auto
              hence "?h = high z (deg div 2)" 
                using aaaa eq_iff by blast
              hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
                using aaa by linarith
              then show False 
                by (metis "33" \<open>high x (deg div 2) = high z (deg div 2)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> add_diff_cancel_left' bit_concat_def bit_split_inv diff_diff_left zero_less_diff)
            qed
            hence "high z(deg div 2) \<ge> sc" 
              using not_less by blast
            then show " z \<ge> res"
            proof(cases "high z(deg div 2) = sc")
              case True
              hence "vebt_member (treeList ! (high z(deg div 2))) (low z (deg div 2))" 
                using abe by blast
              have "low z (deg div 2) \<ge> miny"
                using True \<open>min_in_set (set_vebt' (treeList ! the (vebt_succ summary (high x (deg div 2))))) miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> abe min_in_set_def set_vebt'_def by auto
              hence "z \<ge> res"
                by (metis (full_types) True \<open>res = 2 ^ (deg div 2) * sc + miny\<close> add_le_cancel_left bit_concat_def bit_split_inv mult.commute)
              then show ?thesis by simp
            next
              case False
              hence "high z(deg div 2) > sc"
                using \<open>sc \<le> high z (deg div 2)\<close> le_less by blast
              then show ?thesis
                by (metis \<open>high res (deg div 2) = sc\<close> div_le_mono high_def leD linear)
            qed
          qed
          hence "is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x res" 
            using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h  +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h))))\<close>
              \<open>res = the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h)))\<close> \<open>x < res\<close> succ_member by blast
          moreover have "Some res = Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc)" 
            by (metis \<open>Some miny = vebt_mint (treeList !the (vebt_succ summary (high x (deg div 2))))\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> add_def mul_def option_shift.simps(3))
          ultimately show ?thesis
            by (metis (mono_tags) is_succ_in_set_def \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h))\<close> eq_iff option.inject)
        qed
      qed
    next
      case False
      hence 0:"vebt_succ (Node (Some (mi, ma)) deg treeList summary) x  = None"
        by (simp add: \<open>2 \<le> deg\<close> \<open>mi \<le> x\<close> succ_greatereq_min)
      have 1:"x \<ge> 2^deg"
        by (metis "4.hyps"(4) "4.hyps"(5) "4.hyps"(6) False \<open>deg div 2 = n\<close> high_def le_less_linear less_mult_imp_div_less mult_2 power2_eq_square power_even_eq)
      hence "x \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
        using "4.hyps"(10) "4.hyps"(9) member_inv set_vebt'_def by fastforce
      hence "\<nexists> ss. is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x ss"
        using "4.hyps"(10) 1 \<open>mi \<le> x\<close> member_inv succ_member by fastforce
      then show ?thesis using 0 by auto
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "Suc n = m"  and "deg = n + m" and "length treeList = 2^m \<and> invar_vebt summary m"
    by blast + 
  hence "n \<ge> 1" 
    using "5.hyps"(1) set_n_deg_not_0 by blast 
  hence "deg \<ge> 2" 
    by (simp add: "5.hyps"(5) "5.hyps"(6))    
  hence "deg div 2 =n" 
    by (simp add: "5.hyps"(5) "5.hyps"(6))
  then show ?case proof(cases "x < mi")
    case True
    hence 0: "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some mi"
      by (simp add: \<open>2 \<le> deg\<close> succ_min)
    have 1:"mi = the (vebt_mint (Node (Some (mi, ma)) deg treeList summary))" by simp
    hence "mi \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
      by (metis VEBT_Member.vebt_member.simps(5) \<open>2 \<le> deg\<close> add_numeral_left arith_simps(1) le_add_diff_inverse mem_Collect_eq numerals(1) plus_1_eq_Suc set_vebt'_def)
    hence 2:"y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> y \<ge> x" for y
      using "5.hyps"(9) True member_inv set_vebt'_def by fastforce
    hence 3: "y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> (y > mi \<Longrightarrow> y \<ge> x)" for y by blast
    hence 4: "\<forall> y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary). y > mi \<longrightarrow> y \<ge> x" by blast
    hence "is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x mi"
      by (metis (mono_tags, lifting) "5.hyps"(9) True \<open>mi \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)\<close> eq_iff less_imp_le_nat mem_Collect_eq member_inv succ_member set_vebt'_def)
    then show ?thesis using 0
      by (metis is_succ_in_set_def antisym_conv option.inject)
  next 
    case False
    hence "x \<ge> mi"by simp  
    then show ?thesis 
    proof(cases "high x (deg div 2)< length treeList ")
      case True
      hence "high x n < 2^m \<and> low x n < 2^n" 
        by (simp add: "5.hyps"(4) \<open>deg div 2 = n\<close> low_def)
      let ?l = "low x (deg div 2)" 
      let ?h = "high x (deg div 2)"
      let ?maxlow = "vebt_maxt (treeList ! ?h)"
      let ?sc = "vebt_succ summary ?h"
      have 1:"vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = 
                            (if ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some ?h +\<^sub>o vebt_succ (treeList ! ?h) ?l
                             else if ?sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc))"
        by (smt True \<open>2 \<le> deg\<close> \<open>mi \<le> x\<close> succ_less_length_list)
      then show ?thesis 
      proof(cases "?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow)")
        case True
        then obtain maxl where 00:"Some maxl = ?maxlow \<and> ?l < maxl" by auto
        have 01:"invar_vebt ((treeList ! ?h)) n \<and> (treeList ! ?h) \<in> set treeList "
          by (metis (full_types) "5.hyps"(1) "5.hyps"(4) \<open>deg div 2 = n\<close> \<open>high x n < 2 ^ m \<and> low x n < 2 ^ n\<close> inthall member_def)
        have  02:"vebt_member ((treeList ! ?h)) maxl" 
          using "00" "01" maxt_member by auto
        hence 03: "\<exists> y. y > ?l \<and> vebt_member ((treeList ! ?h)) y"
          using "00" by blast 
        hence afinite: "finite (set_vebt' (treeList ! ?h)) " 
          using "01" set_vebt_finite by blast
        then obtain succy where 04:"is_succ_in_set (set_vebt' (treeList ! ?h)) ?l succy"
          using "00" "01" maxt_corr obtain_set_succ by fastforce
        hence 05:"Some succy =  vebt_succ (treeList ! ?h) ?l"  using 5(1) 01 by force
        hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x  =  Some (2^(deg div 2)*  ?h + succy) "
          by (metis "1" True add_def  mul_def option_shift.simps(3))
        hence 06: "succy \<in> set_vebt' (treeList ! ?h)" 
          using "04" is_succ_in_set_def by blast
        hence 07: "succy < 2^(deg div 2) \<and> ?h < 2^m \<and> Suc (deg div 2 + deg div 2 ) = deg"  
          using "01" "04" "5.hyps"(5) "5.hyps"(6) \<open>high x n < 2 ^ m \<and> low x n < 2 ^ n\<close> member_bound succ_member by auto
        let ?y = "2^(deg div 2)*  ?h + succy"
        have 08: "vebt_member (treeList ! ?h) succy"
          using "06" set_vebt'_def by auto
        hence 09: "both_member_options (treeList ! ?h) succy"
          using "01" both_member_options_equiv_member by blast
        have 10: "high ?y (deg div 2) = ?h \<and> low ?y (deg div 2) = succy"
          by (simp add: "07" high_inv low_inv mult.commute)
        hence 11: "naive_member (treeList ! ?h) succy 
                \<Longrightarrow> naive_member (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary ?y]
          using "07" "5.hyps"(4) by auto
        have 12: "?y \<ge> mi \<and> ?y \<le> ma" 
          by (metis "01" "07" "09" "10" "5.hyps"(11) "5.hyps"(5) "5.hyps"(8) \<open>deg div 2 = n\<close> less_imp_le_nat)    
        hence 13: "membermima (treeList ! ?h) succy
                \<Longrightarrow> membermima (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using membermima.simps(4)[of mi ma "deg -1" treeList summary ?y] 
          apply(cases "?y = mi \<or> ?y = ma")
          using "07" apply auto[1] 
          using "07" "10" "5.hyps"(4) by auto
        hence 14:"both_member_options (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using "09" "11" both_member_options_def by blast
        have 15: "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?y" 
          by (smt "07" "08" "10" "12" "5.hyps"(4) "5.hyps"(5) VEBT_Member.vebt_member.simps(5) One_nat_def Suc_1 Suc_le_eq Suc_pred \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> add_gr_0 div_greater_zero_iff not_less zero_less_numeral)
        have 16: "Some ?y = vebt_succ (Node (Some (mi, ma)) deg treeList summary) x" 
          by (simp add: \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2) * high x (deg div 2) + succy)\<close>)
        have 17: "x = ?h * 2^(deg div 2) + ?l"
          using bit_concat_def bit_split_inv by auto 
        have 18: "?y - x = ?h * 2^(deg div 2) + succy - ?h * 2^(deg div 2) - ?l " 
          by (metis "17" diff_diff_add mult.commute)
        hence "?y -x > 0"
          using "04" is_succ_in_set_def by auto
        hence 19: "?y > x" 
          using zero_less_diff by blast
        have 20: "z > x \<Longrightarrow> vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<Longrightarrow> z\<ge> ?y " for z 
        proof-
          assume "z > x" and "vebt_member (Node (Some (mi, ma)) deg treeList summary) z"
          hence "high z (deg div 2) \<ge> high x (deg div 2)" 
            by (simp add: div_le_mono high_def)
          then show ?thesis 
          proof(cases "high z (deg div 2) = high x (deg div 2)")
            case True
            hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
              using vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              by (metis "01" "07" "5.hyps"(11) "5.hyps"(5) False \<open>deg div 2 = n\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z\<close> \<open>x < z\<close> both_member_options_equiv_member member_inv)
            hence "succy \<le> low z (deg div 2)" using 04 unfolding is_succ_in_set_def 
              by (metis True \<open>x < z\<close> add_diff_cancel_left' bit_concat_def bit_split_inv diff_diff_left mem_Collect_eq set_vebt'_def zero_less_diff)
            hence "?y \<le> z"
              by (smt True bit_concat_def bit_split_inv diff_add_inverse diff_diff_add diff_is_0_eq mult.commute)
            then show ?thesis by blast
          next
            case False
            hence "high z (deg div 2) > high ?y (deg div 2)"
              using "10" \<open>high x (deg div 2) \<le> high z (deg div 2)\<close> by linarith
            then show ?thesis 
              by (metis div_le_mono high_def nat_le_linear not_le)
          qed
        qed
        hence "is_succ_in_set (set_vebt'  (Node (Some (mi, ma)) deg treeList summary)) x ?y" 
          by (simp add: "15" "19" succ_member)
        then show ?thesis using 16 
          by (metis eq_iff option.inject succ_member)
      next
        case False
        hence i1:"?maxlow =  None \<or> \<not> (Some ?l <\<^sub>o  ?maxlow)" by simp
        hence 2: "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x =  (if ?sc = None then None
                             else Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc))" 
          using "1" by auto
        have " invar_vebt (treeList ! ?h) n"
          by (metis "5"(1) True inthall member_def)
        hence 33:"\<nexists> u. vebt_member (treeList ! ?h) u \<and> u > ?l" 
        proof(cases "?maxlow = None")
          case True
          then show ?thesis using maxt_corr_help_empty[of "treeList ! ?h" n] 
            by (simp add: \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> set_vebt'_def)
        next
          case False
          obtain maxilow where "?maxlow =Some maxilow" 
            using False by blast
          hence "maxilow \<le> ?l" 
            using "i1" by auto
          then show ?thesis
            by (meson \<open>vebt_maxt (treeList ! high x (deg div 2)) = Some maxilow\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> le_imp_less_Suc le_less_trans maxt_corr_help not_less_eq)
        qed
        then show ?thesis 
        proof(cases " ?sc = None")
          case True
          hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x =   None" 
            by (simp add: "2")
          hence "\<nexists> i. is_succ_in_set (set_vebt' summary) ?h i"
            using "5.hyps"(3) True by force
          hence "\<nexists> i. i > ?h \<and> vebt_member summary i " using succ_none_empty[of "set_vebt' summary" ?h]
          proof -
            { fix nn :: nat
              have "\<forall>n. ((is_succ_in_set (Collect (vebt_member summary)) (high x (deg div 2)) esk1_0 \<or> infinite (Collect (vebt_member summary))) \<or> n \<notin> Collect (vebt_member summary)) \<or> \<not> high x (deg div 2) < n" 
                using \<open>\<nexists>i. is_succ_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> succ_none_empty set_vebt'_def by auto
              then have "\<not> high x (deg div 2) < nn \<or> \<not> vebt_member summary nn"
                using "5.hyps"(2) \<open>\<nexists>i. is_succ_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> set_vebt'_def set_vebt_finite by auto }
            then show ?thesis
              by blast
          qed
          hence "(i > x \<and>  vebt_member (Node (Some (mi, ma)) deg treeList summary) i) \<Longrightarrow> False" for i
          proof-
            fix i
            assume "i > x \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i"
            hence 20: "i = mi \<or> i = ma \<or> (high i (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high i (deg div 2))) (low i (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary i] 
              using member_inv by blast
            have "i \<noteq> mi" 
              using \<open>mi \<le> x\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> not_le by blast
            hence "mi \<noteq> ma" 
              using \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> member_inv not_less_iff_gr_or_eq by blast
            hence "i < 2^deg"
              using "5.hyps"(10) \<open>i \<noteq> mi\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> member_inv by fastforce
            hence aa:"i = ma  \<Longrightarrow> both_member_options( treeList ! (high i (deg div 2))) (low i (deg div 2))"  
              using "5.hyps"(11) "5.hyps"(2) "5.hyps"(6) \<open>deg div 2 = n\<close> \<open>i \<noteq> mi\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> deg_not_0 exp_split_high_low(1) by auto
            hence abc:"invar_vebt (treeList ! (high i (deg div 2))) n"
              by (metis "5.hyps"(1) "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) \<open>deg div 2 = n\<close> \<open>i < 2 ^ deg\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> deg_not_0 exp_split_high_low(1) in_set_member inthall zero_less_Suc)
            hence  abd:"i = ma  \<Longrightarrow> vebt_member( treeList ! (high i (deg div 2))) (low i (deg div 2))" 
              using aa valid_member_both_member_options by blast
            hence abe:"vebt_member( treeList ! (high i (deg div 2))) (low i (deg div 2))" 
              using "20" \<open>i \<noteq> mi\<close> by blast
            hence abf:"both_member_options( treeList ! (high i (deg div 2))) (low i (deg div 2))"
              using \<open>invar_vebt (treeList ! high i (deg div 2)) n\<close> both_member_options_equiv_member by blast
            hence abg:"both_member_options summary (high i (deg div 2))" 
              by (metis (full_types) "5.hyps"(5) "5.hyps"(6) "5.hyps"(7) \<open>deg div 2 = n\<close> \<open>i < 2 ^ deg\<close> abc deg_not_0 exp_split_high_low(1) zero_less_Suc)
            hence abh:"vebt_member summary (high i (deg div 2))" 
              using "5.hyps"(2) valid_member_both_member_options by blast
            have aaa:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low i (deg div 2))"
              using \<open>vebt_member (treeList ! high i (deg div 2)) (low i (deg div 2))\<close> by auto
            have abi:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> low i (deg div 2) > ?l" 
              by (metis \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> add_le_cancel_left bit_concat_def bit_split_inv le_neq_implies_less less_imp_le_nat nat_neq_iff) 
            hence abj:"(high i (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> False" using 33 aaa by blast
            hence abk:" (high i (deg div 2)) \<in> (set_vebt' summary) \<and>  (high i (deg div 2)) >  (high x (deg div 2)) " 
              by (metis (full_types) \<open>vebt_member summary (high i (deg div 2))\<close> \<open>x < i \<and> vebt_member (Node (Some (mi, ma)) deg treeList summary) i\<close> div_le_mono high_def le_less mem_Collect_eq set_vebt'_def)       
            then show ?thesis 
              using \<open>\<not> (\<exists>i>high x (deg div 2). vebt_member summary i)\<close> abh by blast
          qed
          then show ?thesis 
            using \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = None\<close> succ_member by auto
        next
          case False
          hence "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = 
                           Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc)"
            by (simp add: False "2")
          obtain sc where "?sc = Some sc" 
            using False by blast
          hence "is_succ_in_set (set_vebt' summary) ?h sc"
            using "5.hyps"(3) by blast
          hence "vebt_member summary sc"
            using succ_member by blast
          hence "both_member_options summary sc" 
            using "5.hyps"(2) both_member_options_equiv_member by auto
          hence "sc < 2^m" 
            using "5.hyps"(2) \<open>vebt_member summary sc\<close> member_bound by blast
          hence "\<exists> miny. both_member_options (treeList ! sc) miny" 
            using "5.hyps"(7) \<open>both_member_options summary sc\<close> by blast
          hence fgh:"set_vebt' (treeList ! sc) \<noteq> {}" 
            by (metis "5.hyps"(1) "5.hyps"(4) \<open>sc < 2 ^ m\<close> empty_Collect_eq inthall member_def set_vebt'_def valid_member_both_member_options)
          hence "invar_vebt (treeList ! the ?sc) n" 
            by (simp add: "5.hyps"(1) "5.hyps"(4) \<open>sc < 2 ^ m\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close>)
          then obtain miny where "Some miny = vebt_mint (treeList ! sc)"
            by (metis fgh Collect_empty_eq VEBT_Member.vebt_member.simps(2) vebt_buildup.simps(2) buildup_gives_empty vebt_mint.elims set_vebt'_def)
          hence "Some miny = vebt_mint (treeList ! the ?sc)"
            by (simp add: \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close>)
          hence "min_in_set (set_vebt' (treeList ! the ?sc)) miny" 
            using \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> mint_corr by auto
          hence scmem:"vebt_member (treeList ! the ?sc) miny" 
            using \<open>Some miny = vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2))))\<close>
              \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> mint_member by auto
          let ?res =  "Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc)"
          obtain res where "res = the ?res" by blast
          hence "res = 2^(deg div 2) * sc + miny" 
            by (metis \<open>Some miny = vebt_mint (treeList ! sc)\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> add_shift mul_shift option.sel)
          have "high res (deg div 2) = sc" 
            by (metis \<open>deg div 2 = n\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>invar_vebt (treeList ! the ?sc) n\<close> high_inv member_bound mult.commute scmem)
          hence "res > x" 
            by (metis is_succ_in_set_def \<open>is_succ_in_set (set_vebt' summary) (high x (deg div 2)) sc\<close> div_le_mono high_def not_le) 
          hence "res > mi"
            using \<open>mi \<le> x\<close> le_less_trans by blast
          hence "res \<le> ma" 
          proof(cases "high res n < high ma n")
            case True
            then show ?thesis 
              by (metis div_le_mono high_def leD nat_le_linear)
          next
            case False
            hence "mi \<noteq> ma"
              by (metis "5.hyps"(4) "5.hyps"(8) \<open>\<exists>miny. both_member_options (treeList ! sc) miny\<close> \<open>sc < 2 ^ m\<close> nth_mem)
            have "high res n < 2^m" 
              using \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>sc < 2 ^ m\<close> by blast
            hence " (\<forall>x. high x n = high res n \<and> both_member_options (treeList ! (high res n)) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma)" using 5(11)
              using \<open>mi \<noteq> ma\<close> by blast
            have "high res n = high res n \<and> both_member_options (treeList ! (high res n)) (low res n)"
              by (metis \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> both_member_options_equiv_member low_inv member_bound mult.commute option.sel scmem)
            then show ?thesis 
              using \<open>\<forall>x. high x n = high res n \<and> both_member_options (treeList ! high res n) (low x n) \<longrightarrow> mi < x \<and> x \<le> ma\<close> by blast
          qed
          hence "vebt_member  (Node (Some (mi, ma)) deg treeList summary) (the ?res)" using vebt_member.simps(5)[of mi ma "deg-2" treeList summary res]
            by (metis "5.hyps"(4) \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = sc\<close> \<open>mi < res\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>res = the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary (high x (deg div 2)) +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2)))))\<close> \<open>sc < 2 ^ m\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> add_2_eq_Suc' le_add_diff_inverse2 less_imp_le low_inv member_bound mult.commute not_less option.sel scmem)
          have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z > x) \<Longrightarrow> z \<ge> res" for z
          proof-
            fix z
            assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z > x"
            hence 20: "z = mi \<or> z = ma \<or> (high z (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              using member_inv by blast
            have "z \<noteq> mi"
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> \<open>mi \<le> x\<close> not_le by blast
            hence "mi \<noteq> ma"
              using \<open>mi < res\<close> \<open>res \<le> ma\<close> not_le by blast
            hence "z < 2^deg" 
              using "5.hyps"(10) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> \<open>z \<noteq> mi\<close> member_inv by fastforce
            hence aa:"z = ma  \<Longrightarrow> both_member_options( treeList ! (high z (deg div 2))) (low z (deg div 2))"
              using "5.hyps"(11) "5.hyps"(2) "5.hyps"(6) \<open>deg div 2 = n\<close> \<open>mi \<noteq> ma\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> deg_not_0 exp_split_high_low(1) by auto
            hence abc:"invar_vebt (treeList ! (high z (deg div 2))) n"
              by (metis "20" "5.hyps"(1) "5.hyps"(10) "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) \<open>deg div 2 = n\<close> \<open>invar_vebt (treeList ! the(vebt_succ summary (high x (deg div 2)))) n\<close> \<open>z \<noteq> mi\<close> deg_not_0 exp_split_high_low(1) nth_mem zero_less_Suc)
            hence  abd:"z = ma  \<Longrightarrow> vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
              using aa valid_member_both_member_options by blast
            hence abe:"vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
              using "20" \<open>z \<noteq> mi\<close> by blast
            hence abf:"both_member_options( treeList ! (high z (deg div 2))) (low z (deg div 2))"
              using \<open>invar_vebt (treeList ! high z (deg div 2)) n\<close> both_member_options_equiv_member by blast
            hence abg:"both_member_options summary (high z (deg div 2))"
              by (metis (full_types) "5.hyps"(5) "5.hyps"(6) "5.hyps"(7) \<open>deg div 2 = n\<close> \<open>invar_vebt (treeList ! the (vebt_succ summary (high x (deg div 2)))) n\<close> \<open>z < 2 ^ deg\<close> deg_not_0 exp_split_high_low(1) zero_less_Suc)
            hence abh:"vebt_member summary (high z (deg div 2))" 
              using "5.hyps"(2) valid_member_both_member_options by blast
            have aaa:"(high z (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low z (deg div 2))"
              using abe by auto
            have "high z(deg div 2)< sc \<Longrightarrow> False" 
            proof-
              assume "high z(deg div 2)< sc"
              hence "vebt_member summary (high z(deg div 2))" 
                using abh by blast
              have aaaa:"?h \<le> high z(deg div 2)" 
                by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> div_le_mono high_def less_imp_le_nat)
              have bbbb:"?h \<ge> high z(deg div 2)"   
                using \<open>is_succ_in_set (set_vebt' summary) (high x (deg div 2)) sc\<close> \<open>high z (deg div 2) < sc\<close> abh leD succ_member by auto
              hence "?h = high z (deg div 2)" 
                using aaaa eq_iff by blast
              hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
                using aaa by linarith
              then show False 
                by (metis "33" \<open>high x (deg div 2) = high z (deg div 2)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> x < z\<close> add_diff_cancel_left' bit_concat_def bit_split_inv diff_diff_left zero_less_diff)
            qed
            hence "high z(deg div 2) \<ge> sc" 
              using not_less by blast
            then show " z \<ge> res"
            proof(cases "high z(deg div 2) = sc")
              case True
              hence "vebt_member (treeList ! (high z(deg div 2))) (low z (deg div 2))" 
                using abe by blast
              have "low z (deg div 2) \<ge> miny"
                using True \<open>min_in_set (set_vebt' (treeList ! the (vebt_succ summary (high x (deg div 2))))) miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> abe min_in_set_def set_vebt'_def by auto
              hence "z \<ge> res"
                by (metis (full_types) True \<open>res = 2 ^ (deg div 2) * sc + miny\<close> add_le_cancel_left bit_concat_def bit_split_inv mult.commute)
              then show ?thesis by simp
            next
              case False
              hence "high z(deg div 2) > sc"
                using \<open>sc \<le> high z (deg div 2)\<close> le_less by blast
              then show ?thesis
                by (metis \<open>high res (deg div 2) = sc\<close> div_le_mono high_def leD linear)
            qed
          qed
          hence "is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x res" 
            using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h))))\<close>
              \<open>res = the (Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h)))\<close> \<open>x < res\<close> succ_member by blast
          moreover have "Some res = Some (2^(deg div 2)) *\<^sub>o ?sc +\<^sub>o vebt_mint (treeList ! the ?sc)" 
            by (metis \<open>Some miny = vebt_mint (treeList ! the (vebt_succ summary (high x (deg div 2))))\<close> \<open>res = 2 ^ (deg div 2) * sc + miny\<close> \<open>vebt_succ summary (high x (deg div 2)) = Some sc\<close> add_def mul_def option_shift.simps(3))
          ultimately show ?thesis
            by (metis (mono_tags) is_succ_in_set_def \<open>vebt_succ (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2)) *\<^sub>o vebt_succ summary ?h +\<^sub>o vebt_mint (treeList ! the (vebt_succ summary ?h))\<close> eq_iff option.inject)
        qed
      qed
    next
      case False
      hence 0:"vebt_succ (Node (Some (mi, ma)) deg treeList summary) x  = None"
        by (simp add: \<open>2 \<le> deg\<close> \<open>mi \<le> x\<close> succ_greatereq_min)
      have 1:"x \<ge> 2^deg" 
        by (metis "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) False One_nat_def Suc_le_eq \<open>1 \<le> n\<close> \<open>deg div 2 = n\<close> exp_split_high_low(1) leI zero_less_Suc)
      hence "x \<notin> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
        using "5.hyps"(10) "5.hyps"(9) member_inv set_vebt'_def by fastforce
      hence "\<nexists> ss. is_succ_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x ss"
        using "5.hyps"(10) 1 \<open>mi \<le> x\<close> member_inv succ_member by fastforce
      then show ?thesis using 0 by auto
    qed
  qed
qed

corollary succ_empty: assumes "invar_vebt t n "  
  shows " (vebt_succ t x = None) = ({y. vebt_member t y \<and> y > x} = {})"
proof
  show " vebt_succ t x = None \<Longrightarrow> {y. vebt_member t y \<and> x < y} = {}"
  proof
    show "vebt_succ t x = None \<Longrightarrow> {y. vebt_member t y \<and> x < y} \<subseteq> {}"
    proof-
      assume "vebt_succ t x = None"
      hence "\<nexists> y. is_succ_in_set (set_vebt' t) x y"
        using assms succ_corr by force
      moreover hence "is_succ_in_set (set_vebt' t) x y \<Longrightarrow> vebt_member t y \<and> x < y " for y by auto
      ultimately show "{y. vebt_member t y \<and> x < y} \<subseteq> {}"
        using assms succ_none_empty set_vebt'_def set_vebt_finite by auto
    qed
    show " vebt_succ t x = None \<Longrightarrow> {} \<subseteq> {y. vebt_member t y \<and> x < y}" by simp
  qed
  show " {y. vebt_member t y \<and> x < y} = {} \<Longrightarrow> vebt_succ t x = None"
  proof-
    assume "{y. vebt_member t y \<and> x < y} = {} "
    hence "is_succ_in_set (set_vebt' t) x y \<Longrightarrow> False" for y 
      using succ_member by auto
    thus "vebt_succ t x  = None" 
      by (meson assms not_Some_eq succ_corr)
  qed
qed

theorem succ_correct: "invar_vebt t n \<Longrightarrow> vebt_succ t x = Some sx \<longleftrightarrow>is_succ_in_set (set_vebt t) x sx" 
  by (simp add: succ_corr set_vebt_set_vebt'_valid)

lemma "is_succ_in_set S x y \<longleftrightarrow> min_in_set {s . s \<in> S \<and> s > x} y" 
  using is_succ_in_set_def min_in_set_def by fastforce

lemma helpyd:"invar_vebt t n \<Longrightarrow> vebt_succ t x = Some y \<Longrightarrow> y < 2^n" 
  using member_bound succ_corr succ_member by blast

lemma geqmaxNone:  
  assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) n ""x \<ge> ma " 
  shows "vebt_succ  (Node (Some (mi, ma)) deg treeList summary) x = None "
proof(rule ccontr)
  assume "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x \<noteq> None"
  then obtain y where "vebt_succ (Node (Some (mi, ma)) deg treeList summary) x =  Some y" by auto
  hence  "y > ma \<and> y \<in> set_vebt' ((Node (Some (mi, ma)) deg treeList summary))" 
    by (smt (verit, ccfv_SIG) assms(1) assms(2) dual_order.strict_trans2 member_inv min_in_set_def vebt_mint.simps(3) mint_corr not_less_iff_gr_or_eq succ_corr succ_member)
  then show False 
    by (metis assms(1) leD vebt_maxt.simps(3) maxt_corr_help mem_Collect_eq set_vebt'_def)
qed

end
end
