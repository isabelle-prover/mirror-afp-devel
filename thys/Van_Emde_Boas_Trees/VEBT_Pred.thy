(*by Ammer*)
theory VEBT_Pred imports VEBT_MinMax VEBT_Insert
begin

section \<open>The Predecessor Operation\<close>

definition is_pred_in_set :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_pred_in_set xs x y =  (y \<in> xs \<and> y < x \<and> (\<forall> z \<in> xs. (z < x \<longrightarrow> z \<le> y)))"

context VEBT_internal begin  
  
subsection \<open>Lemmas on Sets and Predecessorship\<close>

corollary pred_member: "is_pred_in_set (set_vebt' t) x y = (vebt_member t y \<and> y < x \<and> (\<forall> z. vebt_member t z \<and> z < x \<longrightarrow> z \<le> y))" 
  using is_pred_in_set_def set_vebt'_def by auto

lemma "finite (A:: nat set) \<Longrightarrow> A \<noteq> {}\<Longrightarrow> Max A \<in> A"
proof(induction A rule: finite.induct)
  case emptyI
  then show ?case by blast
next
  case (insertI A a)
  then show ?case 
    by (meson Max_in finite_insert)
qed

lemma obtain_set_pred: assumes "(x::nat) > z " and "min_in_set A z" and "finite A"  shows "\<exists> y. is_pred_in_set A x y"
proof-
  have "{y \<in> A. y < x} \<noteq> {}"
    using assms(1) assms(2) min_in_set_def by auto
  hence "Max {y \<in> A. y < x} \<in> {y \<in> A. y < x}" 
    by (metis (full_types) Max_eq_iff finite_M_bounded_by_nat)
  moreover have "i \<in> A\<Longrightarrow> i < x \<Longrightarrow> i \<le> Max {y \<in> A. y < x} " for i by simp
  ultimately have "is_pred_in_set A x (Max {y \<in> A. y < x})" 
    using is_pred_in_set_def by auto
  then show?thesis by auto
qed

lemma pred_none_empty: assumes "(\<nexists> x. is_pred_in_set (xs) a x)"  and "finite xs"shows "\<not> (\<exists> x \<in> xs. ord_class.less x a)"
proof-
  have "\<exists> x \<in> xs. ord_class.less x a \<Longrightarrow> False"
  proof-
    assume "\<exists> x \<in> xs. ord_class.less x a"
    hence "{x \<in> xs. ord_class.less x  a} \<noteq> {}" by auto
    hence "Max {y \<in> xs. y < a} \<in> {y \<in> xs. y < a}"
      by (metis (full_types) Max_eq_iff finite_M_bounded_by_nat)
    moreover hence "i \<in> xs \<Longrightarrow>  ord_class.less i  a\<Longrightarrow> 
             ord_class.less_eq i (Max {y \<in> xs. ord_class.less y  a}) " for i 
      by (simp add: assms(2))
    ultimately have "is_pred_in_set xs a (Max {y \<in> xs. y < a})"
      using is_pred_in_set_def by auto
    then show False 
      using assms(1) by blast
  qed
  then show ?thesis by blast
qed

end

subsection \<open>The actual Function for Predecessor Search\<close>

context begin
  interpretation VEBT_internal .

fun vebt_pred :: "VEBT \<Rightarrow> nat \<Rightarrow> nat option" where
  "vebt_pred (Leaf _ _) 0 = None"|
  "vebt_pred (Leaf a _) (Suc 0) = (if a then Some 0 else None)"|
  "vebt_pred (Leaf a b) _ = (if b then Some 1 else if a then Some 0 else None)"|
  "vebt_pred (Node None _ _ _) _ = None"|
  "vebt_pred (Node _ 0 _ _) _ = None"|
  "vebt_pred (Node _ (Suc 0) _ _) _ = None"|
  "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = (
         if x > ma then Some ma 
         else (let l = low x (deg div 2); h = high x (deg div 2) in 
               if h < length treeList then  
                  let minlow = vebt_mint (treeList ! h) in (
                      if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                         Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_pred (treeList ! h) l
                      else let pr = vebt_pred summary h in
                               if pr = None then (
                                  if x > mi then Some mi 
                                  else None)
                               else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) )
               else None))"

end               
               
context VEBT_internal begin
subsection \<open>Auxiliary Lemmas\<close>

lemma pred_max: 
  assumes "deg \<ge> 2" and "(x::nat) > ma" 
  shows "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some ma"
  by (metis VEBT_Pred.vebt_pred.simps(7) add_2_eq_Suc assms(1) assms(2) le_add_diff_inverse)

lemma pred_lesseq_max: 
  assumes "deg \<ge> 2" and "(x::nat) \<le> ma" 
  shows "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =  (let l = low x (deg div 2); h = high x (deg div 2) in 
                       if h < length treeList then  
  
                            let minlow = vebt_mint (treeList ! h) in 
                            (if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_pred (treeList ! h) l
                             else let pr = vebt_pred summary h in
                             if pr = None then (if x > mi then Some mi else None)
                             else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) )

                     else None)"
  by (smt VEBT_Pred.vebt_pred.simps(7) add_numeral_left assms(1) assms(2) leD le_add_diff_inverse numerals(1) plus_1_eq_Suc semiring_norm(2))

lemma pred_list_to_short: 
  assumes "deg \<ge> 2" and "ord_class.less_eq x ma" and " high x (deg div 2) \<ge> length treeList" 
  shows "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = None" 
  by (simp add: assms(1) assms(2) assms(3) leD pred_lesseq_max)


lemma pred_less_length_list: 
  assumes "deg \<ge> 2" and "ord_class.less_eq x  ma" and " high x (deg div 2) < length treeList" 
  shows
  "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = (let l = low x (deg div 2); h = high x (deg div 2); minlow = vebt_mint (treeList ! h) in 
                            (if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_pred (treeList ! h) l
                             else let pr = vebt_pred summary h in
                             if pr = None then (if x > mi then Some mi else None)
                             else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) ))"
  by (simp add: assms(1) assms(2) assms(3) pred_lesseq_max)

subsection \<open>Correctness Proof\<close>

theorem pred_corr: "invar_vebt t n \<Longrightarrow> vebt_pred t x = Some px == is_pred_in_set (set_vebt' t) x px"
proof(induction t n arbitrary: x px rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
  proof(cases x)
    case 0
    then show ?thesis
      by (simp add: is_pred_in_set_def)
  next
    case (Suc sucX)
    hence "x \<ge> 0 \<and> x = Suc sucX" by auto
    then show ?thesis
    proof(cases sucX)
      case 0
      then show ?thesis
        by (simp add: Suc pred_member)
    next
      case (Suc nat)
      hence "x\<ge> 2" 
        by (simp add: \<open>0 \<le> x \<and> x = Suc sucX\<close>)
      then show ?thesis
      proof(cases b)
        case True
        hence "vebt_pred (Leaf a b) x = Some 1"
          by (simp add: Suc \<open>0 \<le> x \<and> x = Suc sucX\<close>)
        moreover have "is_pred_in_set (set_vebt' (Leaf a b)) x 1" 
          by (simp add: Suc True \<open>0 \<le> x \<and> x = Suc sucX\<close> pred_member)
        ultimately show ?thesis
          using pred_member by auto
      next
        case False
        hence "b = False" by simp
        then show ?thesis
        proof(cases a)
          case True
          hence "vebt_pred (Leaf a b) x = Some 0" 
            by (simp add: False Suc \<open>0 \<le> x \<and> x = Suc sucX\<close>)
          moreover have "is_pred_in_set (set_vebt' (Leaf a b)) x 0"
            by (simp add: False True \<open>0 \<le> x \<and> x = Suc sucX\<close> pred_member)
          ultimately show ?thesis 
            by (metis False VEBT_Member.vebt_member.simps(1) option.sel pred_member)
        next
          case False
          then show ?thesis
            by (simp add: Suc \<open>0 \<le> x \<and> x = Suc sucX\<close> pred_member)
        qed
      qed
    qed
  qed
next
  case (2 treeList n summary m deg)
  then show ?case
    by (simp add: pred_member)
next
  case (3 treeList n summary m deg)
  then show ?case
    by (simp add: pred_member)
next
  case (4 treeList n summary m deg mi ma)
  hence "n = m" and "n \<ge> 1" and "deg \<ge> 2" and "deg = n + m"
       apply blast+ 
    using "4.hyps"(2) "4.hyps"(5) Suc_le_eq deg_not_0 apply auto[1]
    using "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) deg_not_0 apply fastforce
    by (simp add: "4.hyps"(6))
  moreover hence thisvalid:"invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using 4 invar_vebt.intros(4)[of treeList n summary m]  by blast
  ultimately have "deg div 2 =n" and "length treeList = 2^n" 
    using add_self_div_2 apply blast by (simp add: "4.hyps"(4) "4.hyps"(5))
  then show ?case
  proof(cases "x > ma")
    case True
    hence 0: "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some ma" 
      by (simp add: \<open>2 \<le> deg\<close> pred_max)
    have 1:"ma = the (vebt_maxt (Node (Some (mi, ma)) deg treeList summary))" by simp
    hence "ma \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
      by (metis VEBT_Member.vebt_member.simps(5) \<open>2 \<le> deg\<close> add_numeral_left arith_simps(1) le_add_diff_inverse mem_Collect_eq numerals(1) plus_1_eq_Suc set_vebt'_def)
    hence 2:"y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> y \<le> x" for y
      using "4.hyps"(9) True member_inv set_vebt'_def by fastforce
    hence 3: "y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> (y < ma \<Longrightarrow> y \<le> x)" for y by blast
    hence 4: "\<forall> y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary). y < ma \<longrightarrow> y \<le> x" by blast
    hence "is_pred_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x ma" 
      by (metis "4.hyps"(9) True \<open>ma \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)\<close> less_or_eq_imp_le mem_Collect_eq member_inv pred_member set_vebt'_def)
    then show ?thesis 
      by (metis "0" option.sel leD le_less_Suc_eq not_less_eq pred_member)
  next
    case False
    hence "x \<le> ma"by simp  
    then show ?thesis 
    proof(cases "high x (deg div 2)< length treeList ")
      case True
      hence "high x n < 2^n \<and> low x n < 2^n"
        by (simp add: \<open>deg div 2 = n\<close> \<open>length treeList = 2 ^ n\<close> low_def)
      let ?l = "low x (deg div 2)" 
      let ?h = "high x (deg div 2)"
      let ?minlow = "vebt_mint (treeList ! ?h)"
      let ?pr = "vebt_pred summary ?h"
      have 1:"vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = 
                           (if ?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some ?h +\<^sub>o vebt_pred (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in
                             if pr = None then (if x > mi then Some mi else None)
                             else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) )"
        by (smt True \<open>2 \<le> deg\<close> \<open>x \<le> ma\<close> pred_less_length_list)     
      then show ?thesis 
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        then obtain minl where 00:"(Some minl = ?minlow) \<and> ?l > minl" by auto
        have 01:"invar_vebt ((treeList ! ?h)) n \<and> (treeList ! ?h) \<in> set treeList "
          by (simp add: "4.hyps"(1) "4.hyps"(4) "4.hyps"(5) \<open>deg div 2 = n\<close> \<open>high x n < 2 ^ n \<and> low x n < 2 ^ n\<close>)
        have  02:"vebt_member ((treeList ! ?h)) minl" 
          using "00" "01" mint_member by auto
        hence 03: "\<exists> y. y < ?l \<and> vebt_member ((treeList ! ?h)) y"
          using "00" by blast 
        hence afinite: "finite (set_vebt' (treeList ! ?h)) " 
          using "01" set_vebt_finite by blast
        then obtain predy where 04:"is_pred_in_set (set_vebt' (treeList ! ?h)) ?l predy"
          using "00" "01" mint_corr obtain_set_pred by fastforce
        hence 05:"Some predy =  vebt_pred (treeList ! ?h) ?l"  using 4(1) 01 by force
        hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x  =  Some (2^(deg div 2)*  ?h + predy) "
          using  "1" True add_def mul_def option_shift.simps(3) by metis
        hence 06: "predy \<in> set_vebt' (treeList ! ?h)" 
          using "04" is_pred_in_set_def by blast
        hence 07: "predy < 2^(deg div 2) \<and> ?h < 2^(deg div 2) \<and> deg div 2 + deg div 2 = deg" 
          using "01" "04" "4.hyps"(5) "4.hyps"(6) \<open>high x n < 2 ^ n \<and> low x n < 2 ^ n\<close> member_bound pred_member by auto
        let ?y = "2^(deg div 2)*  ?h + predy"
        have 08: "vebt_member (treeList ! ?h) predy"
          using "06" set_vebt'_def by auto
        hence 09: "both_member_options (treeList ! ?h) predy"
          using "01" both_member_options_equiv_member by blast
        have 10: "high ?y (deg div 2) = ?h \<and> low ?y (deg div 2) = predy"
          by (simp add: "07" high_inv low_inv mult.commute)
        hence 14:"both_member_options (Node (Some (mi, ma)) deg treeList summary) ?y" 
          by (metis "07" "09" "4.hyps"(4) "4.hyps"(5) Suc_1 \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_chilf_to_complete_tree plus_1_eq_Suc)
        have 15: "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?y" 
          using "14" thisvalid valid_member_both_member_options by blast
        have 16: "Some ?y = vebt_pred (Node (Some (mi, ma)) deg treeList summary) x" 
          by (simp add: \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2) * high x (deg div 2) + predy)\<close>)
        have 17: "x = ?h * 2^(deg div 2) + ?l"
          using bit_concat_def bit_split_inv by auto 
        have 18: "x - ?y =   ?h * 2^(deg div 2) + ?l -?h * 2^(deg div 2) - predy " 
          by (metis "17" diff_diff_add mult.commute)
        hence 19: "?y < x" 
          using "04" "17" mult.commute nat_add_left_cancel_less pred_member by fastforce
        have 20: "z < x \<Longrightarrow> vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<Longrightarrow> z\<le> ?y " for z 
        proof-
          assume "z < x" and "vebt_member (Node (Some (mi, ma)) deg treeList summary) z"
          hence "high z (deg div 2) \<le> high x (deg div 2)" 
            by (simp add: div_le_mono high_def)
          then show ?thesis 
          proof(cases "high z (deg div 2) = high x (deg div 2)")
            case True
            hence 0000: "high z (deg div 2) = high x (deg div 2)" by simp
            then show ?thesis
            proof(cases "z = mi")
              case True
              then show ?thesis
                using "15" vebt_mint.simps(3) mint_corr_help thisvalid by blast
            next
              case False    
              hence ad:"vebt_member (treeList ! ?h) (low z (deg div 2))" 
                using vebt_member.simps(5)[of mi ma "deg-2" treeList summary z]
                by (metis True \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z\<close> \<open>x \<le> ma\<close> \<open>z < x\<close> leD member_inv)
              have "is_pred_in_set (set_vebt' (treeList ! ?h)) ?l predy" 
                using "04" by blast
              have "low z (deg div 2) < ?l" 
                by (metis (full_types) True \<open>z < x\<close> bit_concat_def bit_split_inv nat_add_left_cancel_less)
              hence "predy \<ge> low z (deg div 2)" using 04 ad unfolding is_pred_in_set_def
                by (simp add: set_vebt'_def)
              hence "?y \<ge> z" 
                by (smt True bit_concat_def bit_split_inv diff_add_inverse diff_diff_add diff_is_0_eq mult.commute)
              then show ?thesis by blast
            qed
          next
            case False
            hence "high z (deg div 2) < high ?y (deg div 2)"
              using "10" \<open>high z (deg div 2) \<le> high x (deg div 2)\<close> by linarith
            then show ?thesis 
              by (metis div_le_mono high_def nat_le_linear not_le)
          qed
        qed
        hence "is_pred_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x ?y" 
          by (simp add: "15" "19" pred_member)
        then show ?thesis using 16
          by (metis eq_iff option.inject pred_member)
      next
        case False
        hence i1:"?minlow =  None \<or> \<not> (Some ?l >\<^sub>o  ?minlow)" by simp
        hence 2: "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =  (
                            if ?pr = None then (if x > mi 
                                                then Some mi 
                                                else None)
                             else Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr))" 
          using "1" by auto
        have " invar_vebt (treeList ! ?h) n"
          by (metis "4"(1) True inthall member_def)
        hence 33:"\<nexists> u. vebt_member (treeList ! ?h) u \<and> u < ?l"
        proof(cases "?minlow = None")
          case True
          then show ?thesis using mint_corr_help_empty[of "treeList ! ?h" n] 
            by (simp add: \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> set_vebt'_def)
        next
          case False
          obtain minilow where "?minlow =Some minilow" 
            using False by blast
          hence "minilow \<ge> ?l" 
            using "i1" by auto
          then show ?thesis
            by (meson \<open>vebt_mint (treeList ! high x (deg div 2)) = Some minilow\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> leD less_le_trans mint_corr_help)
        qed
        then show ?thesis 
        proof(cases "?pr= None")
          case True
          hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =  (if x > mi then Some mi else  None)" 
            by (simp add: "2")
          hence "\<nexists> i. is_pred_in_set (set_vebt' summary) ?h i"
            using "4.hyps"(3) True by force
          hence "\<nexists> i. i < ?h \<and> vebt_member summary i " using pred_none_empty[of "set_vebt' summary" ?h] 
          proof -
            { fix nn :: nat
              have "\<forall>n. ((is_pred_in_set (Collect (vebt_member summary)) (high x (deg div 2)) esk1_0 \<or> infinite (Collect (vebt_member summary))) \<or> n \<notin> Collect (vebt_member summary)) \<or> \<not> n < high x (deg div 2)"
                using \<open>\<nexists>i. is_pred_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> pred_none_empty set_vebt'_def by auto
              then have "\<not> nn < high x (deg div 2) \<or> \<not> vebt_member summary nn"
                by (metis (no_types) "4.hyps"(2) \<open>\<nexists>i. is_pred_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> mem_Collect_eq set_vebt'_def set_vebt_finite) }
            then show ?thesis
              by blast
          qed
          then show ?thesis 
          proof(cases "x > mi")
            case True
            hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some mi" 
              by (simp add: \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = (if mi < x then Some mi else None)\<close>)
            have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z  \<and> z < x \<and> z > mi) \<Longrightarrow> False" for z
            proof-
              assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z  \<and> z < x \<and> z > mi"
              hence "vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2))"
                using \<open>x \<le> ma\<close> member_inv not_le by blast
              moreover hence "high z (deg div 2) < 2^m" 
                using "4.hyps"(4) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> \<open>x \<le> ma\<close> member_inv by fastforce
              moreover hence "invar_vebt (treeList ! (high z (deg div 2))) n" using 4(1)
                by (simp add: "4.hyps"(4))
              ultimately have "vebt_member summary (high z (deg div 2))" using 4(7) 
                using "4.hyps"(2) both_member_options_equiv_member by blast
              have "(high z (deg div 2)) \<le> ?h" 
                by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> div_le_mono high_def less_or_eq_imp_le)
              then show False 
                by (metis "33" \<open>\<not> (\<exists>i<high x (deg div 2). vebt_member summary i)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> \<open>vebt_member (treeList ! high z (deg div 2)) (low z (deg div 2))\<close> \<open>vebt_member summary (high z (deg div 2))\<close> bit_concat_def bit_split_inv le_neq_implies_less nat_add_left_cancel_less)
            qed
            hence "is_pred_in_set (set_vebt' ((Node (Some (mi, ma)) deg treeList summary))) x mi" 
              by (metis VEBT_Member.vebt_member.simps(5) True \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse le_less_linear pred_member)
            then show ?thesis 
              by (metis \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some mi\<close> \<open>x \<le> ma\<close> option.sel leD member_inv pred_member)
          next
            case False
            hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = None"
              by (simp add: "2" True)
            then show ?thesis 
              by (metis (full_types) False less_trans member_inv option.distinct(1) pred_max pred_member)
          qed
        next
          case False
          hence fst:"vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =
                    Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr)"
            using "2" by presburger 
          obtain pr where "?pr = Some pr" 
            using False by blast
          hence "is_pred_in_set (set_vebt' summary) ?h pr"
            using "4.hyps"(3) by blast
          hence "vebt_member summary pr"
            using pred_member by blast
          hence "both_member_options summary pr" 
            using "4.hyps"(2) both_member_options_equiv_member by auto
          hence "pr < 2^m" 
            using "4.hyps"(2) \<open>vebt_member summary pr\<close> member_bound by blast
          hence "\<exists> maxy. both_member_options (treeList ! pr) maxy" 
            using "4.hyps"(7) \<open>both_member_options summary pr\<close> by blast
          hence fgh:"set_vebt' (treeList ! pr) \<noteq> {}"
            by (metis "4.hyps"(1) "4.hyps"(2) "4.hyps"(4) \<open>vebt_member summary pr\<close> empty_Collect_eq member_bound nth_mem set_vebt'_def valid_member_both_member_options)
          hence "invar_vebt (treeList ! the ?pr) n"
            by (simp add: "4.hyps"(1) "4.hyps"(4) \<open>pr < 2 ^ m\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close>)
          then obtain maxy where "Some maxy = vebt_maxt (treeList ! pr)" 
            by (metis \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> fgh option.sel vebt_maxt.elims maxt_corr_help_empty)
          hence "Some maxy = vebt_maxt (treeList ! the ?pr)" 
            by (simp add: \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close>)
          hence "max_in_set (set_vebt' (treeList ! the ?pr)) maxy" 
            using \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> maxt_corr by auto
          hence scmem:"vebt_member (treeList ! the ?pr) maxy"
            using \<open>Some maxy = vebt_maxt (treeList ! the (vebt_pred summary (high x (deg div 2))))\<close> \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> maxt_member by force
          let ?res =  "Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr)"
          obtain res where snd: "res = the ?res" by blast
          hence "res = 2^(deg div 2) * pr + maxy" 
            by (metis \<open>Some maxy = vebt_maxt (treeList ! pr)\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> add_def option.sel mul_def option_shift.simps(3))
          have "high res (deg div 2) = pr" 
            by (metis \<open>deg div 2 = n\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> \<open>invar_vebt (treeList ! the ?pr) n\<close> high_inv member_bound mult.commute scmem)
          hence "res < x" 
            by (metis \<open>is_pred_in_set (set_vebt' summary) (high x (deg div 2)) pr\<close> div_le_mono high_def pred_member verit_comp_simplify1(3))
          have "both_member_options (treeList ! (high res (deg div 2))) (low res (deg div 2))"
            by (metis \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = pr\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> both_member_options_equiv_member option.sel low_inv member_bound mult.commute scmem)
          have "both_member_options (Node (Some (mi, ma)) deg treeList summary) res" 
            by (metis "4.hyps"(2) "4.hyps"(4) "4.hyps"(6) \<open>1 \<le> n\<close> \<open>both_member_options (treeList ! high res (deg div 2)) (low res (deg div 2))\<close> \<open>high res (deg div 2) = pr\<close> \<open>vebt_member summary pr\<close> both_member_options_from_chilf_to_complete_tree member_bound trans_le_add1) 
          hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) res" 
            using thisvalid valid_member_both_member_options by auto
          hence "res > mi"
            by (metis "4.hyps"(11) \<open>both_member_options (treeList ! high res (deg div 2)) (low res (deg div 2))\<close> \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = pr\<close> \<open>pr < 2 ^ m\<close> \<open>res < x\<close> \<open>x \<le> ma\<close> less_le_trans member_inv)
          hence "res < ma"
            using \<open>res < x\<close> \<open>x \<le> ma\<close> less_le_trans by blast
          have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x) \<Longrightarrow> z \<le> res" for z
          proof-
            fix z
            assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x"
            hence 20: "z = mi \<or> z = ma \<or> (high z (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              using member_inv by blast
            have "z \<noteq> ma" 
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> \<open>x \<le> ma\<close> leD by blast
            hence "mi \<noteq> ma" 
              by (metis \<open>mi < res\<close> \<open>res < x\<close> \<open>x \<le> ma\<close> leD less_trans)
            hence "z < 2^deg" 
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> member_bound thisvalid by blast
            hence abc:"invar_vebt (treeList ! (high z (deg div 2))) n" 
              by (metis "4.hyps"(1) "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) \<open>deg div 2 = n\<close> \<open>z < 2 ^ deg\<close> \<open>length treeList = 2 ^ n\<close> deg_not_0 exp_split_high_low(1) in_set_member inthall)
            then show "z \<le> res"
            proof(cases "z = mi")
              case True
              then show ?thesis
                using \<open>mi < res\<close> by auto
            next
              case False
              hence abe:"vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
                using "20" \<open>z \<noteq> ma\<close> by blast
              hence abh:"vebt_member summary (high z (deg div 2))"
                by (metis "20" "4.hyps"(2) "4.hyps"(4) "4.hyps"(7) False \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> \<open>x \<le> ma\<close> abc both_member_options_equiv_member not_le)
              have aaa:"(high z (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low z (deg div 2))"
                using abe by auto
              have "high z(deg div 2) > pr \<Longrightarrow> False" 
              proof-
                assume "high z(deg div 2) > pr"
                hence "vebt_member summary (high z(deg div 2))" 
                  using abh by blast
                have aaaa:"?h \<le> high z(deg div 2)"
                  by (meson \<open>is_pred_in_set (set_vebt' summary) (high x (deg div 2)) pr\<close> \<open>pr < high z (deg div 2)\<close> abh leD not_le_imp_less pred_member)
                have bbbb:"?h \<ge> high z(deg div 2)" 
                  by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> div_le_mono dual_order.strict_implies_order high_def)
                hence "?h = high z (deg div 2)" 
                  using aaaa eq_iff by blast
                hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
                  using aaa by linarith
                hence "(low z (deg div 2)) < ?l" 
                  by (metis \<open>high x (deg div 2) = high z (deg div 2)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> add_le_cancel_left div_mult_mod_eq high_def less_le low_def)
                then show False 
                  using "33" \<open>vebt_member (treeList ! high x (deg div 2)) (low z (deg div 2))\<close> by blast
              qed
              hence "high z(deg div 2) \<le> pr" 
                using not_less by blast
              then show " z \<le> res"
              proof(cases "high z(deg div 2) = pr")
                case True
                hence "vebt_member (treeList ! (high z(deg div 2))) (low z (deg div 2))" 
                  using abe by blast
                have "low z (deg div 2) \<le> maxy"
                  using True \<open>Some maxy = vebt_maxt (treeList ! pr)\<close> abc abe maxt_corr_help by auto
                hence "z \<le> res"
                  by (metis True \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> add_le_cancel_left div_mult_mod_eq high_def low_def mult.commute)
                then show ?thesis by simp
              next
                case False
                hence "high z(deg div 2) < pr" 
                  by (simp add: \<open>high z (deg div 2) \<le> pr\<close> less_le)
                then show ?thesis
                  by (metis \<open>high res (deg div 2) = pr\<close> div_le_mono high_def leD linear)
              qed
            qed
          qed
          hence "is_pred_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x res"
            using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) res\<close> \<open>res < x\<close> pred_member by presburger 
          then show ?thesis using fst snd
            by (metis \<open>Some maxy = vebt_maxt (treeList ! the (vebt_pred summary (high x (deg div 2))))\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> add_shift dual_order.eq_iff mul_shift pred_member)
        qed
      qed
    next
      case False
      then show ?thesis 
        by (metis "4.hyps"(10) "4.hyps"(5) "4.hyps"(6) \<open>1 \<le> n\<close> \<open>deg div 2 = n\<close> \<open>length treeList = 2 ^ n\<close> \<open>x \<le> ma\<close> exp_split_high_low(1) le_less_trans le_neq_implies_less not_less not_less_zero zero_neq_one)
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
  moreover hence thisvalid:"invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using 5 invar_vebt.intros(5)[of treeList n summary m]  by blast
  ultimately have "deg div 2 =n" by simp
  then show ?case
  proof(cases "x > ma")
    case True
    hence 0: "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some ma" 
      by (simp add: \<open>2 \<le> deg\<close> pred_max)
    have 1:"ma = the (vebt_maxt (Node (Some (mi, ma)) deg treeList summary))" by simp
    hence "ma \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)"
      by (metis VEBT_Member.vebt_member.simps(5) \<open>2 \<le> deg\<close> add_numeral_left arith_simps(1) le_add_diff_inverse mem_Collect_eq numerals(1) plus_1_eq_Suc set_vebt'_def)
    hence 2:"y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> y \<le> x" for y
      using "5.hyps"(9) True member_inv set_vebt'_def by fastforce
    hence 3: "y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary) \<Longrightarrow> (y < ma \<Longrightarrow> y \<le> x)" for y by blast
    hence 4: "\<forall> y \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary). y < ma \<longrightarrow> y \<le> x" by blast
    hence "is_pred_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x ma" 
      by (metis "5.hyps"(9) True \<open>ma \<in> set_vebt' (Node (Some (mi, ma)) deg treeList summary)\<close> less_or_eq_imp_le mem_Collect_eq member_inv pred_member set_vebt'_def)
    then show ?thesis 
      by (metis "0" option.sel leD le_less_Suc_eq not_less_eq pred_member)
  next
    case False
    hence "x \<le> ma"by simp  
    then show ?thesis 
    proof(cases "high x (deg div 2)< length treeList ")
      case True
      hence "high x n < 2^m \<and> low x n < 2^n"
        by (simp add: \<open>deg div 2 = n\<close> \<open>length treeList = 2 ^ m\<close> low_def)
      let ?l = "low x (deg div 2)" 
      let ?h = "high x (deg div 2)"
      let ?minlow = "vebt_mint (treeList ! ?h)"
      let ?pr = "vebt_pred summary ?h"
      have 1:"vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = 
                           (if ?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow) then 
                                                    Some (2^(deg div 2)) *\<^sub>o Some ?h +\<^sub>o vebt_pred (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in
                             if pr = None then (if x > mi then Some mi else None)
                             else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) )"
        by (smt True \<open>2 \<le> deg\<close> \<open>x \<le> ma\<close> pred_less_length_list)     
      then show ?thesis 
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        then obtain minl where 00:"(Some minl = ?minlow) \<and> ?l > minl" by auto
        have 01:"invar_vebt ((treeList ! ?h)) n \<and> (treeList ! ?h) \<in> set treeList "
          by (metis "5.hyps"(1) \<open>deg div 2 = n\<close> \<open>high x n < 2 ^ m \<and> low x n < 2 ^ n\<close> \<open>length treeList = 2 ^ m \<and> invar_vebt summary m\<close> inthall member_def)
        have  02:"vebt_member ((treeList ! ?h)) minl" 
          using "00" "01" mint_member by auto
        hence 03: "\<exists> y. y < ?l \<and> vebt_member ((treeList ! ?h)) y"
          using "00" by blast 
        hence afinite: "finite (set_vebt' (treeList ! ?h)) " 
          using "01" set_vebt_finite by blast
        then obtain predy where 04:"is_pred_in_set (set_vebt' (treeList ! ?h)) ?l predy"
          using "00" "01" mint_corr obtain_set_pred by fastforce
        hence 05:"Some predy =  vebt_pred (treeList ! ?h) ?l"  using 5(1) 01 by force
        hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x  =  Some (2^(deg div 2)*  ?h + predy) "
          by (metis "1" True add_def mul_def option_shift.simps(3))
        hence 06: "predy \<in> set_vebt' (treeList ! ?h)" 
          using "04" is_pred_in_set_def by blast
        hence 07: "predy < 2^(deg div 2) \<and> ?h < 2^(deg div 2 +1) \<and> deg div 2 + deg div 2 +1 = deg"
          using "04" "5.hyps"(5) "5.hyps"(6) \<open>high x n < 2 ^ m \<and> low x n < 2 ^ n\<close> pred_member by force
        let ?y = "2^(deg div 2)*  ?h + predy"
        have 08: "vebt_member (treeList ! ?h) predy"
          using "06" set_vebt'_def by auto
        hence 09: "both_member_options (treeList ! ?h) predy"
          using "01" both_member_options_equiv_member by blast
        have 10: "high ?y (deg div 2) = ?h \<and> low ?y (deg div 2) = predy"
          by (simp add: "07" high_inv low_inv mult.commute)
        hence 14:"both_member_options (Node (Some (mi, ma)) deg treeList summary) ?y"
          using "07" "09" "5.hyps"(4) \<open>deg div 2 = n\<close> \<open>high x n < 2 ^ m \<and> low x n < 2 ^ n\<close> both_member_options_from_chilf_to_complete_tree by auto
        have 15: "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?y"
          using "14" thisvalid valid_member_both_member_options by blast
        have 16: "Some ?y = vebt_pred (Node (Some (mi, ma)) deg treeList summary) x" 
          by (simp add: \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some (2 ^ (deg div 2) * high x (deg div 2) + predy)\<close>)
        have 17: "x = ?h * 2^(deg div 2) + ?l"
          using bit_concat_def bit_split_inv by auto 
        have 18: "x - ?y =   ?h * 2^(deg div 2) + ?l -?h * 2^(deg div 2) - predy " 
          by (metis "17" diff_diff_add mult.commute)
        hence 19: "?y < x" 
          using "04" "17" mult.commute nat_add_left_cancel_less pred_member by fastforce
        have 20: "z < x \<Longrightarrow> vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<Longrightarrow> z\<le> ?y " for z 
        proof-
          assume "z < x" and "vebt_member (Node (Some (mi, ma)) deg treeList summary) z"
          hence "high z (deg div 2) \<le> high x (deg div 2)" 
            by (simp add: div_le_mono high_def)
          then show ?thesis 
          proof(cases "high z (deg div 2) = high x (deg div 2)")
            case True
            hence 0000: "high z (deg div 2) = high x (deg div 2)" by simp
            then show ?thesis
            proof(cases "z = mi")
              case True
              then show ?thesis 
                by (metis "15" "5.hyps"(9) add.left_neutral le_add2 less_imp_le_nat member_inv)
            next
              case False    
              hence ad:"vebt_member (treeList ! ?h) (low z (deg div 2))" 
                using vebt_member.simps(5)[of mi ma "deg-2" treeList summary z]
                by (metis True \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z\<close> \<open>x \<le> ma\<close> \<open>z < x\<close> leD member_inv)
              have "is_pred_in_set (set_vebt' (treeList ! ?h)) ?l predy" 
                using "04" by blast
              have "low z (deg div 2) < ?l" 
                by (metis (full_types) True \<open>z < x\<close> bit_concat_def bit_split_inv nat_add_left_cancel_less)
              hence "predy \<ge> low z (deg div 2)" using 04 ad unfolding is_pred_in_set_def
                by (simp add: set_vebt'_def)
              hence "?y \<ge> z" 
                by (smt True bit_concat_def bit_split_inv diff_add_inverse diff_diff_add diff_is_0_eq mult.commute)
              then show ?thesis by blast
            qed
          next
            case False
            hence "high z (deg div 2) < high ?y (deg div 2)"
              using "10" \<open>high z (deg div 2) \<le> high x (deg div 2)\<close> by linarith
            then show ?thesis 
              by (metis div_le_mono high_def nat_le_linear not_le)
          qed
        qed
        hence "is_pred_in_set (set_vebt'(Node (Some (mi, ma)) deg treeList summary)) x ?y" 
          by (simp add: "15" "19" pred_member)
        then show ?thesis using 16
          by (metis eq_iff option.inject pred_member)
      next
        case False
        hence i1:"?minlow =  None \<or> \<not> (Some ?l >\<^sub>o  ?minlow)" by simp
        hence 2: "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =  (
                            if ?pr = None then (if x > mi 
                                                then Some mi 
                                                else None)
                             else Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr))" 
          using "1" by auto
        have " invar_vebt (treeList ! ?h) n"
          by (metis "5"(1) True inthall member_def)
        hence 33:"\<nexists> u. vebt_member (treeList ! ?h) u \<and> u < ?l"
        proof(cases "?minlow = None")
          case True
          then show ?thesis using mint_corr_help_empty[of "treeList ! ?h" n] 
            by (simp add: \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> set_vebt'_def)
        next
          case False
          obtain minilow where "?minlow =Some minilow" 
            using False by blast
          hence "minilow \<ge> ?l" 
            using "i1" by auto
          then show ?thesis
            by (meson \<open>vebt_mint (treeList ! high x (deg div 2)) = Some minilow\<close> \<open>invar_vebt (treeList ! high x (deg div 2)) n\<close> leD less_le_trans mint_corr_help)
        qed
        then show ?thesis 
        proof(cases "?pr= None")
          case True
          hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =  (if x > mi then Some mi else  None)" 
            by (simp add: "2")
          hence "\<nexists> i. is_pred_in_set (set_vebt' summary) ?h i"
            using "5.hyps"(3) True by force
          hence "\<nexists> i. i < ?h \<and> vebt_member summary i " using pred_none_empty[of "set_vebt' summary" ?h] 
          proof -
            { fix nn :: nat
              have "\<forall>n. ((is_pred_in_set (Collect (vebt_member summary)) (high x (deg div 2)) esk1_0 \<or> infinite (Collect (vebt_member summary))) \<or> n \<notin> Collect (vebt_member summary)) \<or> \<not> n < high x (deg div 2)"
                using \<open>\<nexists>i. is_pred_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> pred_none_empty set_vebt'_def by auto
              then have "\<not> nn < high x (deg div 2) \<or> \<not> vebt_member summary nn"
                by (metis (no_types) "5.hyps"(2) \<open>\<nexists>i. is_pred_in_set (set_vebt' summary) (high x (deg div 2)) i\<close> mem_Collect_eq set_vebt'_def set_vebt_finite) }
            then show ?thesis
              by blast
          qed
          then show ?thesis 
          proof(cases "x > mi")
            case True
            hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some mi" 
              by (simp add: \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = (if mi < x then Some mi else None)\<close>)
            have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z  \<and> z < x \<and> z > mi) \<Longrightarrow> False" for z
            proof-
              assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z  \<and> z < x \<and> z > mi"
              hence "vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2))"
                using \<open>x \<le> ma\<close> member_inv not_le by blast
              moreover hence "high z (deg div 2) < 2^m" 
                using "5.hyps"(4) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> \<open>x \<le> ma\<close> member_inv by fastforce
              moreover hence "invar_vebt (treeList ! (high z (deg div 2))) n" using 5(1)
                by (simp add: "5.hyps"(4))
              ultimately have "vebt_member summary (high z (deg div 2))" using 5(7) 
                using "5.hyps"(2) both_member_options_equiv_member by blast
              have "(high z (deg div 2)) \<le> ?h" 
                by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> div_le_mono high_def less_or_eq_imp_le)
              then show False 
                by (metis "33" \<open>\<not> (\<exists>i<high x (deg div 2). vebt_member summary i)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x \<and> mi < z\<close> \<open>vebt_member (treeList ! high z (deg div 2)) (low z (deg div 2))\<close> \<open>vebt_member summary (high z (deg div 2))\<close> bit_concat_def bit_split_inv le_neq_implies_less nat_add_left_cancel_less)
            qed
            hence "is_pred_in_set (set_vebt' ((Node (Some (mi, ma)) deg treeList summary))) x mi" 
              by (metis VEBT_Member.vebt_member.simps(5) True \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse le_less_linear pred_member)
            then show ?thesis 
              by (metis \<open>vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = Some mi\<close> \<open>x \<le> ma\<close> option.sel leD member_inv pred_member)
          next
            case False
            hence "vebt_pred (Node (Some (mi, ma)) deg treeList summary) x = None"
              by (simp add: "2" True)
            then show ?thesis 
              by (metis (full_types) False less_trans member_inv option.distinct(1) pred_max pred_member)
          qed
        next
          case False
          hence fst:"vebt_pred (Node (Some (mi, ma)) deg treeList summary) x =
                    Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr)"
            using "2" by presburger 
          obtain pr where "?pr = Some pr" 
            using False by blast
          hence "is_pred_in_set (set_vebt' summary) ?h pr"
            using "5.hyps"(3) by blast
          hence "vebt_member summary pr"
            using pred_member by blast
          hence "both_member_options summary pr" 
            using "5.hyps"(2) both_member_options_equiv_member by auto
          hence "pr < 2^m" 
            using "5.hyps"(2) \<open>vebt_member summary pr\<close> member_bound by blast
          hence "\<exists> maxy. both_member_options (treeList ! pr) maxy" 
            using "5.hyps"(7) \<open>both_member_options summary pr\<close> by blast
          hence fgh:"set_vebt' (treeList ! pr) \<noteq> {}"
            by (metis "5.hyps"(1) "5.hyps"(4) Collect_empty_eq \<open>pr < 2 ^ m\<close> nth_mem set_vebt'_def valid_member_both_member_options)
          hence "invar_vebt (treeList ! the ?pr) n"
            by (simp add: "5.hyps"(1) "5.hyps"(4) \<open>pr < 2 ^ m\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close>)
          then obtain maxy where "Some maxy = vebt_maxt (treeList ! pr)" 
            by (metis \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> fgh option.sel vebt_maxt.elims maxt_corr_help_empty)
          hence "Some maxy = vebt_maxt (treeList ! the ?pr)" 
            by (simp add: \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close>)
          hence "max_in_set (set_vebt' (treeList ! the ?pr)) maxy" 
            using \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> maxt_corr by auto
          hence scmem:"vebt_member (treeList ! the ?pr) maxy"
            using \<open>Some maxy = vebt_maxt (treeList ! the (vebt_pred summary (high x (deg div 2))))\<close> \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> maxt_member by force
          let ?res =  "Some (2^(deg div 2)) *\<^sub>o ?pr +\<^sub>o vebt_maxt (treeList ! the ?pr)"
          obtain res where snd: "res = the ?res" by blast
          hence "res = 2^(deg div 2) * pr + maxy" 
            by (metis \<open>Some maxy = vebt_maxt (treeList ! pr)\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> add_def option.sel mul_def option_shift.simps(3))
          have "high res (deg div 2) = pr" 
            by (metis \<open>deg div 2 = n\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> \<open>invar_vebt (treeList ! the ?pr) n\<close> high_inv member_bound mult.commute scmem)
          hence "res < x" 
            by (metis \<open>is_pred_in_set (set_vebt' summary) (high x (deg div 2)) pr\<close> div_le_mono high_def pred_member verit_comp_simplify1(3))
          have "both_member_options (treeList ! (high res (deg div 2))) (low res (deg div 2))"
            by (metis \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = pr\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> \<open>invar_vebt (treeList ! the (vebt_pred summary (high x (deg div 2)))) n\<close> both_member_options_equiv_member option.sel low_inv member_bound mult.commute scmem)
          have "both_member_options (Node (Some (mi, ma)) deg treeList summary) res" 
            by (metis "5.hyps"(2) "5.hyps"(4) "5.hyps"(6) \<open>1 \<le> n\<close> \<open>both_member_options (treeList ! high res (deg div 2)) (low res (deg div 2))\<close> \<open>high res (deg div 2) = pr\<close> \<open>vebt_member summary pr\<close> both_member_options_from_chilf_to_complete_tree member_bound trans_le_add1) 
          hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) res" 
            using thisvalid valid_member_both_member_options by auto
          hence "res > mi"
            by (metis "5.hyps"(11) \<open>both_member_options (treeList ! high res (deg div 2)) (low res (deg div 2))\<close> \<open>deg div 2 = n\<close> \<open>high res (deg div 2) = pr\<close> \<open>pr < 2 ^ m\<close> \<open>res < x\<close> \<open>x \<le> ma\<close> less_le_trans member_inv)
          hence "res < ma"
            using \<open>res < x\<close> \<open>x \<le> ma\<close> less_le_trans by blast
          have "(vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x) \<Longrightarrow> z \<le> res" for z
          proof-
            fix z
            assume "vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x"
            hence 20: "z = mi \<or> z = ma \<or> (high z (deg div 2) < length treeList 
                                    \<and> vebt_member ( treeList ! (high z (deg div 2))) (low z (deg div 2)))" using
              vebt_member.simps(5)[of mi ma "deg-2" treeList summary z] 
              using member_inv by blast
            have "z \<noteq> ma" 
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> \<open>x \<le> ma\<close> leD by blast
            hence "mi \<noteq> ma" 
              by (metis \<open>mi < res\<close> \<open>res < x\<close> \<open>x \<le> ma\<close> leD less_trans)
            hence "z < 2^deg" 
              using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> member_bound thisvalid by blast
            hence "(high z (deg div 2)) <2^m" 
              by (metis "5.hyps"(5) "5.hyps"(6) \<open>1 \<le> n\<close> \<open>deg div 2 = n\<close> exp_split_high_low(1) less_le_trans numeral_One zero_less_Suc zero_less_numeral)
            hence abc:"invar_vebt (treeList ! (high z (deg div 2))) n" 
              by (simp add: "5.hyps"(1) "5.hyps"(4))
            then show "z \<le> res"
            proof(cases "z = mi")
              case True
              then show ?thesis
                using \<open>mi < res\<close> by auto
            next
              case False
              hence abe:"vebt_member( treeList ! (high z (deg div 2))) (low z (deg div 2))" 
                using "20" \<open>z \<noteq> ma\<close> by blast
              hence abh:"vebt_member summary (high z (deg div 2))"
                using "5.hyps"(7) \<open>high z (deg div 2) < 2 ^ m\<close> \<open>length treeList = 2 ^ m \<and> invar_vebt summary m\<close> abc both_member_options_equiv_member by blast
              have aaa:"(high z (deg div 2)) = (high x (deg div 2)) \<Longrightarrow> vebt_member (treeList ! ?h) (low z (deg div 2))"
                using abe by auto
              have "high z(deg div 2) > pr \<Longrightarrow> False" 
              proof-
                assume "high z(deg div 2) > pr"
                hence "vebt_member summary (high z(deg div 2))" 
                  using abh by blast
                have aaaa:"?h \<le> high z(deg div 2)"
                  by (meson \<open>is_pred_in_set (set_vebt' summary) (high x (deg div 2)) pr\<close> \<open>pr < high z (deg div 2)\<close> abh leD not_le_imp_less pred_member)
                have bbbb:"?h \<ge> high z(deg div 2)" 
                  by (simp add: \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> div_le_mono dual_order.strict_implies_order high_def)
                hence "?h = high z (deg div 2)" 
                  using aaaa eq_iff by blast
                hence "vebt_member (treeList ! ?h) (low z (deg div 2))" 
                  using aaa by linarith
                hence "(low z (deg div 2)) < ?l" 
                  by (metis \<open>high x (deg div 2) = high z (deg div 2)\<close> \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) z \<and> z < x\<close> add_le_cancel_left div_mult_mod_eq high_def less_le low_def)
                then show False 
                  using "33" \<open>vebt_member (treeList ! high x (deg div 2)) (low z (deg div 2))\<close> by blast
              qed
              hence "high z(deg div 2) \<le> pr" 
                using not_less by blast
              then show " z \<le> res"
              proof(cases "high z(deg div 2) = pr")
                case True
                hence "vebt_member (treeList ! (high z(deg div 2))) (low z (deg div 2))" 
                  using abe by blast
                have "low z (deg div 2) \<le> maxy"
                  using True \<open>Some maxy = vebt_maxt (treeList ! pr)\<close> abc abe maxt_corr_help by auto
                hence "z \<le> res"
                  by (metis True \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> add_le_cancel_left div_mult_mod_eq high_def low_def mult.commute)
                then show ?thesis by simp
              next
                case False
                hence "high z(deg div 2) < pr" 
                  by (simp add: \<open>high z (deg div 2) \<le> pr\<close> less_le)
                then show ?thesis
                  by (metis \<open>high res (deg div 2) = pr\<close> div_le_mono high_def leD linear)
              qed
            qed
          qed
          hence "is_pred_in_set (set_vebt' (Node (Some (mi, ma)) deg treeList summary)) x res"
            using \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) res\<close> \<open>res < x\<close> pred_member by presburger 
          then show ?thesis using fst snd
            by (metis \<open>Some maxy = vebt_maxt (treeList ! the (vebt_pred summary (high x (deg div 2))))\<close> \<open>vebt_pred summary (high x (deg div 2)) = Some pr\<close> \<open>res = 2 ^ (deg div 2) * pr + maxy\<close> add_shift dual_order.eq_iff mul_shift pred_member)
        qed
      qed
    next
      case False
      then show ?thesis
        by (metis "5.hyps"(10) "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) \<open>1 \<le> n\<close> \<open>deg div 2 = n\<close> \<open>x \<le> ma\<close> exp_split_high_low(1) le_0_eq le_less_trans verit_comp_simplify1(3) zero_less_Suc zero_neq_one)
    qed
  qed
qed

corollary pred_empty: assumes "invar_vebt t n " 
  shows " (vebt_pred t x = None) = ({y. vebt_member t y \<and> y < x} = {})" 
proof
  show " vebt_pred t x = None \<Longrightarrow> {y. vebt_member t y \<and> x > y} = {}"
  proof
    show "vebt_pred t x = None \<Longrightarrow> {y. vebt_member t y \<and> x > y} \<subseteq> {}"
    proof-
      assume "vebt_pred t x = None"
      hence "\<nexists> y. is_pred_in_set (set_vebt' t) x y" 
        using assms pred_corr by force
      moreover hence "is_pred_in_set (set_vebt' t) x y \<Longrightarrow> vebt_member t y \<and> x < y " for y by auto
      ultimately show "{y. vebt_member t y \<and> x > y} \<subseteq> {}"
        using assms pred_none_empty set_vebt'_def set_vebt_finite by auto
    qed
    show " vebt_pred t x = None \<Longrightarrow> {} \<subseteq> {y. vebt_member t y \<and> x > y}" by simp
  qed
  show " {y. vebt_member t y \<and> x > y} = {} \<Longrightarrow> vebt_pred t x = None"
  proof-
    assume "{y. vebt_member t y \<and> x > y} = {} "
    hence "is_pred_in_set (set_vebt' t) x y \<Longrightarrow> False" for y 
      using pred_member by auto
    thus "vebt_pred t x  = None"
      by (meson assms option_shift.elims pred_corr)
  qed
qed

theorem pred_correct: "invar_vebt t n \<Longrightarrow> vebt_pred t x = Some sx \<longleftrightarrow>is_pred_in_set (set_vebt t) x sx" 
  by (simp add: pred_corr set_vebt_set_vebt'_valid)

lemma helpypredd:"invar_vebt t n \<Longrightarrow> vebt_pred t x = Some y \<Longrightarrow> y < 2^n" 
  using member_bound pred_corr pred_member by blast

lemma "invar_vebt t n \<Longrightarrow> vebt_pred t x = Some y \<Longrightarrow> y < x"
  by (simp add: pred_corr pred_member)

end
end

