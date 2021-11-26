(*by Ammer*)
theory VEBT_Bounds imports VEBT_Height VEBT_Member VEBT_Insert VEBT_Succ VEBT_Pred
begin

section \<open>Upper Bounds for canonical Functions: Relationships between Run Time and Tree Heights\<close>

subsection \<open>Membership test\<close>

context begin

  interpretation VEBT_internal .

fun T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r::"VEBT  \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Leaf a b) x = 2 + (if x = 0 then 1 else 1 +( if x=1 then 1 else 1))"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node None _ _ _) x = 2"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node _ 0 _ _) x = 2"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node _ (Suc 0) _ _) x = 2"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 2 + (
  if x = mi then 1 else 1+ (
  if x = ma then 1  else 1+( 
  if x < mi then 1  else 1+ (
 if x > ma then 1 else 9 +
  (let
        h = high x (deg div 2);
       l = low x (deg div 2) in 
     (if h < length treeList 
         then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
         else 1))))))"


fun T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r'::"VEBT  \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Leaf a b) x = 1"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node None _ _ _) x = 1"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node _ 0 _ _) x = 1"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node _ (Suc 0) _ _) x = 1"|
  "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1+(
 if x = mi then 0 else (
  if x = ma then 0  else ( 
  if x < mi then 0  else  (
 if x > ma then 0 else if (x>mi \<and> x < ma) then 
  (let
        h = high x (deg div 2);
       l = low x (deg div 2) in 
        (if h < length treeList  
         then  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
         else 0))
else 0))))"


lemma height_node: "invar_vebt  (Node (Some (mi, ma)) deg treeList summary) n
                    \<Longrightarrow> height  (Node (Some (mi, ma)) deg treeList summary) >= 1" 
  using height.simps(2) by presburger

theorem member_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r t x \<le> (1+height t)*15"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case by simp
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "n \<ge> 1 \<and> m \<ge> 1"
    by (metis Nat.add_0_right Suc_leI deg_not_0 plus_1_eq_Suc)
  hence "deg \<ge> 2" 
    by (simp add: "4.hyps"(4))
  then show ?case
  proof(cases "x = mi")
    case True
    hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 3"  
      using T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r.simps(5)[of mi ma "deg -2" treeList summary x]
      by (smt (z3) Suc_1 Suc_diff_le Suc_eq_plus1 Suc_leD \<open>2 \<le> deg\<close> diff_Suc_1 diff_Suc_Suc eval_nat_numeral(3))
    then show ?thesis by simp
  next
    case False
    hence "x \<noteq> mi" by simp
    hence 1:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 3 + (
             if x = ma then 1  else 1+( 
             if x < mi then 1  else 1+ (
             if x > ma then 1 else 9 +
            (let h = high x (deg div 2); l = low x (deg div 2) in 
                 (if h < length treeList 
                  then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                  else 1)))))" 
      using  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r.simps(5)[of mi ma "deg -2" treeList summary x]
      by (smt (z3) One_nat_def Suc_1 \<open>2 \<le> deg\<close> add_Suc_shift le_add_diff_inverse numeral_3_eq_3 plus_1_eq_Suc)
    then show ?thesis 
    proof(cases "x = ma")
      case True
      hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 4" using 1 by auto
      then show ?thesis by simp
    next
      case False
      hence "x \<noteq> ma" by simp
      hence 2:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 4 +( 
                 if x < mi then 1  else 1+ (
                 if x > ma then 1 else 9 +
                 (let
                 h = high x (deg div 2);
                 l = low x (deg div 2) in 
                (if h < length treeList 
                 then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                 else 1))))" 
        using 1 by simp
      then show ?thesis 
      proof(cases "x < mi")
        case True
        hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 5" using 2 by auto
        then show ?thesis by simp
      next
        case False
        hence "x > mi"
          using \<open>x \<noteq> mi\<close> antisym_conv3 by blast
        hence 3:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 5 + (
                 if x > ma then 1 else 9 +
                 (let  h = high x (deg div 2); l = low x (deg div 2) in 
                 (if h < length treeList 
                  then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                  else 1)))" 
          using 2 by simp
        then show ?thesis
        proof(cases "x > ma")
          case True
          hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 6" using 3 by simp
          then show ?thesis by simp
        next
          case False
          hence "x < ma"
            by (meson \<open>x \<noteq> ma\<close> nat_neq_iff)
          hence 4:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 14+
                     (let h = high x (deg div 2); l = low x (deg div 2) in 
                     (if h < length treeList 
                      then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                      else 1))"
            using 3 by simp
          let ?h = "high x (deg div 2)"
          let ?l = " low x (deg div 2)"
          have "?h < length treeList" 
            using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>x < ma\<close> high_bound_aux by force
          hence 5:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 15  + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! ?h) ?l" 
            using "4" by presburger
          moreover have "invar_vebt (treeList ! ?h) n \<and>  (treeList ! ?h) \<in> set treeList "
            using "4.IH"(1) \<open>high x (deg div 2) < length treeList\<close> nth_mem by blast
          moreover hence " T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! ?h) ?l \<le>  (1 + height (treeList ! ?h))*15" using "4.IH"(1) by simp
          ultimately have 6:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x \<le>
          15  + 15 * (1 + height (treeList ! ?h))" by simp
          moreover  have "i< length treeList \<Longrightarrow>
               height (treeList ! i) \<le> Max (height ` (insert summary (set treeList)))" for i
            apply (induction treeList arbitrary: i)
             apply simp 
             apply (meson List.finite_set Max_ge finite_imageI finite_insert image_iff nth_mem subsetD subset_insertI)
            done
          moreover hence " (1 + height (treeList ! ?h)) \<le> height  (Node (Some (mi, ma)) deg treeList summary)" 
            by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
          moreover hence " 14 * (1 + height (treeList ! ?h)) \<le> 14 * height  (Node (Some (mi, ma)) deg treeList summary)" by simp
          ultimately show ?thesis using 6 algebra_simps add_mono_thms_linordered_semiring(2) mult.right_neutral order_trans by force
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "n \<ge> 1 \<and> m \<ge> 1"
    by (metis le_add1 plus_1_eq_Suc set_n_deg_not_0)
  hence "deg \<ge> 2" 
    by (simp add: "5.hyps"(4))
  then show ?case
  proof(cases "x = mi")
    case True
    hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 3"  
      using T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r.simps(5)[of mi ma "deg -2" treeList summary x]
      by (smt (z3) One_nat_def Suc_nat_number_of_add \<open>2 \<le> deg\<close> le_add_diff_inverse numeral_3_eq_3 numerals(1) plus_1_eq_Suc semiring_norm(2))
    then show ?thesis by simp
  next
    case False
    hence "x \<noteq> mi" by simp
    hence 1:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 3 + (
                if x = ma then 1  else 1+( 
                if x < mi then 1  else 1+ (
                if x > ma then 1 else 9 +
               (let h = high x (deg div 2); l = low x (deg div 2) in 
                 (if h < length treeList 
                  then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                  else 1)))))" 
      using  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r.simps(5)[of mi ma "deg -2" treeList summary x]
      by (smt (z3) One_nat_def Suc_1 \<open>2 \<le> deg\<close> add_Suc_shift le_add_diff_inverse numeral_3_eq_3 plus_1_eq_Suc)
    then show ?thesis 
    proof(cases "x = ma")
      case True
      hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 4" using 1 by auto
      then show ?thesis by simp
    next
      case False
      hence "x \<noteq> ma" by simp
      hence 2:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 4 +( 
                if x < mi then 1  else 1+ (
                if x > ma then 1 else 9 +
               (let h = high x (deg div 2); l = low x (deg div 2) in 
               (if h < length treeList 
                then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                else 1))))" 
        using 1 by simp
      then show ?thesis 
      proof(cases "x < mi")
        case True
        hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 5" using 2 by auto
        then show ?thesis by simp
      next
        case False
        hence "x > mi"
          using \<open>x \<noteq> mi\<close> antisym_conv3 by blast
        hence 3:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 5 + (
                  if x > ma then 1 else 9 +
                  (let h = high x (deg div 2); l = low x (deg div 2) in 
                  (if h < length treeList  then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l else 1)))"
          using 2 by simp
        then show ?thesis
        proof(cases "x > ma")
          case True
          hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 6" using 3 by simp
          then show ?thesis by simp
        next
          case False
          hence "x < ma"
            by (meson \<open>x \<noteq> ma\<close> nat_neq_iff)
          hence 4:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 14+
                     (let  h = high x (deg div 2); l = low x (deg div 2) in 
                     (if h < length treeList 
                      then 1 + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! h) l 
                      else 1))" 
            using 3 by simp
          let ?h = "high x (deg div 2)"
          let ?l = " low x (deg div 2)"
          have "?h < length treeList" 
            by (metis "5.hyps"(2) "5.hyps"(3) "5.hyps"(4) "5.hyps"(8) \<open>x < ma\<close> add_Suc_right add_self_div_2 even_Suc_div_two high_bound_aux odd_add order.strict_trans)
          hence 5:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x = 15  + T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! ?h) ?l" 
            using "4" by presburger
          moreover have "invar_vebt (treeList ! ?h) n \<and>  (treeList ! ?h) \<in> set treeList "
            using "5.IH"(1) \<open>high x (deg div 2) < length treeList\<close> nth_mem by blast
          moreover hence " T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (treeList ! ?h) ?l \<le>  (1 + height (treeList ! ?h))*15" using "5.IH"(1) by simp
          ultimately have 6:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r (Node (Some (mi, ma)) deg treeList summary) x \<le>
                             15  + 15 * (1 + height (treeList ! ?h))" 
            by simp
          moreover  have "i< length treeList \<Longrightarrow>
               height (treeList ! i) \<le> Max (height ` (insert summary (set treeList)))" for i
            apply (induction treeList arbitrary: i)
             apply simp 
             apply (meson List.finite_set Max_ge finite_imageI finite_insert image_iff nth_mem subsetD subset_insertI)
            done
          moreover hence " (1 + height (treeList ! ?h)) \<le> height  (Node (Some (mi, ma)) deg treeList summary)" 
            by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
          moreover hence " 15 * (1 + height (treeList ! ?h)) \<le> 15 * height  (Node (Some (mi, ma)) deg treeList summary)" by simp
          ultimately show ?thesis using 6 
              algebra_simps add_mono_thms_linordered_semiring(2) mult.right_neutral order_trans by force
        qed
      qed
    qed
  qed
qed

theorem member_bound_height': "invar_vebt t n \<Longrightarrow> T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' t x \<le> (1+height t)" 
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (4 treeList n summary m deg mi ma)
  hence "n \<ge> 1 \<and> m \<ge> 1"
    by (metis Nat.add_0_right Suc_leI deg_not_0 plus_1_eq_Suc)
  hence "deg \<ge> 2" 
    by (simp add: "4.hyps"(4))
  then show ?case
  proof(cases "x = mi")
    case True
    hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1"  
      using T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r'.simps(5)[of mi ma "deg -2" treeList summary x] 
      by (smt (z3) One_nat_def \<open>2 \<le> deg\<close> add_2_eq_Suc ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
    then show ?thesis by simp
  next
    case False
    hence "x \<noteq> mi" by simp
    hence 1:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 + (
               if x = ma then 0  else ( 
               if x < mi then 0  else (
               if x > ma then 0 else 
               (let h = high x (deg div 2);  l = low x (deg div 2) in 
               (if h < length treeList 
                  then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                  else 0)))))" 
      using  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r'.simps(5)[of mi ma "deg -2" treeList summary x] 
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse linorder_not_less nat_less_le)
    then show ?thesis 
    proof(cases "x = ma")
      case True
      hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 1 by auto
      then show ?thesis by simp
    next
      case False
      hence "x \<noteq> ma" by simp
      hence 2:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 +( 
                   if x < mi then 0  else (
                   if x > ma then 0 else 
                   (let h = high x (deg div 2); l = low x (deg div 2) in 
                   (if h < length treeList 
                    then  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                    else 0))))" 
        using 1 by simp
      then show ?thesis 
      proof(cases "x < mi")
        case True
        hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 2 by auto
        then show ?thesis by simp
      next
        case False
        hence "x > mi"
          using \<open>x \<noteq> mi\<close> antisym_conv3 by blast
        hence 3:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 + (
                   if x > ma then 0 else 
                  (let h = high x (deg div 2); l = low x (deg div 2) in 
                  (if h < length treeList 
                   then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                   else 0)))" 
          using 2 by simp
        then show ?thesis
        proof(cases "x > ma")
          case True
          hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 3 by simp
          then show ?thesis by simp
        next
          case False
          hence "x < ma"
            by (meson \<open>x \<noteq> ma\<close> nat_neq_iff)
          hence 4:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1+
                       (let h = high x (deg div 2); l = low x (deg div 2) in 
                       (if h < length treeList 
                        then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                        else 0))" 
            using 3 by simp
          let ?h = "high x (deg div 2)"
          let ?l = " low x (deg div 2)"
          have "?h < length treeList" 
            using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>x < ma\<close> high_bound_aux by force
          hence 5:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1+ T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! ?h) ?l" 
            using "4" by presburger
          moreover have "invar_vebt (treeList ! ?h) n \<and>  (treeList ! ?h) \<in> set treeList "
            using "4.IH"(1) \<open>high x (deg div 2) < length treeList\<close> nth_mem by blast
          moreover hence " T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! ?h) ?l \<le>  (1 + height (treeList ! ?h))*1" using "4.IH"(1) by simp
          ultimately have 6:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x \<le>
                               1 + (1 + height (treeList ! ?h))" by simp
          moreover  have "i< length treeList \<Longrightarrow>
               height (treeList ! i) \<le> Max (height ` (insert summary (set treeList)))" for i
            apply (induction treeList arbitrary: i)
             apply simp 
             apply (meson List.finite_set Max_ge finite_imageI finite_insert image_iff nth_mem subsetD subset_insertI)
            done
          moreover hence " (1 + height (treeList ! ?h)) \<le> height  (Node (Some (mi, ma)) deg treeList summary)" 
            by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
          moreover hence " 14 * (1 + height (treeList ! ?h)) \<le> 14 * height  (Node (Some (mi, ma)) deg treeList summary)" by simp
          ultimately show ?thesis using 6 algebra_simps add_mono_thms_linordered_semiring(2) mult.right_neutral order_trans by force
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "n \<ge> 1 \<and> m \<ge> 1" 
    by (metis le_add1 plus_1_eq_Suc set_n_deg_not_0)
  hence "deg \<ge> 2" 
    by (simp add: "5.hyps"(4))
  then show ?case
  proof(cases "x = mi")
    case True
    hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1"  
      using T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r'.simps(5)[of mi ma "deg -2" treeList summary x] 
      by (smt (z3) One_nat_def \<open>2 \<le> deg\<close> add_2_eq_Suc ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
    then show ?thesis by simp
  next
    case False
    hence "x \<noteq> mi" by simp
    hence 1:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 + (
                if x = ma then 0  else ( 
                if x < mi then 0  else (
                if x > ma then 0 else 
               (let h = high x (deg div 2); l = low x (deg div 2) in 
               (if h < length treeList 
                then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                 else 0)))))" 
      using  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r'.simps(5)[of mi ma "deg -2" treeList summary x] 
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse linorder_not_less nat_less_le)
    then show ?thesis 
    proof(cases "x = ma")
      case True
      hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 1 by auto
      then show ?thesis by simp
    next
      case False
      hence "x \<noteq> ma" by simp
      hence 2:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 +( 
                     if x < mi then 0  else (
                     if x > ma then 0 else 
                    (let h = high x (deg div 2); l = low x (deg div 2) in 
                    (if h < length treeList 
                     then  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                     else 0))))"
        using 1 by simp
      then show ?thesis 
      proof(cases "x < mi")
        case True
        hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 2 by auto
        then show ?thesis by simp
      next
        case False
        hence "x > mi"
          using \<open>x \<noteq> mi\<close> antisym_conv3 by blast
        hence 3:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1 + (
                    if x > ma then 0 else 
                    (let h = high x (deg div 2); l = low x (deg div 2) in 
                    (if h < length treeList 
                     then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                     else 0)))" 
          using 2 by simp
        then show ?thesis
        proof(cases "x > ma")
          case True
          hence "T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1" using 3 by simp
          then show ?thesis by simp
        next
          case False
          hence "x < ma"
            by (meson \<open>x \<noteq> ma\<close> nat_neq_iff)
          hence 4:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1+
                     (let h = high x (deg div 2);  l = low x (deg div 2) in 
                     (if h < length treeList 
                      then T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! h) l 
                      else 0))" 
            using 3 by simp
          let ?h = "high x (deg div 2)"
          let ?l = " low x (deg div 2)"
          have "?h < length treeList" 
            using "5.hyps"(2) "5.hyps"(3) "5.hyps"(4) "5.hyps"(8) \<open>x < ma\<close> high_bound_aux
            by (metis add_Suc_right add_self_div_2 even_Suc_div_two odd_add order.strict_trans)
          hence 5:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x = 1+ T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! ?h) ?l" 
            using "4" by presburger
          moreover have "invar_vebt (treeList ! ?h) n \<and>  (treeList ! ?h) \<in> set treeList "
            using "5.IH"(1) \<open>high x (deg div 2) < length treeList\<close> nth_mem by blast
          moreover hence " T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (treeList ! ?h) ?l \<le>  (1 + height (treeList ! ?h))*1" using "5.IH"(1) by simp
          ultimately have 6:"T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r' (Node (Some (mi, ma)) deg treeList summary) x \<le>
          1 + (1 + height (treeList ! ?h))" by simp
          moreover  have "i< length treeList \<Longrightarrow>
               height (treeList ! i) \<le> Max (height ` (insert summary (set treeList)))" for i
            apply (induction treeList arbitrary: i)
             apply simp 
             apply (meson List.finite_set Max_ge finite_imageI finite_insert image_iff nth_mem subsetD subset_insertI)
            done
          moreover hence " (1 + height (treeList ! ?h)) \<le> height  (Node (Some (mi, ma)) deg treeList summary)" 
            by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
          moreover hence " 14 * (1 + height (treeList ! ?h)) \<le> 14 * height  (Node (Some (mi, ma)) deg treeList summary)" by simp
          ultimately show ?thesis using 6 algebra_simps add_mono_thms_linordered_semiring(2) mult.right_neutral order_trans by force
        qed
      qed
    qed
  qed
qed simp+

theorem member_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r t x \<le> 30 + 15 * lb (lb u)"
  using member_bound_height[of t n x]  height_double_log_univ_size[of u n t] algebra_simps by simp

subsection \<open>Minimum, Maximum, Emptiness Test\<close>

fun T\<^sub>m\<^sub>i\<^sub>n\<^sub>t::"VEBT \<Rightarrow> nat" where
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (Leaf a b) = (1+ (if a then 0 else 1 + (if b then 1 else 1)))"|
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (Node None _ _ _) = 1"|
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (Node (Some (mi,ma)) _ _ _ ) = 1"


lemma mint_bound: "T\<^sub>m\<^sub>i\<^sub>n\<^sub>t t \<le>  3" by (induction t rule: T\<^sub>m\<^sub>i\<^sub>n\<^sub>t.induct) auto

fun T\<^sub>m\<^sub>a\<^sub>x\<^sub>t::"VEBT \<Rightarrow> nat" where
  "T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (Leaf a b) = (1+ (if b then 1 else 1 +( if a then 1  else 1)))"|
  "T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (Node None _ _ _) = 1"|
  "T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (Node (Some (mi,ma)) _ _ _ ) = 1"


lemma maxt_bound: "T\<^sub>m\<^sub>a\<^sub>x\<^sub>t t \<le>  3" by (induction t rule: T\<^sub>m\<^sub>a\<^sub>x\<^sub>t.induct) auto

fun T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l::"VEBT \<Rightarrow> nat" where
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l (Leaf False False) = 1"|
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l (Leaf _ _ ) = 1"|
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l (Node None _ _ _) = 1"|
  "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l (Node (Some _) _ _ _) = 1"


lemma minNull_bound: "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l t \<le> 1"
  by (metis T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l.elims order_refl)

subsection \<open>Insertion\<close>

fun T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t::"VEBT \<Rightarrow> nat \<Rightarrow>nat" where
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Leaf a b) x = 1+ (if x=0 then 1  else 1 + (if x=1 then 1 else 1))"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node info 0 ts s) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node info (Suc 0) ts s) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node None (Suc deg) treeList summary) x = 2"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
  (  let xn = (if x < mi then mi else x); minn = (if x< mi then x else mi);
         l= low xn (deg div 2); h = high xn (deg div 2)
         in
              ( if h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! h) l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! h)+
                               (if minNull (treeList ! h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary h else 1)
               else 1))"

fun T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'::"VEBT \<Rightarrow> nat \<Rightarrow>nat" where
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Leaf a b) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node info 0 ts s) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node info (Suc 0) ts s) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node None (Suc deg) treeList summary) x = 1"|
  "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
     (let xn = (if x < mi then mi else x); minn = (if x< mi then x else mi);
                  l= low xn (deg div 2); h = high xn (deg div 2)
                   in ( if h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! h) l + 
                               (if minNull (treeList ! h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary h else 1) else 1))"

lemma insersimp:assumes "invar_vebt t n" and  "\<nexists> x. both_member_options t x " shows "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t t y \<le> 3"
proof-
  from assms(1) show ?thesis 
  proof(cases)
    case (1 a b)
    then show ?thesis by simp
  next
    case (2 treeList n summary m)
    hence "n+m \<ge> 2"
      by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
    then show ?thesis using   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(4)[of "n+m-2" treeList summary y]
      by (metis "2"(1) "2"(6) add.commute add_2_eq_Suc le_add2 numeral_3_eq_3 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  next
    case (3 treeList n summary m)
    hence "n+m \<ge> 2" 
      by (metis add_mono_thms_linordered_semiring(1) le_add1 nat_1_add_1 plus_1_eq_Suc set_n_deg_not_0)
    then show ?thesis using   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(4)[of "n+m-2" treeList summary y]
      by (metis "3"(1) "3"(6) add.commute add_2_eq_Suc le_add2 numeral_3_eq_3 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  next
    case (4 treeList n summary m mi ma)
    hence "membermima (Node (Some (mi, ma)) (n+m) treeList summary) mi " 
      by (metis Suc_pred assms(1) deg_not_0 membermima.simps(4))
    hence False 
      using "4"(1) "4"(6) assms(2) both_member_options_def by blast
    then show ?thesis by simp
  next
    case (5 treeList n summary m mi ma)
    hence "membermima (Node (Some (mi, ma)) (n+m) treeList summary) mi " 
      by (metis Suc_pred assms(1) deg_not_0 membermima.simps(4))
    hence False
      using "5"(1) "5"(6) assms(2) both_member_options_def by blast
    then show ?thesis by simp
  qed
qed

lemma insertsimp: "invar_vebt t n \<Longrightarrow>  minNull t \<Longrightarrow>  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t t  l \<le> 3" 
  using insersimp min_Null_member valid_member_both_member_options by blast

lemma insersimp':assumes "invar_vebt t n" and  "\<nexists> x. both_member_options t x " shows "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' t y \<le> 1"
  using assms(1) 
  apply cases
  apply simp 
  apply(metis add_self_div_2 deg_not_0 div_greater_zero_iff  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(4) add_2_eq_Suc dual_order.refl less_eqE)
  apply(cases "n\<ge> 2") 
  apply(smt (z3)   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(4)[of "n-2"] T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.elims le_Suc_eq  add_2_eq_Suc le_refl ordered_cancel_comm_monoid_diff_class.add_diff_inverse)  
  apply (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  apply(cases "n\<ge> 2")  
  apply(metis Suc_pred assms(1) assms(2) both_member_options_def deg_not_0 membermima.simps(4))
  apply(metis add_self_div_2 deg_not_0 div_greater_zero_iff  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(4) add_2_eq_Suc dual_order.refl less_eqE)
  apply(cases "n\<ge> 2")  
  apply(metis Suc_pred assms(1) assms(2) both_member_options_def deg_not_0 membermima.simps(4))
  apply (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
 done

lemma insertsimp': "invar_vebt t n \<Longrightarrow>  minNull t \<Longrightarrow>  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' t  l \<le> 1" 
  using insersimp' min_Null_member valid_member_both_member_options by blast

theorem insert_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t t x \<le> (1+height t)*23"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    using  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(1)[of a b x] height.simps(1)[of a b] by simp+ 
next
  case (2 treeList n summary m deg)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  moreover hence "height (Node None deg treeList summary) \<ge> 1" using  height.simps(2)[of None deg treeList summary] by simp
  ultimately show ?case using  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(4)[of "deg-2"treeList summary x] algebra_simps
    by (smt (z3) Suc_1 add_lessD1 eval_nat_numeral(3) le_add_diff_inverse less_Suc_eq_le linorder_not_less mult.left_neutral plus_1_eq_Suc)
next
  case (3 treeList n summary m deg)
  hence "deg \<ge> 2" 
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  moreover hence "height (Node None deg treeList summary) \<ge> 1" using  height.simps(2)[of None deg treeList summary] by simp
  ultimately show ?case using  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(4)[of "deg-2"treeList summary x] algebra_simps
    by (smt (z3) Suc_1 add_lessD1 eval_nat_numeral(3) le_add_diff_inverse less_Suc_eq_le linorder_not_less mult.left_neutral plus_1_eq_Suc)
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  let ?xn = "(if x < mi then mi else x)"
  let ?minn = "(if x< mi then x else mi)"
  let ?l= "low ?xn (deg div 2)" 
  let ?h = "high ?xn (deg div 2)"
  show ?case
  proof(cases "x < mi")
    case True
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1) else 1)"
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h <  length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l \<le> 3"
          by (smt (z3) "0" "1" "4.IH"(1) insertsimp le_add1 nat_add_left_cancel_le nth_mem numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 22 +
               T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 +
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)"
          by (smt (verit, ccfv_SIG) add.commute minNull_bound nat_add_left_cancel_le numeral_Bit0 numeral_Bit1 order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h" using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + (height summary +1)*23" using "4.IH"(2)
          by (smt (verit) add.commute add_le_cancel_left add_le_mono add_mono_thms_linordered_semiring(1) nat_add_left_cancel_le)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> ((1+ height summary)+1 )*23" by simp
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps 
          by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 23\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 diff_eq_eq diff_le_eq diff_less_eq distrib_left distrib_right eq_diff_eq le_diff_eq left_diff_distrib left_diff_distrib' less_diff_eq mult.assoc mult.commute mult.left_commute power_mult_distrib right_diff_distrib right_diff_distrib' scaleR_add_left scaleR_add_right scale_left_diff_distrib scale_right_diff_distrib add_mono le_trans mult_le_mono order_refl)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 20+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ (1+ height (treeList ! ?h))*23"
          by (meson "4.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x  \<le> ((1+ height (treeList!?h))+1)*23" by simp
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis 
        using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(7) "4.hyps"(8) True high_bound_aux by auto
    qed
  next 
    case False
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l \<le> 3"
          by (smt (z3) "0" "1" "4.IH"(1) insertsimp le_add1 nat_add_left_cancel_le nth_mem numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 22 +
               T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 +
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)"
          by (smt (verit, ccfv_SIG) add.commute minNull_bound nat_add_left_cancel_le numeral_Bit0 numeral_Bit1 order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h" using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + (height summary +1)*23" using "4.IH"(2)
          by (smt (verit) add.commute add_le_cancel_left add_le_mono add_mono_thms_linordered_semiring(1) nat_add_left_cancel_le)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> ((1+ height summary)+1 )*23" by simp
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps 
          by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 23\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 diff_eq_eq diff_le_eq diff_less_eq distrib_left distrib_right eq_diff_eq le_diff_eq left_diff_distrib left_diff_distrib' less_diff_eq mult.assoc mult.commute mult.left_commute power_mult_distrib right_diff_distrib right_diff_distrib' scaleR_add_left scaleR_add_right scale_left_diff_distrib scale_right_diff_distrib add_mono le_trans mult_le_mono order_refl)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 20+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ (1+ height (treeList ! ?h))*23"
          by (meson "4.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x  \<le> ((1+ height (treeList!?h))+1)*23" by simp
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis
        using "0" by force
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2" 
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  let ?xn = "(if x < mi then mi else x)"
  let ?minn = "(if x< mi then x else mi)"
  let ?l= "low ?xn (deg div 2)" 
  let ?h = "high ?xn (deg div 2)"
  show ?case
  proof(cases "x < mi")
    case True
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
          ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
          T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
          (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l \<le> 3"
          by (smt (z3) "0" "1" "5.IH"(1) insertsimp le_add1 nat_add_left_cancel_le nth_mem numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 22 +
                  T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+(if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 
               23 + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)"
          by (smt (verit, ccfv_SIG) add.commute minNull_bound nat_add_left_cancel_le numeral_Bit0 numeral_Bit1 order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h" using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + (height summary +1)*23" using "5.IH"(2)
          by (smt (verit) add.commute add_le_cancel_left add_le_mono add_mono_thms_linordered_semiring(1) nat_add_left_cancel_le)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> ((1+ height summary)+1 )*23" by simp
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps 
          by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 23\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 diff_eq_eq diff_le_eq diff_less_eq distrib_left distrib_right eq_diff_eq le_diff_eq left_diff_distrib left_diff_distrib' less_diff_eq mult.assoc mult.commute mult.left_commute power_mult_distrib right_diff_distrib right_diff_distrib' scaleR_add_left scaleR_add_right scale_left_diff_distrib scale_right_diff_distrib add_mono le_trans mult_le_mono order_refl)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 20+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ (1+ height (treeList ! ?h))*23"
          by (meson "5.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x  \<le> ((1+ height (treeList!?h))+1)*23" by simp
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis
        by (smt (z3) "0" Suc_eq_plus1 Suc_numeral add_lessD1 linorder_not_less mult_Suc not_add_less1 plus_1_eq_Suc semiring_norm(5) semiring_norm(8))
    qed
  next 
    case False
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 19+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+
                (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l \<le> 3"
          by (smt (z3) "0" "1" "5.IH"(1) insertsimp le_add1 nat_add_left_cancel_le nth_mem 
              numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 22 +
               T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)+(if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 +
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h else 1)"
          by (smt (verit, ccfv_SIG) add.commute minNull_bound nat_add_left_cancel_le numeral_Bit0 numeral_Bit1 order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t summary ?h" using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23 + (height summary +1)*23" using "5.IH"(2)
          by (smt (verit) add.commute add_le_cancel_left add_le_mono add_mono_thms_linordered_semiring(1) nat_add_left_cancel_le)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> ((1+ height summary)+1 )*23" by simp
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps 
          by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 23\<close> add.assoc add.commute add.left_commute add_diff_eq diff_add_eq diff_diff_add diff_diff_eq2 diff_eq_eq diff_le_eq diff_less_eq distrib_left distrib_right eq_diff_eq le_diff_eq left_diff_distrib left_diff_distrib' less_diff_eq mult.assoc mult.commute mult.left_commute power_mult_distrib right_diff_distrib right_diff_distrib' scaleR_add_left scaleR_add_right scale_left_diff_distrib scale_right_diff_distrib add_mono le_trans mult_le_mono order_refl)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x = 20+
              T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l + T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l  (treeList ! ?h)" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x \<le> 23+ (1+ height (treeList ! ?h))*23"
          by (meson "5.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t (Node (Some (mi,ma)) deg treeList summary) x  \<le> ((1+ height (treeList!?h))+1)*23" by simp
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis
        using "0" by force
    qed
  qed
qed


theorem insert_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t t x \<le> 46 + 23 * lb (lb u)"
  using insert_bound_height[of t n x]  height_double_log_univ_size[of u n t] algebra_simps by simp

theorem insert'_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' t x \<le> (1+height t)"
proof(induction  t  n arbitrary: x rule: invar_vebt.induct )
  case (2 treeList n summary m deg)
  then show ?case apply(cases "deg \<ge> 2")
    apply (metis "2.hyps"(1) "2.hyps"(3) "2.hyps"(4) Suc_leI T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(4) add_le_cancel_right deg_not_0 le_add2 le_add_diff_inverse nat_less_le plus_1_eq_Suc)
    apply (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
    done
next
  case (3 treeList n summary m deg)
  then show ?case apply(cases "deg \<ge> 2")
    apply (metis T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(4) add_Suc_shift leI le_Suc_ex not_add_less1 one_add_one plus_1_eq_Suc) 
    by (metis One_nat_def Suc_eq_plus1 T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(3) add.commute add_mono le_SucE le_add1 numeral_2_eq_2)
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  let ?xn = "(if x < mi then mi else x)"
  let ?minn = "(if x< mi then x else mi)"
  let ?l= "low ?xn (deg div 2)" 
  let ?h = "high ?xn (deg div 2)"
  show ?case
  proof(cases "x < mi")
    case True
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h <  length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
      T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l +(if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)" 
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l \<le> 1" 
          by (metis "0" "1" "4.IH"(1) insertsimp' nat_le_iff_add nth_mem)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h" using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + (height summary +1)" using "4.IH"(2) 
          using "1" \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! high (if x < mi then mi else x) (deg div 2)) (low (if x < mi then mi else x) (deg div 2)) \<le> 1\<close> add_mono_thms_linordered_semiring(1) by fastforce
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps by linarith
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
           1+   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l " using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ (1+ height (treeList ! ?h))"
          using "4.IH"(1) True by force
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis   using "0" Suc_eq_plus1 le_add2 plus_1_eq_Suc by presburger
    qed
  next 
    case False
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x =
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l +
                (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)"
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l \<le> 1"
          by (smt (z3) "0" "1" "4.IH"(1) insertsimp' le_add1 nat_add_left_cancel_le nth_mem numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h" using True by simp
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps
          by (smt (z3) "1" "4.IH"(2) True \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! high (if x < mi then mi else x) (deg div 2)) (low (if x < mi then mi else x) (deg div 2)) \<le> 1\<close> add_mono order_trans)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 1+
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ (1+ height (treeList ! ?h))"
          by (meson "4.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis
        using "0" by force
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2" 
    by (metis Suc_1 add_mono le_add1 plus_1_eq_Suc set_n_deg_not_0)
  let ?xn = "(if x < mi then mi else x)"
  let ?minn = "(if x< mi then x else mi)"
  let ?l= "low ?xn (deg div 2)" 
  let ?h = "high ?xn (deg div 2)"
  show ?case
  proof(cases "x < mi")
    case True
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + 
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)
 else 1)" using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h <  length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
      T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)"
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l \<le> 1" 
          by (metis "0" "1" "5.IH"(1) insertsimp' nat_le_iff_add nth_mem)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+
                               (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h"
          using True by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + (height summary +1)" 
          using "5.IH"(2) "1" \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! high (if x < mi then mi else x) (deg div 2))
                 (low (if x < mi then mi else x) (deg div 2)) \<le> 1\<close> add_mono_thms_linordered_semiring(1) 
          by fastforce
        then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps by linarith
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
           1+   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l " using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ (1+ height (treeList ! ?h))"
          using "5.IH"(1) True by force
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis   using "0" Suc_eq_plus1 le_add2 plus_1_eq_Suc by presburger
    qed
  next 
    case False
    hence 0:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x =
              ( if ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1) else 1)" 
      using T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t'.simps(5)[of mi ma "deg -2 " treeList summary x]
      by (smt (z3) \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse)
    then show ?thesis 
    proof(cases " ?h < length treeList \<and> \<not> (x = mi \<or> x = ma)")
      case True
      hence 1: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 
                T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l + (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)"
        using 0 by simp
      then show ?thesis 
      proof(cases " minNull (treeList ! ?h)")
        case True 
        hence " T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l \<le> 1"
          by (smt (z3) "0" "1" "5.IH"(1) insertsimp' le_add1 nat_add_left_cancel_le nth_mem numeral_3_eq_3 order_trans plus_1_eq_Suc)
        hence 2: "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+
                          (if minNull (treeList ! ?h) then  T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h else 1)" 
          using 1 algebra_simps by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1 + T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' summary ?h" 
          using True by simp
        then show ?thesis 
          using height_compose_summary[of summary "Some (mi, ma)" deg treeList] algebra_simps
          by (smt (z3) "1" "5.IH"(2) True \<open>T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! high (if x < mi then mi else x) (deg div 2)) (low (if x < mi then mi else x) (deg div 2)) \<le> 1\<close> add_mono order_trans)
      next
        case False
        hence 2:"T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x = 1+
                 T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l" using 1 by simp
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (treeList ! ?h) ?l "
          using minNull_bound[of "treeList ! ?h"] algebra_simps by linarith
        hence "T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t' (Node (Some (mi,ma)) deg treeList summary) x \<le> 1+ (1+ height (treeList ! ?h))"
          by (meson "5.IH"(1) True nat_add_left_cancel_le nth_mem order_trans)
        moreover have " (treeList!?h) \<in> set treeList" 
          using True nth_mem by blast
        ultimately show ?thesis using height_compose_child[of "treeList!?h" treeList "Some (mi, ma)" deg summary] algebra_simps
          by (smt (verit, ccfv_SIG) Suc_leI add.right_neutral le_add1 le_imp_less_Suc mult_le_mono order_trans plus_1_eq_Suc) 
      qed
    next
      case False
      then show ?thesis
        using "0" by force
    qed
  qed
qed simp+

subsection \<open>Successor Function\<close>

fun T\<^sub>s\<^sub>u\<^sub>c\<^sub>c::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Leaf _ b) 0 = 1+ (if b then 1 else 1)"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Leaf _ _) (Suc n) = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node None _ _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node _ 0 _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node _ (Suc 0) _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x = 1+ (
               if x < mi then 1
               else (let l = low x (deg div 2); h = high x (deg div 2) in 10 + 
                    (if h < length treeList then  1+ T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! h) + (
                            let maxlow = vebt_maxt (treeList ! h) in 3 +
                            (if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                                                   4 +  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! h) l
                             else let sc = vebt_succ summary h in 1+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary h + 1 + (
                             if sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the sc) ))))

                     else 1)))"

fun T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'::"VEBT \<Rightarrow> nat \<Rightarrow> nat" where
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Leaf _ b) 0 = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Leaf _ _) (Suc n) = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node None _ _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node _ 0 _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node _ (Suc 0) _ _) _ = 1"|
  "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x =(
               if x < mi then 1
               else (let l = low x (deg div 2); h = high x (deg div 2) in  
                    (if h < length treeList then  (
                            let maxlow = vebt_maxt (treeList ! h) in 
                            (if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                                                    1+ T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! h) l
                             else let sc = vebt_succ summary h in  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' summary h + (
                             if sc = None then 1
                             else 1 )))
                     else 1)))"

theorem succ_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>s\<^sub>u\<^sub>c\<^sub>c t x \<le> (1+height t)*27"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case using  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(1)[of a b] 
  proof -
    have "\<forall>b v ba n. T\<^sub>s\<^sub>u\<^sub>c\<^sub>c v n = 1 \<or> Leaf b ba \<noteq> v \<or> 0 = n"
      using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.elims by blast
    then show ?thesis
      by (metis (no_types) Nat.add_0_right \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Leaf a b) 0 = 1 + (if b then 1 else 1)\<close> height.simps(1) nat_mult_1 numeral_le_iff one_add_one one_le_numeral semiring_norm(68) semiring_norm(72))
  qed
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case  by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case
  proof(cases "x < mi")
    case True
    then show ?thesis using  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x]
      by (smt (z3) Suc_leI \<open>2 \<le> deg\<close> add_2_eq_Suc distrib_right le_add_diff_inverse linorder_not_less mult.left_neutral numeral_le_one_iff plus_1_eq_Suc semiring_norm(70) trans_le_add1)
  next
    case False
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    show ?thesis 
    proof(cases "?h < length treeList")
      case True
      hence "?h < length treeList" by simp
      hence 0:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =12 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + (
                            let maxlow = vebt_maxt (treeList ! ?h) in 3 +
                            (if maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  maxlow) then 
                                                   4 +  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l
                             else let sc = vebt_succ summary ?h in 1+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h + 1 + (
                             if sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the sc) ))))" using 
        T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x] False True 
        by (smt (z3) \<open>2 \<le> deg\<close> add.commute add.left_commute add_2_eq_Suc' le_add_diff_inverse numeral_plus_one semiring_norm(5) semiring_norm(8))
      let ?maxlow= "vebt_maxt (treeList ! ?h)"
      let ?sc="vebt_succ summary ?h"
      have 1:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =15 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                            (if ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow) then 
                                                   4 +  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l
                             else 2+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +  (
                             if ?sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc))))" using 0 by auto
      then show ?thesis
      proof(cases " ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow)")
        case True
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x = 
                   19 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l" 
          using 1 by simp
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 22 + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l" using maxt_bound[of "treeList ! ?h"] 
          by simp
        moreover have a:"treeList ! ?h \<in> set treeList "
          by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 22 + (1+ height (treeList ! ?h))*27" 
          by (meson "4.IH"(1) nat_add_left_cancel_le order_trans)
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 ((1+ height (treeList ! ?h))+1)*27" by simp
        then show ?thesis 
          using height_compose_child[of "treeList ! ?h" treeList "Some (mi, ma)" deg summary] a
          by (smt (z3) Suc_leI add.commute dual_order.strict_trans2 le_imp_less_Suc linorder_not_less mult.commute mult_le_mono2 plus_1_eq_Suc) 
      next
        case False
        have 2:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =17 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                             T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +  (
                             if ?sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc)))" using 1
          by (smt (z3) False Suc_eq_plus1 add.assoc add.commute add_2_eq_Suc' eval_nat_numeral(3) numeral_plus_one semiring_norm(2) semiring_norm(8))       
        then show ?thesis 
        proof(cases " ?sc = None")
          case True
          hence 3:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =
                   18 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h "
            using 2 by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 21 +   T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h" 
            using maxt_bound[of "treeList ! ?h"] by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 21 +   (1+ height summary)*27"
            by (metis "3" "4.IH"(2) add_le_cancel_right add_le_mono)
          then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
        next
          case False
          hence 3:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =21 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                             T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +   T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc)" using 2 by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 27+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h " 
            using maxt_bound[of "treeList ! ?h"] mint_bound[of "treeList ! the ?sc"] by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 27+ (1+height summary)*27"
            by (meson "4.IH"(2) add_mono_thms_linordered_semiring(2) dual_order.trans) 
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> ((1+height summary)+1)*27" by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> (height (Node (Some (mi, ma)) deg treeList summary) + 1)*27"
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList]
            by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 27\<close> add.commute add_mono le_numeral_extra(4) le_trans mult.commute mult_le_mono2)
          then show ?thesis by simp
        qed
      qed
    next
      case False
      hence " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x = 12" 
        using  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x]
        by (smt (z3) "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(7) "4.hyps"(8) \<open>2 \<le> deg\<close> add_Suc add_self_div_2 dual_order.strict_trans2 high_bound_aux le_add_diff_inverse less_imp_le_nat numeral_plus_one numerals(1) plus_1_eq_Suc semiring_norm(2) semiring_norm(5) semiring_norm(8))
      then show ?thesis
        by auto
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case
  proof(cases "x < mi")
    case True
    then show ?thesis 
      using  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x]
      by (smt (z3) Suc_leI \<open>2 \<le> deg\<close> add_2_eq_Suc distrib_right le_add_diff_inverse linorder_not_less mult.left_neutral numeral_le_one_iff plus_1_eq_Suc semiring_norm(70) trans_le_add1)
  next
    case False
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    show ?thesis 
    proof(cases "?h < length treeList")
      case True
      hence "?h < length treeList" by simp
      hence 0:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =12 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + (
                            let maxlow = vebt_maxt (treeList ! ?h) in 3 +
                            (if maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  maxlow) then 
                                                   4 +  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l
                             else let sc = vebt_succ summary ?h in 1+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h + 1 + (
                             if sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the sc) ))))" using 
        T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x] False True 
        by (smt (z3) \<open>2 \<le> deg\<close> add.commute add.left_commute add_2_eq_Suc' le_add_diff_inverse numeral_plus_one semiring_norm(5) semiring_norm(8))
      let ?maxlow= "vebt_maxt (treeList ! ?h)"
      let ?sc="vebt_succ summary ?h"
      have 1:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =15 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                            (if ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow) then 
                                                   4 +  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l
                             else 2+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +  (
                             if ?sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc))))" using 0 by auto
      then show ?thesis
      proof(cases " ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o  ?maxlow)")
        case True
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x = 
                   19 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l" using 1 by simp
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 22 + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (treeList ! ?h) ?l" using maxt_bound[of "treeList ! ?h"] by simp
        moreover have a:"treeList ! ?h \<in> set treeList "
          by (simp add: \<open>high x (deg div 2) < length treeList\<close>)
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 22 + (1+ height (treeList ! ?h))*27" 
          by (meson "5.IH"(1) nat_add_left_cancel_le order_trans)
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 
                 ((1+ height (treeList ! ?h))+1)*27" by simp
        then show ?thesis using height_compose_child[of "treeList ! ?h" treeList "Some (mi, ma)" deg summary] a
          by (smt (z3) Suc_leI add.commute dual_order.strict_trans2 le_imp_less_Suc linorder_not_less mult.commute mult_le_mono2 plus_1_eq_Suc) 
      next
        case False
        have 2:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =17 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                             T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +  (
                             if ?sc = None then 1
                             else (4 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc)))" using 1
          by (smt (z3) False Suc_eq_plus1 add.assoc add.commute add_2_eq_Suc' eval_nat_numeral(3) numeral_plus_one semiring_norm(2) semiring_norm(8))       
        then show ?thesis 
        proof(cases " ?sc = None")
          case True
          hence 3:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =18 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                             T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h " using 2 by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 21 +   T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h" 
            using maxt_bound[of "treeList ! ?h"] by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 21 +   (1+ height summary)*27"
            by (metis "3" "5.IH"(2) add_le_cancel_right add_le_mono)
          then show ?thesis using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
        next
          case False
          hence 3:"T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x =21 + T\<^sub>m\<^sub>a\<^sub>x\<^sub>t  (treeList ! ?h) + 
                             T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h +   T\<^sub>m\<^sub>i\<^sub>n\<^sub>t (treeList ! the ?sc)" using 2 by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 27+  T\<^sub>s\<^sub>u\<^sub>c\<^sub>c summary ?h " 
            using maxt_bound[of "treeList ! ?h"] mint_bound[of "treeList ! the ?sc"] by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> 27+ (1+height summary)*27"
            by (meson "5.IH"(2) add_mono_thms_linordered_semiring(2) dual_order.trans) 
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> ((1+height summary)+1)*27" by simp
          hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> (height (Node (Some (mi, ma)) deg treeList summary) + 1)*27"
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList]
            by (simp add: \<open>1 + height summary \<le> height (Node (Some (mi, ma)) deg treeList summary)\<close> \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x \<le> (1 + height summary + 1) * 27\<close> add.commute add_mono le_numeral_extra(4) le_trans mult.commute mult_le_mono2)
          then show ?thesis by simp
        qed
      qed
    next
      case False
      hence " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c (Node (Some (mi, ma)) deg treeList summary) x = 12" using
              T\<^sub>s\<^sub>u\<^sub>c\<^sub>c.simps(6)[of mi ma "deg-2" treeList summary x] "5.hyps"(2) "5.hyps"(3) "5.hyps"(4)
             "5.hyps"(7) "5.hyps"(8) \<open>2 \<le> deg\<close> add_Suc add_self_div_2 dual_order.strict_trans2
              high_bound_aux le_add_diff_inverse less_imp_le_nat numeral_plus_one numerals(1)
              plus_1_eq_Suc semiring_norm(2) semiring_norm(5) semiring_norm(8) apply auto 
        by (smt (z3) "5.hyps"(4) le_less_trans less_trans power_Suc)
      then show ?thesis
        by auto
    qed
  qed
qed

theorem succ_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>s\<^sub>u\<^sub>c\<^sub>c t x \<le> 54 + 27 * lb (lb u)"
  using succ_bound_height[of t n x] height_double_log_univ_size[of u n t] by simp

theorem succ'_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' t x \<le> (1+height t)"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    by (metis One_nat_def T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(1) T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(2) height.simps(1) le_add2 le_add_same_cancel2 le_neq_implies_less less_imp_Suc_add order_refl plus_1_eq_Suc)
next
  case (4 treeList n summary m deg mi ma)
  hence degprop: "deg \<ge> 2"
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case
  proof(cases "x< mi")
    case True
    then show ?thesis using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop 
      by (metis add_2_eq_Suc le_add_diff_inverse le_numeral_extra(4) trans_le_add1)
  next
    case False
    hence "x \<ge> mi" by simp
    let ?l = "low x (deg div 2)" 
    let ?h = "high x (deg div 2)"
    show ?thesis
    proof(cases "?h < length treeList")
      case True
      hence hprop: "?h < length treeList" by simp
      let ?maxlow = "vebt_maxt (treeList ! ?h)"
      show ?thesis 
      proof(cases " ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o ?maxlow)")
        case True
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x =  1+ T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! ?h) ?l"
          using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop hprop 
          by (smt (z3) False add_2_eq_Suc le_add_diff_inverse)
        moreover have " (treeList ! ?h) \<in> set treeList" 
          using hprop nth_mem by blast
        moreover have " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! ?h) ?l \<le> 1+ height (treeList ! ?h)" using 4(1)  calculation by blast
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height (treeList ! ?h)" by simp  
        then show ?thesis
          by (smt (z3) Suc_le_mono \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x = 1 + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! high x (deg div 2)) (low x (deg div 2))\<close> \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! high x (deg div 2)) (low x (deg div 2)) \<le> 1 + height (treeList ! high x (deg div 2))\<close> \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> height_compose_child le_trans plus_1_eq_Suc)
      next
        case False
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x =  1+ T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' summary ?h"
          using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop hprop 
          apply(cases " vebt_succ summary ?h") using False add_2_eq_Suc le_add_diff_inverse
          apply (smt (z3) Suc_eq_plus1 \<open>mi \<le> x\<close> linorder_not_less plus_1_eq_Suc)+
          done
        moreover have " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' summary ?h \<le> 1+ height summary" using 4(2)  calculation by blast
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height summary" by simp     
        then show ?thesis 
          by (simp add: le_trans)
      qed
    next
      case False
      then show ?thesis  using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop
        by (smt (z3) add_2_eq_Suc leI le_add_diff_inverse not_add_less1)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence degprop: "deg \<ge> 2" 
    by (metis Suc_1 add_mono le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case
  proof(cases "x< mi")
    case True
    then show ?thesis using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop 
      by (metis add_2_eq_Suc le_add_diff_inverse le_numeral_extra(4) trans_le_add1)
  next
    case False
    hence "x \<ge> mi" by simp
    let ?l = "low x (deg div 2)" 
    let ?h = "high x (deg div 2)"
    show ?thesis
    proof(cases "?h < length treeList")
      case True
      hence hprop: "?h < length treeList" by simp
      let ?maxlow = "vebt_maxt (treeList ! ?h)"
      show ?thesis 
      proof(cases " ?maxlow \<noteq> None \<and> (Some ?l <\<^sub>o ?maxlow)")
        case True
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x =  1+ T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! ?h) ?l"
          using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop hprop 
          by (smt (z3) False add_2_eq_Suc le_add_diff_inverse)
        moreover have " (treeList ! ?h) \<in> set treeList" 
          using hprop nth_mem by blast
        moreover have " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! ?h) ?l \<le> 1+ height (treeList ! ?h)" using 5(1)  calculation by blast
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height (treeList ! ?h)" by simp  
        then show ?thesis
          by (smt (z3) Suc_le_mono \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x = 1 + T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! high x (deg div 2)) (low x (deg div 2))\<close> \<open>T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (treeList ! high x (deg div 2)) (low x (deg div 2)) \<le> 1 + height (treeList ! high x (deg div 2))\<close> \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> height_compose_child le_trans plus_1_eq_Suc)
      next
        case False
        hence "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x =  1+ T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' summary ?h"
          using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop hprop 
          by (cases " vebt_succ summary ?h")
            (smt (z3) Suc_eq_plus1 \<open>mi \<le> x\<close> linorder_not_less plus_1_eq_Suc False add_2_eq_Suc le_add_diff_inverse)+
        moreover have " T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' summary ?h \<le> 1+ height summary" using 5(2)  calculation by blast
        ultimately have "T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1+ height summary" by simp     
        then show ?thesis 
          by (simp add: le_trans)
      qed
    next
      case False
      then show ?thesis  using T\<^sub>s\<^sub>u\<^sub>c\<^sub>c'.simps(6)[of  mi ma "deg-2" treeList summary x] degprop
        by (smt (z3) add_2_eq_Suc leI le_add_diff_inverse not_add_less1)
    qed
  qed
qed simp+

theorem succ_bound_size_univ': "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>s\<^sub>u\<^sub>c\<^sub>c' t x \<le> 2 +  lb (lb u)"
  using succ'_bound_height[of t n x] height_double_log_univ_size[of u n t] by simp

subsection \<open>Predecessor Function\<close>

fun T\<^sub>p\<^sub>r\<^sub>e\<^sub>d::"VEBT \<Rightarrow> nat \<Rightarrow> nat " where
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Leaf _ _) 0 = 1"|
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Leaf a _) (Suc 0) = 1+ (if a then 1 else 1)"|
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Leaf a b) _ = 1+ (if b then 1 else 1+ (if a then 1 else 1))"|

"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node None _ _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node _ 0 _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node _ (Suc 0) _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x = 1+ (
                       if x > ma then 1 
                       else (let l = low x (deg div 2); h = high x (deg div 2) in 10 + 1+
                       (if h < length treeList then  
  
                            let minlow = vebt_mint (treeList ! h) in 2 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! h) + 3 + 
                            (if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                                                   4 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! h) l
                             else let pr = vebt_pred summary h in  1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary h+ 1 + (
                             if pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the pr) ))
                     else 1)))"

theorem pred_bound_height: "invar_vebt t n \<Longrightarrow> T\<^sub>p\<^sub>r\<^sub>e\<^sub>d t x \<le> (1+height t)*29"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case apply(cases x) 
    using  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(1)[of a b] apply simp   
    apply(cases "x > 1")
    using  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(3)[of a b] 
    apply (smt (z3) One_nat_def Suc_eq_numeral height.simps(1) less_Suc_eq_le less_antisym less_imp_Suc_add mult.left_neutral not_less numeral_One numeral_eq_iff numeral_le_one_iff plus_1_eq_Suc pred_numeral_simps(3) semiring_norm(70) semiring_norm(85))
    using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(2)[of a b] apply simp
    done
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
  proof(cases "x > ma")
    case True
    hence " T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =2" using  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(7)[of mi ma "deg-2" treeList summary x ]
      by (smt (z3) Suc_1 \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse plus_1_eq_Suc)
    then show ?thesis by simp
  next
    case False
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    have 0: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x = 1 + 10 +1 + 
                       (if ?h < length treeList then  
  
                            let minlow = vebt_mint (treeList ! ?h) in 2 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) + 3 + 
                            (if minlow \<noteq> None \<and> (Some ?l >\<^sub>o  minlow) then 
                                                   4 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in  1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ 1 + (
                             if pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the pr) ))
                     else 1)" 
      using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(7)[of mi ma "deg-2" treeList summary x] False \<open>2 \<le> deg\<close>  
      by (smt (z3) Suc_1 Suc_eq_plus1 add.assoc add.commute le_add_diff_inverse)
    then show ?thesis
    proof(cases " ?h < length treeList")
      case True
      let ?minlow = "vebt_mint (treeList ! ?h)"
      have 1: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =17 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                            (if ?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow) then 
                                                   4 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in  1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ 1 + (
                             if pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the pr) ))" using True 0 by simp
      then show ?thesis
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        have 2: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =21 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                               T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l" using True 1 by simp
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le> 24 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l" using mint_bound by simp
        moreover hence "(treeList ! ?h)  \<in> set treeList"
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) False high_bound_aux by force
        ultimately have "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le> 24 +  (1 +  height(treeList ! ?h))*29" 
          using "4.IH"  by (meson nat_add_left_cancel_le order_trans)
        hence  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le>
                    24 +  (height (Node (Some (mi, ma)) deg treeList summary))*29" 
          using height_compose_child[of "treeList ! ?h" treeList "Some(mi, ma)" deg summary]
          by (meson \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> add_le_cancel_left le_refl mult_le_mono order_trans)
        then show ?thesis by simp
      next
        case False
        let ?pr = "vebt_pred summary ?h "
        have 2: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =19 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                             T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ (
                             if ?pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the ?pr))" using False 1 by auto
        hence 3:"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>22  +
                             T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ (
                             if ?pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the ?pr))" using mint_bound[of "treeList ! ?h"] by simp
        then show ?thesis
        proof(cases " ?pr = None")
          case True
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>24  +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h" using 3 by simp
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>24  +  (1+ height summary) *  29" 
            by (meson "4.IH"(2) add_le_mono dual_order.trans le_refl)
          hence  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>
               24  +  (height  (Node (Some (mi, ma)) deg treeList summary) ) *  29" 
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
          then show ?thesis by simp
        next
          case False 
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>29  +
                             T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h " using maxt_bound[of "treeList ! the ?pr"] 3 by auto
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>29  +  (1+ height summary) *  29" 
            using "4.IH"(2)[of ?h] by simp
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>
               29  +  (height (Node (Some (mi, ma)) deg treeList summary)) *  29" 
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger      
          then show ?thesis by simp
        qed
      qed
    next
      case False
      then show ?thesis using 0 by simp
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case
  proof(cases "x > ma")
    case True
    hence " T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =2" using  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(7)[of mi ma "deg-2" treeList summary x ]
      by (smt (z3) Suc_1 \<open>2 \<le> deg\<close> add_2_eq_Suc le_add_diff_inverse plus_1_eq_Suc)
    then show ?thesis by simp
  next
    case False
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    have 0: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x = 1 + 10 +1 + 
                       (if ?h < length treeList then  
  
                            let minlow = vebt_mint (treeList ! ?h) in 2 + T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) + 3 + 
                            (if minlow \<noteq> None \<and> (Some ?l >\<^sub>o  minlow) then 
                                                   4 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in  1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ 1 + (
                             if pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the pr) ))
                     else 1)"
      using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d.simps(7)[of mi ma "deg-2" treeList summary x] False \<open>2 \<le> deg\<close>  
      by (smt (z3) Suc_1 Suc_eq_plus1 add.assoc add.commute le_add_diff_inverse)
    then show ?thesis
    proof(cases " ?h < length treeList")
      case True
      hence " ?h < length treeList" by simp
      let ?minlow = "vebt_mint (treeList ! ?h)"
      have 1: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =17 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                            (if ?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow) then 
                                                   4 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l
                             else let pr = vebt_pred summary ?h in  1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ 1 + (
                             if pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the pr) ))" 
        using True 0 by simp
      then show ?thesis
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        have 2: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =21 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                               T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l" using True 1 by simp
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le> 24 +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (treeList ! ?h) ?l" using mint_bound by simp
        moreover hence "(treeList ! ?h)  \<in> set treeList" 
          by (meson \<open>high x (deg div 2) < length treeList\<close> nth_mem)
        ultimately have "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le> 24 +  (1 +  height(treeList ! ?h))*29" 
          using "5.IH"  by (meson nat_add_left_cancel_le order_trans)
        hence  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x \<le>
                    24 +  (height (Node (Some (mi, ma)) deg treeList summary))*29" 
          using height_compose_child[of "treeList ! ?h" treeList "Some(mi, ma)" deg summary]
          by (meson \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> add_le_cancel_left le_refl mult_le_mono order_trans)
        then show ?thesis by simp
      next
        case False
        let ?pr = "vebt_pred summary ?h "
        have 2: "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x =19 +  T\<^sub>m\<^sub>i\<^sub>n\<^sub>t(treeList ! ?h) +
                             T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ (
                             if ?pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the ?pr))" 
          using False 1 by auto
        hence 3:"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>22  +
                             T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h+ (
                             if ?pr = None then 1 + (if x > mi then 1 else 1)
                             else 4 +  T\<^sub>m\<^sub>a\<^sub>x\<^sub>t (treeList ! the ?pr))" using mint_bound[of "treeList ! ?h"] by simp
        then show ?thesis
        proof(cases " ?pr = None")
          case True
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>24  +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h" using 3 by simp
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>24  +  (1+ height summary) *  29" 
            by (meson "5.IH"(2) add_le_mono dual_order.trans le_refl)
          hence  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>
               24  +  (height  (Node (Some (mi, ma)) deg treeList summary) ) *  29" 
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger
          then show ?thesis by simp
        next
          case False 
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>29  +  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d summary ?h " 
            using maxt_bound[of "treeList ! the ?pr"] 3 by auto
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>29  +  (1+ height summary) *  29" 
            using "5.IH"(2)[of ?h] by simp
          hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d (Node (Some (mi, ma)) deg treeList summary) x  \<le>
               29  +  (height (Node (Some (mi, ma)) deg treeList summary)) *  29" 
            using height_compose_summary[of summary "Some (mi, ma)" deg treeList] by presburger      
          then show ?thesis by simp
        qed
      qed
    next
      case False
      then show ?thesis using 0 by simp
    qed
  qed
qed


theorem pred_bound_size_univ: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>p\<^sub>r\<^sub>e\<^sub>d t x \<le> 58 + 29 * lb (lb u)"
  using pred_bound_height[of t n x] height_double_log_univ_size[of u n t] by simp

fun T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'::"VEBT \<Rightarrow> nat \<Rightarrow> nat " where
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Leaf _ _) 0 = 1"|
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Leaf a _) (Suc 0) = 1"|
  "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Leaf a b) _ = 1"|

"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node None _ _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node _ 0 _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node _ (Suc 0) _ _) _ = 1"|
"T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x = (
                       if x > ma then 1 
                       else (let l = low x (deg div 2); h = high x (deg div 2) in 
                       (if h < length treeList then  
  
                            let minlow = vebt_mint (treeList ! h) in  
                            (if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                                                   1+  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! h) l
                             else let pr = vebt_pred summary h in   T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' summary h+ (
                             if pr = None then 1 
                             else 1 ))
                     else 1)))"

theorem pred_bound_height': "invar_vebt t n\<Longrightarrow> T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' t x \<le> (1 + height t)"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    by (metis One_nat_def Suc_eq_plus1_left T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(1) T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(2) T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(3) vebt_buildup.cases height.simps(1) le_refl)
next
  case (4 treeList n summary m deg mi ma)
  hence degprop:"deg \<ge> 2" 
    by (metis add_self_div_2 deg_not_0 div_greater_zero_iff)
  then show ?case 
  proof(cases "x > ma")
    case True
    then show ?thesis using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop
      by (metis add_2_eq_Suc le_add_diff_inverse le_numeral_extra(4) trans_le_add1)
  next
    case False
    hence "x \<le> ma" by simp
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    show ?thesis
    proof(cases "?h< length treeList")
      case True
      hence hprop: "?h< length treeList" by simp
      let  ?minlow = "vebt_mint (treeList ! ?h)"
      show ?thesis 
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x =  1+  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! ?h) ?l"
          using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop hprop
          by (smt (z3) False add_2_eq_Suc le_add_diff_inverse)
        moreover have "treeList  ! ?h \<in> set treeList" using hprop by simp
        moreover hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! ?h) ?l \<le> 1 + height (treeList ! ?h)" using 4(1) by simp
        ultimately have "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x \<le>  1+  1+ height (treeList ! ?h)" by simp
        then show ?thesis 
          by (smt (z3) Suc_le_mono \<open>T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x = 1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! high x (deg div 2)) (low x (deg div 2))\<close> \<open>T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! high x (deg div 2)) (low x (deg div 2)) \<le> 1 + height (treeList ! high x (deg div 2))\<close> \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> height_compose_child le_trans plus_1_eq_Suc)
      next
        case False
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x =  1+  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' summary ?h" 
          using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop hprop 
          by (cases "vebt_pred summary ?h") 
            (smt (z3) Suc_eq_plus1 \<open>x \<le> ma\<close> add_2_eq_Suc le_add_diff_inverse linorder_not_less plus_1_eq_Suc)+
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1 +height summary" using 4(2)[of ?h] by simp
        then show ?thesis by(simp add: le_trans)
      qed
    next
      case False
      then show ?thesis   using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop 
        by (metis "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>x \<le> ma\<close> add_self_div_2 high_bound_aux le_less_trans)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence degprop:"deg \<ge> 2" 
    by (metis Suc_1 leD less_numeral_extra(1) not_add_less1 not_less_eq_eq not_less_iff_gr_or_eq plus_1_eq_Suc set_n_deg_not_0)
  then show ?case 
  proof(cases "x > ma")
    case True
    then show ?thesis using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop
      by (metis add_2_eq_Suc le_add_diff_inverse le_numeral_extra(4) trans_le_add1)
  next
    case False
    hence "x \<le> ma" by simp
    let ?l = "low x (deg div 2)"
    let ?h = "high x (deg div 2)"
    show ?thesis
    proof(cases "?h< length treeList")
      case True
      hence hprop: "?h< length treeList" by simp
      let  ?minlow = "vebt_mint (treeList ! ?h)"
      show ?thesis 
      proof(cases "?minlow \<noteq> None \<and> (Some ?l >\<^sub>o  ?minlow)")
        case True
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x =  1+  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! ?h) ?l"
          using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop hprop
          by (smt (z3) False add_2_eq_Suc le_add_diff_inverse)
        moreover have "treeList  ! ?h \<in> set treeList" using hprop by simp
        moreover hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! ?h) ?l \<le> 1 + height (treeList ! ?h)" using 5(1) by simp
        ultimately have "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x \<le>  1+  1+ height (treeList ! ?h)" by simp
        then show ?thesis 
          by (smt (z3) Suc_le_mono \<open>T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x = 1 + T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! high x (deg div 2)) (low x (deg div 2))\<close> \<open>T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (treeList ! high x (deg div 2)) (low x (deg div 2)) \<le> 1 + height (treeList ! high x (deg div 2))\<close> \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> height_compose_child le_trans plus_1_eq_Suc)
      next
        case False
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x =  1+  T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' summary ?h" 
          using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop hprop 
          by (cases "vebt_pred summary ?h") 
            (smt (z3) Suc_eq_plus1 \<open>x \<le> ma\<close> add_2_eq_Suc le_add_diff_inverse linorder_not_less plus_1_eq_Suc)+
        hence "T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' (Node (Some (mi, ma)) deg treeList summary) x \<le> 1 + 1 +height summary" using 5(2)[of ?h] by simp
        then show ?thesis by(simp add: le_trans)
      qed
    next
      case False
      then show ?thesis   using T\<^sub>p\<^sub>r\<^sub>e\<^sub>d'.simps(7)[of mi ma "deg -2" treeList summary x ] degprop 
        by (smt (z3) add_2_eq_Suc leI le_add_diff_inverse not_add_less1) 
    qed
  qed
qed simp+

theorem pred_bound_size_univ': "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>p\<^sub>r\<^sub>e\<^sub>d' t x \<le> 2 + lb (lb u)"
  using pred_bound_height'[of t n x] height_double_log_univ_size[of u n t] by simp

end
end
