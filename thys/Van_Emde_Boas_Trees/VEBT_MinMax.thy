(*by Ammer*)
theory VEBT_MinMax imports VEBT_Member
begin

section \<open>The Minimum and Maximum Operation\<close>

fun vebt_mint :: "VEBT \<Rightarrow> nat option" where
  "vebt_mint (Leaf a b) = (if a then Some 0 else if b then Some 1 else None)"|
  "vebt_mint (Node None _ _ _) = None"|
  "vebt_mint (Node (Some (mi,ma)) _ _ _ ) = Some mi"


fun vebt_maxt :: "VEBT \<Rightarrow> nat option" where
  "vebt_maxt (Leaf a b) = (if b then Some 1 else if a then Some 0 else None)"|
  "vebt_maxt (Node None _ _ _) = None"|
  "vebt_maxt (Node (Some (mi,ma)) _ _ _ ) = Some ma"


context VEBT_internal begin  
  
fun option_shift::"('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow>'a option \<Rightarrow>'a option\<Rightarrow> 'a option" where
"option_shift _ None _ = None"|
"option_shift _ _ None = None"|
"option_shift f (Some a) (Some b) = Some (f a b)"

definition power::"nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl"^\<^sub>o" 81) where
"power= option_shift (^)"

definition add::"nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl"+\<^sub>o" 79) where
"add= option_shift (+)"

definition mul::"nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl"*\<^sub>o" 80) where
"mul = option_shift (*)"

fun option_comp_shift::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
"option_comp_shift _ None _ = False"|
"option_comp_shift _ _ None = False"|
"option_comp_shift f (Some x) (Some y) =  f x y"

fun less::"nat option \<Rightarrow> nat option \<Rightarrow> bool" (infixl"<\<^sub>o" 80) where
"less x y= option_comp_shift (<) x y"

fun lesseq::"nat option \<Rightarrow> nat option \<Rightarrow> bool" (infixl"\<le>\<^sub>o" 80) where
"lesseq x y = option_comp_shift (\<le>) x y"

fun greater::"nat option \<Rightarrow> nat option \<Rightarrow> bool" (infixl">\<^sub>o" 80) where
"greater x y = option_comp_shift (>) x y"

lemma add_shift:"x+y = z \<longleftrightarrow> Some x +\<^sub>o Some y = Some z" 
  by (simp add: add_def)

lemma mul_shift:"x*y = z \<longleftrightarrow> Some x *\<^sub>o Some y = Some z" by (simp add: mul_def)

lemma power_shift:"x^y = z \<longleftrightarrow> Some x ^\<^sub>o Some y = Some z" by (simp add: power_def)

lemma less_shift: "x < y \<longleftrightarrow> Some x <\<^sub>o Some y" by simp

lemma lesseq_shift: "x \<le> y \<longleftrightarrow> Some x \<le>\<^sub>o Some y" by simp

lemma greater_shift: "x > y \<longleftrightarrow> Some x >\<^sub>o Some y" by simp

definition max_in_set :: "nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "max_in_set xs x \<longleftrightarrow> (x \<in> xs \<and> (\<forall> y \<in> xs. y \<le> x))"

lemma maxt_member: "invar_vebt t n \<Longrightarrow> vebt_maxt t = Some maxi \<Longrightarrow> vebt_member t maxi"
proof(induction t n  arbitrary: maxi rule: invar_vebt.induct)
case (1 a b)
  then show ?case
    by (metis VEBT_Member.vebt_member.simps(1) vebt_maxt.simps(1) option.distinct(1) option.inject zero_neq_one)
next
case (2 treeList n summary m deg)
  then show ?case
    by simp
next
case (3 treeList n summary m deg)
  then show ?case
    by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2" 
    by (metis One_nat_def Suc_le_eq add_mono deg_not_0 numeral_2_eq_2 plus_1_eq_Suc)
  then show ?case
    by (metis "4.prems" VEBT_Member.vebt_member.simps(5) Suc_diff_Suc Suc_pred lessI less_le_trans vebt_maxt.simps(3) numeral_2_eq_2 option.inject zero_less_Suc)
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_leI le_add2 less_add_same_cancel2 less_le_trans not_less_iff_gr_or_eq not_one_le_zero numeral_2_eq_2 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case
    by (metis "5.prems" VEBT_Member.vebt_member.simps(5) add_2_eq_Suc le_add_diff_inverse vebt_maxt.simps(3) option.inject)
qed


lemma maxt_corr_help: "invar_vebt t n \<Longrightarrow> vebt_maxt t = Some maxi \<Longrightarrow> vebt_member t x \<Longrightarrow> maxi \<ge> x " 
  by (smt VEBT_Member.vebt_member.simps(1) le_less vebt_maxt.elims member_inv mi_ma_2_deg option.simps(1) option.simps(3) zero_le_one)

lemma maxt_corr_help_empty: "invar_vebt t n \<Longrightarrow> vebt_maxt t = None \<Longrightarrow> set_vebt' t = {}" 
  by (metis (full_types) VEBT_Member.vebt_member.simps(1) empty_Collect_eq vebt_maxt.elims minNull.simps(4) min_Null_member option.distinct(1) set_vebt'_def)


theorem maxt_corr:assumes "invar_vebt t n" and "vebt_maxt t = Some x" shows "max_in_set (set_vebt' t) x" 
  unfolding set_vebt'_def Max_def max_in_set_def
  using assms(1) assms(2) maxt_corr_help maxt_member by blast

theorem maxt_sound:assumes "invar_vebt t n" and  "max_in_set (set_vebt' t) x" shows "vebt_maxt t = Some x"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) empty_Collect_eq le_less max_in_set_def
 maxt_corr_help maxt_corr_help_empty maxt_member mem_Collect_eq not_le option.exhaust set_vebt'_def)


definition min_in_set :: "nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "min_in_set xs x \<longleftrightarrow> (x \<in> xs \<and> (\<forall> y \<in> xs. y \<ge> x))"

lemma mint_member: "invar_vebt t n \<Longrightarrow> vebt_mint t = Some maxi \<Longrightarrow> vebt_member t maxi"
proof(induction t n  arbitrary: maxi rule: invar_vebt.induct)
case (1 a b)
  then show ?case
    by (metis VEBT_Member.vebt_member.simps(1) vebt_mint.simps(1) option.distinct(1) option.inject zero_neq_one)
next
case (2 treeList n summary m deg)
  then show ?case
    by simp
next
case (3 treeList n summary m deg)
  then show ?case
    by simp
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2" 
    by (metis One_nat_def Suc_le_eq add_mono deg_not_0 numeral_2_eq_2 plus_1_eq_Suc)
  then show ?case
    by (metis "4.prems" VEBT_Member.vebt_member.simps(5) One_nat_def Suc_diff_Suc Suc_pred dual_order.strict_trans1 le_imp_less_Suc le_numeral_extra(4) vebt_mint.simps(3) numeral_2_eq_2 option.inject zero_le_one)
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    by (metis Suc_leI le_add2 less_add_same_cancel2 less_le_trans not_less_iff_gr_or_eq not_one_le_zero numeral_2_eq_2 plus_1_eq_Suc set_n_deg_not_0)
  then show ?case using  "5.prems" VEBT_Member.vebt_member.simps(5) add_2_eq_Suc  le_add_diff_inverse vebt_mint.simps(3)
    by (metis option.inject)
qed


lemma mint_corr_help: "invar_vebt t n \<Longrightarrow> vebt_mint t = Some mini \<Longrightarrow> vebt_member t x \<Longrightarrow> mini \<le> x " 
  by (smt VEBT_Member.vebt_member.simps(1) eq_iff option.inject less_imp_le_nat member_inv mi_ma_2_deg vebt_mint.elims of_nat_0 of_nat_0_le_iff of_nat_le_iff option.simps(3))

lemma mint_corr_help_empty: "invar_vebt t n \<Longrightarrow> vebt_mint t = None \<Longrightarrow> set_vebt' t = {}"
  by (metis VEBT_internal.maxt_corr_help_empty option.distinct(1) vebt_maxt.simps(1) vebt_maxt.simps(2) vebt_mint.elims)

theorem mint_corr:assumes "invar_vebt t n" and "vebt_mint t = Some x" shows "min_in_set (set_vebt' t) x"
  using assms(1) assms(2) min_in_set_def mint_corr_help mint_member set_vebt'_def by auto

theorem mint_sound:assumes "invar_vebt t n" and  "min_in_set (set_vebt' t) x" shows "vebt_mint t = Some x"
  by (metis assms(1) assms(2) empty_Collect_eq eq_iff mem_Collect_eq min_in_set_def
 mint_corr_help mint_corr_help_empty mint_member option.exhaust set_vebt'_def)

lemma summaxma:assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" and "mi \<noteq> ma"
  shows "the (vebt_maxt summary) = high ma (deg div 2)"
proof-
  from assms(1) show ?thesis 
  proof(cases)
    case (4 n m)
    have "both_member_options summary (high ma n)" 
      using "4"(10) "4"(2) "4"(4) "4"(5) "4"(6) "4"(9) assms(2) deg_not_0 exp_split_high_low(1) by blast
    have "high ma n \<le> the (vebt_maxt summary)" using  "4"(2) \<open>both_member_options summary 
          (high ma n)\<close> empty_Collect_eq option.inject maxt_corr_help maxt_corr_help_empty 
          not_None_eq set_vebt'_def valid_member_both_member_options
      by (metis option.exhaust_sel)
    have "high ma n < the (vebt_maxt summary) \<Longrightarrow> False"
    proof-
      assume "high ma n < the (vebt_maxt summary)"
      obtain maxs where "Some maxs = vebt_maxt summary" 
        by (metis "4"(2) \<open>both_member_options summary (high ma n)\<close> empty_Collect_eq maxt_corr_help_empty
            not_None_eq set_vebt'_def valid_member_both_member_options) 
      hence "\<exists> x. both_member_options (treeList ! maxs) x" 
        by (metis "4"(2) "4"(6) both_member_options_equiv_member maxt_member member_bound)
      then obtain x where "both_member_options (treeList ! maxs) x"
        by auto
      hence "vebt_member (treeList ! maxs) x"
        by (metis "4"(1) "4"(2) "4"(3) \<open>Some maxs = vebt_maxt summary\<close> maxt_member member_bound nth_mem valid_member_both_member_options)
      have "maxs < 2^m" 
        by (metis "4"(2) \<open>Some maxs = vebt_maxt summary\<close> maxt_member member_bound)
      have "invar_vebt (treeList ! maxs) n"
        by (metis "4"(1) "4"(3) \<open>maxs < 2 ^ m\<close> inthall member_def)
      hence "x < 2^n"
        using \<open>vebt_member (treeList ! maxs) x\<close> member_bound by auto
      let ?X =  "2^n*maxs + x"
      have "high ?X n = maxs" 
        by (simp add: \<open>x < 2 ^ n\<close> high_inv mult.commute)
      hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) (2^n*maxs + x)" 
        by (metis "4"(3) "4"(4) "4"(5) One_nat_def Suc_leI \<open>both_member_options (treeList ! maxs) x\<close> \<open>maxs < 2 ^ m\<close> \<open>x < 2 ^ n\<close> add_self_div_2 assms(1) both_member_options_from_chilf_to_complete_tree deg_not_0 low_inv mult.commute)
      hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?X"
        using assms(1) both_member_options_equiv_member by auto
      have "high ?X n> high ma n"
        by (metis \<open>Some maxs = vebt_maxt summary\<close> \<open>high (2 ^ n * maxs + x) n = maxs\<close> \<open>high ma n < the (vebt_maxt summary)\<close> option.exhaust_sel option.inject option.simps(3))
     hence "?X > ma"  
        by (metis div_le_mono high_def not_le)
      then show ?thesis 
        by (metis "4"(8) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * maxs + x)\<close> leD member_inv not_less_iff_gr_or_eq)
    qed
    then show ?thesis
      using "4"(4) "4"(5) \<open>high ma n \<le> the (vebt_maxt summary)\<close> by fastforce
next
  case (5 n m)
   have "both_member_options summary (high ma n)" 
     by (metis "5"(10) "5"(5) "5"(6) "5"(9) div_eq_0_iff assms(2) div_exp_eq high_def nat.simps(3) numerals(2) power_not_zero)
      have "high ma n \<le> the (vebt_maxt summary)" 
        by (metis "5"(2) VEBT_Member.vebt_member.simps(2) \<open>both_member_options summary (high ma n)\<close> vebt_maxt.elims maxt_corr_help minNull.simps(1) min_Null_member option.exhaust_sel option.simps(3) valid_member_both_member_options)
   have "high ma n < the (vebt_maxt summary) \<Longrightarrow> False"
    proof-
      assume "high ma n < the (vebt_maxt summary)"
      obtain maxs where "Some maxs = vebt_maxt summary" 
        by (metis "5"(2) \<open>both_member_options summary (high ma n)\<close> empty_Collect_eq maxt_corr_help_empty
         not_None_eq set_vebt'_def valid_member_both_member_options) 
      hence "\<exists> x. both_member_options (treeList ! maxs) x" 
        by (metis "5"(2) "5"(6) both_member_options_equiv_member maxt_member member_bound)
      then obtain x where "both_member_options (treeList ! maxs) x"
        by auto
      hence "vebt_member (treeList ! maxs) x" 
        by (metis "5"(1) "5"(2) "5"(3) \<open>Some maxs = vebt_maxt summary\<close> both_member_options_equiv_member maxt_member member_bound nth_mem)
      have "maxs < 2^m" 
        by (metis "5"(2) \<open>Some maxs = vebt_maxt summary\<close> maxt_member member_bound)
      have "invar_vebt (treeList ! maxs) n"
        by (metis "5"(1) "5"(3) \<open>maxs < 2 ^ m\<close> inthall member_def)
      hence "x < 2^n"
        using \<open>vebt_member (treeList ! maxs) x\<close> member_bound by auto
      let ?X =  "2^n*maxs + x"
      have "high ?X n = maxs" 
        by (simp add: \<open>x < 2 ^ n\<close> high_inv mult.commute)
      hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) (2^n*maxs + x)" 
        by (smt (z3) "5"(3) "5"(4) "5"(5) \<open>both_member_options (treeList ! maxs) x\<close> \<open>maxs < 2 ^ m\<close> \<open>x < 2 ^ n\<close> add_Suc_right add_self_div_2 both_member_options_from_chilf_to_complete_tree even_Suc_div_two le_add1 low_inv mult.commute odd_add plus_1_eq_Suc)
    hence "vebt_member (Node (Some (mi, ma)) deg treeList summary) ?X"
        using assms(1) both_member_options_equiv_member by auto
      have "high ?X n> high ma n"
        by (metis \<open>Some maxs = vebt_maxt summary\<close> \<open>high (2 ^ n * maxs + x) n = maxs\<close> \<open>high ma n < the (vebt_maxt summary)\<close> option.sel)
     hence "?X > ma" 
        by (metis div_le_mono high_def not_le)
      then show ?thesis 
        by (metis "5"(8) \<open>vebt_member (Node (Some (mi, ma)) deg treeList summary) (2 ^ n * maxs + x)\<close> leD member_inv not_less_iff_gr_or_eq)
    qed
    then show ?thesis
      using "5"(4) "5"(5) \<open>high ma n \<le> the(vebt_maxt summary)\<close> by fastforce
  qed
qed

lemma maxbmo: "vebt_maxt t = Some x \<Longrightarrow> both_member_options t x"
  apply(induction t rule: vebt_maxt.induct)
    apply auto
  apply (metis both_member_options_def naive_member.simps(1) option.distinct(1) option.sel zero_neq_one)
  by (metis One_nat_def Suc_le_D both_member_options_def div_by_1 div_greater_zero_iff membermima.simps(3) membermima.simps(4) not_gr0)

lemma misiz:"invar_vebt t n \<Longrightarrow> Some m = vebt_mint t \<Longrightarrow> m < 2^n" 
  by (metis member_bound mint_member)  

lemma mintlistlength: assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) n " " 
    mi \<noteq> ma " shows " ma > mi \<and> (\<exists> m. Some m = vebt_mint summary \<and> m < 2^(n - n div 2))"
  using assms(1) 
proof cases
  case (4 n m)
  hence "both_member_options (treeList ! high ma n) (low ma n)" 
    by (metis assms(2) high_bound_aux)
  moreover  hence "both_member_options summary (high ma n)" 
    using "4"(10) "4"(6) "4"(7) high_bound_aux by blast
  moreover  then obtain mini where "Some mini = vebt_mint summary" 
    by (metis "4"(3) empty_Collect_eq mint_corr_help_empty option.exhaust_sel set_vebt'_def valid_member_both_member_options)
  moreover hence "mini < 2^m" 
    by (metis "4"(3)  mint_member member_bound)
  moreover have "m = (deg - deg div 2)" using 4(6) 4(5) 
    by auto
  ultimately show ?thesis using 4(1) assms 4(9) by auto
next
  case (5 n m)
  hence "both_member_options (treeList ! high ma n) (low ma n)" 
    by (metis assms(2) high_bound_aux)
  moreover  hence "both_member_options summary (high ma n)" 
    using "5"(10) "5"(6) "5"(7) high_bound_aux by blast
  moreover  then obtain mini where "Some mini = vebt_mint summary" 
    by (metis "5"(3) empty_Collect_eq mint_corr_help_empty option.exhaust_sel set_vebt'_def valid_member_both_member_options)
  moreover hence "mini < 2^m" 
    by (metis "5"(3)  mint_member member_bound)
  moreover have "m = (deg - deg div 2)" using 5(6) 5(5) 
    by auto
  ultimately show ?thesis using 5(1) assms 5(9) by auto
qed

lemma power_minus_is_div:
  "b \<le> a \<Longrightarrow> (2 :: nat) ^ (a - b) = 2 ^ a div 2 ^ b"
  apply (induct a arbitrary: b)
   apply simp
  apply (erule le_SucE)
   apply (clarsimp simp:Suc_diff_le le_iff_add power_add)
  apply simp
  done

lemma nested_mint:assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) n " "n = Suc (Suc va) ""
    \<not> ma < mi "" ma \<noteq> mi " shows "
    high (the (vebt_mint summary) * (2 * 2 ^ (va div 2)) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))
    < length treeList"
proof-
  have setprop: "t \<in> set treeList \<Longrightarrow> invar_vebt t (n div 2 )" for t using assms(1)
    by (cases) simp+
  have listlength: "length treeList = 2^(n - n div 2)" using assms(1)
    by (cases) simp+
  have sumprop: "invar_vebt summary (n - n div 2)" using assms(1)
    by (cases) simp+
  have mimaxprop: "mi \<le> ma \<and> ma \<le> 2^n" using assms(1)
    by cases  simp+
  hence xbound: "mi \<le> x \<Longrightarrow> x \<le> ma \<Longrightarrow> high x (n div 2) \<le> length treeList " for x 
    using div_le_dividend div_le_mono high_def listlength power_minus_is_div by auto
  have contcong:"i < length treeList \<Longrightarrow> \<exists> x. both_member_options (treeList ! i) x \<longleftrightarrow> both_member_options summary i " for i
    using assms(1)by cases  auto+
  obtain m where " Some m = vebt_mint summary \<and> m < 2^(n - n div 2)"
    using assms(1) assms(4) mintlistlength by blast
  then obtain miny where "(vebt_mint (treeList ! the (vebt_mint summary))) =Some miny" 
    by (metis both_member_options_equiv_member contcong empty_Collect_eq listlength mint_corr_help_empty mint_member nth_mem option.exhaust_sel option.sel setprop sumprop set_vebt'_def)
  hence "miny < 2^(n div 2)" 
    by (metis \<open>\<And>thesis. (\<And>m. Some m = vebt_mint summary \<and> m < 2 ^ (n - n div 2) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> listlength misiz nth_mem option.sel setprop)
  then show ?thesis 
    by (metis \<open>\<And>thesis. (\<And>m. Some m = vebt_mint summary \<and> m < 2 ^ (n - n div 2) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>vebt_mint (treeList ! the (vebt_mint summary)) = Some miny\<close> assms(2) div2_Suc_Suc high_inv listlength option.sel power_Suc)
qed

lemma minminNull: "vebt_mint t = None \<Longrightarrow> minNull t" 
  by (metis minNull.simps(1) minNull.simps(4) vebt_mint.elims option.distinct(1))

lemma minNullmin: "minNull t \<Longrightarrow> vebt_mint t = None" 
  by (metis minNull.elims(2) vebt_mint.simps(1) vebt_mint.simps(2))

  
end  
end
