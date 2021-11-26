(*by Ammer*)
theory VEBT_Height imports VEBT_Definitions Complex_Main
begin

context VEBT_internal begin

section \<open>Heights of van Emde Boas Trees\<close>

fun height::"VEBT \<Rightarrow> nat" where
  "height (Leaf a b) = 0"|
  "height (Node _ deg treeList summary) = (1+ Max (height ` (insert summary (set treeList))))"

abbreviation "lb x \<equiv> log 2 x"

lemma setceilmax:  "invar_vebt s m \<Longrightarrow>\<forall> t \<in> set listy. invar_vebt t n  
     \<Longrightarrow>m = Suc n \<Longrightarrow>(\<forall> t \<in> set listy. height t = \<lceil>lb n \<rceil> ) \<Longrightarrow> height s  =  \<lceil>lb m\<rceil>
      \<Longrightarrow> Max (height ` (insert s (set listy))) =  \<lceil>lb m\<rceil>"  
proof(induction listy)
  case Nil
  hence "Max (height ` (insert s(set []))) = height s" by simp
  then show ?case using Nil by simp
next
  case (Cons a list)
  have "Max (height ` insert s (set (a # list))) =
 max (height a) (Max (height ` insert s (set ( list))))"
    by (simp add: insert_commute)
  moreover have "max (height a) (Max (height ` insert s (set ( list)))) = max (height a) \<lceil>lb m \<rceil>" 
    using Cons insert_iff list.simps(15) max_def of_nat_max by force
  moreover have " \<forall> t \<in> set (a#list). invar_vebt t n " using Cons by simp
  moreover hence "invar_vebt a n" by simp 
  hence "m \<ge> n"
    by (simp add: Cons.prems(3))
  hence "lb m \<ge> lb n" 
    using deg_not_0 \<open>invar_vebt a n\<close> by fastforce
  hence "\<lceil> lb m\<rceil> \<ge> \<lceil> lb n\<rceil>" 
    by (simp add: ceiling_mono)
  moreover hence " max \<lceil>log 2 n \<rceil> \<lceil>log 2 m \<rceil> =  \<lceil>log 2 m \<rceil>" by simp
  ultimately show ?case 
    using Cons.prems(4) \<open>invar_vebt a n\<close>
    by (metis list.set_intros(1))
qed

lemma log_ceil_idem: 
  assumes"(x::real) \<ge> 1" 
  shows "\<lceil>lb x \<rceil> = \<lceil>lb \<lceil>x\<rceil>\<rceil>" 
proof-
  have "\<lceil>log 2 x \<rceil> \<ge> 0" 
    by (smt (verit, ccfv_SIG) assms zero_le_ceiling zero_le_log_cancel_iff)
  have " \<lceil>log 2 x \<rceil> -1 < log 2 x \<and>log 2 x  \<le> \<lceil>log 2 x \<rceil>" 
    by linarith
  moreover hence "2 powr (\<lceil>log 2 x \<rceil> -1) < x  \<and> x \<le> 2 powr ( \<lceil>log 2 x \<rceil>)" 
    by (smt (verit, ccfv_SIG) assms less_log_iff real_nat_ceiling_ge)
  moreover hence "2 powr ((\<lceil>log 2 x \<rceil> -1)) < \<lceil>x\<rceil>" and " \<lceil>x\<rceil> \<le> 2 powr (\<lceil>log 2 x \<rceil>)" 
     apply linarith 
    using \<open>0 \<le> \<lceil>log 2 x\<rceil>\<close> calculation(2) ceiling_mono powr_int by fastforce 
  moreover hence  " \<lceil>log 2 x \<rceil> -1 < log 2 \<lceil> x \<rceil> \<and>log 2 \<lceil>x\<rceil> \<le> \<lceil>log 2 x \<rceil>" 
    by (smt (verit, best) assms ceiling_correct less_log_iff)
  ultimately show ?thesis 
    by linarith
qed

lemma heigt_uplog_rel:"invar_vebt t n \<Longrightarrow> (height t) = \<lceil>lb n\<rceil>" 
proof(induction t n rule: invar_vebt.induct)
  case (1 a b)
  then show ?case by simp
next
  case (2 treeList n summary m deg)  
  hence "m \<ge> n" by simp
  hence "log 2 m \<ge> log 2 n" 
    by (simp add: "2.hyps"(3))
  hence "\<lceil> log 2 m\<rceil> \<ge> \<lceil> log 2 n\<rceil>"
    by (simp add: "2.hyps"(3))
  have "Max (height ` (insert summary (set treeList))) = \<lceil> log 2 m\<rceil>" 
    by (smt (verit, best) "2.IH"(1) "2.IH"(2) "2.hyps"(3) List.finite_set Max_in empty_is_image finite_imageI finite_insert image_iff insert_iff insert_not_empty)
  hence "height (Node None deg treeList summary) = 1+  \<lceil> log 2 m\<rceil>" by simp
  moreover have "1+  \<lceil> log 2 m\<rceil> = \<lceil>1+ log 2 m\<rceil>" by linarith
  moreover have "1+ log 2 m = log 2 (2*m)" 
    using "2.hyps"(1) deg_not_0 log_mult by force
  moreover hence "\<lceil>1+ log 2 m\<rceil> = \<lceil>log 2 (2*m)\<rceil>" by simp
  moreover hence " \<lceil>log 2 (2*m)\<rceil>  = \<lceil>log 2 (n+m)\<rceil>" 
    using "2.hyps"(3) by force
  ultimately show ?case 
    using "2.hyps"(4) by metis
next
  case (3 treeList n summary m deg)
  hence 00: "n \<ge> 1 \<and> Suc n = m" 
    using set_n_deg_not_0 by blast
  hence 0:"m \<ge> n"using 3  by simp
  hence 1:"log 2 m \<ge> log 2 n"
    using "3.IH"(1) "3.hyps"(2) set_n_deg_not_0 by fastforce
  hence 2:"\<lceil> log 2 m\<rceil> \<ge> \<lceil> log 2 n\<rceil>"
    by (simp add: ceiling_mono)
  have 3: "Max (height ` (insert summary (set treeList))) = \<lceil> log 2 m\<rceil>" 
    using "3.IH"(1) "3.IH"(2) "3.hyps"(3) List.finite_set Max_in empty_is_image
      finite_imageI finite_insert image_iff insert_iff insert_not_empty  "3.hyps"(1) setceilmax by auto
  hence 4:"height (Node None deg treeList summary) = 1+  \<lceil> log 2 m\<rceil>" by simp
  have 5:"1+  \<lceil> log 2 m\<rceil> = \<lceil>1+ log 2 m\<rceil>" by linarith
  have 6:"1+ log 2 m = log 2 (m+m)" 
    using "3.hyps"(1) deg_not_0 log_mult by force
  hence 7:"log 2 (m+n) = 1+log 2 ((n+m) / 2) "
    by (simp add: "3.hyps"(3) log_divide)
  have 8:"log 2 ((n+m) / 2)  = log 2 (n + 1/2)" 
    by (smt (verit, best) "3.hyps"(3) field_sum_of_halves of_nat_Suc of_nat_add)
  have 9 : "\<lceil> log 2 (n + 1/2) \<rceil> = \<lceil> log 2 \<lceil>n + 1/2 \<rceil> \<rceil>" 
    by (smt (verit) "00" field_sum_of_halves log_ceil_idem of_nat_1 of_nat_mono)
  hence 10: " \<lceil>n + 1/2 \<rceil> = m" using 00 by linarith 
  hence 11: "\<lceil> log 2 (n + 1/2) \<rceil>  = \<lceil> log 2 m \<rceil> " using 9 by simp
  hence 12:"\<lceil> 1+ log 2 (n + 1/2) \<rceil>  = \<lceil>1+ log 2 m \<rceil>" 
    by (smt (verit) ceiling_add_one)
  hence "\<lceil> log 2 (n + n+1) \<rceil>  = \<lceil> log 2 (m+m) \<rceil>"
    using "3.hyps"(3) "6" "7" "8" by force
  then show ?case 
    by (metis "12" "3.hyps"(4) "4" "5" "7" "8" add.commute)
next
  case (4 treeList n summary m deg mi ma)
  hence "m \<ge> n" by simp
  hence "log 2 m \<ge> log 2 n" 
    by (simp add: "4.hyps"(3))
  hence "\<lceil> log 2 m\<rceil> \<ge> \<lceil> log 2 n\<rceil>"
    by (simp add: "4.hyps"(3))
  have "Max (height ` (insert summary (set treeList))) = \<lceil> log 2 m\<rceil>" 
    by (smt (verit, best) "4.IH"(1) "4.IH"(2) "4.hyps"(3) List.finite_set Max_in empty_is_image finite_imageI finite_insert image_iff insert_iff insert_not_empty)
  hence "height (Node None deg treeList summary) = 1+  \<lceil> log 2 m\<rceil>" by simp
  moreover have "1+  \<lceil> log 2 m\<rceil> = \<lceil>1+ log 2 m\<rceil>" by linarith
  moreover have "1+ log 2 m = log 2 (2*m)" 
    using "4.hyps"(1) deg_not_0 log_mult by force
  moreover hence "\<lceil>1+ log 2 m\<rceil> = \<lceil>log 2 (2*m)\<rceil>" by simp
  moreover hence " \<lceil>log 2 (2*m)\<rceil>  = \<lceil>log 2 (n+m)\<rceil>" 
    using "4.hyps"(3) by force
  ultimately show ?case 
    by (metis "4.hyps"(4) height.simps(2))
next
  case (5 treeList n summary m deg mi ma)
  hence 00: "n \<ge> 1 \<and> Suc n = m" 
    using set_n_deg_not_0 by blast
  hence 0:"m \<ge> n"using 5  by simp
  hence 1:"log 2 m \<ge> log 2 n"
    using "5.IH"(1) "5.hyps"(2) set_n_deg_not_0 by fastforce
  hence 2:"\<lceil> log 2 m\<rceil> \<ge> \<lceil> log 2 n\<rceil>"
    by (simp add: ceiling_mono)
  have 3: "Max (height ` (insert summary (set treeList))) = \<lceil> log 2 m\<rceil>" 
    using "5.IH"(1) "5.IH"(2) "5.hyps"(3) List.finite_set Max_in empty_is_image
      finite_imageI finite_insert image_iff insert_iff insert_not_empty  "5.hyps"(1) setceilmax by auto
  hence 4:"height (Node None deg treeList summary) = 1+  \<lceil> log 2 m\<rceil>" by simp
  have 5:"1+  \<lceil> log 2 m\<rceil> = \<lceil>1+ log 2 m\<rceil>" by linarith
  have 6:"1+ log 2 m = log 2 (m+m)" 
    using "5.hyps"(1) deg_not_0 log_mult by force
  hence 7:"log 2 (m+n) = 1+log 2 ((n+m) / 2) "
    by (simp add: "5.hyps"(3) log_divide)
  have 8:"log 2 ((n+m) / 2)  = log 2 (n + 1/2)" 
    by (smt (verit, best) "5.hyps"(3) field_sum_of_halves of_nat_Suc of_nat_add)
  have 9 : "\<lceil> log 2 (n + 1/2) \<rceil> = \<lceil> log 2 \<lceil>n + 1/2 \<rceil> \<rceil>" 
    by (smt (verit) "00" field_sum_of_halves log_ceil_idem of_nat_1 of_nat_mono)
  hence 10: " \<lceil>n + 1/2 \<rceil> = m" using 00 by linarith 
  hence 11: "\<lceil> log 2 (n + 1/2) \<rceil>  = \<lceil> log 2 m \<rceil> " using 9 by simp
  hence 12:"\<lceil> 1+ log 2 (n + 1/2) \<rceil>  = \<lceil>1+ log 2 m \<rceil>" 
    by (smt (verit) ceiling_add_one)
  hence "\<lceil> log 2 (n + n+1) \<rceil>  = \<lceil> log 2 (m+m) \<rceil>"
    using "5.hyps"(3) "6" "7" "8" by force
  then show ?case
    using "4" "5" "5.hyps"(3) "5.hyps"(4) "6" by force
qed

lemma two_powr_height_bound_deg: 
  assumes "invar_vebt t n " 
  shows " 2^(height t) \<le> 2*(n::nat)" 
proof-
  have " (height t) = \<lceil> log 2 n\<rceil>" 
    by (simp add: assms heigt_uplog_rel)
  moreover  have "\<lceil> log 2 n\<rceil> \<le> log 2 n +1" by simp
  moreover hence "2 powr \<lceil> log 2 n\<rceil> \<le> 2 powr  (log 2 n +1)" by simp
  moreover have " 2 powr  (log 2 n +1) = 2 powr 1 * 2 powr  (log 2 n)"
    by (simp add: powr_add)
  moreover hence " 2 powr  (log 2 n +1) = 2 * n" 
    using assms deg_not_0 by force
  ultimately show ?thesis 
    by (metis linorder_not_less not_one_le_zero of_int_0 of_int_less_iff of_int_numeral of_int_of_nat_eq of_nat_le_iff one_add_one order_less_le powr_realpow real_of_nat_eq_numeral_power_cancel_iff zle_add1_eq_le)
qed

text \<open>Main Theorem\<close>

theorem height_double_log_univ_size: 
  assumes "u = 2^deg" and "invar_vebt t deg " 
  shows "height t \<le> 1 + lb (lb u)" 
proof-
  have "(height t) = \<lceil>lb deg\<rceil>" 
    by (simp add: assms(2) heigt_uplog_rel)
  have "2^(height t) \<le> 2 *  deg" using assms(2)  two_powr_height_bound_deg[of t deg] 
    by (meson dual_order.eq_iff dual_order.trans self_le_ge2_pow)
  hence "height t \<le> 1 + lb deg" 
    using \<open>int (height t) = \<lceil>lb (real deg)\<rceil>\<close> by linarith
  hence "height t \<le> 1 + lb (lb u)" using assms by simp
  thus ?thesis by simp
qed

lemma height_compose_list:  " t\<in> set treeList \<Longrightarrow>
 Max (height ` (insert summary (set treeList)))  \<ge>  height t"
  apply(induction treeList) apply simp 
  by (meson List.finite_set Max_ge finite_imageI finite_insert image_eqI subsetD subset_insertI)

lemma height_compose_child:  " t\<in> set treeList \<Longrightarrow>
 height (Node info deg treeList summary)  \<ge> 1+  height t" by simp

lemma height_compose_summary: " height (Node info deg treeList summary)  \<ge> 1+  height summary" by simp

lemma  height_i_max: " i < length x13 \<Longrightarrow>
       height (x13 ! i) \<le> max foo  (Max (height ` set x13))"
  by (meson List.finite_set Max_ge finite_imageI max.coboundedI2 nth_mem rev_image_eqI)

lemma max_ins_scaled: " n* height x14 \<le> m + n* Max (insert (height x14) (height ` set x13))"
  by (meson List.finite_set Max_ge finite_imageI finite_insert insertI1 mult_le_mono2 trans_le_add2)

lemma max_idx_list: 
  assumes "i < length x13 "
  shows " n * height (x13 !i) \<le> Suc (Suc (n * max (height x14) (Max (height ` set x13))))" 
  by (metis assms height_i_max less_Suc_eq mult_le_mono2 nat_less_le)

end
end
