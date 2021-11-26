(*by Ammer*)
theory VEBT_BuildupMemImp
  imports
    VEBT_List_Assn
    VEBT_Space
    "Deriving.Derive"
    VEBT_Member VEBT_Insert
    "HOL-Library.Countable"
    "Time_Reasoning/Time_Reasoning" VEBT_DeleteBounds
begin  

section \<open>Imperative van Emde Boas Trees\<close>

datatype VEBTi = Nodei "(nat*nat) option" nat "VEBTi array" VEBTi | Leafi bool bool 

derive countable VEBTi  
instance VEBTi :: heap by standard

subsection \<open>Assertions on van Emde Boas Trees\<close>
fun vebt_assn_raw :: "VEBT \<Rightarrow> VEBTi \<Rightarrow> assn" where
  "vebt_assn_raw (Leaf a b) (Leafi ai bi) = \<up>(ai=a \<and> bi=b)"
| "vebt_assn_raw (Node mmo deg tree_list summary) (Nodei mmoi degi tree_array summaryi) = (
    \<up>(mmoi=mmo \<and> degi=deg)
    * vebt_assn_raw summary summaryi
    * (\<exists>\<^sub>A tree_is. tree_array \<mapsto>\<^sub>a tree_is * list_assn vebt_assn_raw tree_list tree_is)
  )"
| "vebt_assn_raw _ _ = false"  

lemmas [simp del] = vebt_assn_raw.simps

context VEBT_internal begin

lemmas [simp] = vebt_assn_raw.simps



lemma TBOUND_VEBT_case[TBOUND]: assumes "\<And> a b. ti = Leafi a b \<Longrightarrow> TBOUND (f a b) (bnd a b)"
   "\<And> info deg treeArray summary . ti = Nodei info deg treeArray summary \<Longrightarrow>
   TBOUND (f' info deg treeArray summary) (bnd'  info deg treeArray summary) "   

  shows "TBOUND (case ti of Leafi a b \<Rightarrow> f a b |
                       Nodei info deg treeArray summary \<Rightarrow> f' info deg treeArray summary) 
                (case ti of Leafi a b \<Rightarrow> bnd a b |
                      Nodei info deg treeArray summary \<Rightarrow> bnd' info deg treeArray summary)"
  using assms 
  apply(cases ti)
  apply auto
 done



text \<open>Some Lemmas\<close>

lemma length_corresp:"(\<exists>\<^sub>A tree_is. tree_array \<mapsto>\<^sub>a tree_is) = true \<Longrightarrow> return (length tree_is ) = Array_Time.len tree_array" 
proof-
  assume "(\<exists>\<^sub>A tree_is. tree_array \<mapsto>\<^sub>a tree_is) = true "
  then obtain tree_is where " tree_array \<mapsto>\<^sub>a tree_is =  true" 
    by (metis mod_h_bot_iff(2) mod_h_bot_iff(4) mod_h_bot_iff(8))
  then show ?thesis
    by (metis assn_basic_inequalities(5) merge_true_star snga_same_false)
qed

lemma heaphelp:assumes " h \<Turnstile>
         xa \<mapsto>\<^sub>a tree_is * list_assn vebt_assn_raw treeList tree_is *
         vebt_assn_raw summary xb *\<up>(None = None \<and> n = n)*
         \<up> (xc = Nodei None n xa xb)"
  shows "h \<Turnstile> vebt_assn_raw (Node None n treeList summary) xc"
proof-
  have "h \<Turnstile> vebt_assn_raw (Node None n treeList summary) (Nodei None n xa xb)"
    using vebt_assn_raw.simps(2)[of None n treeList summary None n xa xb] apply simp 
    by (metis assms mod_pure_star_dist star_aci(2))
  then show ?thesis 
    using assms by auto
qed

lemma assnle:"  list_assn vebt_assn_raw treeList tree_is * (x13 \<mapsto>\<^sub>a tree_is * vebt_assn_raw summary x14) \<Longrightarrow>\<^sub>A
         vebt_assn_raw summary x14 * x13 \<mapsto>\<^sub>a tree_is * list_assn vebt_assn_raw treeList tree_is" 
  using star_aci(2) by auto

lemma ext:" y < length treeList \<Longrightarrow>x13 \<mapsto>\<^sub>a tree_is *  (vebt_assn_raw summary x14 *
         (vebt_assn_raw (treeList ! y) (tree_is ! y) * listI_assn ({0..<length treeList} - {y}) vebt_assn_raw treeList tree_is))
      \<Longrightarrow>\<^sub>A (x13 \<mapsto>\<^sub>a tree_is *  vebt_assn_raw summary x14 *
         ( listI_assn ({0..<length treeList} - {y}) vebt_assn_raw treeList tree_is) )*vebt_assn_raw (treeList ! y) (tree_is ! y) "
  by (metis assn_aci(9) ent_refl star_aci(2))

lemma txe:"y < length treeList \<Longrightarrow> vebt_assn_raw (treeList ! y) (tree_is ! y) * x13 \<mapsto>\<^sub>a tree_is * vebt_assn_raw summary x14 *
       listI_assn ({0..<length treeList} - {y}) vebt_assn_raw treeList tree_is \<Longrightarrow>\<^sub>A
       vebt_assn_raw summary x14 * x13 \<mapsto>\<^sub>a tree_is * list_assn vebt_assn_raw treeList tree_is" 
  by (smt (z3) assn_aci(9) assn_times_comm assnle atLeastLessThan_iff less_nat_zero_code listI_assn_extract list_assn_conv_idx not_less)

lemma recomp: " i < length treeList \<Longrightarrow> vebt_assn_raw (treeList ! i) (tree_is ! i) *
       listI_assn ({0..<length treeList} - {i}) vebt_assn_raw treeList tree_is *
       x13 \<mapsto>\<^sub>a tree_is *
       vebt_assn_raw summary x14 \<Longrightarrow>\<^sub>A
       vebt_assn_raw summary x14 * x13 \<mapsto>\<^sub>a tree_is  * list_assn vebt_assn_raw treeList tree_is" 
  by (smt (z3) ab_semigroup_mult_class.mult.commute ab_semigroup_mult_class.mult.left_commute atLeastLessThan_iff ent_refl listI_assn_extract list_assn_conv_idx zero_le)

lemma repack: "i < length treeList \<Longrightarrow>
vebt_assn_raw (treeList ! i) (tree_is ! i) *
         Rest *
          (x13 \<mapsto>\<^sub>a tree_is * vebt_assn_raw summary x14 *
          listI_assn ({0..<length treeList} - {i}) vebt_assn_raw treeList tree_is)
      \<Longrightarrow>\<^sub>A  Rest* vebt_assn_raw summary x14 *  x13 \<mapsto>\<^sub>a tree_is *  list_assn vebt_assn_raw treeList tree_is" 
  apply-
  by (smt (z3) assn_times_assoc atLeastLessThan_iff entails_def leI less_nat_zero_code listI_assn_extract list_assn_conv_idx mod_pure_star_dist star_aci(2))

lemma big_assn_simp: "h < length treeList \<Longrightarrow>
 vebt_assn_raw (vebt_delete(treeList ! h) l) x *
        \<up> (xaa =  vebt_mint (vebt_delete(treeList ! h) l)) *
       ( x13 \<mapsto>\<^sub>a (tree_is [h := x]) *
         vebt_assn_raw summary x14 *
         listI_assn ({0..<length treeList} - {h}) vebt_assn_raw treeList tree_is) \<Longrightarrow>\<^sub>A
 x13 \<mapsto>\<^sub>a tree_is[h:=x]  *  vebt_assn_raw summary x14 *  \<up> (xaa =  vebt_mint (vebt_delete(treeList ! h) l)) *
list_assn vebt_assn_raw  (treeList[h:= (vebt_delete(treeList ! h) l)]) (tree_is[h:= x]) "
  by (smt (z3) Diff_iff ab_semigroup_mult_class.mult.left_commute assn_aci(10) atLeastLessThan_iff ent_refl insertCI insert_Diff_single insert_absorb leI length_list_update less_nat_zero_code listI_assn_subst list_assn_conv_idx mult.right_neutral)

lemma tcd: "i < length treeList \<Longrightarrow> length treeList = length treeList' \<Longrightarrow>
  vebt_assn_raw y x * x13 \<mapsto>\<^sub>a tree_is[i:= x] *  vebt_assn_raw summary x14 * listI_assn ({0..<length treeList} - {i}) vebt_assn_raw (treeList[i :=y]) (tree_is[i := x])
\<Longrightarrow>\<^sub>A x13 \<mapsto>\<^sub>a tree_is[i:= x] *  vebt_assn_raw summary x14 * list_assn vebt_assn_raw (treeList[i :=y]) (tree_is[i := x])" 
  by (smt (z3) ab_semigroup_mult_class.mult.commute assn_aci(10) atLeastLessThan_iff ent_pure_pre_iff entails_def leI length_list_update less_nat_zero_code listI_assn_def listI_assn_extract list_assn_conv_idx nth_list_update_eq)

lemma big_assn_simp': "h < length treeList ==> xaa = vebt_delete (treeList ! h)l \<Longrightarrow>
       vebt_assn_raw xaa x * \<up> (xb = vebt_mint xaa) *
       (x13 \<mapsto>\<^sub>a tree_is[h := x] * vebt_assn_raw summary x14 *
        listI_assn ({0..<length treeList} - {h}) vebt_assn_raw treeList tree_is) \<Longrightarrow>\<^sub>A
       (x13 \<mapsto>\<^sub>a tree_is[h:= x] * vebt_assn_raw summary x14 *  \<up> (xb = vebt_mint xaa) * 
      list_assn vebt_assn_raw (treeList[h:= xaa])  (tree_is[h:= x]))" 
  by (smt (verit, best) Diff_iff assn_aci(9) ent_refl insertCI length_list_update listI_assn_weak_cong mult.right_neutral nth_list_update_neq pure_false pure_true star_false_left star_false_right tcd)


lemma refines_case_VEBTi[refines_rule]: assumes "ti = ti'" "\<And> a b. refines (f1 a b) (f1' a b)"
"\<And> info deg treeArray summary . refines (f2 info deg treeArray summary) (f2' info deg treeArray summary) "
  shows "refines (case ti of Leafi a b \<Rightarrow> f1 a b |
           Nodei info deg treeArray summary \<Rightarrow> f2 info deg treeArray summary) 
 (case ti' of Leafi a b\<Rightarrow> f1' a b  |
           Nodei info deg treeArray summary \<Rightarrow> f2' info deg treeArray summary)"
  using assms apply (cases ti') apply simp_all
  done

subsection\<open>High and low Bitsequences Definition\<close>

definition highi::"nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "highi x n == return (x div (2^n))"

definition lowi::"nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "lowi x n == return (x mod (2^n))"

lemma highi_h: "<emp> highi x n <\<lambda> r. \<up>(r = high x n)>"
  by (simp add: high_def highi_def return_cons_rule)

lemma highi_hT: "<emp> highi x n <\<lambda> r. \<up>(r = high x n)>T[1]" 
  by (metis cons_post_rule entails_def highi_def highi_h httI order_refl time_return)

lemma lowi_h: "<emp> lowi x n <\<lambda> r. \<up>(r = low x n)>"
  by (simp add: low_def lowi_def return_cons_rule)

lemma lowi_hT: "<emp> lowi x n <\<lambda> r. \<up>(r = low x n)>T[1]"
  by (metis httI lowi_def lowi_h order_refl time_return)

section \<open>Imperative Implementation of $vebt-buildup$\<close>

fun replicatei::"nat \<Rightarrow>'a Heap  \<Rightarrow> ('a list) Heap" where
  "replicatei  0 x = return []"|
  "replicatei (Suc n) x = do{ y <- x;
                            ys <- replicatei n x;
                            return (y#ys)  }"

lemma time_replicate: "\<lbrakk>\<And>h. time x h \<le> c \<rbrakk> \<Longrightarrow> time (replicatei n x) h \<le> (1+(1+c)*n)"
  apply (induction n arbitrary: h)
   apply (simp add: time_simp algebra_simps)
  apply (auto simp: time_simp fails_simp algebra_simps)
  by (metis add_le_mono group_cancel.add2 nat_arith.suc1)

lemma TBOUND_replicate: "\<lbrakk>TBOUND x c\<rbrakk> \<Longrightarrow> TBOUND (replicatei n x) (1+(1+c)*n)"
  by (meson TBOUND_def time_replicate)

lemma refines_replicate[refines_rule]:
  "refines f f' \<Longrightarrow> refines (replicatei n f) (replicatei n f')"
  apply (induction n)
   apply simp_all
  apply refines
  done

fun vebt_buildupi'::"nat \<Rightarrow> VEBTi Heap" where
  "vebt_buildupi' 0 = return (Leafi False False)"|
  "vebt_buildupi' (Suc 0) = return (Leafi False False)"|
  "vebt_buildupi' n =  (if even n then (let half = n div 2 in do{
                              treeList <- replicatei  (2^half) (vebt_buildupi' half); 
                              assert' (length treeList = 2^half);
                              trees <- Array_Time.of_list  treeList;
                              summary <- (vebt_buildupi' half);
                              return (Nodei None n  trees summary)})
              else (let half = n div 2 in  do{
                              treeList <-    replicatei (2^(Suc half)) (vebt_buildupi' half); 
                              assert' (length treeList = 2^Suc half);
                              trees <- Array_Time.of_list  treeList;    
                              summary <- (vebt_buildupi' (Suc half));            
                              return (Nodei None n trees summary)} ))"

end                              

context begin
  interpretation VEBT_internal .

fun vebt_buildupi::"nat \<Rightarrow> VEBTi Heap" where
  "vebt_buildupi 0 = return (Leafi False False)"|
  "vebt_buildupi (Suc 0) = return (Leafi False False)"|
  "vebt_buildupi n =  (if even n then (let half = n div 2 in do{
                              treeList <- replicatei  (2^half) (vebt_buildupi half); 
                              trees <- Array_Time.of_list  treeList;
                              summary <- (vebt_buildupi half);
                              return (Nodei None n  trees summary)})
              else (let half = n div 2 in  do{
                              treeList <-    replicatei (2^(Suc half)) (vebt_buildupi half); 
                              trees <- Array_Time.of_list  treeList;    
                              summary <- (vebt_buildupi (Suc half));            
                              return (Nodei None n trees summary)} ))"
                              
end                              
   
context VEBT_internal begin
                           
lemma vebt_buildupi_refines: "refines (vebt_buildupi n) (vebt_buildupi' n)"                          
  apply (induction n rule: vebt_buildupi.induct) 
   apply (subst vebt_buildupi.simps; subst vebt_buildupi'.simps; refines)+
  done

fun T_vebt_buildupi where
  "T_vebt_buildupi 0 = Suc 0"
| "T_vebt_buildupi (Suc 0) = Suc 0"  
| "T_vebt_buildupi (Suc (Suc n)) = (
    if even n then 
      Suc (Suc (Suc (T_vebt_buildupi (Suc (n div 2)) +
                         (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi (Suc (n div 2)) * 2 ^ (n div 2))))))
    else  
          Suc (Suc (Suc (T_vebt_buildupi (Suc (Suc (n div 2))) +
                         (8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi (Suc (n div 2)) * 2 ^ (n div 2)))))))"

lemma TBOUND_vebt_buildupi:
  defines "foo \<equiv> T_vebt_buildupi"
  shows "TBOUND (vebt_buildupi' n) (foo n)"
  supply [simp del] = vebt_buildupi'.simps
  supply [TBOUND] = TBOUND_replicate
  apply (induction n rule: vebt_buildupi.induct)
  apply (subst vebt_buildupi'.simps)
  apply (rule TBOUND_mono)
  apply (TBOUND_step)
  apply(rule asm_rl[of "_ \<le> _"])
  apply defer_le
  apply (subst vebt_buildupi'.simps)
  apply (rule TBOUND_mono)
  apply (TBOUND_step)
  apply(rule asm_rl[of "_ \<le> _"])
  apply defer_le
  apply (subst vebt_buildupi'.simps)
  apply (rule TBOUND_mono)
  apply TBOUND_step+  
  apply(rule asm_rl[of "_ \<le> _"])
  apply defer_le
  apply (all \<open>((determ \<open>thin_tac \<open>TBOUND _ _\<close>\<close>)+)? \<close>)
  apply (simp_all add: foo_def)
  done

lemma T_vebt_buildupi: "time (vebt_buildupi' n) h \<le> T_vebt_buildupi n"
  using TBOUND_vebt_buildupi[THEN TBOUNDD] .

lemma repli_cons_repl: "<Q> x <\<lambda> r. Q*  A y r > \<Longrightarrow> <Q> replicatei n x <\<lambda> r. Q*list_assn A (replicate n y) r >"
proof(induction n arbitrary: Q)
  case (Suc n)
  then show ?case 
    apply (sep_auto heap: "Suc.IH"(1)) 
    apply (smt (z3) assn_aci(10) cons_post_rule ent_refl fi_rule)
    apply sep_auto
   done
qed sep_auto

corollary repli_emp:  "<emp> x <\<lambda> r.  A y r > \<Longrightarrow> <emp> replicatei n x <\<lambda> r. list_assn A (replicate n y) r >"
  apply(rule cons_post_rule)
  apply(rule repli_cons_repl[where Q = emp])
  apply sep_auto+
 done


lemma builupi'corr: "<emp> vebt_buildupi' n <\<lambda> r. vebt_assn_raw (vebt_buildup n) r>"
proof(induction n rule: vebt_buildup.induct)
  case (3 n)
  then show ?case 
  proof(cases "even (Suc (Suc n))")
    case True
    then show ?thesis 
      apply( simp add: vebt_buildupi'.simps(2))
      apply(rule bind_rule)
      apply(sep_auto heap: repli_cons_repl)
      apply(rule "3.IH"(1)) 
      apply simp+ 
      apply sep_auto  
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD; simp)
      apply (sep_auto heap: "3.IH"(1))
      done
  next 
    case False
    hence 11:" <xa \<mapsto>\<^sub>a x * list_assn vebt_assn_raw (replicate (4 * 2 ^ (n div 2)) (vebt_buildup (Suc (n div 2)))) x>
       vebt_buildupi' (Suc (Suc (Suc n) div 2)) <\<lambda> r. xa \<mapsto>\<^sub>a x * list_assn vebt_assn_raw (replicate (4 * 2 ^ (n div 2)) (vebt_buildup (Suc (n div 2)))) x *
         vebt_assn_raw ( vebt_buildup (Suc (Suc (Suc n) div 2))) r>" for xa x
    proof -
      show ?thesis
        by (metis (no_types) "3.IH"(4) False frame_rule_left mult.right_neutral)
    qed
    hence "vebt_buildupi' (Suc (Suc n)) =  do{ treeList <-    replicatei (2^(Suc  ((Suc (Suc n)) div 2))) (vebt_buildupi'  ((Suc (Suc n)) div 2)); 
                          assert' (length treeList = (2^(Suc  ((Suc (Suc n)) div 2))));
                          trees <- Array_Time.of_list  treeList;    
                           summary <- (vebt_buildupi' (Suc  ((Suc (Suc n)) div 2)));            
                          return (Nodei None (Suc (Suc n)) trees summary)}"
      using vebt_buildupi'.simps(3)[of n] Let_def False 
      by auto
    moreover have "<emp>  do{treeList <-    replicatei (2^(Suc  ((Suc (Suc n)) div 2))) (vebt_buildupi'  ((Suc (Suc n)) div 2)); 
                          assert' (length treeList = (2^(Suc  ((Suc (Suc n)) div 2))));
                          trees <- Array_Time.of_list  treeList;    
                           summary <- (vebt_buildupi' (Suc  ((Suc (Suc n)) div 2)));            
                          return (Nodei None (Suc (Suc n)) trees summary)} <vebt_assn_raw (vebt_buildup (Suc (Suc n)))>" 
      apply(rule bind_rule)
      apply(sep_auto heap: repli_cons_repl)
      apply(rule "3.IH"(3)) 
      using False  apply simp 
      using False  apply simp 
      apply(rule assert'_bind_rule)
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD; simp)
      apply(rule bind_rule)
      apply sep_auto
      apply(rule bind_rule)
      apply (rule 11) 
      apply vcg
      proof-
        fix x xa xb xc
        show " xa \<mapsto>\<^sub>a x * list_assn vebt_assn_raw (replicate (4 * 2 ^ (n div 2)) (vebt_buildup (Suc (n div 2)))) x *
         vebt_assn_raw (vebt_buildup (Suc (Suc (Suc n) div 2))) xb * \<up> (xc = Nodei None (Suc (Suc n)) xa xb) \<Longrightarrow>\<^sub>A vebt_assn_raw (vebt_buildup (Suc (Suc n))) xc"
         apply(rule entailsI)
         proof-
           fix h
           assume " h \<Turnstile>xa \<mapsto>\<^sub>a x * list_assn vebt_assn_raw (replicate (4 * 2 ^ (n div 2)) (vebt_buildup (Suc (n div 2)))) x *
             vebt_assn_raw (vebt_buildup (Suc (Suc (Suc n) div 2))) xb * \<up> (xc = Nodei None (Suc (Suc n)) xa xb)"
           then show "   h \<Turnstile> vebt_assn_raw (vebt_buildup (Suc (Suc n))) xc" 
           using heaphelp by (smt (z3) False SLN_def SLN_right ab_semigroup_mult_class.mult.commute ab_semigroup_mult_class.mult.left_commute vebt_buildup.simps(3) div2_Suc_Suc even_numeral even_two_times_div_two numeral_Bit0_div_2 power_Suc power_commutes pure_true)
      qed
    qed
    then show ?thesis using calculation
      by presburger
  qed
qed  sep_auto+

lemma htt_vebt_buildupi': "< emp> (vebt_buildupi' n) <\<lambda> r. vebt_assn_raw (vebt_buildup n) r> T [T_vebt_buildupi n]"
  apply (rule httI_TBOUND)
  apply (rule builupi'corr)
  apply (rule TBOUND_vebt_buildupi)
  done

lemma builupicorr: "<emp> vebt_buildupi n <\<lambda> r. vebt_assn_raw (vebt_buildup n) r>"
  using vebt_buildupi_refines builupi'corr hoare_triple_refines by blast

lemma htt_vebt_buildupi: "<emp> (vebt_buildupi n) <\<lambda> r. vebt_assn_raw (vebt_buildup n) r> T [T_vebt_buildupi n]"
  apply (rule htt_refine)
  apply (rule htt_vebt_buildupi')
  apply (rule vebt_buildupi_refines)
  done

text \<open>Closed bound for $T-vebt-buildupi$\<close>

text \<open>Amortization\<close>

lemma T_vebt_buildupi_gq_0: "T_vebt_buildupi n > 0"
  apply(induction n rule : T_vebt_buildupi.induct)
    apply auto
  done

fun T_vebt_buildupi'::"nat \<Rightarrow> int" where
  "T_vebt_buildupi' 0 = 1"
| "T_vebt_buildupi' (Suc 0) = 1"  
| "T_vebt_buildupi' (Suc (Suc n)) = (
    if even n then 
      3+(T_vebt_buildupi' (Suc (n div 2)) +
            (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2))))
    else  
          3+ (T_vebt_buildupi' (Suc (Suc (n div 2))) +
           (8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))))"

lemma Tbuildupi_buildupi': "T_vebt_buildupi n = T_vebt_buildupi' n"
  by(induction n rule: T_vebt_buildupi.induct) auto

fun Tb::"nat \<Rightarrow> int" where
  "Tb 0 = 3"
| "Tb (Suc 0) =3"  
| "Tb (Suc (Suc n)) = (
    if even n then 
          5+ Tb (Suc (n div 2))  +  (Tb (Suc (n div 2))) * 2 ^ (Suc (n div 2))
    else  
          5 + Tb (Suc (Suc (n div 2)))  + (Tb (Suc (n div 2))) * 2 ^(Suc (Suc (n div 2))))"

lemma Tb_T_vebt_buildupi': "T_vebt_buildupi' n \<le> Tb n - 2"
proof(induction n rule: T_vebt_buildupi.induct)
  case 1
  then show ?case 
    apply(subst Tb.simps)
    apply(subst T_vebt_buildupi'.simps)
    apply simp
    done
next
  case 2
  then show ?case
    apply(subst Tb.simps)
    apply(subst T_vebt_buildupi'.simps)
    apply simp
    done
next
  case (3 n)
  then show ?case
  proof(cases "even (Suc (Suc n))")
    case True
    then show ?thesis 
      apply(subst Tb.simps)
      apply(subst T_vebt_buildupi'.simps)
      using True apply simp 
      thm 3
    proof-
      have 0:"T_vebt_buildupi' (Suc (n div 2)) +
       (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))
       \<le> Tb (Suc (n div 2)) - 2  + 2^(Suc (n div 2))*2 +
                 2^(Suc (n div 2)) * (T_vebt_buildupi' (Suc (n div 2)))" 
        using "3.IH"(1) True algebra_simps by simp
      moreover have 1:"2^(Suc (n div 2))*2 +
                 2^(Suc (n div 2)) * (T_vebt_buildupi' (Suc (n div 2))) = 
                 2^(Suc (n div 2)) * (T_vebt_buildupi' (Suc (n div 2)) +  2)" by algebra
      ultimately have  2:"T_vebt_buildupi' (Suc (n div 2)) +
               (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))
               \<le> Tb (Suc (n div 2)) - 2  + 
                 2^(Suc (n div 2)) * (T_vebt_buildupi' (Suc (n div 2)) + 2)"by linarith      
      hence  3:" (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2))) * 2 ^ (n div 2))
            \<le> 2* 2^(Suc (n div 2))+ 2^(Suc (n div 2))  * ((Tb (Suc (n div 2)) - 2))"
        using "3.IH"(1) True by simp
      hence  4:" (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2))) * 2 ^ (n div 2))
                \<le> 2^(Suc (n div 2))  * ((Tb (Suc (n div 2)) - 2) +  2)" 
        using algebra_simps by (smt (verit, del_insts) "1")
      hence  4:"   T_vebt_buildupi' (Suc (n div 2)) +
           (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2))) * 2 ^ (n div 2))
             \<le> Tb (Suc (n div 2)) - (2::int) + 2^(Suc (n div 2)) * (Tb (Suc (n div 2)))"
        using "3.IH"(1) True by simp
      have 5:" (x::int) \<le> (y::int) - (z::int) + a \<Longrightarrow> z \<ge> 0 \<Longrightarrow> x \<le> y + a" for x y z a by simp
      have  "T_vebt_buildupi' (Suc (n div 2)) +
              (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))
               \<le> Tb (Suc (n div 2)) + 2^(Suc (n div 2)) * (Tb (Suc (n div 2)))" using 
        5[of " T_vebt_buildupi' (Suc (n div 2)) +
               (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2))) * 2 ^ (n div 2))" 
          " Tb (Suc (n div 2))"   2  "Tb (Suc (n div 2)) * (2 * 2 ^ (n div 2))"]  4 by simp
      then show "T_vebt_buildupi' (Suc (n div 2)) +
            (4 * 2 ^ (n div 2) + 2 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))
             \<le> Tb (Suc (n div 2)) + Tb (Suc (n div 2)) * (2 * 2 ^ (n div 2))" 
        using  power_Suc [of  2 "(n div 2)"] mult.commute by metis
    qed
  next
    case False
    have "3 +
          (T_vebt_buildupi' (Suc (Suc (n div 2))) +
           (8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2))))
              \<le>  5 + Tb (Suc (Suc (n div 2))) + Tb (Suc (n div 2)) * 2 ^ Suc (Suc (n div 2)) - 2"
    proof-
      have 0:"3 +
          (T_vebt_buildupi' (Suc (Suc (n div 2))) +
           (8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2))))
          \<le>  1 + Tb (Suc (Suc (n div 2))) + (8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi' (Suc (n div 2)) * 2 ^ (n div 2)))"
        using "3.IH"(3) False by simp
      moreover have "  4 * (T_vebt_buildupi' (Suc (n div 2))*2 ^ (n div 2)) \<le>
             4 * ((Tb (Suc (n div 2)) - 2) * 2 ^ (n div 2))"  
        using "3.IH"(4) False algebra_simps by simp
      moreover have "8 * 2 ^ (n div 2) + 4 * ((Tb (Suc (n div 2)) - 2) * 2 ^ (n div 2)) = 
            4* (2 *  2 ^ (n div 2) + ((Tb (Suc (n div 2)) - 2) * 2 ^ (n div 2)))" by simp
      moreover have "4* (2 *  2 ^ (n div 2) + ((Tb (Suc (n div 2)) - 2) * 2 ^ (n div 2))) = 
            4* ( ((Tb (Suc (n div 2)) - 2) +  2) * 2 ^ (n div 2))" by algebra
      moreover hence "4* (2 *  2 ^ (n div 2) + ((Tb (Suc (n div 2)) - 2) * 2 ^ (n div 2))) = 
            4* ((Tb (Suc (n div 2)) ) * 2 ^ (n div 2))" by simp
      ultimately have  "8 * 2 ^ (n div 2) + 4 * (T_vebt_buildupi' (Suc (n div 2))*2 ^ (n div 2)) \<le>
               4 * (((Tb (Suc (n div 2))-2) + 2 ) * 2 ^ (n div 2))" by presburger
      then show ?thesis using 0 by force
    qed
    then show ?thesis 
      apply(subst Tb.simps)
      apply(subst T_vebt_buildupi'.simps)
      using False by simp
  qed qed

fun Tb'::"nat \<Rightarrow> nat" where
  "Tb' 0 = 3"
| "Tb' (Suc 0) =3"  
| "Tb' (Suc (Suc n)) = (
    if even n then 
          5+ Tb' (Suc (n div 2))  +  (Tb' (Suc (n div 2))) * 2 ^ (Suc (n div 2))
    else  
          5 + Tb' (Suc (Suc (n div 2)))  + (Tb' (Suc (n div 2))) * 2 ^(Suc (Suc (n div 2))))"

lemma Tb_Tb': "Tb t = Tb' t"
  by(induction t rule: Tb.induct) auto

lemma Tb_T_vebt_buildupi: "T_vebt_buildupi n \<le> Tb n - 2"
  using Tb_T_vebt_buildupi'  Tbuildupi_buildupi' by simp

lemma Tb_T_vebt_buildupi'': "T_vebt_buildupi n \<le> Tb' n - 2"
  using Tb_T_vebt_buildupi[of n] Tb_Tb' by simp

lemma Tb'_cnt: "Tb' n \<le> 5 * cnt' (vebt_buildup n)"
proof(induction n rule: vebt_buildup.induct)
  case (3 n)
  then show ?case 
  proof(cases "even n")
    case True
    have 0:" 5 + Tb' (Suc (n div 2)) + Tb' (Suc (n div 2)) * 2 ^ Suc (n div 2)
    \<le> 5 * cnt' ( let half = Suc (Suc n) div 2
                      in Node None (Suc (Suc n)) (replicate (2 ^ half) (vebt_buildup half))
                          (vebt_buildup half))" 
      unfolding Let_def
      apply(subst cnt'.simps)
    proof-
      have 0:"5 * (1 + cnt' (vebt_buildup (Suc (Suc n) div 2)) +
            foldr (+)
             (map cnt' (replicate (2 ^ (Suc (Suc n) div 2)) (vebt_buildup (Suc (Suc n) div 2)))) 0) = 
            5 * (1 + cnt' (vebt_buildup (Suc (Suc n) div 2))  + (2 ^ (Suc (Suc n) div 2)) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"
        using map_replicate[of cnt' "(2 ^ (Suc (Suc n) div 2))" "(vebt_buildup (Suc (Suc n) div 2))"]
          foldr_same_int[of "replicate (2 ^ (Suc (Suc n) div 2)) (cnt' (vebt_buildup (Suc (Suc n) div 2)))"
            "(cnt' (vebt_buildup (Suc (Suc n) div 2)))"] length_replicate by simp
      have 1:" Tb' (Suc (n div 2)) * 2 ^ Suc (n div 2)
            \<le> 5 * (2 ^ (Suc (Suc n) div 2) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"
        using True "3.IH"(1)[of "Suc (Suc n) div 2"] by simp
      have 2:" Tb' (Suc (n div 2)) \<le> 5 * cnt' (vebt_buildup (Suc (Suc n) div 2))"
        using True "3.IH"(1)[of "Suc (Suc n) div 2"] by simp
      show "5 + Tb' (Suc (n div 2)) + Tb' (Suc (n div 2)) * 2 ^ Suc (n div 2)
           \<le> 5 * (1 + cnt' (vebt_buildup (Suc (Suc n) div 2)) +
            foldr (+)
             (map cnt' (replicate (2 ^ (Suc (Suc n) div 2)) (vebt_buildup (Suc (Suc n) div 2)))) 0)"
        apply(rule ord_le_eq_trans[where b = "5 * (1 + cnt' (vebt_buildup (Suc (Suc n) div 2))  
                                     + (2 ^ (Suc (Suc n) div 2)) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"])
         defer
        using 0 apply simp
        using 1  2 "order.trans" trans_le_add1 algebra_simps 
        by (smt (z3) add_le_cancel_left add_mono_thms_linordered_semiring(1) mult_Suc_right plus_1_eq_Suc)
    qed
    show ?thesis
      apply (subst vebt_buildup.simps)
      apply(subst Tb'.simps)
      using 0 True apply simp
      done
  next
    case False
    have 0:" 5 + Tb' (Suc (Suc (n div 2))) + Tb' (Suc (n div 2)) * 2 ^ Suc (Suc (n div 2))
         \<le> 5 * cnt' ( let half = Suc (Suc n) div 2
                      in Node None (Suc (Suc n)) (replicate (2 ^ Suc half) (vebt_buildup half))
                          (vebt_buildup (Suc half)))" 
      unfolding Let_def
      apply(subst cnt'.simps)
    proof-
      have 0:"5 * (1 + cnt' (vebt_buildup (Suc (Suc (Suc n) div 2))) +
            foldr (+) (map cnt' (replicate (2 ^ Suc (Suc (Suc n) div 2)) (vebt_buildup (Suc (Suc n) div 2))))0)
             =  5 * (1 + cnt' (vebt_buildup (Suc (Suc (Suc n) div 2)))  + (2 ^ Suc (Suc (Suc n) div 2)) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"
        using map_replicate[of cnt' "(2 ^ Suc (Suc (Suc n) div 2))" "(vebt_buildup (Suc (Suc n) div 2))"]
          foldr_same_int[of "replicate (2 ^ Suc (Suc (Suc n) div 2)) (cnt' (vebt_buildup (Suc (Suc n) div 2)))"
            "(cnt' (vebt_buildup (Suc (Suc n) div 2)))"] length_replicate by simp
      have 1:" Tb' (Suc (n div 2)) * 2 ^ ((Suc n) div 2)
           \<le> 5 * (2 ^ (Suc (Suc n) div 2) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"
        using False "3.IH"(3)[of " (Suc (Suc n) div 2)"] by simp
      have 2:" Tb' (Suc (Suc (n div 2))) \<le> 5 * cnt' (vebt_buildup (Suc (Suc (Suc n) div 2)))"
        using False "3.IH"(4)[of "(Suc n) div 2"] by simp 
      show " 5 + Tb' (Suc (Suc (n div 2))) + Tb' (Suc (n div 2)) * 2 ^ Suc (Suc (n div 2))
             \<le> 5 * (1 + cnt' (vebt_buildup (Suc (Suc (Suc n) div 2))) +
              foldr (+)
             (map cnt' (replicate (2 ^ Suc (Suc (Suc n) div 2)) (vebt_buildup (Suc (Suc n) div 2)))) 0)"

        apply(rule ord_le_eq_trans[where b = "5 * (1 + cnt' (vebt_buildup (Suc (Suc (Suc n) div 2)))
                                     + (2 ^ Suc (Suc (Suc n) div 2)) * cnt' (vebt_buildup (Suc (Suc n) div 2)))"])
         defer
        using 0 apply simp
        using 1  2 "order.trans" trans_le_add1 algebra_simps
        by (smt (z3) "3.IH"(3) False add_le_cancel_left add_mono_thms_linordered_semiring(1) diff_diff_cancel diff_le_self div2_Suc_Suc even_Suc mult_Suc_right plus_1_eq_Suc)
    qed 
    show ?thesis
      apply (subst vebt_buildup.simps)
      apply(subst Tb'.simps)
      using 0 False apply simp
      done
  qed
qed (subst vebt_buildup.simps cnt'.simps  Tb'.simps , simp )+

lemma T_vebt_buildupi_cnt': "T_vebt_buildupi n  \<le> 5 * cnt (vebt_buildup n)" 
  apply(rule ord_le_eq_trans[where b = "real (5 * cnt' (vebt_buildup n))"])
   defer
  apply(simp add: cnt_cnt_eq)
  apply(rule of_nat_mono)
  apply(rule order.trans[])
  apply(rule Tb_T_vebt_buildupi'')
  apply(rule order.trans[where b = "Tb' n"])
  apply simp
  apply(rule Tb'_cnt)
  done

lemma T_vebt_buildupi_univ: 
  assumes "u =2^n "
  shows   "T_vebt_buildupi n  \<le>10 * u"
proof-
  have "cnt (vebt_buildup n) \<le> 2 * u"
    using count_buildup[of n] assms by simp
  hence "real (T_vebt_buildupi n)  \<le> 5 * 2 * u"
    using T_vebt_buildupi_cnt'[of n] by simp
  then show ?thesis by simp
qed

lemma htt_vebt_buildupi'_univ: 
  assumes "u = 2^n"
  shows
    "< emp> (vebt_buildupi' n) <\<lambda> r. vebt_assn_raw (vebt_buildup n) r> T [10 * u]"
  apply (rule httI_TBOUND)
   apply (rule builupi'corr)
  apply (rule TBOUND_mono[where t = "T_vebt_buildupi n"])
   apply (rule TBOUND_vebt_buildupi)
  using T_vebt_buildupi_univ[of u n] assms apply simp
  done

text \<open>We obtain the main theorem for $buildupi$\<close>

lemma htt_vebt_buildupi_univ: 
  assumes "u = 2^n"
  shows
    "< emp> (vebt_buildupi n) <\<lambda> r. vebt_assn_raw (vebt_buildup n) r> T [10 * u]"
  using  vebt_buildupi_refines
  by (metis VEBT_internal.htt_vebt_buildupi'_univ assms htt_refine)

lemma vebt_buildupi_rule: "<\<up> (n > 0)> vebt_buildupi  n <\<lambda> r. vebt_assn_raw (vebt_buildup n) r > T[10 * 2^n]"  
proof-
  have vebt_buildupi'_rule: "<\<up> (n > 0)> vebt_buildupi' n <\<lambda> r. vebt_assn_raw (vebt_buildup n) r >"
    using builupicorr[of n] 
    apply simp 
    using VEBT_internal.builupi'corr by blast
  have vebt_buildupi'_rule_univ: "<\<up> (n > 0)> vebt_buildupi' n <\<lambda> r. vebt_assn_raw (vebt_buildup n) r > T[10 * 2^n]"  
    apply (rule httI_TBOUND)
    apply(rule vebt_buildupi'_rule) 
    apply(rule TBOUND_refines[where c = "vebt_buildupi' n"])
    apply(rule TBOUND_mono[where t="T_vebt_buildupi n"])
    apply(rule TBOUND_vebt_buildupi)
    using T_vebt_buildupi_univ[of "2^n" n] 
    apply simp
    apply(rule refines_refl)
    done
  show ?thesis
    using  vebt_buildupi_refines htt_refine vebt_buildupi'_rule_univ by blast
qed


lemma TBOUND_buildupi: assumes "n>0" shows " TBOUND (vebt_buildupi n) (10 * 2 ^ n)" 
  using vebt_buildupi_rule[of n] unfolding htt_def TBOUND_def 
  apply auto 
  subgoal for h
    using time_return[of "Leafi False False" h]  by simp
  subgoal for h
    using time_return[of "Leafi False False" h]  by simp
  done

section \<open>Minimum and Maximum Determination\<close>

end                              

context begin
  interpretation VEBT_internal .

fun vebt_minti::"VEBTi \<Rightarrow> nat option Heap" where
  "vebt_minti (Leafi a b) =  (if a then return ( Some 0) else if b then return (Some 1) else  return None)"|
  "vebt_minti (Nodei None _ _ _) = return None"|
  "vebt_minti (Nodei (Some (mi,ma)) _ _ _ ) = return (Some mi)"

fun vebt_maxti::"VEBTi \<Rightarrow> nat option Heap" where
  "vebt_maxti (Leafi a b) = (if b then return (Some 1) else if a then return (Some 0) else return  None)"|
  "vebt_maxti (Nodei None _ _ _) = return None"|
  "vebt_maxti (Nodei (Some (mi,ma)) _ _ _ ) = return (Some ma)"

end

context VEBT_internal begin 
  
lemma vebt_minti_h:"<vebt_assn_raw t ti> vebt_minti ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_mint t)>" 
  by  (cases t rule: vebt_mint.cases; cases ti rule: vebt_minti.cases) (sep_auto+)
  
lemma vebt_maxti_h:"<vebt_assn_raw t ti> vebt_maxti ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_maxt t)>"
  by  (cases t rule: vebt_mint.cases; cases ti rule: vebt_minti.cases) (sep_auto+)

lemma TBOUND_vebt_maxti[TBOUND]: "TBOUND (vebt_maxti t) 1"  
  apply (induction t rule: vebt_maxti.induct)
    apply (subst vebt_maxti.simps| TBOUND_step)+
  done

lemma TBOUND_vebt_minti[TBOUND]: "TBOUND (vebt_minti t) 1"  
  apply (induction t rule: vebt_minti.induct)
    apply (subst vebt_minti.simps| TBOUND_step)+
  done

lemma vebt_minti_hT:"<vebt_assn_raw t ti> vebt_minti ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_mint t)>T[1]"
  using TBOUND_vebt_minti httI_TBOUND vebt_minti_h by blast

lemma vebt_maxti_hT:"<vebt_assn_raw t ti> vebt_maxti ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_maxt t)>T[1]"
  using TBOUND_vebt_maxti httI_TBOUND vebt_maxti_h by blast

lemma vebt_maxtilist:"i < length ts \<Longrightarrow>
 <list_assn vebt_assn_raw ts tsi> vebt_maxti (tsi ! i)
      < \<lambda> r. \<up>(r = vebt_maxt (ts ! i)) *list_assn vebt_assn_raw ts tsi>"
  apply(unwrap_idx i)
  apply (sep_auto heap: vebt_maxti_h)
  apply(wrap_idx R: listI_assn_reinsert_upd)
  apply sep_auto
  done

lemma vebt_mintilist:"i < length ts \<Longrightarrow>
 <list_assn vebt_assn_raw ts tsi> vebt_minti (tsi ! i)
      < \<lambda> r. \<up>(r = vebt_mint (ts ! i)) *list_assn vebt_assn_raw ts tsi>"
  apply(unwrap_idx i)
  apply (sep_auto heap: vebt_minti_h)
  apply(wrap_idx R: listI_assn_reinsert_upd)
  apply sep_auto
  done

section \<open>Membership Test on imperative van Emde Boas Trees\<close>

end

context begin
interpretation VEBT_internal .

partial_function (heap_time) vebt_memberi::"VEBTi  \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "vebt_memberi t x = 
 (case t of 
        (Leafi a b ) \<Rightarrow> return (if x = 0 then a else if x=1 then b else False) |
         (Nodei info deg treeList summary ) \<Rightarrow> (
                 case info of None \<Rightarrow> return False |
                  (Some (mi, ma)) \<Rightarrow> ( if deg \<le> 1 then return False else (
                                            if x = mi then return True else 
                                            if x = ma then return True else 
                                            if x < mi then return False else 
                                            if x > ma then return False else 
                                            (do {
                                                h \<leftarrow> highi x (deg div 2);
                                                l \<leftarrow> lowi x (deg div 2);
                                                len \<leftarrow> Array_Time.len treeList;
                                                if h < len then do {
                                                th \<leftarrow> Array_Time.nth treeList h;
                                                vebt_memberi th l
                                                } else return False
                                            })))))"

end

context VEBT_internal begin                                            
                                            
partial_function (heap_time) vebt_memberi'::"VEBT \<Rightarrow>VEBTi  \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "vebt_memberi' t ti x = 
 (case ti of 
        (Leafi a b ) \<Rightarrow> return (if x = 0 then a else if x=1 then b else False) |
         (Nodei info deg treeArray summary ) \<Rightarrow> ( do {assert' (is_Node t);
                 case info of None \<Rightarrow> return False |
                  (Some (mi, ma)) \<Rightarrow> ( if deg \<le> 1 then return False else (
                                            if x = mi then return True else 
                                            if x = ma then return True else 
                                            if x < mi then return False else 
                                            if x > ma then return False else 
                                            (do {                                                
                                                let (info',deg',treeList,summary') = 
                                                 (case t of (Node info' deg' treeList summary') \<Rightarrow>
                                                  (info', deg', treeList, summary'));    
                                                 assert'(info= info' \<and> deg = deg');                                          
                                                 h \<leftarrow> highi x (deg div 2);
                                                 l \<leftarrow> lowi x (deg div 2);
                                                 assert'(l = low x (deg div 2) \<and> h = high x (deg div 2));
                                                 len \<leftarrow> Array_Time.len treeArray;
                                                 assert'(len = length treeList);
                                                 if h < len then do { 
                                                   assert'(h = high x (deg div 2) \<and> h < length treeList);                                              
                                                   th \<leftarrow> Array_Time.nth treeArray h;
                                                   vebt_memberi' (treeList ! h) th l } 
                                                 else return False
                                            })))}))"

lemma highsimp: "return (high x n) = highi x n" 
  by (simp add: high_def highi_def)

lemma lowsimp: "return (low x n) = lowi x n"
  by (simp add: low_def lowi_def)

lemma TBOUND_highi[TBOUND]: "TBOUND (highi x n) 1"
  unfolding highi_def
  apply TBOUND_step
  done

lemma TBOUND_lowi[TBOUND]: "TBOUND (lowi x n) 1"
  unfolding lowi_def
  apply TBOUND_step
  done

text \<open>Correctness of $vebt-memberi$\<close>

lemma  vebt_memberi'_rf_abstr:" <vebt_assn_raw t ti> vebt_memberi' t ti x <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_member t x)>"
proof(induction t x arbitrary: ti rule: vebt_member.induct)
  case (1 a b x)
  then show ?case apply (subst vebt_memberi'.simps) by(cases ti; sep_auto)
next
  case (2 uu uv uw x)
  then show ?case apply (subst vebt_memberi'.simps) by(cases ti; sep_auto)
next
  case (3 v uy uz x)
  then show ?case apply (subst vebt_memberi'.simps) by(cases ti; sep_auto)
next
  case (4 v vb vc x)
  then show ?case apply (subst vebt_memberi'.simps) by(cases ti; sep_auto)
next
  case (5 mi ma va treeList summary x)
  note IH[sep_heap_rules] = "5.IH" (*[THEN cons_post_rule]*)
  show ?case 
    apply (subst vebt_memberi'.simps) unfolding highi_def lowi_def 
    apply (cases ti;sep_auto)
    apply(simp add: low_def )
    apply(simp add: high_def )
    apply sep_auto
    apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
    apply(simp add: high_def)
    apply sep_auto
    apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)  
    subgoal
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)  
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="(x div (2 * 2 ^ (va div 2)))"])
      apply simp
      apply simp
      apply (sep_auto simp: high_def low_def)   
      apply (rule listI_assn_reinsert)
      apply frame_inference
      apply simp
      apply simp
      apply (rewrite in "\<hole> \<Longrightarrow>\<^sub>A _" list_assn_conv_idx[symmetric])
      apply sep_auto   
      done
    apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
    apply (sep_auto simp: high_def)
    done 
qed

lemma TBOUND_vebt_memberi:
  defines foo_def: "\<And> t x. foo t x \<equiv> 4 * (1+height t)"
  shows "TBOUND (vebt_memberi' t ti x) (foo t x)"  
  apply (induction arbitrary: t ti x rule: vebt_memberi'.fixp_induct)  
    apply (rule TBOUND_fi'_adm)
    apply (rule TBOUND_empty) 
    subgoal for f t ti x
      apply(rule TBOUND_mono)
      apply ( TBOUND_step)+
      unfolding foo_def
      apply (auto split: VEBTi.splits option.splits VEBT.splits)   
      apply (meson List.finite_set Max_ge finite_imageI imageI le_max_iff_disj nth_mem)
    done
  done

lemma vebt_memberi_refines: "refines (vebt_memberi ti  x) (vebt_memberi' t ti x)" 
  apply (induction arbitrary: t ti x rule: vebt_memberi'.fixp_induct)
  subgoal using refines_adm[where t = "\<lambda> arg. vebt_memberi (snd (fst arg)) (snd arg)"]
    by simp
  subgoal by simp
  subgoal for f t ti x
    apply(subst vebt_memberi.simps)
    apply refines
    done
  done

lemma htt_vebt_memberi:
  "<vebt_assn_raw t ti>vebt_memberi ti x <\<lambda> r. vebt_assn_raw t ti *  \<up>(r = vebt_member t x)>T[ 5 + 5 * height t]"
  apply (rule htt_refine[where c = "vebt_memberi' t ti x"])
   prefer 2
   apply(rule vebt_memberi_refines)
  apply (rule httI_TBOUND)
   apply(rule vebt_memberi'_rf_abstr)
  apply(rule TBOUND_mono)
   apply(rule TBOUND_vebt_memberi)
  apply simp
  done

lemma htt_vebt_memberi_invar_vebt: assumes "invar_vebt t n" shows 
  "<vebt_assn_raw t ti> vebt_memberi ti x <\<lambda> r. vebt_assn_raw t ti *  \<up>(r = vebt_member t x)>T[5 + 5 * (nat \<lceil>lb n \<rceil>)]"
  by (metis assms heigt_uplog_rel htt_vebt_memberi nat_int)

subsection \<open>$minNulli$: empty tree?\<close>

fun minNulli::"VEBTi \<Rightarrow> bool Heap" where
  "minNulli (Leafi False False) = return True"|
  "minNulli (Leafi _ _ ) = return False"|
  "minNulli (Nodei None _ _ _) = return True"|
  "minNulli (Nodei (Some _) _ _ _) = return  False"

lemma minNulli_rule[sep_heap_rules]: "<vebt_assn_raw t ti> minNulli ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = minNull t)>" 
  by  (cases t rule: minNull.cases; cases ti rule: minNulli.cases) (sep_auto+)

lemma TBOUND_minNulli[TBOUND]: "TBOUND (minNulli t) 1"  
  apply (induction t rule: minNulli.induct)
   apply (subst minNulli.simps | TBOUND_step)+
  done

lemma minNrulli_ruleT: 
  "<vebt_assn_raw t ti> minNulli ti <\<lambda>r. vebt_assn_raw t ti * \<up>(r = minNull t)>T[1]"
  by (metis TBOUND_minNulli hoare_triple_def httI_TBOUND minNulli_rule)


section \<open>Imperative $vebt-insert$ to van Emde Boas Tree\<close>

end

context begin
interpretation VEBT_internal .


partial_function (heap_time) vebt_inserti::"VEBTi \<Rightarrow> nat \<Rightarrow>VEBTi Heap" where
  "vebt_inserti t x = (case t of 
                (Leafi a b) \<Rightarrow> (if x=0 then return (Leafi True b) else if x=1 
                                        then return (Leafi a True) else return (Leafi a b)) |
                (Nodei info deg treeArray summary) \<Rightarrow> ( case info of None \<Rightarrow>  
                                                                if deg \<le> 1 then  
                                                                    return  (Nodei info deg treeArray summary)
                                                               else 
                                                                    return (Nodei (Some (x,x)) deg treeArray summary)|
                                                      (Some minma) \<Rightarrow>  
                                                            ( if deg \<le> 1
                                                      then return  (Nodei info deg treeArray summary) 
                                                       else  (  do{
                                                         mi <- return (fst minma);
                                                         ma <- return (snd minma);
                                                         xn <- (if x < mi then return mi else return x);
                                                         minn <- (if x < mi then return x else return mi);
                                                         l<- lowi xn (deg div 2);
                                                         h <- highi xn (deg div 2);
                                                         len \<leftarrow> Array_Time.len treeArray; 
                                                         if h < len \<and> \<not> (x = mi \<or> x = ma) then do {
                                                            node <- Array_Time.nth treeArray h;
                                                            empt <- minNulli node;
                                                            newnode <- vebt_inserti node l;
                                                            newarray <- Array_Time.upd h newnode treeArray;
                                                            newsummary<-(if empt then
                                                                      vebt_inserti summary h
                                                                      else  return summary); 
                                                            man <- (if xn > ma then return xn else return ma);
                                                            return (Nodei (Some (minn, man)) deg newarray newsummary)} 
                                                         else return  (Nodei (Some (mi,ma)) deg treeArray summary)
                                                     }))))"

end

context VEBT_internal begin                                                     
                                                     
partial_function (heap_time) vebt_inserti'::"VEBT \<Rightarrow>VEBTi \<Rightarrow> nat \<Rightarrow>VEBTi Heap" where
  "vebt_inserti' t ti x = (case ti of 
                (Leafi a b) \<Rightarrow> (if x=0 then return (Leafi True b) else if x=1 
                                        then return (Leafi a True) else return (Leafi a b)) |
                (Nodei info deg treeArray summary) \<Rightarrow> ( case info of None \<Rightarrow>  
                                                                if deg \<le> 1 then  
                                                                    return  (Nodei info deg treeArray summary)
                                                               else 
                                                                    return (Nodei (Some (x,x)) deg treeArray summary)|
                                                      (Some minma) \<Rightarrow>  
                                                            ( if deg \<le> 1
                                                      then return  (Nodei info deg treeArray summary) 
                                                       else  (  
                                          do{
                                              assert' (is_Node t);
                                              let (info',deg',treeList,summary') = 
                                              (case t of (Node info' deg' treeList summary') \<Rightarrow>
                                              (info', deg', treeList, summary'));  
                                              assert'(info= info' \<and> deg = deg'); 
                                                         let (mi', ma') = (the info');  
                                                         mi <- return (fst minma);
                                                         ma <- return (snd minma);
                                                         xn <- (if x < mi then return mi else return x);
                                                         let xn' =  (if x < mi' then  mi' else x);
                                                         minn <- (if x < mi then return x else return mi);
                                                         let  minn' = (if x < mi' then x else mi');
                                                         l<- lowi xn (deg div 2);
                                                         assert' (l = low xn' (deg' div 2));
                                                         h <- highi xn (deg div 2);
                                                         len \<leftarrow> Array_Time.len treeArray; 
                                                         if h < len \<and> \<not> (x = mi \<or> x = ma) then do {
                                                            assert' (h = high xn' (deg' div 2));
                                                            assert'( h < length treeList);
                                                            node <- Array_Time.nth treeArray h;
                                                            empt <- minNulli node;
                                                            assert' (empt = minNull (treeList ! h));
                                                            newnode <- vebt_inserti' (treeList ! h) node l;
                                                            newarray <- Array_Time.upd h newnode treeArray;
                                                            newsummary<-(if empt then
                                                                      vebt_inserti' summary' summary h
                                                                      else  return summary); 
                                                            man <- (if xn > ma then return xn else return ma);
                                                            return (Nodei (Some (minn, man)) deg newarray newsummary)} 
                                                         else return  (Nodei (Some (mi,ma)) deg treeArray summary)
                                                     }))))"

lemmas listI_assn_wrap_insert = listI_assn_reinsert_upd'[
           where  x="VEBT_Insert.vebt_insert _ _" and  A=vebt_assn_raw ]

lemma  vebt_inserti'_rf_abstr: "<vebt_assn_raw t ti> vebt_inserti' t ti x <\<lambda>r. vebt_assn_raw ( vebt_insert t x) r >" 
proof(induction t x arbitrary: ti rule: vebt_insert.induct)
  case (1 a b x)
  then show ?case by (subst vebt_inserti'.simps)(cases ti; sep_auto)
next
  case (2 info ts s x)
  then show ?case by (subst vebt_inserti'.simps) (cases ti; sep_auto)
next
  case (3 info ts s x)
  then show ?case by(subst vebt_inserti'.simps) (cases ti; sep_auto)
next
  case (4 v treeList summary x)
  then show ?case by (subst vebt_inserti'.simps)(cases ti; sep_auto)
next
  case (5 mi ma va treeList summary x)
  note IH1 = "5.IH"(1)[OF refl refl _ _]
  note IH2 = "5.IH"(2)[OF refl refl refl]
  show ?case  
    apply (cases ti)
    subgoal 
      supply [split del] = if_split
      apply (subst vebt_inserti'.simps; clarsimp split del: )
      apply (assn_simp; intro normalize_rules)
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
      apply (simp only:  fold_if_return distrib_if_bind heap_monad_laws)
      apply (clarsimp simp: lowi_def highi_def)
      apply (sep_auto simp: lowi_def highi_def) 
      apply(simp add: low_def) 
      apply (metis fst_conv)
      apply(rule bind_rule)
      apply sep_auto
      apply (simp cong: if_cong)
      apply sep_auto
      apply(simp add: high_def)
      apply (unwrap_idx "((if x < mi then mi else x) div (2 * 2 ^ (va div 2)))")
      apply (sep_auto simp: low_def high_def)
      apply (heap_rule IH1)
      subgoal
        by (simp add: low_def high_def split: if_splits)
      subgoal 
        by (simp add: low_def high_def split: if_splits)
      subgoal 
        by (simp add: low_def high_def split: if_splits)
      apply (sep_auto simp: low_def high_def)
      apply (heap_rule IH2)
      subgoal 
        by (simp add: low_def high_def split: if_splits)
      subgoal 
        by (simp add: low_def high_def)
      subgoal 
        by (simp add: low_def high_def split: if_splits)
      apply (wrap_idx R: listI_assn_wrap_insert)
      apply (sep_auto simp: low_def high_def Let_def)
      apply (wrap_idx R: listI_assn_wrap_insert)
      apply (sep_auto simp: low_def high_def Let_def)+
     done
   subgoal 
     by simp
  done
qed

lemma TBOUND_minNull: "minNull t \<Longrightarrow> TBOUND (vebt_inserti' t ti x ) 1"
  apply(subst vebt_inserti'.simps)
  apply(cases t rule: minNull.cases; simp)
  apply TBOUND+
   apply (auto split: VEBTi.splits option.splits)
  done

lemma TBOUND_vebt_inserti:
  defines foo_def: "\<And> t x. foo t x \<equiv> if minNull t then 1 else 13 * (1+height t)"
  shows "TBOUND (vebt_inserti' t ti x) (foo t x)"  
proof-
  have fooNull:"minNull t \<Longrightarrow> foo t x = 1" for t x using foo_def by simp
  have fooElse: "foo t x \<le> 13* (1+ height t)" for t using foo_def by simp
  show ?thesis
    apply (induction arbitrary: t ti x rule: vebt_inserti'.fixp_induct)  
    apply (rule TBOUND_fi'_adm)
    apply (rule TBOUND_empty) 
    apply (rule TBOUND_mono)
    apply TBOUND_step+
     apply (simp split!: VEBTi.splits VEBT.split option.splits prod.splits if_split)
     apply(simp_all add: foo_def height_i_max)
    done
qed 

lemma vebt_inserti_refines: "refines (vebt_inserti ti  x) (vebt_inserti' t ti x)" 
  apply (induction arbitrary: t ti x rule: vebt_inserti'.fixp_induct) 
  subgoal using refines_adm[where t = "\<lambda> arg. vebt_inserti (snd (fst arg)) (snd arg)"]
    by simp
  subgoal
    by simp
  apply(subst vebt_inserti.simps)
  apply refines
  done

lemma htt_vebt_inserti:
  "<vebt_assn_raw t ti> vebt_inserti ti x <\<lambda> r.  vebt_assn_raw (vebt_insert t x) r>T[ 13 + 13 * height t]"
  apply (rule htt_refine[where c = "vebt_inserti' t ti x"])
   prefer 2
   apply(rule vebt_inserti_refines)
    apply (rule httI_TBOUND)
   apply(rule vebt_inserti'_rf_abstr)
    apply(rule TBOUND_mono)
    apply(rule TBOUND_vebt_inserti)
    apply simp
  done

lemma htt_vebt_inserti_invar_vebt: assumes "invar_vebt t n" shows 
  "<vebt_assn_raw t ti> vebt_inserti ti x <\<lambda> r.  vebt_assn_raw (vebt_insert t x) r>T[13 + 13 * (nat \<lceil>lb n \<rceil>)]"
  by (metis assms heigt_uplog_rel htt_vebt_inserti nat_int)

end
end
