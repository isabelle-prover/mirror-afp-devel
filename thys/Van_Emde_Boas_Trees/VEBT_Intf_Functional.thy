section \<open>Functional Interface\<close>
theory VEBT_Intf_Functional
imports Main
  VEBT_Definitions VEBT_Space
  VEBT_Uniqueness
  VEBT_Member 
  VEBT_Insert VEBT_InsertCorrectness 
  VEBT_MinMax 
  VEBT_Pred VEBT_Succ 
  VEBT_Bounds 
  VEBT_Delete VEBT_DeleteCorrectness VEBT_DeleteBounds
  
begin

  subsection \<open>Code Generation Setup\<close>

  subsubsection \<open>Code Equations\<close>
  text \<open>Code generator seems to not support patterns and nat code target\<close>
  
  context begin
    interpretation VEBT_internal .
  
  lemma vebt_member_code[code]:
    "vebt_member (Leaf a b) x = (if x = 0 then a else if x=1 then b else False)" 
    "vebt_member (Node None t r e) x = False"
    "vebt_member (Node (Some (mi, ma)) deg treeList summary) x = 
    (if deg = 0 \<or> deg = Suc 0 then False else (
      if x = mi then True else 
      if x = ma then True else 
      if x < mi then False else 
     if x > ma then False else 
      (let
            h = high x (deg div 2);
           l = low x (deg div 2) in 
         (if h < length treeList 
             then vebt_member (treeList ! h) l 
             else False))))"
        apply simp
       apply simp 
    proof(goal_cases)
      case 1
      consider "deg = 0"| "deg = Suc 0" 
        | n  where "deg = Suc (Suc n)"
        by (meson vebt_buildup.cases)
      then show ?case apply(cases)
        by simp_all 
    qed

  lemma vebt_insert_code[code]:
    "vebt_insert (Leaf a b) x = (if x=0 then Leaf True b else if x=1 then Leaf a True else Leaf a b)"
    "vebt_insert (Node info deg treeList summary) x = (
      if deg \<le> 1 then  
        (Node info deg treeList summary) 
      else ( case info of 
        None \<Rightarrow>  (Node (Some (x,x)) deg  treeList summary)
      | Some mima \<Rightarrow> ( case mima of (mi, ma) \<Rightarrow> (     
          let 
            xn = (if x < mi then mi else x); 
            minn = (if x< mi then x else mi);
            l= low xn (deg div 2); h = high xn (deg div 2)
          in ( 
            if h < length treeList \<and> \<not> (x = mi \<or> x = ma) then
              Node (Some (minn, max xn ma)) 
                   deg 
                   (treeList[h:= vebt_insert (treeList ! h) l])
                   (if minNull (treeList ! h) then  vebt_insert summary h else summary)
            else Node (Some (mi, ma)) deg treeList summary)
      ))))" 
      apply simp
     apply simp 
  proof(goal_cases)
    case 1
    consider "deg = 0"| "deg = Suc 0" 
      | n  where "deg = Suc (Suc n)"
      by (meson vebt_buildup.cases)
    then show ?case apply(cases) 
        apply simp+ 
      apply(cases info) 
       apply simp+
      apply(cases "the info")
      apply simp 
      by meson
  
  qed 

  lemma vebt_succ_code[code]:
    "vebt_succ (Leaf a b) x = (if b\<and> x = 0 then Some 1 else None)"
    "vebt_succ (Node info  deg treeList summary) x = (if deg \<le> 1 then None else
    (case info of None \<Rightarrow> None |
    (Some mima) \<Rightarrow> (case mima of (mi, ma) \<Rightarrow> (
                   if x < mi then (Some mi) 
                   else (let l = low x (deg div 2); h = high x (deg div 2) in( 
                        if h < length treeList then  
                                let maxlow = vebt_maxt (treeList ! h) in 
                                (if maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow) then 
                                                        Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_succ (treeList ! h) l
                                 else let sc = vebt_succ summary h in
                                 if sc = None then None
                                 else Some (2^(deg div 2)) *\<^sub>o sc +\<^sub>o vebt_mint (treeList ! the sc) )
    
                         else None))))))"
    apply (cases "(Leaf a b,x)" rule: vebt_succ.cases; simp)                       
    apply (cases "(Node info  deg treeList summary,x)" rule: vebt_succ.cases; simp add: Let_def)
    done

  lemma vebt_pred_code[code]:
    "vebt_pred (Leaf a b) x = (if x = 0 then None else if x = 1 then 
                                      (if a then Some 0 else None) else
                               (if b then Some 1 else if a then Some 0 else None))" and
    "vebt_pred (Node info deg treeList summary) x =(if deg \<le> 1 then None else (
    case info of None \<Rightarrow> None |
    (Some mima) \<Rightarrow> (case mima of (mi, ma) \<Rightarrow> (
                           if x > ma then Some ma 
                           else (let l = low x (deg div 2); h = high x (deg div 2) in 
                           if h < length treeList then  
                                let minlow = vebt_mint (treeList ! h) in 
                                (if minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow) then 
                                                        Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o vebt_pred (treeList ! h) l
                                 else let pr = vebt_pred summary h in
                                 if pr = None then (if x > mi then Some mi else None)
                                 else Some (2^(deg div 2)) *\<^sub>o pr +\<^sub>o vebt_maxt (treeList ! the pr) )
                         else None)))))"
    apply (cases "(Leaf a b,x)" rule: vebt_pred.cases; simp)                       
    apply (cases "(Node info  deg treeList summary,x)" rule: vebt_pred.cases; simp add: Let_def)
    done                       
                       

  lemma vebt_delete_code[code]:
    "vebt_delete (Leaf a b) x = (if x = 0 then Leaf False b else if x = 1 then Leaf a False else Leaf a b)"
    "vebt_delete (Node info deg treeList summary) x = (
      case info of 
        None \<Rightarrow> (Node info deg treeList summary)  
      | Some mima \<Rightarrow> (
          if deg \<le> 1 then (Node info deg treeList summary) 
          else (case mima of (mi, ma) \<Rightarrow> ( 
            if (x < mi \<or> x > ma) then (Node (Some (mi, ma)) deg treeList summary)
            else if (x = mi \<and> x = ma) then (Node None deg treeList summary)
            else let 
              xn = (if x = mi then the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                     else x);
              minn = (if x = mi then xn else mi);
              l = low xn (deg div 2);
              h = high xn (deg div 2) 
            in
              if h < length treeList then let 
                newnode = vebt_delete (treeList ! h) l;
                newlist = treeList[h:= newnode]
              in
                if minNull newnode then let 
                  sn = vebt_delete summary h;
                  maxn = 
                    if xn = ma then let 
                      maxs = vebt_maxt sn 
                      in 
                        if maxs = None then minn 
                        else 2^(deg div 2) * the maxs + the (vebt_maxt (newlist ! the maxs))
                    else ma
                  in (Node (Some (minn, maxn)) deg newlist sn)
                else let
                  maxn = (if xn = ma then h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                     else ma)
                in (Node (Some (minn, maxn)) deg newlist summary)
              else (Node (Some (mi, ma)) deg treeList summary)
     ))))"
    apply (cases "(Leaf a b,x)" rule: vebt_delete.cases; simp)                       
    apply (cases "(Node info  deg treeList summary,x)" rule: vebt_delete.cases; simp add: Let_def)
    done
end
    
lemmas [code] = 
  VEBT_internal.high_def VEBT_internal.low_def VEBT_internal.minNull.simps
  VEBT_internal.less.simps VEBT_internal.mul_def VEBT_internal.add_def
  VEBT_internal.option_comp_shift.simps VEBT_internal.option_shift.simps
  
export_code 
  vebt_buildup 
  vebt_insert 
  vebt_member 
  vebt_maxt 
  vebt_mint 
  vebt_pred 
  vebt_succ 
  vebt_delete 
  checking SML   

subsection \<open>Correctness Lemmas\<close>

named_theorems vebt_simps \<open>Simplifier rules for VEBT functional interface\<close>

locale vebt_inst =
  fixes n :: nat
begin  

  interpretation VEBT_internal .

subsubsection \<open>Space Bound\<close>
theorem vebt_space_linear_bound: 
  fixes t
  defines "u \<equiv> 2^n"
  shows "invar_vebt t n \<Longrightarrow> space t \<le> 12*u" 
  by (simp add: space_bound u_def)

subsubsection \<open>Buildup\<close>
lemma invar_vebt_buildup[vebt_simps]: "invar_vebt (vebt_buildup n) n \<longleftrightarrow> n>0" 
  by (auto simp add: buildup_gives_valid deg_not_0)

lemma set_vebt_buildup[vebt_simps]: "set_vebt (vebt_buildup i) = {}" 
  by (metis VEBT_internal.buildup_gives_empty VEBT_internal.buildup_gives_valid VEBT_internal.set_vebt_set_vebt'_valid neq0_conv invar_vebt.intros(1) vebt_buildup.simps(1)) 

lemma time_vebt_buildup: "u = 2^n \<Longrightarrow> T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p  n \<le> 26 * u"
  using vebt_buildup_bound by simp
  
subsubsection \<open>Equality\<close>
lemma set_vebt_equal[vebt_simps]: "invar_vebt t\<^sub>1 n \<Longrightarrow> invar_vebt t\<^sub>2 n \<Longrightarrow> t\<^sub>1=t\<^sub>2 \<longleftrightarrow> set_vebt t\<^sub>1 = set_vebt t\<^sub>2"
  by (auto simp: unique_tree)

subsubsection \<open>Member\<close>
lemma set_vebt_member[vebt_simps]: "invar_vebt t n \<Longrightarrow> vebt_member t x \<longleftrightarrow> x\<in>set_vebt t"  
  by (rule member_correct)
  
theorem time_vebt_member: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>  T\<^sub>m\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>r t x \<le> 30 + 15 * lb (lb u)"
  using member_bound_size_univ by auto
  
  
subsubsection \<open>Insert\<close>
theorem invar_vebt_insert[vebt_simps]: "invar_vebt t n \<Longrightarrow> x< 2^n \<Longrightarrow> invar_vebt (vebt_insert t x) n"
  by (simp add: valid_pres_insert)

theorem set_vebt_insert[vebt_simps]: "invar_vebt t n  \<Longrightarrow> x < 2^n  \<Longrightarrow> set_vebt (vebt_insert t x) = set_vebt t \<union> {x}" 
  by (meson insert_correct[symmetric])

theorem time_vebt_insert: "invar_vebt t n \<Longrightarrow> u =  2^n \<Longrightarrow>   T\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t t x \<le> 46 + 23 * lb (lb u)" 
  by (meson insert_bound_size_univ)
  
  
subsubsection \<open>Maximum\<close>
theorem set_vebt_maxt: "invar_vebt t n \<Longrightarrow> vebt_maxt t = Some x \<longleftrightarrow> max_in_set (set_vebt t) x"  
  by (metis maxt_sound maxt_corr set_vebt_set_vebt'_valid)  

theorem set_vebt_maxt': "invar_vebt t n \<Longrightarrow> vebt_maxt t = Some x \<longleftrightarrow> (x\<in>set_vebt t \<and> (\<forall>y\<in>set_vebt t. x\<ge>y))"  
  using set_vebt_maxt unfolding max_in_set_def by blast
  
lemma set_vebt_maxt''[vebt_simps]: 
  "invar_vebt t n \<Longrightarrow> vebt_maxt t = (if set_vebt t = {} then None else Some (Max (set_vebt t)))"
  by (metis Max_ge Max_in VEBT_internal.set_vebt_finite VEBT_internal.set_vebt_set_vebt'_valid empty_iff option.exhaust set_vebt_maxt')
  
lemma time_vebt_maxt: "T\<^sub>m\<^sub>a\<^sub>x\<^sub>t t \<le>  3" 
  by (simp add: maxt_bound)
  
  
subsubsection \<open>Minimum\<close>
theorem set_vebt_mint[vebt_simps]: "invar_vebt t n \<Longrightarrow> vebt_mint t = Some x \<longleftrightarrow> min_in_set (set_vebt t) x"  
  by (metis VEBT_internal.mint_corr VEBT_internal.mint_sound VEBT_internal.set_vebt_set_vebt'_valid)

theorem set_vebt_mint': "invar_vebt t n \<Longrightarrow> vebt_mint t = Some x \<longleftrightarrow> (x\<in>set_vebt t \<and> (\<forall>y\<in>set_vebt t. x\<le>y))"  
  using set_vebt_mint unfolding min_in_set_def by blast

lemma set_vebt_mint''[vebt_simps]: 
  "invar_vebt t n \<Longrightarrow> vebt_mint t = (if set_vebt t = {} then None else Some (Min (set_vebt t)))"
  by (metis Min_in Min_le VEBT_internal.set_vebt_finite VEBT_internal.set_vebt_set_vebt'_valid empty_iff option.exhaust set_vebt_mint')
  
lemma time_vebt_mint: "T\<^sub>m\<^sub>i\<^sub>n\<^sub>t t \<le>  3" 
  by (simp add: mint_bound)  

subsection \<open>Emptiness determination\<close>
text \<open> A tree is empty if and only if its minimum is None\<close>

lemma vebt_minNull_mint: " minNull t \<longleftrightarrow> vebt_mint t = None"
  by (meson VEBT_internal.minNullmin VEBT_internal.minminNull)
  
lemma set_vebt_minNull: "invar_vebt t n \<Longrightarrow> minNull t \<longleftrightarrow> set_vebt t = {}"
  by (metis VEBT_internal.minNullmin VEBT_internal.minminNull VEBT_internal.mint_corr_help_empty VEBT_internal.set_vebt_set_vebt'_valid vebt_inst.set_vebt_mint'')

lemma time_vebt_minNull: "T\<^sub>m\<^sub>i\<^sub>n\<^sub>N\<^sub>u\<^sub>l\<^sub>l t \<le> 1" 
  using minNull_bound by auto

subsubsection \<open>Successor\<close>
theorem set_vebt_succ: "invar_vebt t n \<Longrightarrow> vebt_succ t x = Some sx \<longleftrightarrow> is_succ_in_set (set_vebt t) x sx" 
  by (simp add: succ_corr set_vebt_set_vebt'_valid)
    
lemma set_vebt_succ'[vebt_simps]: "invar_vebt t n \<Longrightarrow> vebt_succ t x = (if \<exists>  y \<in> set_vebt t. y > x then Some (LEAST y \<in> set_vebt t. y > x) else None)"
  apply (clarsimp;safe)
  subgoal
    apply(clarsimp simp add: succ_correct is_succ_in_set_def Least_le)
    by (metis (no_types, lifting) LeastI_ex)
  subgoal by (meson succ_correct is_succ_in_set_def option.exhaust_sel)
  done

theorem time_vebt_succ: 
  fixes t defines "u \<equiv> 2^n"
  shows "invar_vebt t n \<Longrightarrow>   T\<^sub>s\<^sub>u\<^sub>c\<^sub>c t x \<le> 54 + 27 * lb (lb u)" 
  using succ_bound_size_univ unfolding u_def by presburger
  
  
subsubsection \<open>Predecessor\<close>  
theorem set_vebt_pred: "invar_vebt t n \<Longrightarrow> vebt_pred t x = Some px \<longleftrightarrow> is_pred_in_set (set_vebt t) x px" 
  by (simp add: pred_corr set_vebt_set_vebt'_valid)

theorem set_vebt_pred'[vebt_simps]: "invar_vebt t n \<Longrightarrow> 
  vebt_pred t x = (if \<exists>  y \<in> set_vebt t. y < x then Some (GREATEST y. y \<in> set_vebt t \<and> y < x) else None)" 
  apply (clarsimp simp: member_correct pred_empty pred_correct is_pred_in_set_def)
  by (metis (no_types, lifting) GreatestI_nat Greatest_le_nat less_imp_le)

theorem time_vebt_pred:   fixes t defines "u \<equiv> 2^n"
  shows "invar_vebt t n \<Longrightarrow> T\<^sub>p\<^sub>r\<^sub>e\<^sub>d t x \<le> 58 + 29 * lb (lb u)"
  unfolding u_def by (meson pred_bound_size_univ)
  
  
subsubsection \<open>Delete\<close>  
theorem invar_vebt_delete[vebt_simps]: "invar_vebt t n \<Longrightarrow> invar_vebt (vebt_delete t x) n" 
  by (simp add: delete_pres_valid)

theorem set_vebt_delete[vebt_simps]: "invar_vebt t n \<Longrightarrow> set_vebt (vebt_delete t x) = set_vebt t - {x}" 
  by (metis delete_correct invar_vebt_delete set_vebt_set_vebt'_valid)

theorem time_vebt_delete:   fixes t defines "u \<equiv> 2^n"
  shows "invar_vebt t n \<Longrightarrow> T\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e  t x \<le> 140 + 70 * lb (lb u)" 
  unfolding u_def by (meson delete_bound_size_univ)
  
end  
  
subsection \<open>Interface Usage Example\<close>
  
experiment
begin

  definition "test n xs ys \<equiv> let
    t = vebt_buildup n;
    t = foldl vebt_insert t (0#xs);
    
    f = (\<lambda>x. if vebt_member t x then x else the (vebt_pred t x))
  in 
    map f ys"

    
  context fixes n :: nat begin  
    interpretation vebt_inst n .
        
    lemmas [simp] = vebt_simps  
      
    lemma [simp]: 
      assumes "invar_vebt t n" "\<forall>x\<in>set xs. x<2^n"
      shows "invar_vebt (foldl vebt_insert t xs) n"
      using assms apply (induction xs arbitrary: t)
      by auto 
  
    lemma [simp]: 
      assumes "invar_vebt t n" "\<forall>x\<in>set xs. x<2^n"
      shows "set_vebt (foldl vebt_insert t xs) = set_vebt t \<union> set xs"
      using assms
      apply (induction xs arbitrary: t)
      apply auto 
      done
                
    lemma "\<lbrakk>\<forall>x\<in>set xs. x<2^n; n>0\<rbrakk> \<Longrightarrow> test n xs ys = map (\<lambda>y. (GREATEST y'. y'\<in>insert 0 (set xs) \<and> y'\<le>y)) ys"
      unfolding test_def
      apply (auto simp add: Let_def)
      subgoal by (metis (mono_tags, lifting) Greatest_equality le_zero_eq)
      subgoal by (metis (no_types, lifting) Greatest_equality order_refl)
      subgoal by (metis less_le)
      done
      
  end    

end


  (* TODO: Use uniqueness to define = operation! *)

end

