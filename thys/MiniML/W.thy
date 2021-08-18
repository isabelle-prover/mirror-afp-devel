(* Title:     MiniML/W.thy
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Correctness and completeness of type inference algorithm W"

theory W
imports MiniML
begin

type_synonym result_W = "(subst * typ * nat) option"

\<comment> \<open>type inference algorithm W\<close>
fun W :: "[expr, ctxt, nat] => result_W" where
  "W (Var i) A n =  
     (if i < length A then Some( id_subst,   
                                 bound_typ_inst (\<lambda>b. TVar(b+n)) (A!i),   
                                 n + (min_new_bound_tv (A!i)) )  
                      else None)"
  
| "W (Abs e) A n = ( (S,t,m) := W e ((FVar n)#A) (Suc n);
                     Some( S, (S n) -> t, m) )"
  
| "W (App e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ($S1 A) m1;
                         U := mgu ($S2 t1) (t2 -> (TVar m2));
                         Some( $U \<circ> $S2 \<circ> S1, U m2, Suc m2) )"
  
| "W (LET e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ((gen ($S1 A) t1)#($S1 A)) m1;
                         Some( $S2 \<circ> S1, t2, m2) )"


declare Suc_le_lessD [simp]

inductive_cases has_type_casesE:
"A \<turnstile> Var n :: t"
"A \<turnstile> Abs e :: t"
"A \<turnstile> App e1 e2 ::t"
"A \<turnstile> LET e1 e2 ::t"


\<comment> \<open>the resulting type variable is always greater or equal than the given one\<close>
lemma W_var_ge: 
  "W e A n  = Some (S,t,m) \<Longrightarrow> n \<le> m"
proof (induction e arbitrary: A n S t m)
  case Var thus ?case by (auto split: if_splits)
next
  case Abs thus ?case by (fastforce split: split_option_bind_asm)
next
  case App thus ?case by (fastforce split: split_option_bind_asm)
next
  case LET thus ?case by (fastforce split: split_option_bind_asm)
qed

declare W_var_ge [simp] (* FIXME*)

lemma W_var_geD: 
  "Some (S,t,m) = W e A n \<Longrightarrow> n\<le>m"
by (metis W_var_ge)


lemma new_tv_compatible_W: 
  "new_tv n A \<Longrightarrow> Some (S,t,m) = W e A n \<Longrightarrow> new_tv m A"
by (metis W_var_ge new_tv_le)

lemma new_tv_bound_typ_inst_sch: 
  "new_tv n sch \<Longrightarrow> new_tv (n + (min_new_bound_tv sch)) (bound_typ_inst (\<lambda>b. TVar (b + n)) sch)"
proof (induction sch)
  case FVar thus ?case by simp
next
  case BVar thus ?case by simp
next
  case SFun thus ?case by(auto simp add: max_def nle_le dest: new_tv_le add_left_mono)
qed

\<comment> \<open>resulting type variable is new\<close>
lemma new_tv_W [rule_format]: 
  "\<forall>n A S t m. new_tv n A \<longrightarrow> W e A n = Some (S,t,m) \<longrightarrow>     
               new_tv m S \<and> new_tv m t"
proof (induction e)
  case Var thus ?case
    by (auto simp add: new_tv_bound_typ_inst_sch dest: new_tv_nth_nat_A)
next
  case Abs thus ?case
    apply (simp add: new_tv_subst split: split_option_bind)
    by (metis lessI new_tv_Cons new_tv_FVar new_tv_Suc new_tv_compatible_W )
next
  case App thus ?case
    apply (simp split: split_option_bind)
    by (smt (verit, ccfv_threshold) W_var_geD fun.map_comp lessI mgu_new new_tv_Fun new_tv_Suc new_tv_le new_tv_subst new_tv_subst_comp_1 new_tv_subst_scheme_list new_tv_subst_te)
next
  case LET thus ?case
    apply (simp split: split_option_bind)
    by (metis W_var_ge new_tv_Cons new_tv_compatible_gen new_tv_le new_tv_subst_comp_1 new_tv_subst_scheme_list)
qed

lemma free_tv_bound_typ_inst1:
  "v \<notin> free_tv sch \<Longrightarrow> v \<in> free_tv (bound_typ_inst (TVar \<circ> S) sch) \<Longrightarrow> \<exists>x. v = S x"
by (induction sch) auto

lemma free_tv_W [rule_format]: 
  "\<forall>n A S t m v. W e A n = Some (S,t,m) \<longrightarrow>             
          (v\<in>free_tv S \<or> v\<in>free_tv t) \<longrightarrow> v<n \<longrightarrow> v\<in>free_tv A"
proof (induct e)
  case (Var n) then show ?case
    apply (simp (no_asm) add: free_tv_subst split: split_option_bind)
    apply (intro strip)
    apply (case_tac "v : free_tv (A!n)")
    apply (simp add: free_tv_nth_A_impl_free_tv_A)
    apply (drule free_tv_bound_typ_inst1)
    apply (simp (no_asm) add: o_def)
    apply (erule exE)
    apply simp
    done
  case Abs then show ?case
    apply (simp add: free_tv_subst split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S t n1 v)
    apply (erule_tac x = "Suc n" in allE)
    apply (erule_tac x = "FVar n # A" in allE)
    apply (erule_tac x = "S" in allE)
    apply (erule_tac x = "t" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "v" in allE)
    apply (bestsimp intro: cod_app_subst simp add: less_Suc_eq)
    done
  case App then show ?case
    apply (simp (no_asm) split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S t n1 S1 t1 n2 S2 v)
    apply (erule_tac x = "n" in allE)
    apply (erule_tac x = "A" in allE)
    apply (erule_tac x = "S" in allE)
    apply (erule_tac x = "t" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "v" in allE)
    (* second case *)
    apply (erule_tac x = "$ S A" in allE)
    apply (erule_tac x = "S1" in allE)
    apply (erule_tac x = "t1" in allE)
    apply (erule_tac x = "n2" in allE)
    apply (erule_tac x = "v" in allE)
    apply (intro conjI impI | elim conjE)+
    apply (simp add: rotate_Some o_def)
    apply (drule W_var_geD)
    apply (drule W_var_geD)
    apply ( (frule less_le_trans) , (assumption))
    apply clarsimp 
    apply (drule free_tv_comp_subst [THEN subsetD])
    apply (drule sym [THEN mgu_free])
    apply clarsimp 
    apply (fastforce dest: free_tv_comp_subst [THEN subsetD] sym [THEN mgu_free] codD free_tv_app_subst_te [THEN subsetD] free_tv_app_subst_scheme_list [THEN subsetD] less_le_trans less_not_refl2 subsetD)
    apply simp
    apply (drule sym [THEN W_var_geD])
    apply (drule sym [THEN W_var_geD])
    apply ( (frule less_le_trans) , (assumption))
    apply clarsimp
    apply (drule mgu_free)
    apply (fastforce dest: mgu_free codD free_tv_subst_var [THEN subsetD] free_tv_app_subst_te [THEN subsetD] free_tv_app_subst_scheme_list [THEN subsetD] less_le_trans subsetD)
    done
next
  case LET then show ?case
    apply (simp (no_asm) split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S1 t1 n2 S2 t2 n3 v)
    apply (erule_tac x = "n" in allE)
    apply (erule_tac x = "A" in allE)
    apply (erule_tac x = "S1" in allE)
    apply (erule_tac x = "t1" in allE)
    apply (rotate_tac -1)
    apply (erule_tac x = "n2" in allE)
    apply (rotate_tac -1)
    apply (erule_tac x = "v" in allE)
    apply (erule (1) notE impE)
    apply (erule allE,erule allE,erule allE,erule allE,erule allE,erule_tac  x = "v" in allE)
    apply (erule (1) notE impE)
    apply simp
    apply (rule conjI)
    apply (fast dest!: codD free_tv_app_subst_scheme_list [THEN subsetD] free_tv_o_subst [THEN subsetD] W_var_ge dest: less_le_trans)
    apply (fast dest!: codD free_tv_app_subst_scheme_list [THEN subsetD] W_var_ge dest: less_le_trans)
    done
qed

lemma weaken_A_Int_B_eq_empty: "(\<forall>x. x \<in> A \<longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
apply fast
done

lemma weaken_not_elem_A_minus_B: "x \<notin> A \<or> x \<in> B \<Longrightarrow> x \<notin> A - B"
apply fast
done

\<comment> \<open>correctness of W with respect to @{text has_type}\<close>
lemma W_correct_lemma [rule_format]: "\<forall>A S t m n . new_tv n A \<longrightarrow> Some (S,t,m) = W e A n \<longrightarrow> $S A \<turnstile> e :: t"
proof (induct "e")
case (Var n) thus ?case
apply simp
apply (intro strip)
apply (rule has_type.VarI)
apply (simp (no_asm))
apply (simp (no_asm) add: is_bound_typ_instance)
apply (rule exI)
apply (rule refl)
done
case (Abs e) thus ?case
apply (simp add: app_subst_list split: split_option_bind)
apply (intro strip)
apply (erule_tac x = " (mk_scheme (TVar n)) # A" in allE)
apply simp
apply (rule has_type.AbsI)
apply (drule le_refl [THEN le_SucI, THEN new_tv_le])
apply (drule sym)
apply (erule allE)+
apply (erule impE)
apply (erule_tac [2] notE impE, tactic "assume_tac @{context} 2")
apply (simp (no_asm_simp))
by assumption
case (App e1 e2) thus ?case
apply (simp (no_asm) split: split_option_bind)
apply (intro strip)
apply (rename_tac S1 t1 n1 S2 t2 n2 S3)
apply (rule_tac ?t2.0 = "$ S3 t2" in has_type.AppI)
apply (rule_tac S1 = "S3" in app_subst_TVar [THEN subst])
apply (rule app_subst_Fun [THEN subst])
apply (rule_tac t = "$S3 (t2 -> (TVar n2))" and s = "$S3 ($S2 t1) " in subst)
apply (simp add: mgu_eq)
apply (simp only: subst_comp_scheme_list [symmetric] o_def) 
apply ((rule has_type_cl_sub [THEN spec]) , (rule has_type_cl_sub [THEN spec]))
apply (simp add: eq_sym_conv)
apply (simp add: subst_comp_scheme_list [symmetric] o_def has_type_cl_sub eq_sym_conv)
apply (rule has_type_cl_sub [THEN spec])
apply (frule new_tv_W)
apply assumption
apply (drule conjunct1)
apply (frule new_tv_subst_scheme_list)
apply (rule new_tv_le)
apply (rule W_var_ge)
apply assumption
apply assumption
apply (erule thin_rl)
apply (erule allE)+
apply (drule sym)
apply (drule sym)
apply (erule thin_rl)
apply (erule thin_rl)
apply (erule (1) notE impE)
apply (erule (1) notE impE)
by assumption
case (LET e1 e2) thus ?case
apply (simp (no_asm) split: split_option_bind)
apply (intro strip)
(*by (rename_tac "w q m1 S1 t1 m2 S2 t n2" 1); *)
apply (rename_tac S1 t1 m1 S2)
apply (rule_tac ?t1.0 = "$ S2 t1" in has_type.LETI)
 apply (simp (no_asm) add: o_def)
 apply (simp only: subst_comp_scheme_list [symmetric])
 apply (rule has_type_cl_sub [THEN spec])
 apply (drule_tac x = "A" in spec)
 apply (drule_tac x = "S1" in spec)
 apply (drule_tac x = "t1" in spec)
 apply (drule_tac x = "m1" in spec)
 apply (drule_tac x = "n" in spec)
 apply (erule (1) notE impE)
 apply (simp add: eq_sym_conv)
apply (simp (no_asm) add: o_def)
apply (simp only: subst_comp_scheme_list [symmetric])
apply (rule gen_subst_commutes [symmetric, THEN subst])
 apply (rule_tac [2] app_subst_Cons [THEN subst])
 apply (erule_tac [2] thin_rl)
 apply (drule_tac [2] x = "gen ($S1 A) t1 # $ S1 A" in spec)
 apply (drule_tac [2] x = "S2" in spec)
 apply (drule_tac [2] x = "t" in spec)
 apply (drule_tac [2] x = "m" in spec)
 apply (drule_tac [2] x = "m1" in spec)
 apply (frule_tac [2] new_tv_W)
    prefer 2 apply (assumption)
  prefer 2
  apply (metis new_tv_Cons new_tv_compatible_W new_tv_compatible_gen new_tv_subst_scheme_list)
apply (rule weaken_A_Int_B_eq_empty)
apply (rule allI)
apply (intro strip)
apply (rule weaken_not_elem_A_minus_B)
  by (metis free_tv_W free_tv_gen_cons free_tv_le_new_tv new_tv_W)
qed

\<comment> \<open>Completeness of W w.r.t. @{text has_type}\<close>
lemma W_complete_lemma [rule_format]: 
  "\<forall>S' A t' n. $S' A \<turnstile> e :: t' \<longrightarrow> new_tv n A \<longrightarrow>
               (\<exists>S t. (\<exists>m. W e A n = Some (S,t,m)) \<and>
                       (\<exists>R. $S' A = $R ($S A) \<and> t' = $R t))"
  proof (induct e)
    case (Var) thus ?case
     apply (intro strip)
     apply (simp (no_asm) cong add: conj_cong)
     apply (erule has_type_casesE)
     apply (simp add: is_bound_typ_instance)
     apply (erule exE)
     apply (hypsubst)
     apply (rename_tac "S")
     apply (rule_tac x = "\<lambda>x. (if x < n then S' x else S (x - n))" in exI)
     apply (rule conjI)
      apply (simp add: new_if_subst_type_scheme_list)
     apply (simp (no_asm_simp) add: new_if_subst_type_scheme bound_typ_inst_composed_subst [symmetric] new_tv_nth_nat_A o_def nth_subst 
      del: bound_typ_inst_composed_subst)
done
case (Abs e) thus ?case
    apply (intro strip)
    apply (erule has_type_casesE)
    apply (erule_tac x = "\<lambda>x. if x=n then t1 else (S' x) " in allE)
    apply (erule_tac x = " (FVar n) #A" in allE)
    apply (erule_tac x = "t2" in allE)
    apply (erule_tac x = "Suc n" in allE)
    apply (bestsimp dest!: mk_scheme_injective cong: conj_cong split: split_option_bind)
done
case (App e1 e2) thus ?case
   apply (intro strip)
   apply (erule has_type_casesE)
   apply (erule_tac x = "S'" in allE)
   apply (erule_tac x = "A" in allE)
   apply (erule_tac x = "t2 -> t'" in allE)
   apply (erule_tac x = "n" in allE)
   apply safe
   apply (erule_tac x = "R" in allE)
   apply (erule_tac x = "$ S A" in allE)
   apply (erule_tac x = "t2" in allE)
   apply (erule_tac x = "m" in allE)
   apply simp
   apply safe
    apply (blast intro: sym [THEN W_var_geD] new_tv_W [THEN conjunct1] new_tv_le new_tv_subst_scheme_list)

(** LEVEL 33 **)
   apply (subgoal_tac "$ (\<lambda>x. if x=ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) ($ Sa t) = $ (\<lambda>x. if x=ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) (ta -> (TVar ma))")
    apply (rule_tac [2] t = "$ (\<lambda>x. if x = ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) ($ Sa t) " and s = " ($ Ra ta) -> t'" in ssubst)
     prefer 2 apply (simp (no_asm_simp) add: subst_comp_te) prefer 2
     apply (rule_tac [2] eq_free_eq_subst_te)
     prefer 2 apply (intro strip) prefer 2
     apply (subgoal_tac [2] "na \<noteq>ma")
      prefer 3 apply (best dest: new_tv_W sym [THEN W_var_geD] new_tv_not_free_tv new_tv_le)
     apply (case_tac [2] "na:free_tv Sa")
    (* n1 \<notin> free_tv S1 *)
      apply (frule_tac [3] not_free_impl_id)
      prefer 3 apply (simp)
    (* na : free_tv Sa *)
     apply (drule_tac [2] A1 = "$ S A" in trans [OF _ subst_comp_scheme_list])
     apply (drule_tac [2] eq_subst_scheme_list_eq_free)
      prefer 2 apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
     prefer 2 apply (simp (no_asm_simp)) prefer 2
     apply (case_tac [2] "na:dom Sa")
    (* na \<notin> dom Sa *)
      prefer 3 apply (simp add: dom_def)
    (* na : dom Sa *)
     apply (rule_tac [2] eq_free_eq_subst_te)
     prefer 2 apply (intro strip) prefer 2
     apply (subgoal_tac [2] "nb \<noteq> ma")
      apply (frule_tac [3] new_tv_W) prefer 3 apply assumption
      apply (erule_tac [3] conjE)
      apply (drule_tac [3] new_tv_subst_scheme_list)
       prefer 3 apply (fast intro: new_tv_le dest: sym [THEN W_var_geD])
      prefer 3 apply (fastforce dest: new_tv_W new_tv_not_free_tv simp add: cod_def free_tv_subst)
     prefer 2 apply (fastforce simp add: cod_def free_tv_subst)
    prefer 2 apply (simp (no_asm)) prefer 2
    apply (rule_tac [2] eq_free_eq_subst_te)
    prefer 2 apply (intro strip) prefer 2
    apply (subgoal_tac [2] "na \<noteq> ma")
     apply (frule_tac [3] new_tv_W) prefer 3 apply assumption
     apply (erule_tac [3] conjE)
     apply (drule_tac [3] sym [THEN W_var_geD])
     prefer 3 apply (fast dest: new_tv_le new_tv_subst_scheme_list new_tv_W new_tv_not_free_tv)
    apply (case_tac [2] "na: free_tv t - free_tv Sa")
    (* case na \<notin> free_tv t - free_tv Sa *)
     prefer 3 
     apply simp
     apply fast
    (* case na : free_tv t - free_tv Sa *)
    prefer 2 apply simp prefer 2
    apply (drule_tac [2] A1 = "$ S A" and r = "$ R ($ S A)" in trans [OF _ subst_comp_scheme_list])
    apply (drule_tac [2] eq_subst_scheme_list_eq_free)
     prefer 2 
     apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
    (** LEVEL 73 **)
    prefer 2 apply (simp add: free_tv_subst dom_def)
   apply (simp (no_asm_simp) split: split_option_bind)
   apply safe
    apply (drule mgu_Some)
    apply fastforce  
    (** LEVEL 78 *)
   apply (drule mgu_mg, assumption)
   apply (erule exE)
   apply (rule_tac x = "Rb" in exI)
   apply (rule conjI)
    apply (drule_tac [2] x = "ma" in fun_cong)
    prefer 2 apply (simp add: eq_sym_conv)
   apply (simp (no_asm) add: subst_comp_scheme_list)
   apply (simp (no_asm) add: subst_comp_scheme_list [symmetric])
   apply (rule_tac A1 = "($ Sa ($ S A))" in trans [OF _ subst_comp_scheme_list [symmetric]])
   apply (simp add: o_def eq_sym_conv)
   apply (drule_tac s = "Some _" in sym)
   apply (rule eq_free_eq_subst_scheme_list)
   apply safe
   apply (subgoal_tac "ma \<noteq> na")
    apply (frule_tac [2] new_tv_W) prefer 2 apply assumption
    apply (erule_tac [2] conjE)
    apply (drule_tac [2] new_tv_subst_scheme_list)
     prefer 2 apply (fast intro: new_tv_le dest: sym [THEN W_var_geD])
    apply (frule_tac [2] n = "m" in new_tv_W) prefer 2 apply assumption
    apply (erule_tac [2] conjE)
    apply (drule_tac [2] free_tv_app_subst_scheme_list [THEN subsetD])
    apply (tactic \<open>
    (fast_tac (put_claset (claset_of @{theory_context Fun}) @{context}
      addDs [sym RS @{thm W_var_geD}, @{thm new_tv_le}, @{thm codD},
        @{thm new_tv_not_free_tv}]) 2)\<close>)
   apply (case_tac "na: free_tv t - free_tv Sa")
    (* case na \<notin> free_tv t - free_tv Sa *)
    prefer 2 apply simp apply blast
    (* case na : free_tv t - free_tv Sa *)
   apply simp
   apply (drule free_tv_app_subst_scheme_list [THEN subsetD])
   apply (fastforce dest: codD trans [OF _ subst_comp_scheme_list]
      eq_subst_scheme_list_eq_free 
      simp add: free_tv_subst dom_def)
done
case (LET e1 e2) thus ?case
apply safe
  apply (erule has_type_casesE)
  apply (erule_tac x = "S'" in allE)
  apply (erule_tac x = "A" in allE)
  apply (erule_tac x = "t1" in allE)
  apply (erule_tac x = "n" in allE)
  apply (erule (1) notE impE)
  apply (erule (1) notE impE)
  apply safe  
  apply (simp (no_asm_simp))
  apply (erule_tac x = "R" in allE)
  apply (erule_tac x = "gen ($ S A) t # $ S A" in allE)
  apply (erule_tac x = "t'" in allE)
  apply (erule_tac x = "m" in allE)
  apply simp
  apply (drule mp)
   apply (rule has_type_le_env)
    apply assumption
   apply (simp (no_asm))
   apply (rule gen_bound_typ_instance)
  apply (drule mp)
   apply (frule new_tv_compatible_W)
    apply (rule sym)
    apply assumption
   apply (fast dest: new_tv_compatible_gen new_tv_subst_scheme_list new_tv_W)
  apply safe
  apply simp
  apply (rule_tac x = "Ra" in exI)
  apply (simp (no_asm) add: o_def subst_comp_scheme_list [symmetric])
  done
qed

theorem W_complete: 
  "[] \<turnstile> e :: t' \<Longrightarrow> \<exists>S t m. W e [] n = Some(S,t,m) \<and> (\<exists>R. t' = $ R t)"
by (metis W_complete_lemma app_subst_Nil new_tv_Nil)

end
