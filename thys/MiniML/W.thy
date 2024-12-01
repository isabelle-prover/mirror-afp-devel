(* Title:     MiniML/W.thy
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
   2024: Conversion to Isar by LCP
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

inductive_simps has_type_simps:
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

lemma free_tv_W: 
  "W e A n = Some (S,t,m) \<Longrightarrow>           
          (v\<in>free_tv S \<or> v\<in>free_tv t) \<Longrightarrow> v<n \<Longrightarrow> v\<in>free_tv A"
proof (induction e arbitrary: n A S t m v)
  case (Var i) 
  show ?case
  proof (cases "v \<in> free_tv (A!i)")
    case True
    with Var show ?thesis 
      by (metis W.simps(1) free_tv_nth_A_impl_free_tv_A not_None_eq)
  next
    case False
    with Var show ?thesis
      by (force simp: o_def free_tv_nth_A_impl_free_tv_A dest: free_tv_bound_typ_inst1 
          split: if_split_asm)
  qed
next
  case (Abs e n A S t m v) 
  then obtain S1 t1 n1 where "W e (FVar n # A) (Suc n) = Some (S1, t1, n1)"
    by (metis (lifting) W.simps(2) not_None_eq option_bind_eq_None prod_cases3)
  then show ?case
    using Abs.IH [of "FVar n # A" "Suc n" S1 t1 n1 v] Abs.prems 
    by (force simp: codD cod_app_subst)
next
  case (App e1 e2 n A S t m v) 
  then show ?case
  proof (clarsimp split: split_option_bind_asm prod.split_asm)
    fix S' t' n1 S1 t1 n2 S2
    assume v: "v \<in> free_tv ($ S2 \<circ> $ S1 \<circ> S') \<or> v \<in> free_tv (S2 n2)"
      and "v < n"
      and e1: "W e1 A n = Some (S', t', n1)"
      and e2: "W e2 ($ S' A) n1 = Some (S1, t1, n2)"
      and mgu: "mgu ($ S1 t') (t1 -> TVar n2) = Some S2"
    have n: "n \<le> n1" "n1 \<le> n2"
      using e1 e2 by auto
    show "v \<in> free_tv A"
      using v
    proof
      assume v1: "v \<in> free_tv ($ S2 \<circ> $ S1 \<circ> S')"
      then have "v \<in> free_tv S2 \<union> free_tv (\<lambda>x. $ S1 (S' x))"
        by (metis (no_types, lifting) ext comp_apply free_tv_o_subst fun.map_comp
            subsetD)
      moreover
      have "free_tv S2 \<subseteq> insert n2 (free_tv ($ S1 t') \<union> free_tv t1)"
        using mgu mgu_free by fastforce
      ultimately
      show "v \<in> free_tv A"
        using App.IH n v1 \<open>v<n\<close> e1 e2 codD free_tv_app_subst_scheme_list 
        by (smt (verit, ccfv_threshold) Un_iff free_tv_app_subst_te free_tv_o_subst
            fun.map_comp insert_iff linorder_not_less order.strict_trans2 subsetD)
    next
      assume v2: "v \<in> free_tv (S2 n2)"
      then have "v < n1"
        using App.prems n by linarith
      then have "free_tv S2 \<subseteq> free_tv ($ S1 t') \<union> free_tv (t1 -> TVar n2)"
        using mgu mgu_free by blast
      then show "v \<in> free_tv A"
        using App.IH n v2 \<open>v<n\<close> \<open>v<n1\<close> e1 e2 codD free_tv_app_subst_scheme_list 
        by (smt (verit, ccfv_threshold) UnE  cod_app_subst empty_iff 
            free_tv_app_subst_te free_tv_typ.simps insert_iff linorder_not_less subsetD)
    qed
  qed
next
  case (LET e1 e2 n A S t2 n3 v) 
  then show ?case
  proof (clarsimp split: split_option_bind_asm prod.split_asm)
    fix S1 t1 n2 S2
    assume "v \<in> free_tv ($ S2 \<circ> S1) \<or> v \<in> free_tv t2"
      and "v < n"
      and "W e1 A n = Some (S1, t1, n2)"
      and "W e2 (gen ($ S1 A) t1 # $ S1 A) n2 = Some (S2, t2, n3)"
    with LET.IH
    show "v \<in> free_tv A"
      by (smt (verit) Un_iff W_var_geD codD free_tv_app_subst_scheme_list 
          free_tv_gen_cons free_tv_o_subst order.strict_trans2 subsetD)
  qed
qed

lemma weaken_A_Int_B_eq_empty: "(\<forall>x. x \<in> A \<longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
  by blast

lemma weaken_not_elem_A_minus_B: "x \<notin> A \<or> x \<in> B \<Longrightarrow> x \<notin> A - B"
  by blast

\<comment> \<open>correctness of W with respect to @{text has_type}\<close>
lemma W_correct_lemma: "\<lbrakk>new_tv n A; Some (S,t,m) = W e A n\<rbrakk> \<Longrightarrow> $S A \<turnstile> e :: t"
proof (induction "e" arbitrary: A S t m n)
  case Var thus ?case
    using is_bound_typ_instance by (auto split: if_splits)
next
  case (Abs e) thus ?case
    apply (simp split: split_option_bind_asm prod.splits)
    by (metis AbsI app_subst_Cons app_subst_type_scheme.simps(1) lessI new_tv_Cons
        new_tv_FVar new_tv_Suc)
next
  case (App e1 e2) 
  then show ?case
  proof (simp split: split_option_bind_asm prod.splits)
    fix S1 t1 n1 S2 t2 n2 S3
    assume e1: "W e1 A n = Some (S1, t1, n1)"
      and e2: "W e2 ($ S1 A) n1 = Some (S2, t2, n2)"
      and mgu: "mgu ($ S2 t1) (t2 -> TVar n2) = Some S3"
    show "$ (\<lambda>a. $ S3 ($ S2 (S1 a))) A \<turnstile> App e1 e2 :: S3 n2"
    proof (rule has_type.AppI)
      have "$ S3 (t2 -> TVar n2) = $ S3 ($ S2 t1)"
        using mgu mgu_eq by presburger
      with App show "$ (\<lambda>a. $ S3 ($ S2 (S1 a))) A \<turnstile> e1 :: $ S3 t2 -> S3 n2"
        by (metis (no_types) Type.app_subst_Fun Type.app_subst_TVar e1 has_type_cl_sub subst_comp_scheme_list)
      show "$ (\<lambda>a. $ S3 ($ S2 (S1 a))) A \<turnstile> e2 :: $ S3 t2"
        using e1 e2 mgu App
        by (metis has_type_cl_sub new_tv_W new_tv_compatible_W new_tv_subst_scheme_list
            subst_comp_scheme_list)
    qed
  qed
next
  case (LET e1 e2) thus ?case
  proof (simp split: split_option_bind_asm prod.splits)
    fix S1 t1 m1 S2
    assume "new_tv n A"
      and e1: "W e1 A n = Some (S1, t1, m1)"
      and e2: "W e2 (gen ($ S1 A) t1 # $ S1 A) m1 = Some (S2, t, m)"
    show "$ (\<lambda>a. $ S2 (S1 a)) A \<turnstile> LET e1 e2 :: t"
    proof (rule has_type.LETI)
      show "$ (\<lambda>a. $ S2 (S1 a)) A \<turnstile> e1 :: $ S2 t1"
        using LET e1 by (metis (no_types, lifting) has_type_cl_sub subst_comp_scheme_list)
      have "free_tv S2 \<inter> (free_tv t1 - free_tv ($ S1 A)) = {}"
        using e1 e2 LET
        by (smt (verit) DiffD2 Diff_subset free_tv_W free_tv_gen_cons
            free_tv_le_new_tv new_tv_W subsetD weaken_A_Int_B_eq_empty)
      then
      show "gen ($ (\<lambda>a. $ S2 (S1 a)) A) ($ S2 t1) # $ (\<lambda>a. $ S2 (S1 a)) A \<turnstile> e2 :: t"
        using e1 e2 LET
        by (metis app_subst_Cons gen_subst_commutes new_tv_Cons new_tv_W new_tv_compatible_W
            new_tv_compatible_gen new_tv_subst_scheme_list subst_comp_scheme_list)
    qed
  qed
qed

\<comment> \<open>Completeness of W w.r.t. @{text has_type}\<close>
lemma W_complete_lemma: 
  "\<lbrakk>$S' A \<turnstile> e :: t'; new_tv n A\<rbrakk> \<Longrightarrow>
   \<exists>S t. (\<exists>m. W e A n = Some (S,t,m)) \<and> (\<exists>R. $S' A = $R ($S A) \<and> t' = $R t)"
proof (induction e arbitrary: S' A t' n)
  case (Var u) thus ?case
  proof (clarsimp simp add: has_type_simps is_bound_typ_instance)
    fix S :: "nat \<Rightarrow> typ"
    assume A: "new_tv n A" "u < length A"
    show "\<exists>R. $ S' A = $ R A \<and> 
      bound_typ_inst S ($ S' A ! u) = $ R (bound_typ_inst (\<lambda>b. TVar (b + n)) (A ! u))"
    proof (intro exI conjI)
      show "$ S' A = $ (\<lambda>x. if x < n then S' x else S (x - n)) A"
        using Var.prems(2) new_if_subst_type_scheme_list by force
      show "bound_typ_inst S ($ S' A ! u) = $ (\<lambda>x. if x < n then S' x else S (x - n)) (bound_typ_inst (\<lambda>b. TVar (b + n)) (A ! u))"
        using A 
        by (simp add: new_if_subst_type_scheme  new_tv_nth_nat_A o_def nth_subst
                 flip: bound_typ_inst_composed_subst)
    qed
  qed
next
  case (Abs e S' A t' n) 
  then obtain t1 t2 where "t' = t1 -> t2" "mk_scheme t1 # $ S' A \<turnstile> e :: t2"
    by (auto simp: has_type_simps)
  with Abs.prems Abs.IH[of "\<lambda>x. if x=n then t1 else (S' x)" "(FVar n) #A" t2 "Suc n"]
  show ?case
    by (force dest!: mk_scheme_injective)
next
  case (App e1 e2) 
  then obtain t2 where e2t: "$ S' A \<turnstile> e2 :: t2"  and e1t: "$ S' A \<turnstile> e1 :: t2 -> t'"
    by (auto simp: has_type_simps)
  then obtain S t m R 
    where e1: "W e1 A n = Some (S, t, m)" and R: "$ S' A = $ R ($ S A)" "t2 -> t' = $ R t"
    using App by blast
  with App.prems have new_tv_m: "new_tv m ($ S A)"
    by (metis new_tv_W new_tv_compatible_W new_tv_subst_scheme_list)
  with App R
  obtain Sa ta ma Ra where We2: "W e2 ($ S A) m = Some (Sa, ta, ma)"
           and RSA: "$ R ($ S A) = $ Ra ($ Sa ($ S A))" 
           and t2eq: "t2 = $ Ra ta"
    by (metis e2t)
  define F where "F \<equiv> (\<lambda>x. if x = ma then t'
                            else if x \<in> free_tv t - free_tv Sa then R x
                            else Ra x)"
  have "ma \<notin> free_tv t"
    by (metis App.prems(2) W_var_geD We2 e1 new_tv_W new_tv_le
        new_tv_not_free_tv)
  have "$ F (Sa na) = R na" if "na \<in> free_tv t" for na
  proof -
    have "na \<noteq> ma"
      using \<open>ma \<notin> free_tv t\<close> that by auto
    show ?thesis
    proof (cases "na \<in> free_tv Sa")
      case True
      then have "R na = $ Ra (Sa na)"
        by (metis (lifting) App.prems(2) RSA We2 e1 eq_subst_scheme_list_eq_free free_tv_W
            free_tv_le_new_tv new_tv_W subst_comp_scheme_list that)
      then show ?thesis
        by (metis F_def True We2 new_tv_m codD cod_app_subst eq_free_eq_subst_te
            new_tv_W new_tv_not_free_tv weaken_not_elem_A_minus_B)
    next
      case False
      then show ?thesis
        using not_free_impl_id [OF False] \<open>na \<noteq> ma\<close> that
        by (simp add: F_def)
    qed
  qed
  then have *: "$ F ($ Sa t) = $ Ra ta -> t'"
    using eq_free_eq_subst_te subst_comp_te using R t2eq by fastforce
  moreover have "Ra na = F na"
    if "na \<in> free_tv ta" for na
  proof -
    have "na \<noteq> ma"
      using We2 new_tv_W new_tv_m new_tv_not_free_tv that by blast
    show ?thesis
    proof (cases "na \<in> free_tv t - free_tv Sa")
      case True
      then have "$ R ($ S A) = $ (\<lambda>x. $ Ra (Sa x)) ($ S A)"
        by (metis RSA subst_comp_scheme_list)
      then have "Ra na = R na"
        by (metis that App.prems(2) DiffE True Type.app_subst_TVar We2 free_tv_W e1 
            eq_subst_scheme_list_eq_free free_tv_le_new_tv new_tv_W not_free_impl_id)
      with \<open>na \<noteq> ma\<close> True show ?thesis
        by (simp add: F_def)
    next
      case False
      then show ?thesis
        using F_def \<open>na \<noteq> ma\<close> by presburger
    qed
  qed
  ultimately have "$ F ($ Sa t) = $ F (ta -> (TVar ma))"
    by (metis eq_free_eq_subst_te F_def Type.app_subst_Fun Type.app_subst_TVar)
  with mgu_Some obtain Sx Rb where Sx: "mgu ($ Sa t) (ta -> TVar ma) = Some Sx" 
    and Rb: "F = $ Rb \<circ> Sx"
    using mgu_mg by blast
  have t': "t' = $ Rb (Sx ma)"
    by (metis F_def Rb comp_def)
  have "$ Ra ($ Sa ($ S A)) = $ (\<lambda>x. $ Rb (Sx x)) ($ Sa ($ S A))"
  proof (intro eq_free_eq_subst_scheme_list)
    fix na :: nat
    assume na: "na \<in> free_tv ($ Sa ($ S A))"
    then have "ma \<noteq> na"
      by (metis We2 new_tv_W new_tv_compatible_W new_tv_m new_tv_not_free_tv
          new_tv_subst_scheme_list)
    show "Ra na = $ Rb (Sx na)"
    proof (cases "na \<in> free_tv t - free_tv Sa")
      case True
      then have "na \<in> cod Sa \<union> free_tv ($ S A)"
        using free_tv_app_subst_scheme_list na by blast
      with \<open>ma \<noteq> na\<close> Rb show ?thesis
        by (smt (verit, ccfv_SIG) DiffD2 F_def RSA Rb Type.app_subst_TVar Un_iff codD
            comp_apply eq_subst_scheme_list_eq_free not_free_impl_id subst_comp_scheme_list)
    next
      case False
      then show ?thesis
        by (metis F_def Rb \<open>ma \<noteq> na\<close> comp_apply)
    qed
  qed
  then have "$ S' A = $ Rb ($ ($ Sx \<circ> $ Sa \<circ> S) A)"
    by (metis (no_types, lifting) ext R(1) RSA comp_apply fun.map_comp
        subst_comp_scheme_list)
  with We2 Sx show ?case
    by (auto simp add: e1 t')
next
  case (LET e1 e2) 
  then obtain t1 where t1: "$ S' A \<turnstile> e1 :: t1" "gen ($ S' A) t1 # $ S' A \<turnstile> e2 :: t'"
    by (auto simp: has_type_simps)
  then obtain S t m R where e1: "W e1 A n = Some (S, t, m)" "$ S' A = $ R ($ S A)"
      and "gen ($ R ($ S A)) ($ R t) # $ R ($ S A) \<turnstile> e2 :: t'"
    using LET by metis
  then have "$ R (gen ($ S A) t) # $ R ($ S A) \<turnstile> e2 :: t'"
    using gen_bound_typ_instance has_type_le_env le_env_Cons le_env_refl
    by presburger
  moreover
  have "new_tv m (gen ($ S A) t) \<and> new_tv m ($ S A)"
    using LET.prems e1
    by (metis new_tv_W new_tv_compatible_W new_tv_compatible_gen new_tv_subst_scheme_list)
  ultimately show ?case
    using LET.IH(2)[of R "gen ($ S A) t # $ S A" t' m] e1 subst_comp_scheme_list
    by auto
qed

theorem W_complete: 
  "[] \<turnstile> e :: t' \<Longrightarrow> \<exists>S t m. W e [] n = Some(S,t,m) \<and> (\<exists>R. t' = $ R t)"
  by (metis W_complete_lemma app_subst_Nil new_tv_Nil)

end
