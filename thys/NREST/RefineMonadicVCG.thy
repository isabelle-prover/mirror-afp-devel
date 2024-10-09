theory RefineMonadicVCG
  imports "NREST" "DataRefinement"
    "Case_Labeling.Case_Labeling"
begin

\<comment> \<open>Might look similar to \<open>repeat_new\<close> from \<open>HOL-Eisbach.Eisbach\<close>, however the placement of the \<open>?\<close>
  is different, in particular that means this method is allowed to failed\<close>
method repeat_all_new methods m = (m;repeat_all_new \<open>m\<close>)?

lemma R_intro: "A \<le>  \<Down>Id B \<Longrightarrow> A \<le> B" by simp

subsection "ASSERT"

lemma le_R_ASSERTI: "(\<Phi> \<Longrightarrow> M \<le> \<Down> R M') \<Longrightarrow>  M \<le> \<Down> R (ASSERT \<Phi> \<bind> (\<lambda>_. M'))"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma T_ASSERT[vcg_simp_rules]: "Some t \<le> lst (ASSERT \<Phi>) Q \<longleftrightarrow> Some t \<le> Q () \<and> \<Phi>"
  by (cases \<Phi>) vcg'

lemma T_ASSERT_I: "(\<Phi> \<Longrightarrow> Some t \<le> Q ()) \<Longrightarrow> \<Phi> \<Longrightarrow> Some t \<le> lst (ASSERT \<Phi>) Q"
  by (simp add: T_ASSERT T_RETURNT) 


lemma T_RESTemb_iff: "Some t'
       \<le> lst (REST (emb' P t)) Q \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Some (t' + t x) \<le> Q x ) "
  by (auto simp: emb'_def T_pw mii_alt aux1)  


lemma T_RESTemb: "(\<And>x. P x \<Longrightarrow> Some (t' + t x) \<le> Q x)
    \<Longrightarrow> Some t' \<le> lst (REST (emb' P t)) Q"
  by (auto simp: T_RESTemb_iff)

lemma  T_SPEC: "(\<And>x. P x \<Longrightarrow> Some (t' + t x) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> lst (SPEC P t) Q"
  unfolding SPEC_REST_emb'_conv
  by (auto simp: T_RESTemb_iff)

lemma T_SPECT_I: "(Some (t' + t ) \<le> Q x)
    \<Longrightarrow>  Some t' \<le> lst (SPECT [ x \<mapsto> t]) Q"
  by(auto simp:   T_pw mii_alt aux1)   

lemma mm2_map_option: 
  assumes "Some (t'+t) \<le> mm2 (Q x) (x2 x)"
  shows "Some t' \<le> mm2 (Q x) (map_option ((+) t) (x2 x))"
proof(cases "Q x")
  case None
  from assms None show ?thesis 
    by (auto simp: mm2_def split: option.splits if_splits) 
next                        
  case (Some a)
  have arith: "\<not> a < b \<Longrightarrow> t' + t \<le> a - b \<Longrightarrow> a < t + b \<Longrightarrow> False" for b
    by (cases a; cases b; cases t'; cases t) auto
  moreover have arith': "\<not> a < b \<Longrightarrow> t' + t \<le> a - b \<Longrightarrow> \<not> a < t + b \<Longrightarrow> t' \<le> a - (t + b)" for b
    by (cases a; cases b; cases t'; cases t) auto
  ultimately show ?thesis 
    using Some assms by (auto simp: mm2_def split: option.splits if_splits) 
qed

lemma  T_consume: "(Some (t' + t) \<le> lst M Q)
    \<Longrightarrow>  Some t' \<le> lst (consume M t) Q"
  by (auto intro!: mm2_map_option simp: consume_def T_pw mii_alt miiFailt 
      split: nrest.splits option.splits if_splits)

definition "valid t Q M = (Some t \<le> lst M Q)"

subsection \<open>VCG splitter\<close>

ML \<open>
  structure VCG_Case_Splitter = struct
    fun dest_case ctxt t =
      case strip_comb t of
        (Const (case_comb, _), args) =>
          (case Ctr_Sugar.ctr_sugar_of_case ctxt case_comb of
             NONE => NONE
           | SOME {case_thms, ...} =>
               let
                 val lhs = Thm.prop_of (hd (case_thms))
                   |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst;
                 val arity = length (snd (strip_comb lhs));
                 (*val conv = funpow (length args - arity) Conv.fun_conv
                   (Conv.rewrs_conv (map mk_meta_eq case_thms));*)
               in
                 SOME (nth args (arity - 1), case_thms)
               end)
      | _ => NONE;
    
    fun rewrite_with_asm_tac ctxt k =
      Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
        Local_Defs.unfold0_tac ctxt' [nth prems k]) ctxt;
    
    fun split_term_tac ctxt case_term = (
      case dest_case ctxt case_term of
        NONE => no_tac
      | SOME (arg,case_thms) => let 
            val stac = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps case_thms) 
          in 
          (*CHANGED o stac
          ORELSE'*)
          (
            Induct.cases_tac ctxt false [[SOME arg]] NONE []
            THEN_ALL_NEW stac
          ) 
        end 1
    
    
    )

    fun split_tac ctxt = Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} => ALLGOALS (
        SUBGOAL (fn (t, _) => case Logic.strip_imp_concl t of
          @{mpat "Trueprop (Some _ \<le> lst ?prog _)"} => split_term_tac ctxt prog
        | @{mpat "Trueprop (progress ?prog)"} => split_term_tac ctxt prog
        | @{mpat "Trueprop (Case_Labeling.CTXT _ _ _ (valid _ _ ?prog))"} => split_term_tac ctxt prog
        | _ => no_tac
        ))
      ) ctxt 
      THEN_ALL_NEW TRY o Hypsubst.hyp_subst_tac ctxt

  end
\<close>

method_setup vcg_split_case = 
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (CHANGED o (VCG_Case_Splitter.split_tac ctxt)))\<close>

subsection \<open>mm3 and emb\<close>

lemma Some_eq_mm3_Some_conv[vcg_simp_rules]: "Some t = mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t = enat (t' - t''))"
  by (simp add: mm3_def)

lemma Some_eq_mm3_Some_conv': "mm3 t' (Some t'') = Some t \<longleftrightarrow> (t'' \<le> t' \<and> t = enat (t' - t''))"
  using Some_eq_mm3_Some_conv by metis


lemma Some_le_emb'_conv[vcg_simp_rules]: "Some t \<le> emb' Q ft x \<longleftrightarrow> Q x \<and> t \<le> ft x"
  by (auto simp: emb'_def)

lemma Some_eq_emb'_conv[vcg_simp_rules]: "emb' Q tf s = Some t \<longleftrightarrow> (Q s \<and> t = tf s)"
  unfolding emb'_def by(auto split: if_splits)

subsection \<open>Setup Labeled VCG\<close>

context
begin
  interpretation Labeling_Syntax .
  
  lemma LCondRule:
    fixes IC CT defines "CT' \<equiv> (''cond'', IC, []) # CT "
    assumes (* "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
      and *) "b \<Longrightarrow> C\<langle>Suc IC,(''the'', IC, []) # (''cond'', IC, []) # CT,OC1: valid t Q c1 \<rangle>"
      and "~b \<Longrightarrow> C\<langle>Suc OC1,(''els'', Suc OC1, []) # (''cond'', IC, []) # CT,OC: valid t Q c2 \<rangle>"
    shows "C\<langle>IC,CT,OC: valid t Q (if b then c1 else c2)\<rangle>"
    using assms(2-) unfolding LABEL_simps by (simp add: valid_def)

  lemma LouterCondRule:
    fixes IC CT defines "CT' \<equiv> (''cond2'', IC, []) # CT "
    assumes (* "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
      and *) "b \<Longrightarrow> C\<langle>Suc IC,(''the'', IC, []) # (''cond2'', IC, []) # CT,OC1: t \<le> A \<rangle>"
      and "~b \<Longrightarrow> C\<langle>Suc OC1,(''els'', Suc OC1, []) # (''cond2'', IC, []) # CT,OC: t \<le> B \<rangle>"
    shows "C\<langle>IC,CT,OC: t \<le> (if b then A else B)\<rangle>"
    using assms(2-) unfolding LABEL_simps by (simp add: valid_def)
(* NO NAME
lemma  "mm3 (E s) (if I s' then Some (E s') else None) = (if I s' \<and> (E s' \<le> E s) then Some (E s - E s') else None)"
  unfolding mm3_def by (cases "I s'") simp_all
*)
lemma While:
  assumes  "I s0"  "(\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> Some 0 \<le> lst (C s) (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)))"
     "(\<And>s. progress (C s))"
     "(\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow>   Some (t + enat ((E s0) - E x)) \<le> Q x)"
   shows   "Some t \<le> lst (whileIET I E b C s0) Q"
  apply(rule whileIET_rule'[THEN T_conseq4])
     subgoal using assms(2) by simp
    subgoal using assms(3) by simp
   subgoal using assms(1) by simp
  subgoal for x using assms(4) by (cases "I x") (auto simp: Some_eq_mm3_Some_conv' split: if_splits)    
  done

definition "monadic_WHILE b f s \<equiv> do {
  RECT (\<lambda>D s. do { 
    bv \<leftarrow> b s;
    if bv then do {
      s \<leftarrow> f s;
      D s
    } else do {RETURNT s}
  }) s
}"

lemma monadic_WHILE_mono: 
  assumes "\<And>x. bm x \<le> bm' x"
    and "\<And>x t. nofailT (bm' x) \<Longrightarrow> inresT (bm x) True t \<Longrightarrow> c x \<le> c' x"
  shows "(monadic_WHILE bm c x) \<le> (monadic_WHILE bm' c' x)"
  unfolding monadic_WHILE_def apply(rule RECT_mono)
   subgoal by (refine_mono)  
  using assms by (auto intro!: bindT_mono)

lemma z: "inresT A x t \<Longrightarrow> A \<le> B \<Longrightarrow> inresT B x t"
  by (meson fail_inresT pw_le_iff)

lemma monadic_WHILE_mono': 
  assumes 
    "\<And>x. bm x \<le> bm' x"
    and "\<And>x t. nofailT (bm' x) \<Longrightarrow> inresT (bm' x) True t \<Longrightarrow> c x \<le> c' x"
  shows " (monadic_WHILE bm c x) \<le> (monadic_WHILE bm' c' x)"
  unfolding monadic_WHILE_def apply(rule RECT_mono)
  subgoal by(refine_mono)  
  apply(rule bindT_mono)
   apply fact
  using assms by (auto intro!: bindT_mono dest: z[OF _ assms(1)])

lemma monadic_WHILE_refine: 
  assumes 
    "(x, x') \<in> R"
    "\<And>x x'. (x, x') \<in> R \<Longrightarrow> bm x \<le> \<Down>Id (bm' x')"
    and "\<And>x x' t. (x, x') \<in> R \<Longrightarrow> nofailT (bm' x') \<Longrightarrow> inresT (bm' x') True t \<Longrightarrow> c x \<le> \<Down>R (c' x')"
  shows "(monadic_WHILE bm c x) \<le> \<Down>R (monadic_WHILE bm' c' x')"
  unfolding monadic_WHILE_def apply(rule RECT_refine[OF _ assms(1)])
  subgoal by(refine_mono)
  apply(rule bindT_refine'[OF assms(2)])
   subgoal by auto
  by (auto intro!: assms(3) bindT_refine RETURNT_refine)

lemma monadic_WHILE_aux: "monadic_WHILE b f s = monadic_WHILEIT (\<lambda>_. True) b f s"
  unfolding monadic_WHILEIT_def monadic_WHILE_def 
  by simp

\<comment> \<open>No proof\<close>
lemma "lst (c x) Q = Some t \<Longrightarrow> Some t \<le> lst (c x) Q'"
  apply(rule T_conseq6) oops

lemma TbindT_I2: "tt \<le>  lst M (\<lambda>y. lst (f y) Q) \<Longrightarrow>  tt \<le> lst (M \<bind> f) Q"
  by (simp add: T_bindT)

lemma T_conseq7:
  assumes 
    "lst f Q' \<ge> tt"
    "\<And>x t'' M. f = SPECT M \<Longrightarrow> M x \<noteq> None \<Longrightarrow> Q' x = Some t'' \<Longrightarrow> (Q x) \<ge> Some ( t'')" 
  shows "lst f Q \<ge> tt"
  using assms by (cases tt) (auto intro: T_conseq6)

lemma monadic_WHILE_ruleaaa'':
  assumes "monadic_WHILE bm c s = r"
  assumes IS[vcg_rules]: "\<And>s.  
   lst (bm s) (\<lambda>b. if b then lst (c s) (\<lambda>s'. if (s',s)\<in>R then I s' else None) else Q s) \<ge> I s"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *)
  assumes wf: "wf R"
  shows "lst r Q \<ge> I s"
  using assms(1)
  unfolding monadic_WHILE_def
proof (induction rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r ) 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   
  from step.prems
  show ?case 
    apply simp  
    apply (rule TbindT_I2)
    apply(rule T_conseq7)
     apply (rule IS) 
    apply simp    
    apply safe
     subgoal
       apply (rule TbindT_I)
       apply(rule T_conseq6[where Q'="(\<lambda>s'. if (s', x) \<in> R then I s' else None)"])
        subgoal by simp 
        by (auto split: if_splits dest: IH)
    subgoal by(simp add: T_RETURNT)
    done
qed

lemma monadic_WHILE_rule'':
  assumes "monadic_WHILE bm c s = r"
 assumes IS[vcg_rules]: "\<And>s t'. I s = Some t' 
           \<Longrightarrow>  lst (bm s) (\<lambda>b. if b then lst (c s)  (\<lambda>s'. if (s',s)\<in>R then I s' else None)else Q s) \<ge> Some t'"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *)
  assumes "I s = Some t"
  assumes wf: "wf R"
  shows "lst r Q \<ge> Some t"
  using assms(1,3)
  unfolding monadic_WHILE_def
proof (induction arbitrary: t rule: RECT_wf_induct[where R="R"])
  case 1  
  show ?case by fact
next
  case 2
  then show ?case by refine_mono
next
  case step: (3 x D r t') 
  note IH[vcg_rules] = step.IH[OF _ refl] 
  note step.hyps[symmetric, simp]   

  from step.prems
  show ?case 
    apply simp
    apply (rule TbindT_I)
    apply(rule T_conseq6)
     apply (rule IS) apply simp
    apply simp
    apply safe
    subgoal
      apply (rule TbindT_I)
      apply(rule T_conseq6[where Q'="(\<lambda>s'. if (s', x) \<in> R then I s' else None)"])
       subgoal by simp 
      by (auto split: if_splits intro: IH)
    subgoal by vcg'
    done
qed

lemma whileT_rule''':
  fixes I :: "'a \<Rightarrow> nat option"
  assumes "whileT b c s0 = r"
  assumes progress: "\<And>s. progress (c s)" 
  assumes IS[vcg_rules]: "\<And>s t t'. I s = Some t \<Longrightarrow>  b s  \<Longrightarrow> 
           lst (c s) (\<lambda>s'. mm3 t (I s') ) \<ge> Some 0"
    (*  "T (\<lambda>x. T I (c x)) (SPECT (\<lambda>x. if b x then I x else None)) \<ge> Some 0" *) 
  assumes [simp]: "I s0 = Some t0" 
    (*  assumes wf: "wf R" *)                         
  shows "lst r (\<lambda>x. if b x then None else mm3 t0 (I x)) \<ge> Some 0"  
  apply(rule T_conseq4)
   apply(rule whileT_rule''[where I="\<lambda>s. mm3 t0 (I s)"
        and R="measure (the_enat o the o I)", OF assms(1)])
      subgoal for s t'
        apply(cases "I s"; simp)
        subgoal for ti
          using IS[of s ti]  
          apply (cases "c s") apply(simp) 
          subgoal for M
            using progress[of s, THEN progressD, of M]
            \<comment> \<open>TODO: Cleanup\<close>          
            apply(auto simp: T_pw mm3_Some_conv mii_alt mm2_def mm3_def split: option.splits if_splits)
                apply fastforce 
            subgoal 
              by (metis enat_ord_simps(1) le_diff_iff le_less_trans option.distinct(1)) 
            subgoal 
              by (metis diff_is_0_eq' leI less_option_Some option.simps(3) zero_enat_def) 
            subgoal 
              by (smt Nat.add_diff_assoc enat_ile enat_ord_code(1) idiff_enat_enat leI le_add_diff_inverse2 nat_le_iff_add option.simps(3)) 
            subgoal 
              using dual_order.trans by blast 
          done
        done
      done
    by auto

fun Someplus where
  "Someplus None _ = None"
| "Someplus _ None = None"
| "Someplus (Some a) (Some b) = Some (a+b)"

lemma l: "~ (a::enat) < b \<longleftrightarrow> a \<ge> b" by auto

lemma kk: "a\<ge>b \<Longrightarrow> (b::enat) + (a -b) = a" 
  by (cases a; cases b) auto

lemma Tea: "Someplus A B = Some t \<longleftrightarrow> (\<exists>a b. A = Some a \<and> B = Some b \<and> t = a + b)"
  by (cases A; cases B) auto

lemma TTT_Some_nofailT: "lst c Q = Some l \<Longrightarrow> c \<noteq> FAILT"
  unfolding lst_def mii_alt by auto 

lemma GRR: assumes "lst (SPECT Mf) Q = Some l"
  shows "Mf x = None \<or> (Q x\<noteq> None \<and> (Q x) \<ge> Mf x) "
proof - 
  from assms have "None \<notin> {mii Q (SPECT Mf) x |x. True}" 
  unfolding lst_def    
  unfolding Inf_option_def by (auto split: if_splits)   
  then have "None \<noteq> (case Mf x of None \<Rightarrow> Some \<infinity> 
    | Some mt \<Rightarrow> case Q x of None \<Rightarrow> None 
      | Some rt \<Rightarrow> if rt < mt then None else Some (rt - mt))"
  unfolding mii_alt mm2_def
  by (auto)
  then show ?thesis by (auto split: option.splits if_splits)
qed

lemma Someplus_None: "Someplus A B = None \<longleftrightarrow> (A = None \<or> B = None)" 
  by (cases A; cases B) auto

lemma Somemm3: "A \<ge> B \<Longrightarrow> mm3 A (Some B) = Some (A - B)" 
  unfolding mm3_def by auto

lemma neueWhile_rule: assumes "monadic_WHILE bm c s0 = r"
  and step: "\<And>s. I s  \<Longrightarrow>
    Some 0 \<le> lst  (bm s) (\<lambda>b. if b
                   then lst (c s) (\<lambda>s'. (if I s' \<and> (E s' \<le> E s) then Some (enat (E s - E s')) else None))
                   else mm2 (Q s) (Someplus (Some t) (mm3 (E s0) (Some (E s))))  )
      "
  and progress: "\<And>s. progress (c s)"
 (* "mm3 (E s0) (if I s0 then Some (E s0) else None) = Some t" *)
 and I0: "I s0" 
shows "Some t \<le> lst r Q"
proof -
  \<comment> \<open>TODO: Cleanup, will be work\<close>
  show "Some t \<le> lst r Q"
    apply (rule monadic_WHILE_rule''[where I="\<lambda>s. Someplus (Some t) (mm3 (E s0) ((\<lambda>e. if I e
                then Some (E e) else None) s))"  and R="measure (the_enat o the o (\<lambda>e. if I e
                then Some (E e) else None))", simplified])
      apply fact
    subgoal for s t'
      apply(auto split: if_splits)
      apply(rule T_conseq4)
       apply(rule step)
       apply simp 
      apply auto
    proof (goal_cases)
      case (1 b t'')
      from 1(3) TTT_Some_nofailT obtain M where cs: "c s = SPECT M" by force
      { assume A: "\<And>x. M x = None"
        with A have "?case" unfolding cs lst_def mii_alt by simp
      }
      moreover 
      { assume "\<exists>x. M x \<noteq> None"
        then obtain x where i: "M x \<noteq> None" by blast

        let ?T = "lst (c s) (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (enat (E s - E s')) else None)"

        from GRR[OF 1(3)[unfolded cs], where x=x] 
         i have "(if I x \<and> E x \<le> E s then Some (enat (E s - E x)) else None) \<noteq> None \<and> M x \<le> (if I x \<and> E x \<le> E s then Some (enat (E s - E x)) else None)"
          by simp
        then have pf: " I x" "E x \<le> E s" "M x \<le>   Some (enat (E s - E x))  " by (auto split: if_splits)


        then have "M x < Some \<infinity>"  
          using enat_ord_code(4) le_less_trans less_option_Some by blast

        have "Some t'' = ?T" using 1(3) by simp
        also have oo: "?T  \<le>  mm2 (Some (enat (E s - E x))) (M x)"
          unfolding lst_def apply(rule Inf_lower) apply (simp add: mii_alt cs) apply(rule exI[where x=x])
          using pf by simp
  
        also from i have o: "\<dots> < Some \<infinity>"  unfolding mm2_def 
          apply auto  
          using fl by blast
        finally  have tni: "t'' < \<infinity>" by auto
        then have tt: "t' + t'' - t'' = t'" apply(cases t''; cases t') by auto  
  
      have ka: "\<And>x. mii (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (enat (E s - E s')) else None) (c s) x \<ge> Some t''" unfolding lst_def 
        using "1"(3) T_pw by fastforce

      { fix x assume nN: "M x \<noteq> None"
        with progress[of s, unfolded cs progress_def] have strict: "Some 0 < M x" by auto
        from ka[of x] nN  have "E x  < E s" unfolding mii_alt cs progress_def mm2_def
          using strict less_le zero_enat_def by (fastforce simp: l split: if_splits)
      } note strict = this
      have ?case 
  \<comment> \<open>TODO: Cleanup\<close>
        apply(rule T_conseq5[where Q'="(\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (enat (E s - E s')) else None)"])
        using 1(3) apply(auto) [] using 1(2)
        apply (auto simp add: tt  Tea split: if_splits)
        subgoal apply(auto simp add: Some_eq_mm3_Some_conv')
          apply(rule strict) using cs by simp 
        subgoal by(simp add: Some_eq_mm3_Some_conv' Somemm3) 
        done
    }
    ultimately show ?case by blast
    next
      case (2 x t'')
      then show ?case unfolding mm3_def mm2_def by (auto simp add: l kk split: if_splits option.splits)
    qed
    subgoal
      using I0 by simp
    done
qed

definition monadic_WHILEIE  where
  "monadic_WHILEIE I E bm c s = monadic_WHILE bm c s" 

definition "G b d = (if b then Some d else None)"
definition "H Qs t Es0 Es = mm2 Qs (Someplus (Some t) (mm3 (Es0) (Some (Es))))"

lemma neueWhile_rule':
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> nat"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> lst (bm s)  (\<lambda>b. if b then lst (c s) (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (enat (E s - E s')) else None)  else mm2 (Q s) (Someplus (Some t) (mm3 (E s0) (Some (E s))))))"
 and  progress: "\<And>s. progress (c s)"
 and  i: "I s0"
shows "Some t \<le> lst (monadic_WHILEIE I E bm c s0) Q"
  unfolding monadic_WHILEIE_def 
  apply(rule neueWhile_rule[OF refl]) by fact+

lemma neueWhile_rule'':
  fixes s0 :: 'a and I :: "'a \<Rightarrow> bool" and E :: "'a \<Rightarrow> nat"
  assumes
  step: "(\<And>s. I s \<Longrightarrow> Some 0 \<le> lst (bm s) (\<lambda>b. if b then lst (c s) (\<lambda>s'. G (I s' \<and> E s' \<le> E s) (enat (E s - E s'))) else H (Q s) t (E s0) (E s)))"
 and  progress: "\<And>s. progress (c s)"
 and  i: "I s0"
shows "Some t \<le> lst (monadic_WHILEIE I E bm c s0) Q"
  unfolding monadic_WHILEIE_def apply(rule neueWhile_rule[OF refl, where I=I and E=E ])
     using assms unfolding G_def H_def by auto

lemma LmonWhileRule:
  fixes IC CT  
  assumes "V\<langle>(''precondition'', IC, []),(''monwhile'', IC, []) # CT: I s0\<rangle>"
    and "\<And>s. I s \<Longrightarrow>  C\<langle>Suc IC,(''invariant'', Suc IC, []) # (''monwhile'', IC, []) # CT,OC: valid 0 (\<lambda>b. if b then lst (C s) (\<lambda>s'. if I s' \<and> E s' \<le> E s then Some (enat (E s - E s')) else None) else mm2 (Q s) (Someplus (Some t) (mm3 (E s0) (Some (E s))))) (bm s)\<rangle>"
    and "\<And>s. V\<langle>(''progress'', IC, []),(''monwhile'', IC, []) # CT: progress (C s)\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (monadic_WHILEIE I E bm C s0)\<rangle>"  
  using assms(2,3,1) unfolding valid_def LABEL_simps  
  by (rule neueWhile_rule')

lemma LWhileRule:
  fixes IC CT  
  assumes "V\<langle>(''precondition'', IC, []),(''while'', IC, []) # CT: I s0\<rangle>"
    and "\<And>s. I s \<Longrightarrow>  b s \<Longrightarrow>  C\<langle>Suc IC,(''invariant'', Suc IC, []) # (''while'', IC, []) # CT,OC1: valid 0 (\<lambda>s'. mm3 (E s) (if I s' then Some (E s') else None)) (C s)\<rangle>"
    and "\<And>s. V\<langle>(''progress'', IC, []),(''while'', IC, []) # CT: progress (C s)\<rangle>"
    and "\<And>x. \<not> b x \<Longrightarrow>  I x \<Longrightarrow>  (E x) \<le> (E s0) \<Longrightarrow> C\<langle>Suc OC1,(''postcondition'', IC, [])#(''while'', IC, []) # CT,OC: Some (t + enat ((E s0) - E x)) \<le> Q x\<rangle>" 
  shows "C\<langle>IC,CT,OC: valid t Q (whileIET I E b C s0)\<rangle>"
  using assms unfolding valid_def LABEL_simps
  by (rule While)
    
lemma validD: "valid t Q M \<Longrightarrow> Some t \<le> lst M Q" by(simp add: valid_def)

lemma LABELs_to_concl:
  "C\<langle>IC, CT, OC: True\<rangle> \<Longrightarrow> C\<langle>IC, CT, OC: P\<rangle> \<Longrightarrow> P"
  "V\<langle>x, ct: True\<rangle> \<Longrightarrow> V\<langle>x, ct: P\<rangle> \<Longrightarrow> P"
  unfolding LABEL_simps .

lemma LASSERTRule:
  assumes "V\<langle>(''ASSERT'', IC, []),CT: \<Phi>\<rangle>"
    "C\<langle>Suc IC, CT,OC: valid t Q (RETURNT ())\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (ASSERT \<Phi>)\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def )   

lemma LbindTRule:
  assumes "C\<langle>IC,CT,OC: valid t (\<lambda>y. lst (f y) Q) m\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (bindT m f)\<rangle>"
  using assms unfolding LABEL_simps by(simp add: T_bindT valid_def )

lemma LRETURNTRule:
  assumes "C\<langle>IC,CT,OC: Some t \<le> Q x\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (RETURNT x)\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def T_RETURNT)  

lemma LSELECTRule:
  fixes IC CT defines "CT' \<equiv> (''cond'', IC, []) # CT "
  assumes (* "V\<langle>(''vc'', IC, []),(''cond'', IC, []) # CT: p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}\<rangle>"
    and *) "\<And>x. P x \<Longrightarrow> C\<langle>Suc IC,(''Some'', IC, []) # (''SELECT'', IC, []) # CT,OC1: valid (t+T) Q (RETURNT (Some x)) \<rangle>"
    and "\<forall>x. \<not> P x \<Longrightarrow> C\<langle>Suc OC1,(''None'', Suc OC1, []) # (''SELECT'', IC, []) # CT,OC: valid (t+T) Q (RETURNT None) \<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (SELECT P T)\<rangle>"
  using assms(2-) unfolding LABEL_simps by(auto intro: T_SELECT T_SPECT_I simp add: valid_def T_RETURNT) 

lemma LRESTembRule:
  assumes "\<And>x. P x \<Longrightarrow> C\<langle>IC,CT,OC: Some (t + T x) \<le> Q x\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (REST (emb' P T))\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def T_RESTemb) 

lemma LRESTsingleRule:
  assumes "C\<langle>IC,CT,OC: Some (t + t') \<le> Q x\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q (REST [x\<mapsto>t'])\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def T_pw mii_alt aux1)

lemma LTTTinRule:
  assumes "C\<langle>IC,CT,OC: valid t Q M\<rangle>"
  shows "C\<langle>IC,CT,OC: Some t \<le> lst M Q\<rangle>"
  using assms unfolding LABEL_simps by(simp add: valid_def)

lemma LfinaltimeRule:
  assumes "V\<langle>(''time'', IC, []), CT: t \<le> t' \<rangle>" 
  shows "C\<langle>IC,CT,IC: Some t \<le> Some t'\<rangle>"
  using assms unfolding LABEL_simps by simp

lemma LfinalfuncRule:
  assumes "V\<langle>(''func'', IC, []), CT: False \<rangle>"
  shows "C\<langle>IC,CT,IC: Some t \<le> None\<rangle>"
  using assms unfolding LABEL_simps by simp

lemma LembRule:
  assumes "V\<langle>(''time'', IC, []), CT: t \<le> T x \<rangle>"
    and "V\<langle>(''func'', IC, []), CT: P x \<rangle>"
  shows "C\<langle>IC,CT,IC: Some t \<le> emb' P T x\<rangle>"
  using assms unfolding LABEL_simps by (simp add: emb'_def)  

lemma Lmm3Rule:
  assumes "V\<langle>(''time'', IC, []), CT: Va' \<le> Va \<and> t \<le> enat (Va - Va') \<rangle>"
    and "V\<langle>(''func'', IC, []), CT: b \<rangle>"
  shows "C\<langle>IC,CT,IC: Some t \<le> mm3 Va (if b then Some Va' else None) \<rangle>"
  using assms unfolding LABEL_simps by (simp add: mm3_def)    


lemma LinjectRule:
  assumes "Some t \<le> lst A Q \<Longrightarrow> Some t \<le> lst B Q"
      "C\<langle>IC,CT,OC: valid t Q A\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q B\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def)

lemma Linject2Rule:
  assumes "A = B"
      "C\<langle>IC,CT,OC: valid t Q A\<rangle>"
  shows "C\<langle>IC,CT,OC: valid t Q B\<rangle>"
  using assms unfolding LABEL_simps by (simp add: valid_def)


method labeled_VCG_init = ((rule T_specifies_I validD)+), rule Initial_Label
method labeled_VCG_step uses rules = (rule rules[symmetric, THEN Linject2Rule] 
        LTTTinRule LbindTRule 
        LembRule Lmm3Rule
        LRETURNTRule LASSERTRule LCondRule LSELECTRule
        LRESTsingleRule LRESTembRule
        LouterCondRule
        LfinaltimeRule LfinalfuncRule
        LmonWhileRule LWhileRule) | vcg_split_case
 
method labeled_VCG uses rules = labeled_VCG_init, repeat_all_new \<open>labeled_VCG_step rules: rules\<close>
method casified_VCG uses rules = labeled_VCG rules: rules, casify


subsection \<open>Examples, labeled vcg\<close>
\<comment> \<open>Only examples, so not named\<close>
\<comment> \<open>No proof\<close>
lemma "do { x \<leftarrow> SELECT P T;
            (case x of None \<Rightarrow> RETURNT (1::nat) | Some t \<Rightarrow> RETURNT (2::nat))
        } \<le> SPECT (emb Q T')"
  apply labeled_VCG   oops


lemma 
  assumes "b" "c"
  shows "do { ASSERT b;
            ASSERT c;
            RETURNT 1 } \<le> SPECT (emb (\<lambda>x. x>(0::nat)) 1)"
proof (labeled_VCG, casify)
  case ASSERT then show ?case by fact
  case ASSERTa then show ?case by fact
  case func then show ?case by simp
  case time then show ?case by simp 
qed

lemma "do {      
      (if b then RETURNT (1::nat) else RETURNT 2)
    } \<le> SPECT (emb (\<lambda>x. x>0) 1)"
proof (labeled_VCG, casify)
  case cond {
    case the {
      case time 
      then show ?case by simp  
    next
      case func 
      then show ?case by simp   
    }
  next
    case els { (*
      case time 
      then show ?case by simp  
    next *)
      case func 
      then show ?case by simp   
    }
  }
qed simp


lemma 
  assumes "b"
  shows "do {
      ASSERT b;
      (if b then RETURNT (1::nat) else RETURNT 2)
    } \<le> SPECT (emb (\<lambda>x. x>0) 1)"
proof (labeled_VCG, casify)
  case ASSERT then show ?case by fact 
  case cond {
    case the {
      case time 
      then show ?case by simp  
    next
      case func 
      then show ?case by simp   
    }
  next
    case els { (*
    case time 
    then show ?case by simp  
  next *)
      case func 
      then show ?case by simp   
    }
  }
qed simp

end


(* TODO: move *)

lemma SPECT_ub': "T\<le>T' \<Longrightarrow> SPECT (emb' M' T) \<le> \<Down>Id (SPECT (emb' M' T'))"
  unfolding emb'_def by (auto simp: pw_le_iff le_funD order_trans refine_pw_simps)

lemma REST_single_rule[vcg_simp_rules]: "Some t \<le> lst (REST [x\<mapsto>t']) Q \<longleftrightarrow> Some (t+t') \<le> (Q x)"
  by (simp add: T_REST aux1)

subsection "progress solver"

method progress methods solver = 
  (rule asm_rl[of "progress _"], 
    (simp split: prod.splits | intro allI impI conjI | determ \<open>rule progress_rules\<close> 
      | rule disjI1; progress \<open>solver\<close>; fail | rule disjI2; progress \<open>solver\<close>; fail | solver)+) []
method progress' methods solver = 
  (rule asm_rl[of "progress _"], (vcg_split_case | intro allI impI conjI | determ \<open>rule progress_rules\<close> 
      | rule disjI1 disjI2; progress'\<open>solver\<close> | (solver;fail))+) []


lemma 
  assumes "(\<And>s t. P s = Some t \<Longrightarrow> \<exists>s'. Some t \<le> Q s' \<and> (s, s') \<in> R)"
  shows SPECT_refine: "SPECT P \<le> \<Down> R (SPECT Q)"
proof-
  have "P x \<le> \<Squnion> {Q a |a. (x, a) \<in> R}" for x
  proof(cases "P x")
    case [simp]: (Some y)
    from assms[of x, OF Some] obtain s' where s': "Some y \<le> Q s'" "(x, s') \<in> R"
      by blast+
    show ?thesis
      by (rule order.trans[where b="Q s'"]) (auto intro: s' Sup_upper)
  qed auto
  then show ?thesis
    by (auto simp add: conc_fun_def le_fun_def)
qed

subsection \<open>more stuff involving mm3 and emb\<close>

lemma Some_le_mm3_Some_conv[vcg_simp_rules]: "Some t \<le> mm3 t' (Some t'') \<longleftrightarrow> (t'' \<le> t' \<and> t \<le> enat (t' - t''))"
  by (simp add: mm3_def)

lemma embtimeI: "T \<le> T' \<Longrightarrow> emb P T \<le> emb P T'" unfolding emb'_def by (auto simp: le_fun_def split:  if_splits)

lemma not_cons_is_Nil_conv[simp]: "(\<forall>y ys. l \<noteq> y # ys) \<longleftrightarrow> l=[]" by (cases l) auto

lemma mm3_Some0_eq[simp]: "mm3 t (Some 0) = Some t"
  by (auto simp: mm3_def)

lemma ran_emb': "c \<in> ran (emb' Q t) \<longleftrightarrow> (\<exists>s'. Q s' \<and> t s' = c)"
  by(auto simp: emb'_def ran_def)

lemma ran_emb_conv: "Ex Q \<Longrightarrow>  ran (emb Q t) = {t}"
  by (auto simp: ran_emb')

lemma in_ran_emb_special_case: "c\<in>ran (emb Q t) \<Longrightarrow> c\<le>t"
  apply (cases "Ex Q")
   subgoal by (auto simp: ran_emb_conv)
  subgoal by (auto simp: emb'_def)
  done

lemma dom_emb'_eq[simp]: "dom (emb' Q f) = Collect Q"
  by(auto simp: emb'_def split: if_splits)

lemma emb_le_emb: "emb' P T \<le> emb' P' T' \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> P' x \<and>  T x \<le> T' x)"
  unfolding emb'_def by (auto simp: le_fun_def split: if_splits)

(* lemmas [vcg_rules] = T_RESTemb_iff[THEN iffD2] *)

subsection \<open>VCG for monadic programs\<close>

subsubsection \<open>old\<close>

declare mm3_Some_conv [vcg_simp_rules]

lemma SS[vcg_simp_rules]: "Some t = Some t' \<longleftrightarrow> t = t'" by simp
lemma SS': "(if b then Some t else None) = Some t' \<longleftrightarrow> (b \<and> t = t')" by simp 

term "(case s of (a,b) \<Rightarrow> M a b)"
lemma case_T[vcg_rules]: "(\<And>a b. s = (a, b) \<Longrightarrow> t \<le> lst Q (M a b)) \<Longrightarrow> t  \<le> lst Q (case s of (a,b) \<Rightarrow> M a b)"
  by (simp add: split_def)

subsubsection \<open>new setup\<close>

named_theorems vcg_rules' 
lemma if_T[vcg_rules']: "(b \<Longrightarrow> t \<le> lst Ma Q) \<Longrightarrow> (\<not>b \<Longrightarrow> t \<le> lst Mb Q) \<Longrightarrow> t  \<le> lst (if b then Ma else Mb) Q"
   by (simp add: split_def)
lemma RETURNT_T_I[vcg_rules']: "t \<le> Q x \<Longrightarrow> t  \<le> lst (RETURNT x) Q"
   by (simp add: T_RETURNT)
   
declare T_SPECT_I [vcg_rules']
declare TbindT_I  [vcg_rules']
declare T_RESTemb [vcg_rules']
declare T_ASSERT_I [vcg_rules']
declare While[ vcg_rules']

named_theorems vcg_simps'

declare option.case [vcg_simps']

declare neueWhile_rule'' [vcg_rules']

method vcg'_step methods solver uses rules = 
  (intro rules vcg_rules' | vcg_split_case | (progress simp;fail) | (solver; fail))

method vcg' methods solver uses rules = repeat_all_new \<open>vcg'_step solver rules: rules\<close>

declare T_SELECT [vcg_rules']

\<comment> \<open>No proof\<close>
lemma "\<And>c. do {  c \<leftarrow> RETURNT None;
            (case_option (RETURNT (1::nat)) (\<lambda>p. RETURNT (2::nat))) c 
      } \<le> SPECT (emb (\<lambda>x. x>(0::nat)) 1)"
  apply(rule T_specifies_I)
  apply(vcg'\<open>-\<close>)  unfolding  option.case 
  oops

thm option.case

subsection \<open>setup for \<open>refine_vcg\<close>\<close>

lemma If_refine[refine]: "b = b' \<Longrightarrow>
  (b \<Longrightarrow> b' \<Longrightarrow> S1 \<le> \<Down> R S1') \<Longrightarrow>
  (\<not> b \<Longrightarrow> \<not> b' \<Longrightarrow> S2 \<le> \<Down> R S2') \<Longrightarrow> (if b then S1 else S2) \<le> \<Down> R (if b' then S1' else S2')"
  by auto

lemma Case_option_refine[refine]: "(x,x')\<in> \<langle>S\<rangle>option_rel \<Longrightarrow>
  (\<And>y y'. (y,y')\<in>S \<Longrightarrow> S2 y  \<le> \<Down> R (S2' y')) \<Longrightarrow> S1 \<le> \<Down> R S1'
  \<Longrightarrow> (case x of None \<Rightarrow> S1 | Some y \<Rightarrow> S2 y) \<le> \<Down> R (case x' of None \<Rightarrow> S1' | Some y' \<Rightarrow> S2' y')"
  by(auto split: option.split)

\<comment> \<open>Check names\<close>
lemma conc_fun_Id_refined[refine0]: "\<And>S. S \<le> \<Down> Id S" by simp                                          
lemma conc_fun_ASSERT_refine[refine0]: "\<Phi> \<Longrightarrow> (\<Phi> \<Longrightarrow> S \<le> \<Down> R S') \<Longrightarrow> ASSERT \<Phi> \<bind> (\<lambda>_. S) \<le> \<Down> R S'"
     by auto 
declare le_R_ASSERTI [refine0]

declare bindT_refine [refine]
declare WHILET_refine [refine]

\<comment> \<open>Check name\<close>
lemma SPECT_refine_vcg_cons[refine_vcg_cons]: "m \<le> SPECT \<Phi> \<Longrightarrow> (\<And>x. \<Phi> x \<le> \<Psi> x) \<Longrightarrow> m \<le> SPECT \<Psi>"
  by (metis dual_order.trans le_funI nres_order_simps(2))  

end