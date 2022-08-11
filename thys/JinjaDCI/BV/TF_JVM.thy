(*  Title:      JinjaDCI/BV/TF_JVM.thy

    Author:     Tobias Nipkow, Gerwin Klein, Susannah Mansky
    Copyright   2000 TUM, 2019-20 UIUC

    Based on the Jinja theory BV/TF_JVM.thy by Tobias Nipkow and Gerwin Klein
*)

section \<open> The Typing Framework for the JVM \label{sec:JVM} \<close>

theory TF_JVM
imports Jinja.Typing_Framework_err EffectMono BVSpec
begin

definition exec :: "jvm_prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ex_table \<Rightarrow> instr list \<Rightarrow> ty\<^sub>i' err step_type"
where 
  "exec G maxs rT et bs \<equiv>
  err_step (size bs) (\<lambda>pc. app (bs!pc) G maxs rT pc (size bs) et) 
                     (\<lambda>pc. eff (bs!pc) G pc et)"

locale JVM_sl =
  fixes P :: jvm_prog and mxs and mxl\<^sub>0 and n
  fixes b and Ts :: "ty list" and "is" and xt and T\<^sub>r

  fixes mxl and A and r and f and app and eff and step
  defines [simp]: "mxl \<equiv> (case b of Static \<Rightarrow> 0 | NonStatic \<Rightarrow> 1)+size Ts+mxl\<^sub>0"
  defines [simp]: "A   \<equiv> states P mxs mxl"
  defines [simp]: "r   \<equiv> JVM_SemiType.le P mxs mxl"
  defines [simp]: "f   \<equiv> JVM_SemiType.sup P mxs mxl"

  defines [simp]: "app \<equiv> \<lambda>pc. Effect.app (is!pc) P mxs T\<^sub>r pc (size is) xt"
  defines [simp]: "eff \<equiv> \<lambda>pc. Effect.eff (is!pc) P pc xt"
  defines [simp]: "step \<equiv> err_step (size is) app eff"

  defines [simp]: "n \<equiv> size is"
  assumes staticb: "b = Static \<or> b = NonStatic" 

locale start_context = JVM_sl +
  fixes p and C

  assumes wf: "wf_prog p P"
  assumes C:  "is_class P C"
  assumes Ts: "set Ts \<subseteq> types P"

 
  fixes first :: ty\<^sub>i' and start
  defines [simp]: 
  "first \<equiv> Some ([],(case b of Static \<Rightarrow> [] | NonStatic \<Rightarrow> [OK (Class C)]) @ map OK Ts @ replicate mxl\<^sub>0 Err)"
  defines [simp]:
  "start \<equiv> (OK first) #  replicate (size is - 1) (OK None)"
thm start_context.intro

lemma start_context_intro_auxi: 
  fixes  P b Ts p C
  assumes "b = Static \<or> b = NonStatic " 
      and "wf_prog p P"
      and "is_class P C"
      and "set Ts \<subseteq> types P"
    shows " start_context P b Ts p C"
  using start_context.intro[OF JVM_sl.intro] start_context_axioms_def assms  by auto

subsection \<open> Connecting JVM and Framework \<close>

lemma (in start_context) semi: "semilat (A, r, f)"
  apply (insert semilat_JVM[OF wf])
  apply (unfold A_def r_def f_def JVM_SemiType.le_def JVM_SemiType.sup_def states_def)
  apply auto
  done


lemma (in JVM_sl) step_def_exec: "step \<equiv> exec P mxs T\<^sub>r xt is" 
  by (simp add: exec_def)  

lemma special_ex_swap_lemma [iff]: 
  "(? X. (? n. X = A n & P n) & Q X) = (? n. Q(A n) & P n)"
  by blast

lemma ex_in_list [iff]:
  "(\<exists>n. ST \<in> nlists n A \<and> n \<le> mxs) = (set ST \<subseteq> A \<and> size ST \<le> mxs)"
  by (unfold nlists_def) auto

lemma singleton_nlists: 
  "(\<exists>n. [Class C] \<in> nlists n (types P) \<and> n \<le> mxs) = (is_class P C \<and> 0 < mxs)"
  by auto

lemma set_drop_subset:
  "set xs \<subseteq> A \<Longrightarrow> set (drop n xs) \<subseteq> A"
  by (auto dest: in_set_dropD)

lemma Suc_minus_minus_le:
  "n < mxs \<Longrightarrow> Suc (n - (n - b)) \<le> mxs"
  by arith

lemma in_nlistsE:
  "\<lbrakk> xs \<in> nlists n A; \<lbrakk>size xs = n; set xs \<subseteq> A\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (unfold nlists_def) blast

declare is_relevant_entry_def [simp]
declare set_drop_subset [simp]

theorem (in start_context) exec_pres_type:
  "pres_type step (size is) A"
(*<*)
proof -
  let ?n = "size is" and ?app = app and ?step = eff
  let ?mxl = "(case b of Static \<Rightarrow> 0 | NonStatic \<Rightarrow> 1) + length Ts + mxl\<^sub>0"
  let ?A = "opt((Union {nlists n (types P) |n. n <= mxs}) \<times>
                                 nlists ?mxl (err(types P)))"
  have "pres_type (err_step ?n ?app ?step) ?n (err ?A)"
  proof(rule pres_type_lift)
    have "\<And>s pc pc' s'. s\<in>?A \<Longrightarrow> pc < ?n \<Longrightarrow> ?app pc s
             \<Longrightarrow> (pc', s')\<in>set (?step pc s) \<Longrightarrow> s' \<in> ?A"
    proof -
      fix s pc pc' s'
      assume asms: "s\<in>?A" "pc < ?n" "?app pc s" "(pc', s')\<in>set (?step pc s)"
      show "s' \<in> ?A"
      proof(cases s)
        case None
        then show ?thesis using asms by (fastforce dest: effNone)
      next
        case (Some ab)
        then show ?thesis using asms proof(cases "is!pc")
          case Load
          then show ?thesis using asms
            by (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def  
                                xcpt_eff_def norm_eff_def
                          dest: nlistsE_nth_in)
        next
          case Push
          then show ?thesis using asms Some
            by (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def
                                xcpt_eff_def norm_eff_def typeof_lit_is_type)
        next
          case Getfield
          then show ?thesis using asms wf
            by (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def
                                xcpt_eff_def norm_eff_def
                          dest: sees_field_is_type)
        next
          case Getstatic
          then show ?thesis using asms wf
            by (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def
                                xcpt_eff_def norm_eff_def
                          dest: sees_field_is_type)
        next
          case (Invoke M n)
          obtain a b where [simp]: "s = \<lfloor>(a,b)\<rfloor>" using Some asms(1) by blast
          show ?thesis
          proof(cases "a!n = NT")
            case True
            then show ?thesis using Invoke asms wf
              by (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def  
                                  xcpt_eff_def norm_eff_def)
          next
            case False
            have "(pc', s') \<in> set (norm_eff (Invoke M n) P pc (a, b)) \<or>
              (pc', s') \<in> set (xcpt_eff (Invoke M n) P pc (a, b) xt)"
              using Invoke asms(4) by (simp add: Effect.eff_def)
            then show ?thesis proof(rule disjE)
              assume "(pc', s') \<in> set (xcpt_eff (Invoke M n) P pc (a, b) xt)"
              then show ?thesis using Invoke asms(1-3)
                by (fastforce simp: Effect.app_def xcpt_app_def xcpt_eff_def)
            next
              assume norm: "(pc', s') \<in> set (norm_eff (Invoke M n) P pc (a, b))"
              also have "Suc (length a - Suc n) \<le> mxs" using Invoke asms(1,3)
                by (simp add: Effect.app_def xcpt_app_def) arith
              ultimately show ?thesis using False Invoke asms(1-3) wf
                by (auto simp: Effect.app_def xcpt_app_def norm_eff_def wf_mdecl_def
                         dest!: sees_wf_mdecl)
            qed
          qed
        next
          case (Invokestatic C M n)
          obtain a b where [simp]: "s = \<lfloor>(a,b)\<rfloor>" using Some asms(1) by blast
          have "(pc', s') \<in> set (norm_eff (Invokestatic C M n) P pc (a, b)) \<or>
            (pc', s') \<in> set (xcpt_eff (Invokestatic C M n) P pc (a, b) xt)"
            using Invokestatic asms(4) by (simp add: Effect.eff_def)
          then show ?thesis proof(rule disjE)
            assume "(pc', s') \<in> set (xcpt_eff (Invokestatic C M n) P pc (a, b) xt)"
            then show ?thesis using Invokestatic asms(1-3)
              by (fastforce simp: Effect.app_def xcpt_app_def xcpt_eff_def)
          next
            assume norm: "(pc', s') \<in> set (norm_eff (Invokestatic C M n) P pc (a, b))"
            also have "Suc (length a - Suc n) \<le> mxs" using Invokestatic asms(1,3)
              by (simp add: Effect.app_def xcpt_app_def) arith
            ultimately show ?thesis using Invokestatic asms(1-3) wf
              by (auto simp: Effect.app_def xcpt_app_def norm_eff_def wf_mdecl_def
                       dest!: sees_wf_mdecl)
          qed
        qed (fastforce simp: Effect.app_def xcpt_app_def Effect.eff_def  
                             xcpt_eff_def norm_eff_def)+
      qed
    qed
    then show "\<forall>s\<in>?A. \<forall>p. p < ?n \<longrightarrow> ?app p s \<longrightarrow> (\<forall>(q, s')\<in>set (?step p s). s' \<in> ?A)"
      by clarsimp
  qed
  then show ?thesis by (simp add: JVM_states_unfold)
qed
(*>*)

declare is_relevant_entry_def [simp del]
declare set_drop_subset [simp del]

lemma lesubstep_type_simple:
  "xs [\<sqsubseteq>\<^bsub>Product.le (=) r\<^esub>] ys \<Longrightarrow> set xs {\<sqsubseteq>\<^bsub>r\<^esub>} set ys"
(*<*)
proof -
  assume assm: "xs [\<sqsubseteq>\<^bsub>Product.le (=) r\<^esub>] ys"
  have "\<And>a b i y. (a, b) = xs ! i \<Longrightarrow> i < length xs
     \<Longrightarrow> \<exists>\<tau>'. (\<exists>i. (a, \<tau>') = ys ! i \<and> i < length xs) \<and> b \<sqsubseteq>\<^bsub>r\<^esub> \<tau>'"
  proof -
    fix a b i assume ith: "(a, b) = xs ! i" and len: "i < length xs"
    obtain \<tau> where "ys ! i = (a, \<tau>) \<and> r b \<tau>"
      using le_listD[OF assm len] ith
      by (clarsimp simp: lesub_def Product.le_def)
    then have "(a, \<tau>) = ys ! i \<and> b \<sqsubseteq>\<^bsub>r\<^esub> \<tau>"
      by (clarsimp simp: lesub_def)
    with len show "\<exists>\<tau>'. (\<exists>i. (a, \<tau>') = ys ! i \<and> i < length xs) \<and> b \<sqsubseteq>\<^bsub>r\<^esub> \<tau>'"
      by fastforce
  qed
  then show "set xs {\<sqsubseteq>\<^bsub>r\<^esub>} set ys" using assm
    by (clarsimp simp: lesubstep_type_def set_conv_nth)
qed
(*>*)

declare is_relevant_entry_def [simp del]


lemma conjI2: "\<lbrakk> A; A \<Longrightarrow> B \<rbrakk> \<Longrightarrow> A \<and> B" by blast
  
lemma (in JVM_sl) eff_mono:
assumes wf: "wf_prog p P" and "pc < length is" and
  lesub: "s \<sqsubseteq>\<^bsub>sup_state_opt P\<^esub> t" and app: "app pc t"
shows "set (eff pc s) {\<sqsubseteq>\<^bsub>sup_state_opt P\<^esub>} set (eff pc t)"
(*<*)
proof(cases t)
  case None then show ?thesis using lesub
   by (simp add: Effect.eff_def lesub_def)
next
  case tSome: (Some a)
  show ?thesis proof(cases s)
    case None then show ?thesis using lesub
     by (simp add: Effect.eff_def lesub_def)
  next
    case (Some b)
    let ?norm = "\<lambda>x. norm_eff (is ! pc) P pc x"
    let ?xcpt = "\<lambda>x. xcpt_eff (is ! pc) P pc x xt"
    let ?r = "Product.le (=) (sup_state_opt P)"
    let ?\<tau>' = "\<lfloor>eff\<^sub>i (is ! pc, P, a)\<rfloor>"
    {
      fix x assume xb: "x \<in> set (succs (is ! pc) b pc)"
      then have appi: "app\<^sub>i (is ! pc, P, pc, mxs, T\<^sub>r, a)" and
                bia: "P \<turnstile> b \<le>\<^sub>i a" and appa: "app pc \<lfloor>a\<rfloor>"
        using lesub app tSome Some by (auto simp add: lesub_def Effect.app_def)
      have xa: "x \<in> set (succs (is ! pc) a pc)"
        using xb succs_mono[OF wf appi bia] by auto
      then have "(x, ?\<tau>') \<in> (\<lambda>pc'. (pc', ?\<tau>')) ` set (succs (is ! pc) a pc)"
        by (rule imageI)
      moreover have "P \<turnstile> \<lfloor>eff\<^sub>i (is ! pc, P, b)\<rfloor> \<le>' ?\<tau>'"
        using xb xa eff\<^sub>i_mono[OF wf bia] appa by fastforce
      ultimately have "\<exists>\<tau>'. (x, \<tau>') \<in> (\<lambda>pc'. (pc', \<lfloor>eff\<^sub>i (is ! pc, P, a)\<rfloor>)) ` set (succs (is ! pc) a pc) \<and>
              P \<turnstile> \<lfloor>eff\<^sub>i (is ! pc, P, b)\<rfloor> \<le>' \<tau>'" by blast
    }
    then have norm: "set (?norm b) {\<sqsubseteq>\<^bsub>sup_state_opt P\<^esub>} set (?norm a)"
      using tSome Some by (clarsimp simp: norm_eff_def lesubstep_type_def lesub_def)
    obtain a1 b1 a2 b2 where a: "a = (a1, b1)" and b: "b = (a2, b2)"
      using tSome Some by fastforce
    then have a12: "size a2 = size a1" using lesub tSome Some
      by (clarsimp simp: lesub_def list_all2_lengthD)
    have "length (?xcpt b) = length (?xcpt a)"
      by (simp add: xcpt_eff_def split_beta)
    moreover have "\<And>n. n < length (?xcpt b) \<Longrightarrow> (?xcpt b) ! n \<sqsubseteq>\<^bsub>?r\<^esub> (?xcpt a) ! n"
      using lesub tSome Some a b a12
      by (simp add: xcpt_eff_def split_beta fun_of_def) (simp add: lesub_def)
    ultimately have "?xcpt b [\<sqsubseteq>\<^bsub>?r\<^esub>] ?xcpt a"
      by(rule le_listI)
    then have "set (?xcpt b) {\<sqsubseteq>\<^bsub>sup_state_opt P\<^esub>} set (?xcpt a)"
      by (rule lesubstep_type_simple)
    moreover note norm
    ultimately have
     "set (?norm b) \<union> set (?xcpt b) {\<sqsubseteq>\<^bsub>sup_state_opt P\<^esub>} set (?norm a) \<union> set (?xcpt a)"
      by(intro lesubstep_union)
    then show ?thesis using tSome Some by(simp add: Effect.eff_def)
  qed
qed
(*>*)

lemma (in JVM_sl) bounded_step: "bounded step (size is)"
(*<*)
  by (auto simp: bounded_def err_step_def Effect.app_def Effect.eff_def
                 error_def map_snd_def
          split: err.splits option.splits)
(*>*)

theorem (in JVM_sl) step_mono:
  "wf_prog wf_mb P \<Longrightarrow> mono r step (size is) A"
(*<*)
 apply (simp add: JVM_le_Err_conv)  
  apply (insert bounded_step)
  apply (unfold JVM_states_unfold)
  apply (rule mono_lift)    
  apply (subgoal_tac "b = Static \<or> b = NonStatic") 
      apply (fastforce split:if_splits)\<comment>\<open> order_sup_state_opt' order_sup_state_opt'' \<close>
     apply (simp only:staticb)
     apply (unfold app_mono_def lesub_def)
    apply clarsimp
    apply (erule (2) app_mono)
   apply simp
  apply clarify
  apply (drule eff_mono)
      apply (auto simp add: lesub_def)
  done
(*
proof -
  assume wf: "wf_prog wf_mb P"
  let ?r = "sup_state_opt P" and ?n = "length is" and ?app = app and ?step = eff
  let ?A = "opt (\<Union> {list n (types P) |n. n \<le> mxs} \<times>
                list ((case b of Static \<Rightarrow> 0 | NonStatic \<Rightarrow> 1) + length Ts + mxl\<^sub>0)
                 (err (types P)))"
  have "order ?r ?A" using wf by simp
  moreover have "app_mono ?r ?app ?n ?A" using app_mono[OF wf]
    by (clarsimp simp: app_mono_def lesub_def)
  moreover have "bounded (err_step ?n ?app ?step) ?n" using bounded_step
    by simp
  moreover have "\<forall>s p t. s \<in> ?A \<and> p < ?n \<and> s \<sqsubseteq>\<^bsub>?r\<^esub> t \<longrightarrow>
   ?app p t \<longrightarrow> set (?step p s) {\<sqsubseteq>\<^bsub>?r\<^esub>} set (?step p t)"
     using eff_mono[OF wf] by simp
  ultimately have "mono (Err.le ?r) (err_step ?n ?app ?step) ?n (err ?A)"
    by(rule mono_lift)
  then show "mono r step (size is) A" using bounded_step
    by (simp add: JVM_le_Err_conv JVM_states_unfold)
qed
*)
(*>*)


lemma (in start_context) first_in_A [iff]: "OK first \<in> A"
  using Ts C by (cases b; force intro!: nlists_appendI simp add: JVM_states_unfold)


lemma (in JVM_sl) wt_method_def2:
  "wt_method P C' b Ts T\<^sub>r mxs mxl\<^sub>0 is xt \<tau>s =
  (is \<noteq> [] \<and> 
   (b = Static \<or> b = NonStatic) \<and>
   size \<tau>s = size is \<and>
   OK ` set \<tau>s \<subseteq> states P mxs mxl \<and>
   wt_start P C' b Ts mxl\<^sub>0 \<tau>s \<and> 
   wt_app_eff (sup_state_opt P) app eff \<tau>s)"
(*<*)using staticb
  by (unfold wt_method_def wt_app_eff_def wt_instr_def lesub_def
             check_types_def) auto
(*>*)


end
