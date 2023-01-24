section "Lemmas about the While language"

theory WhileLangLemmas imports WhileLang Coinductive.Coinductive_List_Prefix begin

lemma NRC_step_deterministic:
  "star_n step n x y \<Longrightarrow> star_n step n x z \<Longrightarrow> y = z"
proof (induct rule: star_n.induct)
  case (refl_n x)
  then show ?case
    apply -
    by (erule star_n.cases; simp)
next
  case (step_n x y n z)
  then show ?case
    apply (rotate_tac 3)
    apply (erule star_n.cases, simp)
    apply simp
    apply (drule (1) step_deterministic)
    by simp
qed

inductive exec where
  exec_skip:   "exec s Skip s"
| exec_assign: "exec s (Assign n x) (subst n x s)"
| exec_print:  "exec s (Print x) (print x s)"
| exec_seq:    "exec s0 p s1 \<Longrightarrow> exec s1 q s2 \<Longrightarrow>  exec s0 (Seq p q) s2"
| exec_if:     "exec s (if guard x s then p else q) s1 \<Longrightarrow> exec s (If x p q) s1"
| exec_while1: "\<not>guard x s \<Longrightarrow> exec s (While x p) s"
| exec_while2: "guard x s \<Longrightarrow> exec s p s1 \<Longrightarrow> exec s1 (While x p) s2
       \<Longrightarrow> exec s (While x p) s2"

declare exec.intros[intro!]

lemma NRC_step[simp]:
  "star_n step n (Skip,s) (Skip,t) \<Longrightarrow> s = t"
  by (induct n "(Skip, s)" "(Skip, t)" arbitrary: s t rule: star_n.induct; clarsimp)

lemma terminates_Skip:
  "terminates s Skip t \<longleftrightarrow> s = t"
  by (fastforce simp: terminates.simps star_eq_star_n)

lemma NRC_assign[simp]:
  "star_n step n (Assign n' x,s) (Skip, t) \<Longrightarrow> t = subst n' x s"
  by (induct n "(Assign n' x,s)" "(Skip, t)" arbitrary: n' x s t rule: star_n.induct)
     (fastforce dest: NRC_step)

lemma terminates_Assign:
  "terminates s (Assign n x) t \<longleftrightarrow> t = subst n x s"
  by (fastforce simp: terminates.simps star_eq_star_n)

lemma NRC_print[simp]:
  "star_n step n (Print x,s) (Skip, t) \<Longrightarrow> t = print x s"
  by (induct n "(Print x,s)" "(Skip, t)" arbitrary: x s t rule: star_n.induct)
     (fastforce dest: NRC_step)

lemma terminates_Print:
  "terminates s (Print x) t \<longleftrightarrow> t = print x s"
  by (fastforce simp: terminates.simps star_eq_star_n)

lemma terminates_If:
  "terminates s (If x p q) t \<longleftrightarrow> terminates s (if guard x s then p else q) t"
proof -
  have NRC_if1:
    "star_n step n (prog.If x p q, s) (Skip, t) \<Longrightarrow>
         \<exists>n. star_n step n (if guard x s then p else q, s) (Skip, t)" for n
    by (induct n "(If x p q,s)" "(Skip, t)" arbitrary: x p q s t rule: star_n.induct)
      fastforce
  have NRC_if2:
    "star_n step n (if guard x s then p else q, s) (Skip, t) \<Longrightarrow>
         \<exists>n. star_n step n (prog.If x p q, s) (Skip, t)" for n
  proof (induct n "(if guard x s then p else q, s)" "(Skip, t)"
                arbitrary: x p q s t rule: star_n.induct)
    case refl_n
    then show ?case by (fastforce split: if_split_asm)
  next
    case (step_n y n)
    then show ?case by (fastforce split: if_split_asm)
  qed
  show ?thesis
    by (fastforce dest: NRC_if1 NRC_if2 simp: star_eq_star_n terminates.simps)
qed

lemma terminates_While:
  "terminates s (While f c) t \<longleftrightarrow> terminates s (If f (Seq c (While f c)) Skip) t"
proof -
  have NRC_while1:
    "star_n step n (While f c, s) (Skip, t) \<Longrightarrow>
         \<exists>n. star_n step n (prog.If f (Seq c (While f c)) Skip, s) (Skip, t)" for n
    by (induct n "(While f c,s)" "(Skip, t)" arbitrary: f c s t rule: star_n.induct)
      fastforce

  have NRC_while2:
    "star_n step n (prog.If f (Seq c (While f c)) Skip, s) (Skip, t) \<Longrightarrow>
         \<exists>n. star_n step n (While f c, s) (Skip, t)" for n
    by (induct n "(If f (Seq c (While f c)) Skip, s)" "(Skip, t)"
        arbitrary: f c s t rule: star_n.induct)
      fastforce
  show ?thesis
    by (fastforce dest: NRC_while1 NRC_while2 simp: star_eq_star_n terminates.simps)
qed

definition real_step where
  "real_step \<equiv> \<lambda>(p, s) qt. p \<noteq> Skip \<and> step (p,s) qt"

lemma terminates:
  "terminates s p t \<longleftrightarrow> star real_step (p,s) (Skip,t)"
proof -
  have P1: "star_n step n (p, s) (Skip, t) \<Longrightarrow>
            \<exists>n. star_n (\<lambda>(p, s) qt. p \<noteq> Skip \<and> step (p, s) qt) n (p, s) (Skip, t)" for n
  proof (induct n "(p, s)" "(Skip, t)" arbitrary: p s t rule: star_n.induct)
    case refl_n
    then show ?case by fastforce
  next
    case (step_n y n)
    then show ?case
      apply (drule_tac x="fst y" and y="snd y" in meta_spec2)
      apply simp
      by blast
  qed
  have P2: "star_n (\<lambda>(p, s) qt. p \<noteq> Skip \<and> step (p, s) qt) n (p, s) (Skip, t) \<Longrightarrow>
            \<exists>n. star_n step n (p, s) (Skip, t)" for n
    by (induct n "(p, s)" "(Skip, t)" arbitrary: p s t rule: star_n.induct) fastforce+
  show ?thesis
    by (fastforce dest: P1 P2 simp: real_step_def star_eq_star_n terminates.simps)
qed

lemma NRC_real_step_Skip[simp]:
  "star_n real_step n (Skip,s) (Skip,t) \<longleftrightarrow> n = 0 \<and> s = t"
  apply (rule iffI; simp?)
  by (induct n "(Skip, s)" "(Skip, t)" arbitrary: s t rule: star_n.induct)
     (simp add: real_step_def)+

lemma NRC_real_step_not_Skip:
  "p \<noteq> Skip \<Longrightarrow>
  (star_n real_step n (p,s) (Skip,t) \<longleftrightarrow>
   (\<exists>k m. real_step (p,s) m \<and> star_n real_step k m (Skip,t) \<and> n = k + 1))"
  apply (rule iffI; rotate_tac)
  by (induct n "(p, s)" "(Skip, t)" arbitrary: p s t rule: star_n.induct, simp)
     fastforce+

lemma real_step_seqE:                             
  "real_step (Seq p q, s) x \<Longrightarrow>
    (x = (q, s) \<Longrightarrow> p = Skip \<Longrightarrow> P) \<Longrightarrow>
    (\<And>p' s'. x = (Seq p' q, s') \<Longrightarrow>  real_step (p, s) (p', s') \<Longrightarrow> p \<noteq> Skip \<Longrightarrow> P)
       \<Longrightarrow> P"
  by (clarsimp simp: real_step_def) (erule seqE; clarsimp)

lemma real_steps_Seq:
  "star_n real_step n (Seq p q,s) (Skip,t) \<longleftrightarrow>
    (\<exists>n1 n2 m.
      star_n real_step n1 (p,s) (Skip,m) \<and>
      star_n real_step n2 (q,m) (Skip,t) \<and> n = n1 + n2 + 1)"
proof
  assume H: "star_n real_step n (Seq p q, s) (Skip, t)"
  show "\<exists>n1 n2 m.
        star_n real_step n1 (p, s) (Skip, m) \<and>
        star_n real_step n2 (q, m) (Skip, t) \<and> n = n1 + n2 + 1" using H
  proof (induct n "(Seq p q,s)" "(Skip,t)" arbitrary: p q s t rule: star_n.induct)
    fix y n p q s t
    assume P1: "real_step (Seq p q, s) y"
      and P2: "star_n real_step n y (Skip, t)"
      and IH: "\<And>p q s. y = (Seq p q, s) \<Longrightarrow>
          (\<exists>n1 n2 r. star_n real_step n1 (p, s) (Skip, r) \<and>
                     star_n real_step n2 (q, r) (Skip, t) \<and>
                     n = n1 + n2 + 1)"
    then show "\<exists>n1 n2 r. star_n real_step n1 (p, s) (Skip, r) \<and>
           star_n real_step n2 (q, r) (Skip, t) \<and> Suc n = n1 + n2 + 1"
      by (fastforce elim!: real_step_seqE)
  qed
next
  assume H: "\<exists>n1 n2 m.
       star_n real_step n1 (p, s) (Skip, m) \<and>
       star_n real_step n2 (q, m) (Skip, t) \<and> n = n1 + n2 + 1"
  show "star_n real_step n (Seq p q, s) (Skip, t)"
    using H
    apply - 
    apply (case_tac "p=Skip", clarsimp)
     apply (rule step_n[rotated], simp)
     apply (clarsimp simp: real_step_def)
    apply (elim exE conjE)
  proof -
    have H: "star_n real_step n1 (p, s) (Skip, m) \<Longrightarrow>
             star_n real_step n2 (q, m) (Skip, t) \<Longrightarrow>
             p \<noteq> Skip \<Longrightarrow>
             star_n real_step (n1 + n2 + 1) (Seq p q, s) (Skip, t)" for n1 n2 m
      apply (induct n1 "(p, s)" "(Skip, m)" arbitrary: s p m rule: star_n.induct)
       apply (clarsimp simp: real_step_def)
      apply (rename_tac y n s p m)
      apply (subgoal_tac "real_step (Seq p q, s) (Seq (fst y) q, snd y)")
       prefer 2
       apply (clarsimp simp: real_step_def)
      apply (case_tac "fst y = Skip")
       apply (subgoal_tac "\<And>a b. fst a = b \<Longrightarrow> (\<exists>c. a = (b, c) \<and> c = snd a)")
        prefer 2
        apply clarsimp
       apply (drule_tac x="y" and y="Skip" in meta_spec2)
       apply (drule (1) meta_mp)
       apply (elim exE conjE)
       apply (rename_tac c)
       apply (thin_tac "c = snd y")
       apply simp
       apply (erule step_n)
       apply (rule step_n[rotated])
        apply simp
       apply (clarsimp simp: real_step_def)
      apply clarsimp
      done
    thus "\<And>n1 n2 m.
          p \<noteq> Skip \<Longrightarrow>
          star_n real_step n1 (p, s) (Skip, m) \<Longrightarrow>
          star_n real_step n2 (q, m) (Skip, t) \<Longrightarrow>
          n = n1 + n2 + 1 \<Longrightarrow>
          star_n real_step n (Seq p q, s) (Skip, t)" by blast
  qed
qed

lemma terminates_Seq:
  "terminates s (Seq p q) t \<longleftrightarrow> (\<exists>m. terminates s p m \<and> terminates m q t)"
  by (fastforce simp: terminates star_eq_star_n real_steps_Seq)

lemma terminates_eq_exec:
  "terminates s p t \<longleftrightarrow> exec s p t"
proof -
  have P1: "star_n real_step n (p, s) (Skip, t) \<Longrightarrow> exec s p t" for n
  proof (induct n arbitrary: p s t rule: nat_less_induct)
    case (1 n)
    then show ?case
      apply -
      apply (case_tac p; clarsimp)
          apply (erule star_n.cases;
                 clarsimp simp: real_step_def NRC_real_step_Skip[simplified real_step_def])
          apply (drule sym[where s="subst _ _ _"], clarsimp)
         apply (erule star_n.cases;
                clarsimp simp: real_step_def NRC_real_step_Skip[simplified real_step_def])
         apply (drule sym[where s="print _ _"], clarsimp)
        apply (clarsimp simp: real_steps_Seq)
        apply (metis "1.hyps" exec_seq less_add_Suc1 less_add_Suc2)
       apply (erule star_n.cases;
              clarsimp simp: real_step_def NRC_real_step_Skip[simplified real_step_def]
                       split: if_split_asm)
        apply fastforce
       apply fastforce
      apply (erule star_n.cases; clarsimp simp: real_step_def)
      apply (erule whileE, clarsimp)
      apply (erule star_n.cases;
             clarsimp split: if_split_asm simp: NRC_real_step_Skip[simplified real_step_def])
       defer
       apply fastforce
      apply (clarsimp simp: real_steps_Seq[simplified real_step_def])
      by (meson exec_while2 less_SucI less_add_Suc1 less_add_Suc2)
  qed
  then have P1': "terminates s p t \<Longrightarrow> exec s p t"
    by (clarsimp simp: terminates star_eq_star_n)
  have P2: "exec s p t \<Longrightarrow> terminates s p t"
  proof (induct s p t rule: exec.induct; clarsimp)
    case (exec_skip s)
    then show ?case by (clarsimp simp: terminates_Skip)
  next
    case (exec_assign s n x)
    then show ?case by (clarsimp simp: terminates_Assign)
  next
    case (exec_print s x)
    then show ?case by (clarsimp simp: terminates_Print)
  next
    case (exec_seq s0 p s1 q s2)
    then show ?case by (cases s1; fastforce simp: terminates_Seq)
  next
    case (exec_if s x p q s1)
    then show ?case by (cases s1; fastforce simp: terminates_If)
  next
    case (exec_while1 x s p)
    then show ?case by (clarsimp simp: terminates_While terminates_If terminates_Skip)
  next
    case (exec_while2 x s p s1 s2)
    then show ?case
      apply (simp (no_asm) add: terminates_While terminates_If terminates_Skip)
      by (cases s1; fastforce simp: terminates_Seq)
  qed
  show ?thesis using P1' P2 by auto
qed
    
lemma terminates_While_NRC:
  assumes "terminates m p t"
  assumes "p = While f c"
  shows "\<exists>n. star_n (\<lambda>s t. guard f s \<and> terminates s c t) n m t \<and> \<not>guard f t"
  using assms
  apply (simp add: terminates_eq_exec)
  by (induct m "While f c" t arbitrary: f c rule: exec.induct; clarsimp; fastforce)

lemma not_diverges[simp]:
  "~diverges s Skip l"
  "~diverges s (Assign n x) l"
  "~diverges s (Print x) l"
  by (clarsimp simp: diverges.simps terminates_Skip terminates_Assign terminates_Print;
      metis surj_pair)+

lemma star_n_Skip:
  "star_n step n (Skip, s) (c', t) \<Longrightarrow> c' = Skip \<and> t = s"
  apply (induct n)
   apply (erule star_n.cases; clarsimp)+
  done

lemma star_n_Seq:
  "star_n step n (c, s) (c', t) \<Longrightarrow>
         \<exists>n. star_n step n (Seq c p, s) (Seq c' p, t) "
  apply (case_tac "c=Skip")
   apply (fastforce dest!: star_n_Skip)
  apply (induct n arbitrary: c s)
   apply (erule star_n.cases; simp; rename_tac x; case_tac x; rule_tac x=0 in exI, clarsimp)
  apply (erule star_n.cases, simp)
  apply (rename_tac y na z)
  apply (drule_tac x="fst y" and y="snd y" in meta_spec2)
  apply clarsimp
  apply (rename_tac ac ad bb na af bc)
  apply (case_tac "ac=Skip", simp)
   apply (fastforce dest!: star_n_Skip)
  apply clarsimp
  apply fastforce
  done

lemma RTC_Seq:
  "star step (c,s) (c',t) \<Longrightarrow>
   star step (Seq c p, s) (Seq c' p,t)"
  apply (clarsimp simp: star_eq_star_n star_n_Seq)
  done

lemma step_output_mono:
  "step s t \<Longrightarrow> prefix (output_of (snd s)) (output_of (snd t))"
  by (induct rule: step.induct; simp add: subst_def print_def split_def output_of_def)

lemma NRC_step_output_mono:
  "star_n step k (c,s) (c',s') \<Longrightarrow> prefix (output_of s) (output_of s')"
  apply (induct k arbitrary: c s c' s')
  apply (erule star_n.cases; clarsimp)
  apply (erule star_n.cases; clarsimp)
  apply (drule step_output_mono)
  apply fastforce
  done

lemma lprefix_chain_RTC_step':
  "Complete_Partial_Order.chain lprefix {llist_of out | out. (\<exists>q t. step x (q,t,out))}"
  apply (rule chainI)
  apply simp
  apply (elim exE impE conjE)
  by (metis lprefix_down_linear lprefix_llist_ofI prod.inject step_deterministic)

lemma star_n_step_decompose:
  "star_n step n x y \<Longrightarrow> star_n step n' x z \<Longrightarrow> n' < n
    \<Longrightarrow> star_n step (n - n') z y"
  by (fastforce elim!: star_n_decompose step_deterministic NRC_step_deterministic)

lemma lprefix_chain_NRC_step':
  "star_n step n x (q, t, out) \<Longrightarrow>
       star_n step n' x (q', t', out') \<Longrightarrow>
       lprefix (llist_of out) (llist_of out') \<or> lprefix (llist_of out') (llist_of out)"
  apply (insert less_linear[of n n'])
  apply (elim disjE)
    defer 2
    apply (drule (2) star_n_step_decompose,
           metis NRC_step_output_mono internal_case_prod_conv internal_case_prod_def
                 lprefix_llist_of output_of_def)+
  apply simp
  apply (drule (1) NRC_step_deterministic)
  by fastforce

lemma lprefix_chain_NRC_step:
  "Complete_Partial_Order.chain lprefix {llist_of out | out. (\<exists>q t. star_n step n x (q,t,out))}"
  by (rule chainI) (force dest: lprefix_chain_NRC_step')

lemma lprefix_chain_RTC_step:
  "Complete_Partial_Order.chain lprefix {llist_of out | out. (\<exists>q t. star step x (q,t,out))}"
  by (rule chainI) (force dest: lprefix_chain_NRC_step' star_star_n)

lemma lprefix_chain_NRC_step_ex:
  "Complete_Partial_Order.chain lprefix {llist_of out | out. (\<exists>q t n. star_n step n x (q,t,out))}"
  by (subst star_eq_star_n[symmetric]) (rule lprefix_chain_RTC_step)

definition lprefix_rel where
  "lprefix_rel ls ls' \<equiv> \<forall>l \<in> ls. \<exists>l' \<in> ls'. lprefix l l'"

lemma diverges_unique:
  "diverges s p l \<Longrightarrow> \<forall>l'. diverges s p l' \<longrightarrow> l' = l"
  using diverges_deterministic by blast

lemma terminates_unique:
  "terminates s p t \<Longrightarrow> \<forall>t'. terminates s p t' \<longrightarrow> t' = t"
  using terminates_deterministic by blast

(* diverges lemmas *)

lemma star_n_real_step_Seq_exact:
  "star_n real_step n (c, s) (Skip, t) \<Longrightarrow> star_n step n (Seq c c', s) (Seq Skip c', t)"
  by (induct "(c, s)" "(Skip, t)" arbitrary: c s t rule: star_n.induct) (auto simp: real_step_def)

lemma star_n_real_step_Seq_exact':
  "star_n real_step n (c, s) (Skip, t) \<Longrightarrow> star_n real_step n (Seq c c', s) (Seq Skip c', t)"
  by (induct "(c, s)" "(Skip, t)" arbitrary: c s t rule: star_n.induct) (auto simp: real_step_def)

lemma div_Seq1_always_Seq:
  "\<lbrakk> star_n step n (Seq c c', s) (q, s'); c \<noteq> Skip;
     \<forall>a b n. \<not> star_n step n (c, s) (Skip, a, b)\<rbrakk>
         \<Longrightarrow> \<exists>u. q = Seq u c' \<and> u \<noteq> Skip"
proof (induct "(Seq c c', s)" "(q, s')" arbitrary: c c' q s s' rule: star_n.induct)
  case (step_n y n)
  then show ?case
    by cases fastforce+
qed clarsimp

lemma div_Seq1_steps:
  "\<lbrakk>star_n step n (Seq c c', s) (Seq u c', s'); c \<noteq> Skip;
    \<forall>a b n. \<not> star_n step n (c, s) (Skip, a, b)\<rbrakk>
           \<Longrightarrow> star_n step n (c, s) (u, s')"
proof (induct "(Seq c c', s)" "(Seq u c', s')" arbitrary: c c' u s s' rule: star_n.induct)
  case (step_n y n)
  then show ?case by cases fastforce+
qed fastforce

lemma div_Seq1_lSup_eq:
  "\<forall>t. \<not> terminates s c t
    \<Longrightarrow> lSup {llist_of out |out. \<exists>q t. star step (c, s) (q, t, out)} =
        lSup {llist_of out |out. \<exists>q t. star step (Seq c c', s) (q, t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
   apply (clarsimp simp: terminates star_eq_star_n)
   apply (drule star_n_Seq)
   apply fastforce
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
  apply clarsimp
  apply (clarsimp simp: terminates.simps star_eq_star_n)
  apply (frule div_Seq1_always_Seq)
    apply (metis (no_types, opaque_lifting) star_n.simps surj_pair)
   apply simp
  apply (erule star_n.cases, fastforce)
  by (metis (mono_tags, opaque_lifting) div_Seq1_steps prod.collapse refl_n step_n)

lemma star_n_real_step_step:
  "star_n real_step n x y \<Longrightarrow> star_n step n x y"
  by (induct rule: star_n.induct; clarsimp)
     (metis (no_types, lifting) prod.simps(2) real_step_def star_n.simps)

lemma div_Seq2_steps:
  "\<lbrakk> star_n real_step n' (c, s) (Skip, s'); n' < n;
     \<forall>t' n. \<not> star_n real_step n (c', s') (Skip, t');
     star_n step n (Seq c c', s) (q, t, out)\<rbrakk>
         \<Longrightarrow> \<exists>m q t'. star_n step m (c', s') (q, t', out)"
  apply (drule star_n_real_step_Seq_exact[where c'=c'])
  apply (drule (2) star_n_step_decompose)
  apply (erule_tac ?a1.0="n - n'" in star_n.cases)
   apply clarsimp
  apply clarsimp
  apply (erule step.cases; clarsimp)
  apply fastforce
  done

lemma div_Seq2_lSub_eq:
  "\<lbrakk>terminates s c s'; \<forall>t. \<not> terminates s' c' t\<rbrakk>
    \<Longrightarrow> lSup {llist_of out |out. \<exists>q t. star step (Seq c c', s) (q, t, out)} =
        lSup {llist_of out |out. \<exists>q t. star step (c', s') (q, t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply clarsimp
   apply (clarsimp simp: terminates star_eq_star_n)
   apply (rename_tac n na)
   apply (cases s; cases s'; simp)
   apply (case_tac "n < na")
    apply (rule chain_lprefix_lSup[OF lprefix_chain_NRC_step_ex])
    apply (drule (1) div_Seq2_steps; fastforce)
   apply (clarsimp simp: not_less)
   apply (drule star_n_real_step_Seq_exact[where c'=c'])
   apply (rename_tac aa ba)
   apply (subgoal_tac "lprefix (llist_of ba)
                        (lSup {llist_of out |out. \<exists>q t n. star_n step n (c', aa, ba) (q, t, out)})")
    prefer 2
    apply (rule chain_lprefix_lSup[OF lprefix_chain_NRC_step_ex])
    apply fastforce
   apply (case_tac "n=na"; simp?)
    apply (drule (1) NRC_step_deterministic)
    apply clarsimp
   apply (drule le_neq_trans, clarsimp, simp)
   apply (frule_tac n=n and n'=na in star_n_step_decompose; simp?)
   apply (drule_tac k="n-na" in NRC_step_output_mono)
   apply (clarsimp simp: output_of_def)
   apply (meson lprefix_llist_of lprefix_trans)
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
  apply (clarsimp simp: terminates star_eq_star_n)
  apply (drule star_n_real_step_Seq_exact[where c'=c'])
  apply (subgoal_tac "step (Seq Skip c', s') (c', s')")
   apply (drule (1) step_n_rev)
   apply (clarsimp dest!: star_n_star simp: star_eq_star_n[symmetric])
   apply (drule (1) star_trans)
   apply fastforce
  apply clarsimp
  done

lemma diverges_Seq:
  "diverges s (Seq c c') l \<longleftrightarrow> diverges s c l \<or> (\<exists>t. terminates s c t \<and> diverges t c' l)"
  apply (rule iffI)
   apply (case_tac "\<exists>t. terminates s c t"; simp)
    prefer 2
    apply (erule diverges.cases)
    apply (rule diverges.intros)
    apply (clarsimp simp: terminates.simps star_eq_star_n)
    apply (metis (no_types, opaque_lifting) div_Seq1_steps div_Seq1_always_Seq refl_n star_n_Seq)
   apply (rule disjI2, clarsimp)
   apply (rename_tac a b)
   apply (rule_tac x=a in exI, rule_tac x=b in exI, clarsimp)
   apply (clarsimp simp: diverges.simps terminates_Seq)
   apply (simp add: terminates_Seq forall_swap4)
   apply (drule_tac x=a and y=b in spec2)
   apply clarsimp
   apply (drule div_Seq2_lSub_eq; fastforce)
  apply (erule disjE)
   apply (rule diverges.intros, clarsimp)
   apply (rule conjI; clarsimp?)
    apply (erule diverges.cases, clarsimp)
    apply (simp add: terminates_Seq)
   apply (fastforce simp: div_Seq1_lSup_eq diverges.simps)
  apply clarsimp
  apply (erule diverges.cases, clarsimp)
  apply (rule diverges.intros, clarsimp)
  apply (rule conjI; clarsimp?)
  using terminates_Seq terminates_deterministic apply blast
  apply (drule div_Seq2_lSub_eq)
  by simp+

lemma div_true_If_lSup_eq:
  "\<lbrakk>\<forall>t. \<not> terminates s p t; guard f s\<rbrakk>
    \<Longrightarrow> lSup {llist_of out |out. \<exists>qa t. star step (prog.If f p q, s) (qa, t, out)} =
        lSup {llist_of out |out. \<exists>q t. star step (p, s) (q, t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
   apply clarsimp
   apply (erule star.cases; fastforce)
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
  apply clarsimp
  apply (subgoal_tac "step (If f p q, s) (if guard f s then p else q, s)")
   apply simp
   apply (drule (1) step[where r=step])
   apply fastforce
  apply (rule step_if)
  done

lemma div_false_If_lSup_Eq:
  "\<lbrakk>\<forall>t. \<not> terminates s q t; \<not> guard f s\<rbrakk>
    \<Longrightarrow> lSup
         {llist_of out |out. \<exists>qa t. star step (prog.If f p q, s) (qa, t, out)} =
        lSup {llist_of out |out. \<exists>q' t. star step (q, s) (q', t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
   apply clarsimp
   apply (erule star.cases; fastforce)
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
  apply clarsimp
  apply (subgoal_tac "step (If f p q, s) (if guard f s then p else q, s)")
   apply simp
   apply (drule (1) step[where r=step])
   apply fastforce
  apply (rule step_if)
  done

lemma diverges_If:
  "diverges s (If f p q) l = diverges s (if guard f s then p else q) l"
  by (fastforce simp: diverges.simps terminates_If
                      div_true_If_lSup_eq div_false_If_lSup_Eq)

lemma While_body_add3real_step:
  "\<lbrakk>star_n real_step n (c, s) (Skip, s'); guard g s\<rbrakk>
   \<Longrightarrow> star_n real_step (n + 3) (While g c, s) (While g c, s')"
  apply (drule star_n_real_step_Seq_exact'[where c'="While g c"])
  apply (subgoal_tac "real_step (Seq Skip (While g c), s') (While g c, s')")
   apply (drule (1) step_n_rev)
   apply (thin_tac "real_step _ _")
   apply (subgoal_tac "real_step (If g (Seq c (While g c)) Skip, s)
                                 (if guard g s then Seq c (While g c) else Skip, s)")
    apply (simp only: if_True)
    apply (drule (1) step_n[rotated])
    apply (thin_tac "real_step _ _")
    apply (subgoal_tac "real_step (While g c, s) (If g (Seq c (While g c)) Skip, s)")
     apply (drule (1) step_n[rotated])
     apply (thin_tac "real_step _ _")
     apply (simp add: numeral_3_eq_3)
    apply (fastforce simp: real_step_def)+
   apply (simp (no_asm) add: real_step_def)
  apply (fastforce simp: real_step_def)
  done

lemmas While_body_add3step = While_body_add3real_step[THEN star_n_real_step_step]

lemma div_body_While_lSup_eq:
  "\<lbrakk>guard g s; \<forall>t. \<not> terminates s c t\<rbrakk>
    \<Longrightarrow> lSup {llist_of out |out. \<exists>q t. star step (c, s) (q, t, out)} =
        lSup {llist_of out |out. \<exists>q t. star step (While g c, s) (q, t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply clarsimp
   apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
   apply (clarsimp simp:  star_eq_star_n)
   apply (subgoal_tac "step (If g (Seq c (While g c)) Skip, s)
                                  (if guard g s then (Seq c (While g c)) else Skip, s)")
    prefer 2
    apply (rule step_if)
   apply simp
   apply (subgoal_tac "step (While g c, s) (If g (Seq c (While g c)) Skip, s)")
    prefer 2
    apply (rule step_while)
   apply (drule star_n_Seq[where p="While g c"])
   apply (elim exE)
   apply fastforce
  apply (frule div_Seq1_lSup_eq[where c'="While g c"])
  apply (frule div_true_If_lSup_eq[where p="Seq c (While g c)" and q=Skip, rotated, THEN sym])
   apply (clarsimp simp: terminates_Seq)
  apply simp
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
  apply (clarsimp simp: star_eq_star_n)
  apply (erule star_n.cases)
   apply fastforce
  apply clarsimp
  apply (erule step.cases; simp)
  apply clarsimp
  apply fastforce
  done

lemma inf_loop_While_steps:
  "\<lbrakk> star_n real_step n' (c, s) (Skip, s'); n' + 3 < n; guard g s;
     star_n step n (While g c, s) (q, t, out)\<rbrakk>
         \<Longrightarrow> \<exists>q' t' n. star_n step n (While g c, s') (q', t', out)"
  by(blast dest: While_body_add3step star_n_step_decompose)

lemma inf_loop_While_lSup_eq:
  "\<lbrakk>guard g s; terminates s c (a, b); \<forall>aa ba. \<not> terminates (a, b) (While g c) (aa, ba)\<rbrakk>
           \<Longrightarrow> lSup {llist_of out |out. \<exists>q t. star step (While g c, a, b) (q, t, out)} =
               lSup {llist_of out |out. \<exists>q t. star step (While g c, s) (q, t, out)}"
  apply (rule lprefix_antisym)
   apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
   apply (rule chain_lprefix_lSup[OF lprefix_chain_RTC_step])
   apply clarsimp
   apply (clarsimp simp: terminates star_eq_star_n)
   apply (frule (1) While_body_add3step)
   apply (drule (1) star_n_trans, fastforce)
  apply (rule chain_lSup_lprefix[OF lprefix_chain_RTC_step])
  apply clarsimp
  apply (clarsimp simp: terminates star_eq_star_n)
  apply (rename_tac n na)
  apply (case_tac "n + 3 < na")
   apply (rule chain_lprefix_lSup[OF lprefix_chain_NRC_step_ex])
   apply (fastforce dest!: inf_loop_While_steps)
  apply (clarsimp simp: not_less)
  apply (drule (1) While_body_add3step)
  apply (rule lprefix_trans[of _ "llist_of b"])
   apply clarsimp
   apply (case_tac "na = n + 3"; simp?)
    apply (drule (1) NRC_step_deterministic)
    apply clarsimp
   apply (drule le_neq_trans, clarsimp, simp)
   apply (frule_tac n="n+3" and n'=na in star_n_step_decompose; simp?)
   apply (drule_tac k="n+3-na" in NRC_step_output_mono)
   apply (clarsimp simp: output_of_def)
  apply (rule chain_lprefix_lSup[OF lprefix_chain_NRC_step_ex])
  apply fastforce
  done

lemma diverges_While:
  "diverges s (While g c) l \<longleftrightarrow> diverges s (If g (Seq c (While g c)) Skip) l"
  apply (rule iffI; clarsimp simp: diverges_If diverges_Seq)
   defer
   apply (case_tac "guard g s"; simp)
   apply (clarsimp simp: diverges_Seq)
   apply (erule disjE; clarsimp?)
    apply (clarsimp simp: diverges.simps terminates_While terminates_If terminates_Seq)
    apply (fastforce simp: div_body_While_lSup_eq)
   apply (simp (no_asm) add: diverges.simps terminates_While terminates_If)
   apply clarsimp
   apply (simp only: terminates_Seq del: )
   apply (rule conjI)
    apply (clarsimp, drule (1) terminates_deterministic, clarsimp simp: diverges.simps)
   apply (clarsimp simp: diverges.simps)
   apply (fastforce simp: inf_loop_While_lSup_eq)
  apply (case_tac "guard g s"; simp)
   apply (subgoal_tac "diverges s (While g c) l \<Longrightarrow> guard g s
          \<Longrightarrow> (\<forall>a b. \<not> terminates s (Seq c (While g c)) (a, b))")
    prefer 2
    apply (clarsimp simp: diverges.simps terminates_While terminates_If)
   apply (clarsimp simp: terminates_Seq diverges.simps)
   apply (rule context_conjI)
    prefer 2
    apply (fastforce simp: div_body_While_lSup_eq)
   apply clarsimp
   apply (rename_tac a b)
   apply (simp add: forall_swap4)
   apply (drule_tac x=a and y=b in spec2)
   apply clarsimp
   apply (rotate_tac 2)
   apply (drule_tac x=a and y=b in spec2)
   apply clarsimp
   apply (erule notE)
   apply (fastforce simp: inf_loop_While_lSup_eq)
  apply (clarsimp simp: diverges.simps terminates_While terminates_If)
  apply (clarsimp simp: terminates.simps)
  by (metis star.refl surj_pair)

lemma NRC_terminates:
  assumes "star_n (\<lambda>x y. terminates x c y) i s t"
  shows "\<forall>t1. star_n (\<lambda>x y. terminates x c y) i s t1 \<longleftrightarrow> (t = t1)"
proof -
  have "\<And>a b. star_n (\<lambda>x. terminates x c) i s (a, b) \<Longrightarrow> t = (a, b)" using assms
  proof(induct i arbitrary: s t)
    case 0
    show ?case using 0
      by cases (erule star_n.cases; simp)
  next
    case (Suc i)
    show ?case using Suc.prems
      apply cases
      apply(erule star_n.cases; simp)
      by(blast dest: terminates_deterministic Suc.hyps)
  qed
  thus ?thesis using assms by fastforce
qed

lemma step_output_append:
  "step (c, a, b) (c', a', b') \<Longrightarrow> \<exists>new. b' = b @ new"
  by (induct c arbitrary: c' a a' b; fastforce simp: subst_def print_def dest!: seqE whileE)

lemma step_output_extend':
  "step (c, a, b) (c', a', b @ new) \<Longrightarrow> \<forall>xs. step (c, a, xs) (c', a', xs @ new)"
  apply (induct c arbitrary: c' a a' b)
       apply clarsimp
      apply clarsimp
      apply (rename_tac x1 x2 a a' b xs)
      apply (cases new; simp)
       apply (subgoal_tac "(a', xs) = subst x1 x2 (a, xs)")
        apply clarsimp
       apply (clarsimp simp: subst_def)
      apply (clarsimp simp: subst_def)
     apply clarsimp
     apply (rename_tac x a a' b xs)
     apply (subgoal_tac "(a', xs @ new) = print x (a, xs)")
      apply clarsimp
     apply (clarsimp simp: print_def)
    apply (erule seqE)
     apply fastforce
    apply fastforce
   apply (erule ifE)
   apply (erule Pair_inject)
   apply (erule Pair_inject)
   apply (simp only: append_self_conv append.right_neutral)
   apply (rule allI)
   apply (rename_tac x1 c1 c2 c' a a' b xs)
   apply (subgoal_tac "guard x1 (a, b) = guard x1 (a, xs)")
    prefer 2
    apply (simp add: guard_def)
   apply force
  apply (erule whileE)
  apply (erule Pair_inject)
  apply (erule Pair_inject)
  apply (simp only: append_self_conv append.right_neutral)
  apply (rule allI)
  apply (rename_tac x1 c c' a a' b xs)
  apply (subgoal_tac "guard x1 (a, b) = guard x1 (a, xs)")
   prefer 2
   apply (simp add: guard_def)
  apply force
  done

lemma step_output_extend:
  "step (c, a, b) (c', a', b') \<Longrightarrow> \<exists>new. b' = b @ new \<and> (\<forall>xs. step (c, a, xs) (c', a', xs @ new))"
  by (metis step_output_append step_output_extend')

lemma star_n_real_step_output_extend:
  "star_n real_step n (c, s) (Skip, t) \<Longrightarrow>
         \<exists>new. snd t = snd s @ new \<and>
               (\<forall>xs. \<exists>n. star_n real_step n (c, fst s, xs)
                          (Skip, fst t, xs @ new)) "
  apply (induct n arbitrary: c s t)
   apply (erule star_n.cases; fastforce)
  apply clarsimp
  apply (erule star_n.cases; simp)
  apply clarsimp
  apply (rename_tac c a b c' a0 b0 n a' b')
  apply (drule_tac x=c' in meta_spec)
  apply (drule_tac x=a0 and y=b0 in meta_spec2)
  apply (drule_tac x=a' and y=b' in meta_spec2)
  apply clarsimp
  apply (subgoal_tac "c \<noteq> Skip \<and> step (c, a, b) (c', a0, b0)")
   prefer 2
   apply (clarsimp simp: real_step_def)
  apply clarsimp
  apply (drule step_output_extend)
  apply clarsimp
  apply (rotate_tac -1)
  apply (rename_tac new newa xs)
  apply (drule_tac x=xs in spec)
  apply (drule_tac x="xs@newa" in spec)
  apply clarsimp
  apply (thin_tac "real_step _ _")
  apply (subgoal_tac "real_step (c, a, xs) (c', a0, xs @ newa)")
   prefer 2
   apply (clarsimp simp: real_step_def)
  apply (rename_tac na)
  apply (rule_tac x="Suc na" in exI)
  apply fastforce
  done

lemma terminates_history:
  "terminates s c t \<Longrightarrow>
      \<exists>new. snd t = snd s @ new \<and>
            (\<forall>xs. terminates (fst s,xs) c (fst t,xs @ new))"
  apply (clarsimp simp: terminates star_eq_star_n)
  using star_n_real_step_output_extend by auto

lemma terminates_ignores_history:
  "terminates (s, out1) c (t, out2) \<Longrightarrow>
  terminates (s, []) c (t, drop (length out1) out2)"
  by (metis append.simps(1) append_eq_conv_conj prod.sel(1) prod.sel(2) terminates_history)

end