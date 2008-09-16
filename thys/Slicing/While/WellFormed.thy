header {* \isaheader{General well-formedness of While CFG} *}

theory WellFormed 
  imports Interpretation Labels "../Basic/CFGExit_wf" 
begin

subsection {* Definition of some functions *}

fun lhs :: "cmd \<Rightarrow> vname set"
where
  "lhs Skip                = {}"
  | "lhs (V:=e)              = {V}"
  | "lhs (c\<^isub>1;;c\<^isub>2)            = lhs c\<^isub>1"
  | "lhs (if (b) c\<^isub>1 else c\<^isub>2) = {}"
  | "lhs (while (b) c)       = {}"

fun rhs_aux :: "expr \<Rightarrow> vname set"
where
  "rhs_aux (Val v)       = {}"
  | "rhs_aux (Var V)       = {V}"
  | "rhs_aux (e1 \<guillemotleft>bop\<guillemotright> e2) = (rhs_aux e1 \<union> rhs_aux e2)"

fun rhs :: "cmd \<Rightarrow> vname set"
where
  "rhs Skip                = {}"
  | "rhs (V:=e)              = rhs_aux e"
  | "rhs (c\<^isub>1;;c\<^isub>2)            = rhs c\<^isub>1"
  | "rhs (if (b) c\<^isub>1 else c\<^isub>2) = rhs_aux b"
  | "rhs (while (b) c)       = rhs_aux b"


lemma rhs_interpret_eq: 
  "\<lbrakk>interpret b s = Some v'; \<forall>V \<in> rhs_aux b. s V = s' V\<rbrakk> 
   \<Longrightarrow> interpret b s' = Some v'"
proof(induct b arbitrary:v')
  case (Val v)
  from `interpret (Val v) s = Some v'` have "v' = v" by(fastsimp elim:interpret.cases)
  thus ?case by simp
next
  case (Var V)
  hence "s' V = Some v'" by(fastsimp elim:interpret.cases)
  thus ?case by simp
next
  case (BinOp b1 bop b2)
  note IH1 = `\<And>v'. \<lbrakk>interpret b1 s = Some v'; \<forall>V \<in> rhs_aux b1. s V = s' V\<rbrakk> 
             \<Longrightarrow> interpret b1 s' = Some v'`
  note IH2 = `\<And>v'. \<lbrakk>interpret b2 s = Some v'; \<forall>V \<in> rhs_aux b2. s V = s' V\<rbrakk> 
             \<Longrightarrow> interpret b2 s' = Some v'`
  from `interpret (b1 \<guillemotleft>bop\<guillemotright> b2) s = Some v'` 
  have "\<exists>v\<^isub>1 v\<^isub>2. interpret b1 s = Some v\<^isub>1 \<and> interpret b2 s = Some v\<^isub>2 \<and>
                binop bop v\<^isub>1 v\<^isub>2 = Some v'"
    apply(cases "interpret b1 s",simp)
    apply(cases "interpret b2 s",simp)
    by(case_tac "binop bop a aa",simp+)
  then obtain v\<^isub>1 v\<^isub>2 where "interpret b1 s = Some v\<^isub>1"
    and "interpret b2 s = Some v\<^isub>2" and "binop bop v\<^isub>1 v\<^isub>2 = Some v'" by blast
  from `\<forall>V \<in> rhs_aux (b1 \<guillemotleft>bop\<guillemotright> b2). s V = s' V` have "\<forall>V \<in> rhs_aux b1. s V = s' V"
    by simp
  from IH1[OF `interpret b1 s = Some v\<^isub>1` this] have "interpret b1 s' = Some v\<^isub>1" .
  from `\<forall>V \<in> rhs_aux (b1 \<guillemotleft>bop\<guillemotright> b2). s V = s' V` have "\<forall>V \<in> rhs_aux b2. s V = s' V"
    by simp
  from IH2[OF `interpret b2 s = Some v\<^isub>2` this] have "interpret b2 s' = Some v\<^isub>2" .
  with `interpret b1 s' = Some v\<^isub>1` `binop bop v\<^isub>1 v\<^isub>2 = Some v'` show ?case by simp
qed


fun Defs :: "cmd \<Rightarrow> w_node \<Rightarrow> vname set"
where "Defs prog n = {V. \<exists>l c.  n = (_ l _) \<and> labels prog l c \<and> V \<in> lhs c}"

fun Uses :: "cmd \<Rightarrow> w_node \<Rightarrow> vname set"
where "Uses prog n = {V. \<exists>l c.  n = (_ l _) \<and> labels prog l c \<and> V \<in> rhs c}"


subsection {* Lemmas about @{term "prog \<turnstile> n -et\<rightarrow> n'"} to show well-formed 
  properties *}

lemma WCFG_edge_no_Defs_equal:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; V \<notin> Defs prog n\<rbrakk> \<Longrightarrow> (transfer et s) V = s V"
proof(induct rule:WCFG_induct)
  case (WCFG_LAss V' e)
  have label:"labels (V':=e) 0 (V':=e)" and lhs:"V' \<in> lhs (V':=e)"
    by(auto intro:Labels_Base)
  hence "V' \<in> Defs (V':=e) (_0_)" by fastsimp
  with `V \<notin> Defs (V':=e) (_0_)` show ?case by auto
next
  case (WCFG_SeqFirst c\<^isub>1 n et n' c\<^isub>2)
  note IH = `V \<notin> Defs c\<^isub>1 n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c\<^isub>1 n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c\<^isub>1 n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c\<^isub>1 l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c\<^isub>1 l c` have "labels (c\<^isub>1;;c\<^isub>2) l (c;;c\<^isub>2)"
      by(fastsimp intro:Labels_Seq1)
    from `V \<in> lhs c` have "V \<in> lhs (c;;c\<^isub>2)" by simp
    with `labels (c\<^isub>1;;c\<^isub>2) l (c;;c\<^isub>2)` have "V \<in> Defs (c\<^isub>1;;c\<^isub>2) n" by fastsimp
    with `V \<notin> Defs (c\<^isub>1;;c\<^isub>2) n` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_SeqConnect c\<^isub>1 n et c\<^isub>2)
  note IH = `V \<notin> Defs c\<^isub>1 n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c\<^isub>1 n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c\<^isub>1 n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c\<^isub>1 l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c\<^isub>1 l c` have "labels (c\<^isub>1;;c\<^isub>2) l (c;;c\<^isub>2)"
      by(fastsimp intro:Labels_Seq1)
    from `V \<in> lhs c` have "V \<in> lhs (c;;c\<^isub>2)" by simp
    with `labels (c\<^isub>1;;c\<^isub>2) l (c;;c\<^isub>2)` have "V \<in> Defs (c\<^isub>1;;c\<^isub>2) n" by fastsimp
    with `V \<notin> Defs (c\<^isub>1;;c\<^isub>2) n` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `V \<notin> Defs c\<^isub>2 n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c\<^isub>2 n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c\<^isub>2 n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c\<^isub>2 l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c\<^isub>2 l c` have "labels (c\<^isub>1;;c\<^isub>2) (l + #:c\<^isub>1) c"
      by(fastsimp intro:Labels_Seq2)
    with `V \<in> lhs c` have "V \<in> Defs (c\<^isub>1;;c\<^isub>2) (n \<oplus> #:c\<^isub>1)" by fastsimp
    with `V \<notin> Defs (c\<^isub>1;;c\<^isub>2) (n \<oplus> #:c\<^isub>1)` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `V \<notin> Defs c\<^isub>1 n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c\<^isub>1 n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c\<^isub>1 n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c\<^isub>1 l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c\<^isub>1 l c` have "labels (if (b) c\<^isub>1 else c\<^isub>2) (l + 1) c"
      by(fastsimp intro:Labels_CondTrue)
    with `V \<in> lhs c` have "V \<in> Defs (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> 1)" by fastsimp
    with `V \<notin> Defs (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> 1)` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `V \<notin> Defs c\<^isub>2 n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c\<^isub>2 n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c\<^isub>2 n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c\<^isub>2 l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c\<^isub>2 l c` have "labels (if (b) c\<^isub>1 else c\<^isub>2) (l + #:c\<^isub>1 + 1) c"
      by(fastsimp intro:Labels_CondFalse)
    with `V \<in> lhs c` have "V \<in> Defs (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> #:c\<^isub>1 + 1)"
      by(fastsimp simp:nat_add_commute nat_add_left_commute)
    with `V \<notin> Defs (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> #:c\<^isub>1 + 1)` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `V \<notin> Defs c' n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c' n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c' n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c' l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c' l c` have "labels (while (b) c') (l + 2) (c;;while (b) c')"
      by(fastsimp intro:Labels_WhileBody)
    from `V \<in> lhs c` have "V \<in> lhs (c;;while (b) c')" by fastsimp
    with `labels (while (b) c') (l + 2) (c;;while (b) c')`
    have "V \<in> Defs (while (b) c') (n \<oplus> 2)" by fastsimp
    with `V \<notin> Defs (while (b) c') (n \<oplus> 2)` show False by fastsimp
  qed
  from IH[OF this] show ?case .
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `V \<notin> Defs c' n \<Longrightarrow> transfer et s V = s V`
  have "V \<notin> Defs c' n"
  proof(rule ccontr)
    assume "\<not> V \<notin> Defs c' n"
    then obtain c l where [simp]:"n = (_ l _)" and "labels c' l c"
      and "V \<in> lhs c" by fastsimp
    from `labels c' l c` have "labels (while (b) c') (l + 2) (c;;while (b) c')"
      by(fastsimp intro:Labels_WhileBody)
    from `V \<in> lhs c` have "V \<in> lhs (c;;while (b) c')" by fastsimp
    with `labels (while (b) c') (l + 2) (c;;while (b) c')`
    have "V \<in> Defs (while (b) c') (n \<oplus> 2)" by fastsimp
    with `V \<notin> Defs (while (b) c') (n \<oplus> 2)` show False by fastsimp
  qed
  from IH[OF this] show ?case .
qed auto


(*<*)declare One_nat_def [simp del](*>*)

lemma WCFG_edge_transfer_uses_only_Uses:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; \<forall>V \<in> Uses prog n. s V = s' V\<rbrakk>
  \<Longrightarrow> \<forall>V \<in> Defs prog n. (transfer et s) V = (transfer et s') V"
proof(induct rule:WCFG_induct)
  case (WCFG_LAss V e)
  have "Uses (V:=e) (_0_) = {V. V \<in> rhs_aux e}"
    by(fastsimp elim:labels.cases intro:Labels_Base)
  with `\<forall>V'\<in>Uses (V:=e) (_0_). s V' = s' V'` 
  have "\<forall>V'\<in>rhs_aux e. s V' = s' V'" by blast
  have "Defs (V:=e) (_0_) = {V}"
    by(fastsimp elim:labels.cases intro:Labels_Base)
  have "transfer \<Up>\<lambda>s. s(V := interpret e s) s V =
        transfer \<Up>\<lambda>s. s(V := interpret e s) s' V"
  proof(cases "interpret e s")
    case None
    { fix v assume "interpret e s' = Some v"
      with `\<forall>V'\<in>rhs_aux e. s V' = s' V'` have "interpret e s = Some v"
	by(fastsimp intro:rhs_interpret_eq)
      with None have False by(fastsimp split:split_if_asm) }
    with None show ?thesis by fastsimp
  next
    case (Some v)
    hence "interpret e s = Some v" by(fastsimp split:split_if_asm)
    with `\<forall>V'\<in>rhs_aux e. s V' = s' V'`
    have "interpret e s' = Some v" by(fastsimp intro:rhs_interpret_eq)
    with Some show ?thesis by simp
  qed
  with `Defs (V:=e) (_0_) = {V}` show ?case by simp
next
  case (WCFG_SeqFirst c\<^isub>1 n et n' c\<^isub>2)
  note IH = `\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (c\<^isub>1;;c\<^isub>2) n. s V = s' V` have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V"
    by auto(drule Labels_Seq1[of _ _ _ c\<^isub>2],erule_tac x="V" in allE,auto)
  from IH[OF this] have "\<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V" .
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` show ?case using Labels_Base 
    apply clarsimp 
    apply(erule labels.cases,auto dest:WCFG_sourcelabel_less_num_nodes)
    by(erule_tac x="V" in allE,fastsimp)
next
  case (WCFG_SeqConnect c\<^isub>1 n et c\<^isub>2)
  note IH = `\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (c\<^isub>1;;c\<^isub>2) n. s V = s' V` have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V"
    by auto(drule Labels_Seq1[of _ _ _ c\<^isub>2],erule_tac x="V" in allE,auto)
  from IH[OF this] have "\<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V" .
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> (_Exit_)` show ?case using Labels_Base 
    apply clarsimp 
    apply(erule labels.cases,auto dest:WCFG_sourcelabel_less_num_nodes)
    by(erule_tac x="V" in allE,fastsimp)
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c\<^isub>2 n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (c\<^isub>1;;c\<^isub>2) (n \<oplus> #:c\<^isub>1). s V = s' V` have "\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V"
    by(auto,blast dest:Labels_Seq2)
  from IH[OF this] have "\<forall>V\<in>Defs c\<^isub>2 n. transfer et s V = transfer et s' V" .
  with num_inner_nodes_gr_0[of "c\<^isub>1"] show ?case
    apply clarsimp
    apply(erule labels.cases,auto)
    by(cases n,auto dest:label_less_num_inner_nodes)+
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> 1). s V = s' V` 
  have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V" by(auto,blast dest:Labels_CondTrue)
  from IH[OF this] have "\<forall>V\<in>Defs c\<^isub>1 n. transfer et s V = transfer et s' V" .
  with `c\<^isub>1 \<turnstile> n -et\<rightarrow> n'` show ?case
    apply clarsimp 
    apply(erule labels.cases,auto)
    apply(cases n,auto dest:label_less_num_inner_nodes)
    by(cases n,auto dest:WCFG_sourcelabel_less_num_nodes)
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c\<^isub>2 n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> #:c\<^isub>1 + 1). s V = s' V` 
  have "\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V"
    by auto(drule Labels_CondFalse[of _ _ _ b c\<^isub>1],erule_tac x="V" in allE,
       auto simp:nat_add_assoc)
  from IH[OF this] have "\<forall>V\<in>Defs c\<^isub>2 n. transfer et s V = transfer et s' V" .
  with `c\<^isub>2 \<turnstile> n -et\<rightarrow> n'` show ?case
    apply clarsimp 
    apply(erule labels.cases,auto)
    apply(cases n,auto dest:label_less_num_inner_nodes)
    by(cases n,auto dest:WCFG_sourcelabel_less_num_nodes)
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `\<forall>V\<in>Uses c' n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c' n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (while (b) c') (n \<oplus> 2). s V = s' V` have "\<forall>V\<in>Uses c' n. s V = s' V"
    by auto(drule Labels_WhileBody[of _ _ _ b],erule_tac x="V" in allE,auto)
  from IH[OF this] have "\<forall>V\<in>Defs c' n. transfer et s V = transfer et s' V" .
  thus ?case
    apply clarsimp 
    apply(erule labels.cases,auto)
    by(cases n,auto dest:label_less_num_inner_nodes)
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `\<forall>V\<in>Uses c' n. s V = s' V 
    \<Longrightarrow> \<forall>V\<in>Defs c' n. transfer et s V = transfer et s' V`
  from `\<forall>V\<in>Uses (while (b) c') (n \<oplus> 2). s V = s' V` have "\<forall>V\<in>Uses c' n. s V = s' V"
    by auto(drule Labels_WhileBody[of _ _ _ b],erule_tac x="V" in allE,auto)
  from IH[OF this] have "\<forall>V\<in>Defs c' n. transfer et s V = transfer et s' V" .
  thus ?case
    apply clarsimp 
    apply(erule labels.cases,auto)
    by(cases n,auto dest:label_less_num_inner_nodes)
qed (fastsimp elim:labels.cases)+


lemma WCFG_edge_Uses_pred_eq:
  "\<lbrakk>prog \<turnstile> n -et\<rightarrow> n'; \<forall>V \<in> Uses prog n. s V = s' V; pred et s\<rbrakk>
    \<Longrightarrow> pred et s'"
proof(induct rule:WCFG_induct)
  case (WCFG_SeqFirst c\<^isub>1 n et n' c\<^isub>2)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (c\<^isub>1;; c\<^isub>2) n. s V = s' V` have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V"
    by auto(drule Labels_Seq1[of _ _ _ c\<^isub>2],erule_tac x="V" in allE,auto)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_SeqConnect c\<^isub>1 n et c\<^isub>2)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (c\<^isub>1;; c\<^isub>2) n. s V = s' V` have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V"
    by auto(drule Labels_Seq1[of _ _ _ c\<^isub>2],erule_tac x="V" in allE,auto)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_SeqSecond c\<^isub>2 n et n' c\<^isub>1)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (c\<^isub>1;; c\<^isub>2) (n \<oplus> #:c\<^isub>1). s V = s' V`
  have "\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V" by(auto,blast dest:Labels_Seq2)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_CondTrue b c\<^isub>1 c\<^isub>2)
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (_0_). s V = s' V` 
  have all:"\<forall>V. labels (if (b) c\<^isub>1 else c\<^isub>2) 0 (if (b) c\<^isub>1 else c\<^isub>2) \<and> 
            V \<in> rhs (if (b) c\<^isub>1 else c\<^isub>2) \<longrightarrow> (s V = s' V)"
    by fastsimp
  obtain v' where [simp]:"v' = true" by simp
  with `pred (\<lambda>s. interpret b s = Some true)\<^isub>\<surd> s`
  have "interpret b s = Some v'" by simp
  have "labels (if (b) c\<^isub>1 else c\<^isub>2) 0 (if (b) c\<^isub>1 else c\<^isub>2)" by(rule Labels_Base)
  with all have "\<forall>V \<in> rhs_aux b. s V = s' V" by simp
  with `interpret b s = Some v'` have "interpret b s' = Some v'"
    by(rule rhs_interpret_eq)
  thus ?case by simp
next
  case (WCFG_CondFalse b c\<^isub>1 c\<^isub>2)
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (_0_). s V = s' V`
  have all:"\<forall>V. labels (if (b) c\<^isub>1 else c\<^isub>2) 0 (if (b) c\<^isub>1 else c\<^isub>2) \<and> 
              V \<in> rhs (if (b) c\<^isub>1 else c\<^isub>2) \<longrightarrow> (s V = s' V)"
    by fastsimp
  obtain v' where [simp]:"v' = false" by simp
  with `pred (\<lambda>s. interpret b s = Some false)\<^isub>\<surd> s` 
  have "interpret b s = Some v'" by simp
  have "labels (if (b) c\<^isub>1 else c\<^isub>2) 0 (if (b) c\<^isub>1 else c\<^isub>2)" by(rule Labels_Base)
  with all have "\<forall>V \<in> rhs_aux b. s V = s' V" by simp
  with `interpret b s = Some v'` have "interpret b s' = Some v'"
    by(rule rhs_interpret_eq)
  thus ?case by simp
next
  case (WCFG_CondThen c\<^isub>1 n et n' b c\<^isub>2)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> 1). s V = s' V`
  have "\<forall>V\<in>Uses c\<^isub>1 n. s V = s' V" by(auto,blast dest:Labels_CondTrue)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_CondElse c\<^isub>2 n et n' b c\<^isub>1)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (if (b) c\<^isub>1 else c\<^isub>2) (n \<oplus> #:c\<^isub>1 + 1). s V = s' V`
  have "\<forall>V\<in>Uses c\<^isub>2 n. s V = s' V"
    by auto(drule Labels_CondFalse[of _ _ _ b c\<^isub>1],erule_tac x="V" in allE,
       auto simp:nat_add_assoc)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_WhileTrue b c')
  from `\<forall>V\<in>Uses (while (b) c') (_0_). s V = s' V`
  have all:"\<forall>V. labels (while (b) c') 0 (while (b) c') \<and> 
              V \<in> rhs (while (b) c') \<longrightarrow> (s V = s' V)"
    by fastsimp
  obtain v' where [simp]:"v' = true" by simp
  with `pred (\<lambda>s. interpret b s = Some true)\<^isub>\<surd> s`
  have "interpret b s = Some v'" by simp
  have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
  with all have "\<forall>V \<in> rhs_aux b. s V = s' V" by simp
  with `interpret b s = Some v'` have "interpret b s' = Some v'"
    by(rule rhs_interpret_eq)
  thus ?case by simp
next
  case (WCFG_WhileFalse b c')
  from `\<forall>V\<in>Uses (while (b) c') (_0_). s V = s' V`
  have all:"\<forall>V. labels (while (b) c') 0 (while (b) c') \<and> 
              V \<in> rhs (while (b) c') \<longrightarrow> (s V = s' V)"
    by fastsimp
  obtain v' where [simp]:"v' = false" by simp
  with `pred (\<lambda>s. interpret b s = Some false)\<^isub>\<surd> s`
  have "interpret b s = Some v'" by simp
  have "labels (while (b) c') 0 (while (b) c')" by(rule Labels_Base)
  with all have "\<forall>V \<in> rhs_aux b. s V = s' V" by simp
  with `interpret b s = Some v'` have "interpret b s' = Some v'"
    by(rule rhs_interpret_eq)
  thus ?case by simp
next
  case (WCFG_WhileBody c' n et n' b)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c' n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (while (b) c') (n \<oplus> 2). s V = s' V` have "\<forall>V\<in>Uses c' n. s V = s' V"
    by auto(drule Labels_WhileBody[of _ _ _ b],erule_tac x="V" in allE,auto)
  from IH[OF this `pred et s`] show ?case .
next
  case (WCFG_WhileBodyExit c' n et b)
  note IH = `\<lbrakk>\<forall>V\<in>Uses c' n. s V = s' V; pred et s\<rbrakk> \<Longrightarrow> pred et s'`
  from `\<forall>V\<in>Uses (while (b) c') (n \<oplus> 2). s V = s' V` have "\<forall>V\<in>Uses c' n. s V = s' V"
    by auto(drule Labels_WhileBody[of _ _ _ b],erule_tac x="V" in allE,auto)
  from IH[OF this `pred et s`] show ?case .
qed simp_all


(*<*)declare One_nat_def [simp](*>*)

interpretation While_CFG_wf: CFG_wf ["sourcenode" "targetnode" "kind" 
  "valid_edge prog" "Entry" "Defs prog" "Uses prog" "id"]
proof(unfold_locales)
  show "Defs prog (_Entry_) = {} \<and> Uses prog (_Entry_) = {}"
    by(simp add:Defs.simps Uses.simps)
next
  fix a V s
  assume "valid_edge prog a" and "V \<notin> Defs prog (sourcenode a)"
  obtain nx et nx' where [simp]:"a = (nx,et,nx')" by(cases a) auto
  with `valid_edge prog a` have "prog \<turnstile> nx -et\<rightarrow> nx'" by(simp add:valid_edge_def)
  with `V \<notin> Defs prog (sourcenode a)` show "id (transfer (kind a) s) V = id s V"
    by(fastsimp intro:WCFG_edge_no_Defs_equal)
next
  fix a fix s s'::state
  assume "valid_edge prog a" 
    and "\<forall>V\<in>Uses prog (sourcenode a). id s V = id s' V"
  obtain nx et nx' where [simp]:"a = (nx,et,nx')" by(cases a) auto
  with `valid_edge prog a` have "prog \<turnstile> nx -et\<rightarrow> nx'" by(simp add:valid_edge_def)
  with `\<forall>V\<in>Uses prog (sourcenode a). id s V = id s' V`
  show "\<forall>V\<in>Defs prog (sourcenode a).
             id (transfer (kind a) s) V = id (transfer (kind a) s') V"
    by -(drule WCFG_edge_transfer_uses_only_Uses,simp+)
next
  fix a s s'
  assume pred:"pred (kind a) s" and valid:"valid_edge prog a"
    and all:"\<forall>V\<in>Uses prog (sourcenode a). id s V = id s' V"
  obtain nx et nx' where [simp]:"a = (nx,et,nx')" by(cases a) auto
  with `valid_edge prog a` have "prog \<turnstile> nx -et\<rightarrow> nx'" by(simp add:valid_edge_def)
  with `pred (kind a) s` `\<forall>V\<in>Uses prog (sourcenode a). id s V = id s' V`
  show "pred (kind a) s'" by -(drule WCFG_edge_Uses_pred_eq,simp+)
next
  fix a a' 
  assume "valid_edge prog a" and "valid_edge prog a'" 
    and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
  thus "\<exists>Q Q'. kind a = (Q)\<^isub>\<surd> \<and> kind a' = (Q')\<^isub>\<surd> \<and> 
               (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
    by(fastsimp intro!:WCFG_deterministic simp:valid_edge_def)
qed


interpretation While_CFGExit_wf: CFGExit_wf ["sourcenode" "targetnode" "kind" 
  "valid_edge prog" "Entry" "Defs prog" "Uses prog" "id" "Exit"]
proof(unfold_locales)
  show "Defs prog (_Exit_) = {} \<and> Uses prog (_Exit_) = {}"
    by(simp add:Defs.simps Uses.simps)
qed


end
