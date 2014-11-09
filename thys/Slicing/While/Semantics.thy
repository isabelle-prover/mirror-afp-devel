section {* Semantics *}

theory Semantics imports Labels Com begin

subsection {* Small Step Semantics *}


inductive red :: "cmd * state \<Rightarrow> cmd * state \<Rightarrow> bool"
and red' :: "cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool"
  ("((1\<langle>_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
where
   "\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle> == red (c,s) (c',s')"
  | RedLAss:
   "\<langle>V:=e,s\<rangle> \<rightarrow> \<langle>Skip,s(V:=(interpret e s))\<rangle>"

  | SeqRed:
  "\<langle>c\<^sub>1,s\<rangle> \<rightarrow> \<langle>c\<^sub>1',s'\<rangle> \<Longrightarrow> \<langle>c\<^sub>1;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>1';;c\<^sub>2,s'\<rangle>"

  | RedSeq:
  "\<langle>Skip;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<rangle>"

  | RedCondTrue:
  "interpret b s = Some true \<Longrightarrow> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>1,s\<rangle>"

  | RedCondFalse:
  "interpret b s = Some false \<Longrightarrow> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c\<^sub>2,s\<rangle>"

  | RedWhileTrue:
  "interpret b s = Some true \<Longrightarrow> \<langle>while (b) c,s\<rangle> \<rightarrow> \<langle>c;;while (b) c,s\<rangle>"

  | RedWhileFalse:
  "interpret b s = Some false \<Longrightarrow> \<langle>while (b) c,s\<rangle> \<rightarrow> \<langle>Skip,s\<rangle>"

lemmas red_induct = red.induct[split_format (complete)]

abbreviation reds ::"cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool" 
   ("((1\<langle>_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81) where
  "\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle> == red\<^sup>*\<^sup>* (c,s) (c',s')"


subsection{* Label Semantics *}

inductive step :: "cmd \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool"
   ("(_ \<turnstile> (1\<langle>_,/_,/_\<rangle>) \<leadsto>/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
where

StepLAss:
  "V:=e \<turnstile> \<langle>V:=e,s,0\<rangle> \<leadsto> \<langle>Skip,s(V:=(interpret e s)),1\<rangle>"

| StepSeq:
  "\<lbrakk>labels (c\<^sub>1;;c\<^sub>2) l (Skip;;c\<^sub>2); labels (c\<^sub>1;;c\<^sub>2) #:c\<^sub>1 c\<^sub>2; l < #:c\<^sub>1\<rbrakk> 
  \<Longrightarrow> c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>Skip;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1\<rangle>"

| StepSeqWhile:
  "labels (while (b) c') l (Skip;;while (b) c')
  \<Longrightarrow> while (b) c' \<turnstile> \<langle>Skip;;while (b) c',s,l\<rangle> \<leadsto> \<langle>while (b) c',s,0\<rangle>"

| StepCondTrue:
  "interpret b s = Some true 
     \<Longrightarrow> if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1,s,1\<rangle>"

| StepCondFalse:
  "interpret b s = Some false 
  \<Longrightarrow> if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1 + 1\<rangle>"

| StepWhileTrue:
  "interpret b s = Some true 
     \<Longrightarrow> while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>c;;while (b) c,s,2\<rangle>"

| StepWhileFalse:
  "interpret b s = Some false \<Longrightarrow> while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>Skip,s,1\<rangle>"

| StepRecSeq1:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>
  \<Longrightarrow> prog;;c\<^sub>2 \<turnstile> \<langle>c;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c';;c\<^sub>2,s',l'\<rangle>"

| StepRecSeq2:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> 
  \<Longrightarrow> c\<^sub>1;;prog \<turnstile> \<langle>c,s,l + #:c\<^sub>1\<rangle> \<leadsto> \<langle>c',s',l' + #:c\<^sub>1\<rangle>"

| StepRecCond1:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> 
  \<Longrightarrow> if (b) prog else c\<^sub>2 \<turnstile> \<langle>c,s,l + 1\<rangle> \<leadsto> \<langle>c',s',l' + 1\<rangle>"

| StepRecCond2:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> 
  \<Longrightarrow> if (b) c\<^sub>1 else prog \<turnstile> \<langle>c,s,l + #:c\<^sub>1 + 1\<rangle> \<leadsto> \<langle>c',s',l' + #:c\<^sub>1 + 1\<rangle>"

| StepRecWhile:
  "cx \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>
  \<Longrightarrow> while (b) cx \<turnstile> \<langle>c;;while (b) cx,s,l + 2\<rangle> \<leadsto> \<langle>c';;while (b) cx,s',l' + 2\<rangle>"


lemma step_label_less:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<Longrightarrow> l < #:prog \<and> l' < #:prog"
proof(induct rule:step.induct)
  case (StepSeq c\<^sub>1 c\<^sub>2 l s)
  from `labels (c\<^sub>1;;c\<^sub>2) l (Skip;;c\<^sub>2)`
  have "l < #:(c\<^sub>1;; c\<^sub>2)" by(rule label_less_num_inner_nodes)
  thus ?case by(simp add:num_inner_nodes_gr_0)
next
  case (StepSeqWhile b cx l s)
  from `labels (while (b) cx) l (Skip;;while (b) cx)`
  have "l < #:(while (b) cx)" by(rule label_less_num_inner_nodes)
  thus ?case by simp
qed (auto intro:num_inner_nodes_gr_0)



abbreviation steps :: "cmd \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool"
   ("(_ \<turnstile> (1\<langle>_,/_,/_\<rangle>) \<leadsto>*/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81) where 
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle> == 
     (\<lambda>(c,s,l) (c',s',l'). prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>)\<^sup>*\<^sup>* (c,s,l) (c',s',l')"


subsection{* Proof of bisimulation of @{term "\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>"}\\
  and @{term "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>"} via @{term "labels"} *}

(*<*)
lemmas converse_rtranclp_induct3 =
  converse_rtranclp_induct[of _ "(ax,ay,az)" "(bx,by,bz)", split_rule,
                 consumes 1, case_names refl step]
(*>*)


subsubsection {* From @{term "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>"} to
  @{term "\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>"} *}

lemma step_red:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>"
by(induct rule:step.induct,rule RedLAss,auto intro:red.intros)



lemma steps_reds:
  "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>"
proof(induct rule:converse_rtranclp_induct3)
  case refl thus ?case by simp
next
  case (step c s l c'' s'' l'')
  then have "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s'',l''\<rangle>"
    and "\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>" by simp_all
  from `prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s'',l''\<rangle>` have "\<langle>c,s\<rangle> \<rightarrow> \<langle>c'',s''\<rangle>"
    by(fastforce intro:step_red)
  with `\<langle>c'',s''\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>` show ?case
    by(fastforce intro:converse_rtranclp_into_rtranclp)
qed


(*<*)declare fun_upd_apply [simp del] One_nat_def [simp del](*>*)

subsubsection {* From @{term "\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>"} and @{term labels} to
  @{term "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>"} *}

lemma red_step:
  "\<lbrakk>labels prog l c; \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>\<rbrakk>
  \<Longrightarrow> \<exists>l'. prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels prog l' c'"
proof(induct arbitrary:c' rule:labels.induct)
  case (Labels_Base c)
  from `\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>` show ?case
  proof(induct rule:red_induct)
    case (RedLAss V e s)
    have "V:=e \<turnstile> \<langle>V:=e,s,0\<rangle> \<leadsto> \<langle>Skip,s(V:=(interpret e s)),1\<rangle>" by(rule StepLAss)
    have "labels (V:=e) 1 Skip" by(fastforce intro:Labels_LAss)
    with `V:=e \<turnstile> \<langle>V:=e,s,0\<rangle> \<leadsto> \<langle>Skip,s(V:=(interpret e s)),1\<rangle>` show ?case by blast
  next
    case (SeqRed c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
    from `\<exists>l'. c\<^sub>1 \<turnstile> \<langle>c\<^sub>1,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1',s',l'\<rangle> \<and> labels c\<^sub>1 l' c\<^sub>1'`
    obtain l' where "c\<^sub>1 \<turnstile> \<langle>c\<^sub>1,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1',s',l'\<rangle>" and "labels c\<^sub>1 l' c\<^sub>1'" by blast
    from `c\<^sub>1 \<turnstile> \<langle>c\<^sub>1,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1',s',l'\<rangle>` have "c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>c\<^sub>1;;c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1';;c\<^sub>2,s',l'\<rangle>"
      by(rule StepRecSeq1)
    moreover
    from `labels c\<^sub>1 l' c\<^sub>1'` have "labels (c\<^sub>1;;c\<^sub>2) l' (c\<^sub>1';;c\<^sub>2)" by(rule Labels_Seq1)
    ultimately show ?case by blast
  next
    case (RedSeq c\<^sub>2 s)
    have "labels c\<^sub>2 0 c\<^sub>2" by(rule Labels.Labels_Base)
    hence "labels (Skip;;c\<^sub>2) (0 + #:Skip) c\<^sub>2" by(rule Labels_Seq2)
    have "labels (Skip;;c\<^sub>2) 0 (Skip;;c\<^sub>2)" by(rule Labels.Labels_Base)
    with `labels (Skip;;c\<^sub>2) (0 + #:Skip) c\<^sub>2`
    have "Skip;;c\<^sub>2 \<turnstile> \<langle>Skip;;c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:Skip\<rangle>"
      by(fastforce intro:StepSeq)
    with `labels (Skip;;c\<^sub>2) (0 + #:Skip) c\<^sub>2` show ?case by auto
  next
    case (RedCondTrue b s c\<^sub>1 c\<^sub>2)
    from `interpret b s = Some true`
    have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1,s,1\<rangle>"
      by(rule StepCondTrue)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) (0 + 1) c\<^sub>1"
      by(rule Labels_CondTrue,rule Labels.Labels_Base)
    with `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>1,s,1\<rangle>` show ?case by auto
  next
    case (RedCondFalse b s c\<^sub>1 c\<^sub>2)
    from `interpret b s = Some false` 
    have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1 + 1\<rangle>"
      by(rule StepCondFalse)
    have "labels (if (b) c\<^sub>1 else c\<^sub>2) (0 + #:c\<^sub>1 + 1) c\<^sub>2"
      by(rule Labels_CondFalse,rule Labels.Labels_Base)
    with `if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>if (b) c\<^sub>1 else c\<^sub>2,s,0\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1 + 1\<rangle>`
    show ?case by auto
  next
    case (RedWhileTrue b s c)
    from `interpret b s = Some true`
    have "while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>c;; while (b) c,s,2\<rangle>"
      by(rule StepWhileTrue)
    have "labels (while (b) c) (0 + 2) (c;; while (b) c)"
      by(rule Labels_WhileBody,rule Labels.Labels_Base)
    with `while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>c;; while (b) c,s,2\<rangle>`
    show ?case by(auto simp del:add_2_eq_Suc')
  next
    case (RedWhileFalse b s c)
    from `interpret b s = Some false`
    have "while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>Skip,s,1\<rangle>"
      by(rule StepWhileFalse)
    have "labels (while (b) c) 1 Skip" by(rule Labels_WhileExit)
    with `while (b) c \<turnstile> \<langle>while (b) c,s,0\<rangle> \<leadsto> \<langle>Skip,s,1\<rangle>` show ?case by auto
  qed
next
  case (Labels_LAss V e)
  from `\<langle>Skip,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>` have False by(auto elim:red.cases)
  thus ?case by simp
next
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = `\<And>c'. \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle> \<Longrightarrow>
        \<exists>l'. c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>1 l' c'`
  from `\<langle>c;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>` 
  have "(c = Skip \<and> c' = c\<^sub>2 \<and> s = s') \<or> (\<exists>c''. c' = c'';;c\<^sub>2)"
    by -(erule red.cases,auto)
  thus ?case
  proof
    assume [simp]:"c = Skip \<and> c' = c\<^sub>2 \<and> s = s'"
    from `labels c\<^sub>1 l c` have "l < #:c\<^sub>1"
      by(rule label_less_num_inner_nodes[simplified])
    have "labels (c\<^sub>1;;c\<^sub>2) (0 + #:c\<^sub>1) c\<^sub>2"
      by(rule Labels_Seq2,rule Labels_Base)
    from `labels c\<^sub>1 l c` have "labels (c\<^sub>1;; c\<^sub>2) l (Skip;;c\<^sub>2)"
      by(fastforce intro:Labels.Labels_Seq1)
    with `labels (c\<^sub>1;;c\<^sub>2) (0 + #:c\<^sub>1) c\<^sub>2` `l < #:c\<^sub>1` 
    have "c\<^sub>1;; c\<^sub>2 \<turnstile> \<langle>Skip;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c\<^sub>2,s,#:c\<^sub>1\<rangle>"
      by(fastforce intro:StepSeq)
    with `labels (c\<^sub>1;;c\<^sub>2) (0 + #:c\<^sub>1) c\<^sub>2` show ?case by auto
  next
    assume "\<exists>c''. c' = c'';;c\<^sub>2"
    then obtain c'' where [simp]:"c' = c'';;c\<^sub>2" by blast
    with `\<langle>c;;c\<^sub>2,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>` have "\<langle>c,s\<rangle> \<rightarrow> \<langle>c'',s'\<rangle>"
      by(auto elim!:red.cases,induct c\<^sub>2,auto)
    from IH[OF this] obtain l' where "c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s',l'\<rangle>"
      and "labels c\<^sub>1 l' c''" by blast
    from `c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s',l'\<rangle>` have "c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>c;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c'';;c\<^sub>2,s',l'\<rangle>"
      by(rule StepRecSeq1)
    from `labels c\<^sub>1 l' c''` have "labels (c\<^sub>1;;c\<^sub>2) l' (c'';;c\<^sub>2)"
      by(rule Labels.Labels_Seq1)
    with `c\<^sub>1;;c\<^sub>2 \<turnstile> \<langle>c;;c\<^sub>2,s,l\<rangle> \<leadsto> \<langle>c'';;c\<^sub>2,s',l'\<rangle>` show ?case by auto
  qed
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1 c')
  note IH = `\<And>c'. \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle> \<Longrightarrow>
            \<exists>l'. c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>2 l' c'`
  from IH[OF `\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>`] obtain l' where "c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    and "labels c\<^sub>2 l' c'" by blast
  from `c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>` have "c\<^sub>1;; c\<^sub>2 \<turnstile> \<langle>c,s,l + #:c\<^sub>1\<rangle> \<leadsto> \<langle>c',s',l' + #:c\<^sub>1\<rangle>"
    by(rule StepRecSeq2)
  moreover
  from `labels c\<^sub>2 l' c'` have "labels (c\<^sub>1;;c\<^sub>2) (l' + #:c\<^sub>1) c'"
    by(rule Labels.Labels_Seq2)
  ultimately show ?case by blast
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2 c')
  note label = `labels c\<^sub>1 l c` and red = `\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>`
    and IH = `\<And>c'. \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle> \<Longrightarrow>
                   \<exists>l'. c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>1 l' c'`
  from IH[OF `\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>`] obtain l' where "c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    and "labels c\<^sub>1 l' c'" by blast
  from `c\<^sub>1 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>`
  have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>c,s,l + 1\<rangle> \<leadsto> \<langle>c',s',l' + 1\<rangle>"
    by(rule StepRecCond1)
  moreover
  from `labels c\<^sub>1 l' c'` have "labels (if (b) c\<^sub>1 else c\<^sub>2) (l' + 1) c'"
    by(rule Labels.Labels_CondTrue)
  ultimately show ?case by blast
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1 c')
  note IH = `\<And>c'. \<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle> \<Longrightarrow>
            \<exists>l'. c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle> \<and> labels c\<^sub>2 l' c'`
  from IH[OF `\<langle>c,s\<rangle> \<rightarrow> \<langle>c',s'\<rangle>`] obtain l' where "c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    and "labels c\<^sub>2 l' c'" by blast
  from `c\<^sub>2 \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>`
  have "if (b) c\<^sub>1 else c\<^sub>2 \<turnstile> \<langle>c,s,l + #:c\<^sub>1 + 1\<rangle> \<leadsto> \<langle>c',s',l' + #:c\<^sub>1 + 1\<rangle>"
    by(rule StepRecCond2)
  moreover
  from `labels c\<^sub>2 l' c'` have "labels (if (b) c\<^sub>1 else c\<^sub>2) (l' + #:c\<^sub>1 + 1) c'"
    by(rule Labels.Labels_CondFalse)
  ultimately show ?case by blast
next
  case (Labels_WhileBody c' l c b cx)
  note IH = `\<And>c''. \<langle>c,s\<rangle> \<rightarrow> \<langle>c'',s'\<rangle> \<Longrightarrow>
            \<exists>l'. c' \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s',l'\<rangle> \<and> labels c' l' c''`
  from `\<langle>c;;while (b) c',s\<rangle> \<rightarrow> \<langle>cx,s'\<rangle>`
  have "(c = Skip \<and> cx = while (b) c' \<and> s = s') \<or> (\<exists>c''. cx = c'';;while (b) c')"
    by -(erule red.cases,auto)
  thus ?case
  proof
    assume [simp]:"c = Skip \<and> cx = while (b) c' \<and> s = s'"
    have "labels (while (b) c') 0 (while (b) c')"
      by(fastforce intro:Labels_Base)
    from `labels c' l c` have "labels (while (b) c') (l + 2) (Skip;;while (b) c')"
      by(fastforce intro:Labels.Labels_WhileBody simp del:add_2_eq_Suc')
    hence "while (b) c' \<turnstile> \<langle>Skip;;while (b) c',s,l + 2\<rangle> \<leadsto> \<langle>while (b) c',s,0\<rangle>"
      by(rule StepSeqWhile)
    with `labels (while (b) c') 0 (while (b) c')` show ?case by simp blast
  next
    assume "\<exists>c''. cx = c'';;while (b) c'"
    then obtain c'' where [simp]:"cx = c'';;while (b) c'" by blast
    with `\<langle>c;;while (b) c',s\<rangle> \<rightarrow> \<langle>cx,s'\<rangle>` have "\<langle>c,s\<rangle> \<rightarrow> \<langle>c'',s'\<rangle>"
      by(auto elim:red.cases)
    from IH[OF this] obtain l' where "c' \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s',l'\<rangle>"
      and "labels c' l' c''" by blast
    from `c' \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s',l'\<rangle>` 
    have "while (b) c' \<turnstile> \<langle>c;;while (b) c',s,l + 2\<rangle> \<leadsto> \<langle>c'';;while (b) c',s',l' + 2\<rangle>"
      by(rule StepRecWhile)
    moreover
    from `labels c' l' c''` have "labels (while (b) c') (l' + 2) (c'';;while (b) c')"
      by(rule Labels.Labels_WhileBody)
    ultimately show ?case by simp blast
  qed
next
  case (Labels_WhileExit b c' c'')
  from `\<langle>Skip,s\<rangle> \<rightarrow> \<langle>c'',s'\<rangle>` have False by(auto elim:red.cases)
  thus ?case by simp
qed


lemma reds_steps:
  "\<lbrakk>\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>; labels prog l c\<rbrakk>
  \<Longrightarrow> \<exists>l'. prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle> \<and> labels prog l' c'"
proof(induct rule:rtranclp_induct2)
  case refl
  from `labels prog l c` show ?case by blast
next
  case (step c'' s'' c' s')
  note IH = `labels prog l c \<Longrightarrow>    
    \<exists>l'. prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c'',s'',l'\<rangle> \<and> labels prog l' c''`
  from IH[OF `labels prog l c`] obtain l'' where "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c'',s'',l''\<rangle>"
    and "labels prog l'' c''" by blast
  from `labels prog l'' c''` `\<langle>c'',s''\<rangle> \<rightarrow> \<langle>c',s'\<rangle>` obtain l'
    where "prog \<turnstile> \<langle>c'',s'',l''\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>"
    and "labels prog l' c'" by(auto dest:red_step)
  from `prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c'',s'',l''\<rangle>` `prog \<turnstile> \<langle>c'',s'',l''\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>`
  have "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>"
    by(fastforce elim:rtranclp_trans)
  with `labels prog l' c'` show ?case by blast
qed

subsubsection {* The bisimulation theorem *}

theorem reds_steps_bisimulation:
  "labels prog l c \<Longrightarrow> (\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>) = 
     (\<exists>l'. prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle> \<and> labels prog l' c')"
  by(fastforce intro:reds_steps elim:steps_reds)

end
