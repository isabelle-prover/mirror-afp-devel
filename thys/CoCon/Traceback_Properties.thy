theory Traceback_Properties
imports Safety_Properties
begin


section \<open>Traceback properties\<close>

text \<open>In this section, we prove various traceback properties,
by essentially giving trace-based justifications of certain
occurring situations that are relevant for access to information:
%
\begin{description}
\item{\bf Being an author. }
If a user is an author of a paper, then either the user has registered the paper in the first
place or, inductively, has been appointed as coauthor by another author.
%
\item{\bf Being a chair. }
If a user is a chair of a conference, then either that user has registered the conference
which has been approved by the superuser or, inductively, that user has been appointed
by an existing chair of that conference.
%
%
\item{\bf Being a PC member. }
If a user is a PC member in a conference, then the user either must have been the original chair or must
have been appointed by a chair.
%
\item{\bf Being a reviewer. }
If a user is a paper's reviewer, then the user must have been appointed by a chair (from
among the PC members who have not declared a conflict with the paper).
%
\item{\bf Having conflict. }
If a user has conflict with a paper, then the user is either an author of the paper or the
conflict has been declared by that user or by a paper's author, in such a way that between
the moment when the conflict has been last declared and the current moment there is no
transition that successfully removes the conflict.
%
\item{\bf Conference reaching a phase. }
If a conference is in a given phase different from ``no phase'', then this has happened as
a consequence of either a conference approval action by the superuser (if the phase is
Setup) or a phase change action by a chair (otherwise).
\end{description}

More details and explanations can be found in \<^cite>\<open>\<open>Section 3.6\<close> in "cocon-JAR2021"\<close>.
\<close>


subsection \<open>Preliminaries\<close>

inductive trace_between :: "state \<Rightarrow> (state,act,out) trans trace \<Rightarrow> state \<Rightarrow> bool" where
  empty[simp]: "trace_between s [] s"
| step: "\<lbrakk>trace_between s tr sh; step sh a = (ou,s')\<rbrakk> \<Longrightarrow> trace_between s (tr@[Trans sh a ou s']) s'"

inductive_simps
  trace_ft_empty[simp]: "trace_between s [] s'" and
  trace_ft_snoc: "trace_between s (tr@[trn]) s'"
thm trace_ft_empty trace_ft_snoc

lemma trace_ft_append: "trace_between s (tr1@tr2) s'
  \<longleftrightarrow> (\<exists>sh. trace_between s tr1 sh \<and> trace_between sh tr2 s')"
  apply (induction tr2 arbitrary: s' rule: rev_induct)
   apply simp
  apply (subst append_assoc[symmetric], subst trace_ft_snoc)
  apply (auto simp: trace_ft_snoc)
  done

lemma trace_ft_Cons: "trace_between s (trn#tr) s'
  \<longleftrightarrow> (\<exists>sh ou a. trn = Trans s a ou sh \<and> step s a = (ou,sh) \<and> trace_between sh tr s')"
  apply (subst trace_ft_append[where ?tr1.0 = "[trn]", simplified])
  apply (subst trace_ft_snoc[where tr = "[]", simplified])
  by auto

lemmas trace_ft_simps = trace_ft_empty trace_ft_snoc trace_ft_Cons trace_ft_append

inductive trace_to :: " (state,act,out) trans trace \<Rightarrow> state \<Rightarrow> bool" where
  empty: "trace_to [] istate"
| step: "\<lbrakk>trace_to tr s; step s a = (ou,s')\<rbrakk> \<Longrightarrow> trace_to (tr@[Trans s a ou s']) s'"

lemma trace_to_ft: "trace_to tr s \<longleftrightarrow> trace_between istate tr s"
proof (rule,goal_cases)
  case 1 thus ?case
    by induction (auto intro: trace_between.intros)
next
  case 2
  moreover
  {fix s' assume "trace_between s' tr s" hence "s' = istate \<longrightarrow> trace_to tr s"
   by induction (auto intro: trace_to.intros)
  }
  ultimately show ?case by auto
qed

inductive_simps trace_to_empty[simp]: "trace_to [] s"

lemma trace_to_reach: assumes "trace_to tr s" shows "reach s"
  using assms apply induction
   apply (rule reach.intros)
  by (metis reach_step snd_conv)

lemma reach_to_trace: assumes "reach s" obtains tr where "trace_to tr s"
  using assms apply (induction rule: reach_step_induct)
   apply (auto intro: trace_to.intros) []
  by (metis surjective_pairing trace_to.step)

lemma reach_trace_to_conv: "reach s \<longleftrightarrow> (\<exists>tr. trace_to tr s)"
  by (blast intro: trace_to_reach elim: reach_to_trace)

thm trace_to.induct[no_vars]

lemma trace_to_induct[case_names empty step, induct set]:
  "\<lbrakk>trace_to x1 x2; P [] istate;
  \<And>tr s a ou s'.
    \<lbrakk>trace_to tr s; P tr s; reach s; reach s'; step s a = (ou, s')\<rbrakk>
    \<Longrightarrow> P (tr ## Trans s a ou s') s'\<rbrakk>
  \<Longrightarrow> P x1 x2"
  apply (erule trace_to.induct)
   apply simp
  apply (frule trace_to_reach)
  using reach_PairI by blast



subsection \<open>Authorship\<close>

text \<open>
  Only the creator of a paper, and users explicitly added by other authors,
  are authors of a paper.
\<close>

inductive isAut' :: "(state,act,out) trans trace \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> bool" where
  creator: "\<lbrakk> trn = Trans _ (Cact (cPaper cid uid _ pid _ _)) outOK _ \<rbrakk>
    \<Longrightarrow> isAut' (tr@[trn]) cid uid pid"
  (* "The creator of a paper is an author"  *)
| co_author: "\<lbrakk>
  isAut' tr cid uid' pid;
  trn = Trans _ (Cact (cAuthor cid uid' _ pid uid)) outOK _ \<rbrakk>
  \<Longrightarrow> isAut' (tr@[trn]) cid uid pid"
  (* "An author can add any other user as a coauthor" *)
| irrelevant: "isAut' tr cid uid' pid \<Longrightarrow> isAut' (tr@[_]) cid uid' pid"

lemma justify_author:
  assumes "trace_to tr s"
  assumes "isAut s cid uid pid"
  shows "isAut' tr cid uid pid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def)
next
  case (step tr s a ou s')
  show ?case
  proof (cases "isAut s cid uid pid")
    case True with step.IH show ?thesis by (blast intro: isAut'.intros)
  next
    case False
    with step.hyps step.prems obtain
      pass s1 s2 uid' where
      "a=Cact (cPaper cid uid pass pid s1 s2)
      \<or> (a=Cact (cAuthor cid uid' pass pid uid) \<and> isAut s cid uid' pid)"
      and [simp]: "ou=outOK"
      apply (cases a)
        subgoal for x1 apply (cases x1, auto simp add: c_defs) [] .
        subgoal for x2 apply (cases x2, auto simp add: u_defs) [] .
        subgoal for x3 apply (cases x3, auto simp add: uu_defs) [] .
        by simp_all
    thus ?thesis using step.IH
      apply (elim disjE)
      apply (rule isAut'.creator, auto) []
      apply (rule isAut'.co_author, auto) []
      done
  qed
qed


lemma author_justify:
  assumes "trace_to tr s"
  assumes "isAut' tr cid uid pid"
  shows "isAut s cid uid pid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def elim: isAut'.cases)
next
  case (step tr s a ou s')
  from step.prems
  show ?case
  proof (cases)
    case (creator _ _ pass s1 s2)
    hence [simp]: "a=Cact (cPaper cid uid pass pid s1 s2)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs)
  next
    case (co_author _ uid' _ _ pass)
    hence [simp]: "a=Cact (cAuthor cid uid' pass pid uid)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs)
  next
    case (irrelevant) with step.IH have AUT: "isAut s cid uid pid" by simp

    note roles_confIDs[OF \<open>reach s\<close> AUT]
    with AUT \<open>step s a = (ou, s')\<close> show ?thesis
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
      by simp_all
  qed
qed

theorem isAut_eq: "trace_to tr s \<Longrightarrow> isAut s cid uid pid \<longleftrightarrow> isAut' tr cid uid pid"
  (* "Trace-based equivalent of authorship" *)
  using justify_author author_justify
  by (blast)


subsection \<open>Becoming a Conference Chair\<close>

inductive isChair' :: "(state,act,out) trans trace \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> bool" where
  creator: "\<lbrakk> trn=Trans _ (Cact (cConf cid uid _ _ _)) outOK _ \<rbrakk>
    \<Longrightarrow> isChair' (tr@[trn]) cid uid"
| add_chair: "\<lbrakk> isChair' tr cid uid'; trn = Trans _ (Cact (cChair cid uid' _ uid)) outOK _ \<rbrakk>
  \<Longrightarrow> isChair' (tr@[trn]) cid uid"
| irrelevant: "\<lbrakk>isChair' tr cid uid\<rbrakk> \<Longrightarrow> isChair' (tr@[_]) cid uid"

lemma justify_chair:
  assumes "trace_to tr s"
  assumes "isChair s cid uid"
  shows "isChair' tr cid uid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def)
next
  case (step tr s a ou s')
  show ?case
  proof (cases "isChair s cid uid")
    case True with step.IH show ?thesis by (blast intro: isChair'.intros)
  next
    case False
    term cConf
    with step.hyps step.prems obtain
      pass s1 s2 uid' where
      "a=Cact (cConf cid uid pass s1 s2)
      \<or> (a=Cact (cChair cid uid' pass uid) \<and> isChair s cid uid')"
      and [simp]: "ou=outOK"
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp add: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp add: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp add: uu_defs) [] .
      by simp_all
    thus ?thesis using step.IH
      apply (elim disjE)
      apply (rule isChair'.creator, auto) []
      apply (rule isChair'.add_chair, auto) []
      done
  qed
qed

lemma chair_justify:
  assumes "trace_to tr s"
  assumes "isChair' tr cid uid"
  shows "isChair s cid uid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def elim: isChair'.cases)
next
  case (step tr s a ou s')
  from step.prems
  show ?case
  proof (cases)
    case (creator _ _ pass s1 s2)
    hence [simp]: "a=Cact (cConf cid uid pass s1 s2)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs)
  next
    case (add_chair _ uid' _ _ pass)
    hence [simp]: "a=Cact (cChair cid uid' pass uid)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs)
  next
    case (irrelevant) with step.IH have CH: "isChair s cid uid" by simp

    from CH \<open>step s a = (ou, s')\<close> show ?thesis
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
      by simp_all
  qed
qed

theorem isChair_eq: "trace_to tr s \<Longrightarrow> isChair s cid uid = isChair' tr cid uid"
  (* "Trace-based equivalent of being a chair" *)
  using justify_chair chair_justify
  by (blast)


subsection \<open>Committee Membership\<close>

inductive isPC' :: "(state,act,out) trans trace \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> bool" where
  chair: "isChair' tr cid uid \<Longrightarrow> isPC' tr cid uid"
| add_com: "\<lbrakk> isChair' tr cid uid'; trn = Trans _ (Cact (cPC cid uid' _ uid)) outOK _ \<rbrakk>
  \<Longrightarrow> isPC' (tr@[trn]) cid uid"
| irrelevant: "\<lbrakk>isPC' tr cid uid\<rbrakk> \<Longrightarrow> isPC' (tr@[_]) cid uid"

lemma justify_com:
  assumes "trace_to tr s"
  assumes "isPC s cid uid"
  shows "isPC' tr cid uid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def)
next
  case (step tr s a ou s')

  show ?case
  proof (cases "isPC s cid uid")
    case True with step.IH show ?thesis by (blast intro: isPC'.irrelevant)
  next
    case False note noPC = this
    show ?thesis proof (cases "isChair s' cid uid")
      case True thus ?thesis
        by (metis chair justify_chair step.hyps(1) step.hyps(4) trace_to.step)
    next
      case False note noChair=this
      from noPC noChair step.hyps step.prems obtain
        pass uid' where "(a=Cact (cPC cid uid' pass uid))"
        and "isChair s cid uid'"
        and [simp]: "ou=outOK"
        apply (cases a)
        subgoal for x1 apply (cases x1, auto simp add: c_defs) [] .
        subgoal for x2 apply (cases x2, auto simp add: u_defs) [] .
        subgoal for x3 apply (cases x3, auto simp add: uu_defs) [] .
        by simp_all
      thus ?thesis
        apply -
        apply (rule isPC'.add_com, auto simp: isChair_eq[OF \<open>trace_to tr s\<close>]) []
        done
    qed
  qed
qed

lemma com_justify:
  assumes "trace_to tr s"
  assumes "isPC' tr cid uid"
  shows "isPC s cid uid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def elim!: isPC'.cases isChair'.cases)
next
  case (step tr s a ou s')
  from step.prems
  show ?case
  proof (cases)
    case chair thus ?thesis
      by (metis isChair_eq isChair_isPC step.hyps(1) step.hyps(3) step.hyps(4) trace_to.step)
  next
    case (add_com _ uid' _ _ pass)
    hence [simp]: "a=Cact (cPC cid uid' pass uid)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs)
  next
    case (irrelevant) with step.IH have COM: "isPC s cid uid" by simp

    from COM \<open>step s a = (ou, s')\<close> show ?thesis
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
      by simp_all
  qed
qed

theorem isPC_eq: "trace_to tr s \<Longrightarrow> isPC s cid uid = isPC' tr cid uid"
  (* "Trace-based equivalent of committee membership" *)
  using justify_com com_justify
  by (blast)


subsection \<open>Being a Reviewer\<close>

inductive isRev' :: "(state,act,out) trans trace \<Rightarrow> confID \<Rightarrow> userID \<Rightarrow> paperID \<Rightarrow> bool" where
  add_rev: "\<lbrakk> isChair' tr cid uid'; trn = Trans _ (Cact (cReview cid uid' _ pid uid)) outOK _ \<rbrakk>
  \<Longrightarrow> isRev' (tr@[trn]) cid uid pid"
| irrelevant: "\<lbrakk>isRev' tr cid uid pid\<rbrakk> \<Longrightarrow> isRev' (tr@[_]) cid uid pid"

lemma justify_rev:
  assumes "trace_to tr s"
  assumes "isRev s cid uid pid"
  shows "isRev' tr cid uid pid"
  using assms
proof (induction)
  case empty thus ?case
    by (auto simp add: istate_def isRev_def)
next
  case (step tr s a ou s')

  show ?case
  proof (cases "isRev s cid uid pid")
    case True with step.IH show ?thesis by (blast intro: isRev'.irrelevant)
  next
    case False note noRev = this
    with step.hyps step.prems obtain
      pass uid' where "(a=Cact (cReview cid uid' pass pid uid))"
      and "isChair s cid uid'"
      and [simp]: "ou=outOK"
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp add: c_defs isRev_def) [] .
      subgoal for x2 apply (cases x2, auto simp add: u_defs isRev_def) [] .
      subgoal for x3 apply (cases x3, auto simp add: uu_defs isRev_def) [] .
      by simp_all
    thus ?thesis
      apply -
      apply (rule isRev'.add_rev, auto simp: isChair_eq[OF \<open>trace_to tr s\<close>]) []
      done
  qed
qed

lemma rev_justify:
  assumes "trace_to tr s"
  assumes "isRev' tr cid uid pid"
  shows "isRev s cid uid pid"
  using assms
proof (induction arbitrary: uid)
  case (empty s) thus ?case
    by (auto simp add: istate_def elim!: isRev'.cases)
next
  case (step tr s a ou s')
  from step.prems
  show ?case
  proof (cases)
    case (add_rev _ uid' _ _ pass)
    hence [simp]: "a=Cact (cReview cid uid' pass pid uid)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: c_defs isRev_def)
  next
    case (irrelevant) with step.IH have REV: "isRev s cid uid pid" by simp

    note roles_confIDs[OF step.hyps(2)]
    with REV \<open>step s a = (ou, s')\<close> show ?thesis
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs isRev_def) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs isRev_def) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs isRev_def) [] .
      by simp_all
  qed
qed

theorem isRev_eq: "trace_to tr s \<Longrightarrow> isRev s cid uid pid = isRev' tr cid uid pid"
  (* "Trace-based equivalent of being a reviewer" *)
  using justify_rev rev_justify
  by (blast)



subsection "Conflicts"

fun irrev_conflict :: "userID \<Rightarrow> paperID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool"
 (* "Transitions causing irrevokable conflicts" *)
where
  "irrev_conflict uid pid (Trans _ (Cact (cPaper _ uid' _ pid' _ _)) outOK _)
    \<longleftrightarrow> uid'=uid \<and> pid'=pid"
| "irrev_conflict uid pid (Trans _ (Cact (cAuthor _ _ _ pid' uid')) outOK _)
    \<longleftrightarrow> uid'=uid \<and> pid'=pid"
| "irrev_conflict uid pid _ \<longleftrightarrow> False"

fun set_conflict :: "userID \<Rightarrow> paperID \<Rightarrow> (state,act,out) trans \<Rightarrow> bool"
  (* "Transitions setting conflict state, can be revoked by later reset-actions" *)
  where
  "set_conflict uid pid (Trans _ (Cact (cConflict _ _ _ pid' uid')) outOK _)
    \<longleftrightarrow> uid'=uid \<and> pid'=pid"
| "set_conflict uid pid (Trans _ (Uact (uPref _ uid' _ pid' Conflict)) outOK _)
    \<longleftrightarrow> uid'=uid \<and> pid'=pid"
| "set_conflict _ _ _ \<longleftrightarrow> False"

fun reset_conflict :: "userID \<Rightarrow> paperID \<Rightarrow> (state,act,out)trans \<Rightarrow> bool"
  (* "Transitions re-setting conflict state, can be revoked by later set-actions" *)
  where
  "reset_conflict uid pid (Trans _ (Uact (uPref _ uid' _ pid' pr)) outOK _)
    \<longleftrightarrow> uid'=uid \<and> pid'=pid \<and> pr\<noteq>Conflict"
| "reset_conflict _ _ _ \<longleftrightarrow> False"

definition conflict_trace :: "userID \<Rightarrow> paperID \<Rightarrow> (state,act,out) trans trace \<Rightarrow> bool"
  (* "Trace that causes a conflict: It contains either an irrevokable conflict action,
    or the last action concerning conflicts was set-conflict" *)
  where
  "conflict_trace uid pid tr \<equiv>
  (\<exists>trn\<in>set tr. irrev_conflict uid pid trn)
\<or> (\<exists>tr1 trn tr2. tr=tr1@trn#tr2 \<and>
    set_conflict uid pid trn \<and> (\<forall>trn\<in>set tr2. \<not>reset_conflict uid pid trn))"

lemma irrev_conflict_impl_author:
  assumes "trace_to tr s"
  assumes "\<exists>trn\<in>set tr. irrev_conflict uid pid trn"
  shows "\<exists>cid. isAut s cid uid pid"
  using assms
  apply induction
  apply (auto simp add: istate_def) []
  subgoal for _ _ a apply (cases a)
    subgoal for x1 apply (cases x1, auto simp: c_defs, (metis roles_confIDs)+) [] .
    subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
    subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
    by simp_all
  done

lemma irrev_conflict_impl_conflict:
  assumes "trace_to tr s"
  assumes "\<exists>trn\<in>set tr. irrev_conflict uid pid trn"
  shows "pref s uid pid = Conflict"
  by (metis assms(1) assms(2) irrev_conflict_impl_author
    isAut_pref_Conflict reach_trace_to_conv)

lemma conflict_justify:
  assumes TR: "trace_to tr s"
  assumes "conflict_trace uid pid tr"
  shows "pref s uid pid = Conflict"
  using assms(2)
  unfolding conflict_trace_def
proof (cases rule: disjE[consumes 1, case_names irrev set])
  case irrev thus ?thesis by (simp add: irrev_conflict_impl_conflict[OF TR])
next
  case set
  then obtain tr1 trn tr2 where
    [simp]: "tr = tr1 @ trn # tr2" and
    SET: "set_conflict uid pid trn"
    and NRESET: "\<forall>trn\<in>set tr2. \<not> reset_conflict uid pid trn"
    by blast

  from TR obtain s1 s2 a ou where
    [simp]: "trn = Trans s1 a ou s2" and
    TR1: "trace_to tr1 s1" and
    STEP: "step s1 a = (ou,s2)" and
    TR2: "trace_between s2 tr2 s"
    by (fastforce simp add: trace_to_ft trace_ft_simps)

  from STEP SET have "pref s2 uid pid = Conflict"
    apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) []
        subgoal for _ x65 apply (cases x65, auto) [] .
        subgoal for _ _ _ x65 apply (cases x65, auto) [] .
        subgoal for _ _ _ x65 apply (cases x65, auto) [] . .
      by simp_all

  with TR2 NRESET show ?thesis
    apply induction
    subgoal by simp
    subgoal for _ _ _ a apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
      by simp_all
    done
qed

lemma justify_conflict:
  assumes TR: "trace_to tr s"
  assumes "pref s uid pid = Conflict"
  shows "conflict_trace uid pid tr"
  using assms
proof induction
  case empty thus ?case by (auto simp add: istate_def)
next
  case (step tr s a ou s')

  let ?trn = "Trans s a ou s'"

  show ?case proof (cases "pref s uid pid = Conflict")
    case False
    with step.prems \<open>step s a = (ou, s')\<close>
    have "irrev_conflict uid pid ?trn \<or> set_conflict uid pid ?trn"
      apply (cases a)
      subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
      subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
      subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
      by simp_all
    thus ?thesis
      unfolding conflict_trace_def by fastforce
  next
    case True with step.IH have CT: "conflict_trace uid pid tr" .

    from step.prems \<open>step s a = (ou, s')\<close> have "\<not>reset_conflict uid pid ?trn"
      apply (cases a)
      subgoal by simp
      subgoal for x2 by (cases x2, auto simp: u_defs)
      by simp_all

    thus ?thesis using CT
      unfolding conflict_trace_def
      apply clarsimp
      by (metis rotate1.simps(2) set_ConsD set_rotate1)

  qed
qed

theorem conflict_eq:
  assumes "trace_to tr s"
  shows "pref s uid pid = Conflict \<longleftrightarrow> conflict_trace uid pid tr"
  using assms conflict_justify justify_conflict by auto


subsection \<open>Conference Phases\<close>

fun is_uPhase where
  "is_uPhase cid (Trans _ (Uact (uConfA cid' _ _)) outOK _) \<longleftrightarrow> cid'=cid"
| "is_uPhase cid (Trans _ (Uact (uPhase cid' _ _ _)) outOK _) \<longleftrightarrow> cid'=cid"
| "is_uPhase _ _ \<longleftrightarrow> False"

inductive phase' :: "(state,act,out) trans trace \<Rightarrow> confID \<Rightarrow> nat \<Rightarrow> bool" where
  initial: "phase' [] cid noPH"
| approve: "\<lbrakk>phase' tr cid noPH; trn=Trans s (Uact (uConfA cid (voronkov s) _)) outOK _ \<rbrakk>
  \<Longrightarrow> phase' (tr@[trn]) cid setPH"
| advance: "\<lbrakk>trn = (Trans _ (Uact (uPhase cid uid _ ph)) outOK _); isChair' tr cid uid\<rbrakk>
  \<Longrightarrow> phase' (tr@[trn]) cid ph"
| irrelevant: "\<lbrakk>phase' tr cid ph; \<not>is_uPhase cid trn \<rbrakk> \<Longrightarrow> phase' (tr@[trn]) cid ph"

lemma justify_phase:
  assumes "trace_to tr s"
  assumes "phase s cid = ph"
  shows "phase' tr cid ph"
  using assms
proof (induction arbitrary: ph)
  case (empty s) thus ?case
    by (auto simp add: istate_def phase'.initial)
next
  case (step tr s a ou s')
  thus ?case
    apply (cases a)
    subgoal for x1 apply (cases x1, auto simp: c_defs intro: phase'.advance phase'.irrelevant) [] .
    subgoal for x2 apply (cases x2,
      auto
        simp: u_defs isChair_eq
        intro: phase'.advance phase'.irrelevant phase'.approve,
      (fastforce intro: phase'.approve phase'.irrelevant phase'.advance)+
    ) [] .

    subgoal for x3 apply (cases x3, auto simp: uu_defs intro: phase'.irrelevant) [] .
    by (auto intro: phase'.advance phase'.irrelevant)
qed

lemma phase_justify:
  assumes "trace_to tr s"
  assumes "phase' tr cid ph"
  shows "phase s cid = ph"
  using assms
proof (induction arbitrary: ph)
  case (empty s) thus ?case
    by (auto simp add: istate_def elim: phase'.cases)
next
  case (step tr s a ou s')
  from step.prems
  show ?case
  proof (cases)
    case (approve _ _ _ pass _)
    hence [simp]: "a=Uact (uConfA cid (voronkov s) pass)" "ou=outOK" "ph=setPH" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: u_defs)
  next
    case (advance _ _ uid pass _ _)
    hence [simp]: "a=Uact (uPhase cid uid pass ph)" "ou=outOK" by simp_all
    from step.hyps show ?thesis
      by (auto simp add: u_defs)
  next
    case (irrelevant) with step.IH have PH: "phase s cid = ph" "\<not> is_uPhase cid (Trans s a ou s')"
      by simp_all

    from PH \<open>step s a = (ou, s')\<close> show ?thesis
    apply (cases a)
    subgoal for x1 apply (cases x1, auto simp: c_defs) [] .
    subgoal for x2 apply (cases x2, auto simp: u_defs) [] .
    subgoal for x3 apply (cases x3, auto simp: uu_defs) [] .
    by simp_all
  qed auto
qed

theorem phase_eq:
  assumes "trace_to tr s"
  shows "phase s cid = ph \<longleftrightarrow> phase' tr cid ph"
  using assms phase_justify justify_phase by blast

end
