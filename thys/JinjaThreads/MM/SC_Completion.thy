(*  Title:      JinjaThreads/MM/SC_Completion.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Sequentially consistent completion of executions in the JMM} *}

theory SC_Completion imports
  "JMM_Spec"
  "../Framework/FWLTS"
begin

section {* Most recently written values *}

fun mrw_value :: "'m prog \<Rightarrow> ((addr \<times> addr_loc) \<rightharpoonup> (val \<times> bool)) \<Rightarrow> obs_event action \<Rightarrow> ((addr \<times> addr_loc) \<rightharpoonup> (val \<times> bool))"
where
  "mrw_value P vs (NormalAction (WriteMem ad al v)) = vs((ad, al) \<mapsto> (v, True))"
| "mrw_value P vs (NormalAction (NewObj ad C)) =
   (\<lambda>(ad', al). if ad = ad' \<and> al \<in> addr_locs P (Class_type C) \<and> (case vs (ad, al) of None \<Rightarrow> True | Some (v, b) \<Rightarrow> \<not> b)
                then Some (addr_loc_default P (Class_type C) al, False)
                else vs (ad', al))"
| "mrw_value P vs (NormalAction (NewArr ad T n)) =
   (\<lambda>(ad', al). if ad = ad' \<and> al \<in> addr_locs P (Array_type T n) \<and> (case vs (ad, al) of None \<Rightarrow> True | Some (v, b) \<Rightarrow> \<not> b)
                then Some (addr_loc_default P (Array_type T n) al, False)
                else vs (ad', al))"
| "mrw_value P vs _ = vs"

lemma mrw_value_cases:
  obtains ad al v where "x = NormalAction (WriteMem ad al v)"
  | ad C where "x = NormalAction (NewObj ad C)"
  | ad T n where "x = NormalAction (NewArr ad T n)"
  | ad M vs v where "x = NormalAction (ExternalCall ad M vs v)"
  | ad al v where "x = NormalAction (ReadMem ad al v)"
  | t where "x = NormalAction (ThreadStart t)"
  | t where "x = NormalAction (ThreadJoin t)"
  | ad where "x = NormalAction (SyncLock ad)"
  | ad where "x = NormalAction (SyncUnlock ad)"
  | "x = InitialThreadAction"
  | "x = ThreadFinishAction"
by pat_completeness

abbreviation mrw_values :: "'m prog \<Rightarrow> ((addr \<times> addr_loc) \<rightharpoonup> (val \<times> bool)) \<Rightarrow> obs_event action list \<Rightarrow> ((addr \<times> addr_loc) \<rightharpoonup> (val \<times> bool))"
where "mrw_values P \<equiv> foldl (mrw_value P)"

lemma mrw_values_eq_SomeD:
  assumes mrw: "mrw_values P vs0 obs (ad, al) = \<lfloor>(v, b)\<rfloor>"
  and "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>wa. wa \<in> set obs \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
  shows "\<exists>obs' wa obs''. obs = obs' @ wa # obs'' \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and>
            value_written_aux P wa al = v \<and> (is_new_action wa \<longleftrightarrow> \<not> b) \<and>
            (\<forall>ob\<in>set obs''. is_write_action ob \<longrightarrow> (ad, al) \<in> action_loc_aux P ob \<longrightarrow> is_new_action ob \<and> b)"
  (is "?concl obs")
using assms
proof(induct obs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc ob obs)
  note mrw = `mrw_values P vs0 (obs @ [ob]) (ad, al) = \<lfloor>(v, b)\<rfloor>`
  show ?case
  proof(cases "is_write_action ob \<and> (ad, al) \<in> action_loc_aux P ob \<and> (is_new_action ob \<longrightarrow> \<not> b)")
    case True thus ?thesis using mrw
      by(fastsimp elim!: is_write_action.cases intro: action_loc_aux_intros split: split_if_asm)
  next
    case False
    with mrw have "mrw_values P vs0 obs (ad, al) = \<lfloor>(v, b)\<rfloor>"
      by(cases "ob" rule: mrw_value_cases)(auto split: split_if_asm)
    moreover
    { assume "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor>"
      hence "\<exists>wa. wa \<in> set (obs @ [ob]) \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
        by(rule snoc)
      with False have "\<exists>wa. wa \<in> set obs \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
        by auto }
    ultimately have "?concl obs" by(rule snoc)
    thus ?thesis using False mrw by fastsimp
  qed
qed

lemma mrw_values_WriteMemD:
  assumes "NormalAction (WriteMem ad al v') \<in> set obs"
  shows "\<exists>v. mrw_values P vs0 obs (ad, al) = Some (v, True)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(erule disjE)
 apply clarsimp
apply clarsimp
apply(case_tac x rule: mrw_value_cases)
apply simp_all
done

lemma mrw_values_new_actionD:
  assumes "w \<in> set obs" "is_new_action w" "adal \<in> action_loc_aux P w"
  shows "\<exists>v b. mrw_values P vs0 obs adal = Some (v, b)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(erule disjE)
 apply(fastsimp simp add: split_beta elim!: action_loc_aux_cases is_new_action.cases)
apply clarsimp
apply(rename_tac w' obs' v b)
apply(case_tac w' rule: mrw_value_cases)
apply(auto simp add: split_beta)
done

lemma mrw_value_dom_mono:
  "dom vs \<subseteq> dom (mrw_value P vs ob)"
by(cases ob rule: mrw_value_cases) auto

lemma mrw_values_dom_mono:
  "dom vs \<subseteq> dom (mrw_values P vs obs)"
by(induct obs arbitrary: vs)(auto intro: subset_trans[OF mrw_value_dom_mono] del: subsetI)

lemma mrw_values_eq_NoneD:
  assumes "mrw_values P vs0 obs adal = None"
  and "w \<in> set obs" and "is_write_action w" and "adal \<in> action_loc_aux P w"
  shows False
using assms
apply -
apply(erule is_write_action.cases)
apply(fastsimp dest: mrw_values_WriteMemD[where ?vs0.0=vs0 and P=P] mrw_values_new_actionD[where ?vs0.0=vs0] elim: action_loc_aux_cases)+
done

lemma mrw_values_mrw:
  assumes mrw: "mrw_values P vs0 (map snd obs) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  and initial: "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>wa. wa \<in> set (map snd obs) \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
  shows "\<exists>i. i < length obs \<and> P,llist_of (obs @ [(t, NormalAction (ReadMem ad al v))]) \<turnstile> length obs \<leadsto>mrw i \<and> value_written P (llist_of obs) i (ad, al) = v"
proof -
  from mrw_values_eq_SomeD[OF mrw initial]
  obtain obs' wa obs'' where obs: "map snd obs = obs' @ wa # obs''"
    and wa: "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and written: "value_written_aux P wa al = v"
    and new: "is_new_action wa \<longleftrightarrow> \<not> b"
    and last: "\<And>ob. \<lbrakk> ob \<in> set obs''; is_write_action ob; (ad, al) \<in> action_loc_aux P ob \<rbrakk> \<Longrightarrow> is_new_action ob \<and> b"
    by blast
  let ?i = "length obs'"
  let ?E = "llist_of (obs @ [(t, NormalAction (ReadMem ad al v))])"

  from obs have len: "length (map snd obs) = Suc (length obs') + length obs''" by simp
  hence "?i < length obs" by simp
  moreover
  hence obs_i: "action_obs ?E ?i = wa" using len obs
    by(auto simp add: action_obs_def map_eq_append_conv)

  have "P,?E \<turnstile> length obs \<leadsto>mrw ?i"
  proof(rule most_recent_write_for.intros)
    show "length obs \<in> read_actions ?E"
      by(auto intro: read_actions.intros simp add: actions_def action_obs_def)
    show "(ad, al) \<in> action_loc P ?E (length obs)"
      by(simp add: action_obs_def lnth_llist_of)
    show "?E \<turnstile> length obs' \<le>a length obs" using len
      by-(rule action_orderI, auto simp add: actions_def action_obs_def nth_append)
    show "?i \<in> write_actions ?E" using len obs wa
      by-(rule write_actions.intros, auto simp add: actions_def action_obs_def nth_append map_eq_append_conv)
    show "(ad, al) \<in> action_loc P ?E ?i" using obs_i adal by simp

    fix wa'
    assume wa': "wa' \<in> write_actions ?E"
      and adal': "(ad, al) \<in> action_loc P ?E wa'"
    from wa' `?i \<in> write_actions ?E`
    have "wa' \<in> actions ?E" "?i \<in> actions ?E" by simp_all
    hence "?E \<turnstile> wa' \<le>a ?i"
    proof(rule action_orderI)
      assume new_wa': "is_new_action (action_obs ?E wa')"
        and new_i: "is_new_action (action_obs ?E ?i)"
      from new_i obs_i new have b: "\<not> b" by simp

      show "wa' \<le> ?i"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?i < wa'" by simp
        hence "snd (obs ! wa') \<in> set obs''" using obs wa' unfolding in_set_conv_nth
          by -(rule exI[where x="wa' - Suc (length obs')"], auto elim!: write_actions.cases actionsE simp add: action_obs_def lnth_llist_of actions_def nth_append map_eq_append_conv nth_Cons' split: split_if_asm)
        moreover from wa' have "is_write_action (snd (obs ! wa'))"
          by cases(auto simp add: action_obs_def nth_append actions_def split: split_if_asm)
        moreover from adal' wa' have "(ad, al) \<in> action_loc_aux P (snd (obs ! wa'))"
          by(auto simp add: action_obs_def nth_append nth_Cons' actions_def split: split_if_asm elim!: write_actions.cases)
        ultimately show False using last[of "snd (obs ! wa')"] b by simp
      qed
    next
      assume new_wa': "\<not> is_new_action (action_obs ?E wa')"
      with wa' adal' obtain v' where "NormalAction (WriteMem ad al v') \<in> set (map snd obs)"
        unfolding in_set_conv_nth
        by (fastsimp elim!: write_actions.cases is_write_action.cases simp add: action_obs_def actions_def nth_append split: split_if_asm intro!: exI[where x=wa'])
      from mrw_values_WriteMemD[OF this, of P vs0] mrw have b by simp
      with new obs_i have "\<not> is_new_action (action_obs ?E ?i)" by simp
      moreover
      have "wa' \<le> ?i"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?i < wa'" by simp
        hence "snd (obs ! wa') \<in> set obs''" using obs wa' unfolding in_set_conv_nth
          by -(rule exI[where x="wa' - Suc (length obs')"], auto elim!: write_actions.cases actionsE simp add: action_obs_def lnth_llist_of actions_def nth_append map_eq_append_conv nth_Cons' split: split_if_asm)
        moreover from wa' have "is_write_action (snd (obs ! wa'))"
          by cases(auto simp add: action_obs_def nth_append actions_def split: split_if_asm)
        moreover from adal' wa' have "(ad, al) \<in> action_loc_aux P (snd (obs ! wa'))"
          by(auto simp add: action_obs_def nth_append nth_Cons' actions_def split: split_if_asm elim!: write_actions.cases)
        ultimately have "is_new_action (snd (obs ! wa'))" using last[of "snd (obs ! wa')"] by simp
        moreover from new_wa' wa' have "\<not> is_new_action (snd (obs ! wa'))"
          by(auto elim!: write_actions.cases simp add: action_obs_def nth_append actions_def split: split_if_asm)
        ultimately show False by contradiction
      qed
      ultimately
      show "\<not> is_new_action (action_obs ?E ?i) \<and> wa' \<le> ?i" by blast
    qed
    thus "?E \<turnstile> wa' \<le>a ?i \<or> ?E \<turnstile> length obs \<le>a wa'" ..
  qed
  moreover from written `?i < length obs` obs_i
  have "value_written P (llist_of obs) ?i (ad, al) = v"
    by(simp add: value_written_def action_obs_def nth_append)
  ultimately show ?thesis by blast
qed

lemma mrw_values_no_write_unchanged:
  assumes no_write: "\<And>w. \<lbrakk> w \<in> set obs; is_write_action w; adal \<in> action_loc_aux P w \<rbrakk>
  \<Longrightarrow> case vs adal of None \<Rightarrow> False | Some (v, b) \<Rightarrow> b \<and> is_new_action w"
  shows "mrw_values P vs obs adal = vs adal"
using assms
proof(induct obs arbitrary: vs)
  case Nil show ?case by simp
next
  case (Cons ob obs)
  from Cons.prems[of ob]
  have "mrw_value P vs ob adal = vs adal"
    by(cases adal)(cases ob rule: mrw_value_cases, fastsimp+)
  moreover
  have "mrw_values P (mrw_value P vs ob) obs adal = mrw_value P vs ob adal"
  proof(rule Cons.hyps)
    fix w
    assume "w \<in> set obs" "is_write_action w" "adal \<in> action_loc_aux P w"
    with Cons.prems[of w] `mrw_value P vs ob adal = vs adal`
    show "case mrw_value P vs ob adal of None \<Rightarrow> False | \<lfloor>(v, b)\<rfloor> \<Rightarrow> b \<and> is_new_action w" by simp
  qed
  ultimately show ?case by simp
qed

section {* Coinductive version of sequentially consistent prefixes *}

coinductive ta_seq_consist :: "'m prog \<Rightarrow> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool) \<Rightarrow> obs_event action llist \<Rightarrow> bool"
for P :: "'m prog" 
where
  LNil: "ta_seq_consist P vs LNil"
| LCons:
  "\<lbrakk> case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True;
     ta_seq_consist P (mrw_value P vs ob) obs \<rbrakk> 
  \<Longrightarrow> ta_seq_consist P vs (LCons ob obs)"

inductive_simps ta_seq_consist_simps [simp]:
  "ta_seq_consist P vs LNil"
  "ta_seq_consist P vs (LCons ob obs)"

lemma ta_seq_consist_lappend:
  assumes "lfinite obs"
  shows "ta_seq_consist P vs (lappend obs obs') \<longleftrightarrow>
         ta_seq_consist P vs obs \<and> ta_seq_consist P (mrw_values P vs (list_of obs)) obs'"
  (is "?concl vs obs")
using assms
proof(induct arbitrary: vs)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI obs ob)
  have "?concl (mrw_value P vs ob) obs" by fact
  thus ?case using `lfinite obs` by(simp split: action.split add: list_of_LCons)
qed

lemma ta_seq_consist_coinduct_append [consumes 1, case_names ta_seq_consist, case_conclusion ta_seq_consist LNil lappend]:
  assumes major: "X vs obs"
  and step: "\<And>vs obs. X vs obs 
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> ta_seq_consist P vs obs' \<and>
                    (lfinite obs' \<longrightarrow> (X (mrw_values P vs (list_of obs')) obs'' \<or> 
                                       ta_seq_consist P (mrw_values P vs (list_of obs')) obs'')))"
    (is "\<And>vs obs. _ \<Longrightarrow> _ \<or> ?step vs obs")
  shows "ta_seq_consist P vs obs"
proof -
  from major
  have "\<exists>obs' obs''. obs = lappend (llist_of obs') obs'' \<and> ta_seq_consist P vs (llist_of obs') \<and> 
                     X (mrw_values P vs obs') obs''"
    by(auto intro: exI[where x="[]"])
  thus ?thesis
  proof(coinduct)
    case (ta_seq_consist vs obs)
    then obtain obs' obs'' 
      where obs: "obs = lappend (llist_of obs') obs''"
      and sc_obs': "ta_seq_consist P vs (llist_of obs')"
      and X: "X (mrw_values P vs obs') obs''" by blast

    show ?case
    proof(cases obs')
      case Nil
      with X have "X vs obs''" by simp
      from step[OF this] show ?thesis
      proof
        assume "obs'' = LNil" 
        with Nil obs show ?thesis by simp
      next
        assume "?step vs obs''"
        then obtain obs''' obs'''' 
          where obs'': "obs'' = lappend obs''' obs''''" and "obs''' \<noteq> LNil"
          and sc_obs''': "ta_seq_consist P vs obs'''" 
          and fin: "lfinite obs''' \<Longrightarrow> X (mrw_values P vs (list_of obs''')) obs'''' \<or>
                                      ta_seq_consist P (mrw_values P vs (list_of obs''')) obs''''"
          by blast
        from `obs''' \<noteq> LNil` obtain ob obs''''' where obs''': "obs''' = LCons ob obs'''''"
          unfolding neq_LNil_conv by blast
        with Nil obs'' obs have concl1: "obs = LCons ob (lappend obs''''' obs'''')" by simp
        have concl2: "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True"
          using sc_obs''' obs''' by simp

        show ?thesis
        proof(cases "lfinite obs'''")
          case False
          hence "lappend obs''''' obs'''' = obs'''''" using obs''' by(simp add: lappend_inf)
          hence "ta_seq_consist P (mrw_value P vs ob) (lappend obs''''' obs'''')" 
            using sc_obs''' obs''' by simp
          with concl1 concl2 have ?LCons by blast
          thus ?thesis by simp
        next
          case True
          with obs''' obtain obs'''''' where obs''''': "obs''''' = llist_of obs''''''"
            by simp(auto simp add: lfinite_eq_range_llist_of)
          from fin[OF True] have "?LCons"
          proof
            assume X: "X (mrw_values P vs (list_of obs''')) obs''''"
            hence "X (mrw_values P (mrw_value P vs ob) obs'''''') obs''''"
              using obs''''' obs''' by simp
            moreover from obs'''''
            have "lappend obs''''' obs'''' = lappend (llist_of obs'''''') obs''''" by simp
            moreover have "ta_seq_consist P (mrw_value P vs ob) (llist_of obs'''''')" 
              using sc_obs''' obs''' obs''''' by simp
            ultimately show ?thesis using concl1 concl2 by blast
          next
            assume "ta_seq_consist P (mrw_values P vs (list_of obs''')) obs''''"
            with sc_obs''' obs''''' obs'''
            have "ta_seq_consist P (mrw_value P vs ob) (lappend obs''''' obs'''')"
              by(simp add: ta_seq_consist_lappend)
            with concl1 concl2 show ?thesis by blast
          qed
          thus ?thesis by simp
        qed
      qed
    next
      case (Cons ob obs''')
      hence "obs = LCons ob (lappend (llist_of obs''') obs'')"
        using obs by simp
      moreover from sc_obs' Cons 
      have "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True"
        and "ta_seq_consist P (mrw_value P vs ob) (llist_of obs''')" by simp_all
      moreover from X Cons have "X (mrw_values P (mrw_value P vs ob) obs''') obs''" by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma ta_seq_consist_coinduct_append_wf
  [consumes 2, case_names ta_seq_consist, case_conclusion ta_seq_consist LNil lappend]:
  assumes major: "X vs obs a"
  and wf: "wf R"
  and step: "\<And>vs obs a. X vs obs a
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs'' a'. obs = lappend obs' obs'' \<and> ta_seq_consist P vs obs' \<and> (obs' = LNil \<longrightarrow> (a', a) \<in> R) \<and>
                        (lfinite obs' \<longrightarrow> X (mrw_values P vs (list_of obs')) obs'' a' \<or>
                                          ta_seq_consist P (mrw_values P vs (list_of obs')) obs''))"
    (is "\<And>vs obs a. _ \<Longrightarrow> _ \<or> ?step vs obs a")
  shows "ta_seq_consist P vs obs"
proof -
  { fix vs obs a
    assume "X vs obs a"
    with wf
    have "obs = LNil \<or> (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> ta_seq_consist P vs obs' \<and>
          (lfinite obs' \<longrightarrow> (\<exists>a. X (mrw_values P vs (list_of obs')) obs'' a) \<or> 
                            ta_seq_consist P (mrw_values P vs (list_of obs')) obs''))"
      (is "_ \<or> ?step_concl vs obs")
    proof(induct a arbitrary: vs obs rule: wf_induct[consumes 1, case_names wf])
      case (wf a)
      note IH = wf.hyps[rule_format]
      from step[OF `X vs obs a`]
      show ?case
      proof
        assume "obs = LNil" thus ?thesis ..
      next
        assume "?step vs obs a"
        then obtain obs' obs'' a'
          where obs: "obs = lappend obs' obs''"
          and sc_obs': "ta_seq_consist P vs obs'"
          and decr: "obs' = LNil \<Longrightarrow> (a', a) \<in> R"
          and fin: "lfinite obs' \<Longrightarrow> 
                    X (mrw_values P vs (list_of obs')) obs'' a' \<or>
                    ta_seq_consist P (mrw_values P vs (list_of obs')) obs''"
          by blast
        show ?case
        proof(cases "obs' = LNil")
          case True
          hence "lfinite obs'" by simp
          from fin[OF this] show ?thesis
          proof
            assume X: "X (mrw_values P vs (list_of obs')) obs'' a'"
            from True have "(a', a) \<in> R" by(rule decr)
            from IH[OF this X] show ?thesis
            proof
              assume "obs'' = LNil"
              with True obs have "obs = LNil" by simp
              thus ?thesis ..
            next
              assume "?step_concl (mrw_values P vs (list_of obs')) obs''"
              hence "?step_concl vs obs" using True obs by simp
              thus ?thesis ..
            qed
          next
            assume "ta_seq_consist P (mrw_values P vs (list_of obs')) obs''"
            thus ?thesis using obs True
              by cases(auto cong: action.case_cong obs_event.case_cong intro: exI[where x="LCons x LNil", standard])
          qed
        next
          case False
          with obs sc_obs' fin show ?thesis by auto
        qed
      qed
    qed }
  note step' = this

  from major have "\<exists>a. X vs obs a" ..
  thus ?thesis
  proof(coinduct rule: ta_seq_consist_coinduct_append)
    case (ta_seq_consist vs obs)
    then obtain a where "X vs obs a" ..
    thus ?case by(rule step')
  qed
qed

lemma ta_seq_consist_nthI:
  assumes "\<And>i ad al v. \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v) \<rbrakk> 
          \<Longrightarrow> \<exists>b. mrw_values P vs (list_of (ltake (enat i) obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "ta_seq_consist P vs obs"
proof -
  from assms 
  have "\<forall>i ad al v. enat i < llength obs \<longrightarrow> lnth obs i = NormalAction (ReadMem ad al v) \<longrightarrow>
        (\<exists>b. mrw_values P vs (list_of (ltake (enat i) obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>)" by blast
  thus ?thesis
  proof(coinduct rule: ta_seq_consist.coinduct)
    case (ta_seq_consist vs obs)
    hence nth: "\<And>i ad al v. \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v) \<rbrakk> 
               \<Longrightarrow> \<exists>b. mrw_values P vs (list_of (ltake (enat i) obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>" by blast
    show ?case
    proof(cases obs)
      case LNil thus ?thesis by simp
    next
      case (LCons ob obs')
      { fix ad al v
        assume "ob = NormalAction (ReadMem ad al v)"
        with nth[of 0 ad al v] LCons
        have "\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
          by(simp add: zero_enat_def[symmetric]) }
      moreover { 
        fix i ad al v
        assume "enat i < llength obs'" "lnth obs' i = NormalAction (ReadMem ad al v)"
        with LCons nth[of "Suc i" ad al v]
        have "\<exists>b. mrw_values P (mrw_value P vs ob) (list_of (ltake (enat i) obs')) (ad, al) = \<lfloor>(v, b)\<rfloor>"
          by(simp add: iSuc_enat[symmetric]) }
      ultimately have ?LCons using LCons by(simp split: action.split obs_event.split)
      thus ?thesis ..
    qed
  qed
qed

locale executions_sc =
  executions_base \<E> P
  for \<E> :: "execution set"
  and P :: "'m prog" +
  assumes \<E>_new_actions_for_fun:
  "\<lbrakk> E \<in> \<E>; a \<in> new_actions_for P E adal; a' \<in> new_actions_for P E adal \<rbrakk> \<Longrightarrow> a = a'"
  and \<E>_ex_new_action:
  "\<lbrakk> E \<in> \<E>; ra \<in> read_actions E; adal \<in> action_loc P E ra \<rbrakk>
  \<Longrightarrow> \<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
begin

lemma \<E>_new_same_addr_singleton:
  assumes E: "E \<in> \<E>"
  shows "\<exists>a. new_actions_for P E adal \<subseteq> {a}"
by(blast dest: \<E>_new_actions_for_fun[OF E])

lemma new_action_before_read:
  assumes E: "E \<in> \<E>"
  and ra: "ra \<in> read_actions E"
  and adal: "adal \<in> action_loc P E ra"
  and new: "wa \<in> new_actions_for P E adal"
  shows "wa < ra"
using \<E>_new_same_addr_singleton[OF E, of adal] \<E>_ex_new_action[OF E ra adal] new
by auto

lemma most_recent_write_exists:
  assumes E: "E \<in> \<E>"
  and ra: "ra \<in> read_actions E"
  shows "\<exists>wa. P,E \<turnstile> ra \<leadsto>mrw wa"
proof -
  from ra obtain ad al where
    adal: "(ad, al) \<in> action_loc P E ra"
    by(rule read_action_action_locE)

  def Q == "{a. a \<in> write_actions E \<and> (ad, al) \<in> action_loc P E a \<and> E \<turnstile> a \<le>a ra}"
  let ?A = "new_actions_for P E (ad, al)"
  let ?B = "{a. a \<in> actions E \<and> (\<exists>v'. action_obs E a = NormalAction (WriteMem ad al v')) \<and> a \<le> ra}"

  have "Q \<subseteq> ?A \<union> ?B" unfolding Q_def
    by(auto elim!: write_actions.cases action_loc_aux_cases simp add: new_actions_for_def elim: action_orderE)
  moreover from \<E>_new_same_addr_singleton[OF E, of "(ad, al)"]
  have "finite ?A" by(blast intro: finite_subset)
  moreover have "finite ?B" by auto
  ultimately have finQ: "finite Q" 
    by(blast intro: finite_subset)

  from \<E>_ex_new_action[OF E ra adal] ra obtain wa 
    where wa: "wa \<in> Q" unfolding Q_def
    by(fastsimp elim!: new_actionsE is_new_action.cases read_actions.cases intro: write_actionsI action_orderI)
   
  def wa' == "Max_torder (action_order E) Q"

  from wa have "Q \<noteq> {}" "Q \<subseteq> actions E" by(auto simp add: Q_def)
  with finQ have "wa' \<in> Q" unfolding wa'_def
    by(rule Max_torder_in_set[OF torder_action_order])
  hence "E \<turnstile> wa' \<le>a ra" "wa' \<in> write_actions E"
    and "(ad, al) \<in> action_loc P E wa'" by(simp_all add: Q_def)
  with ra adal have "P,E \<turnstile> ra \<leadsto>mrw wa'"
  proof
    fix wa''
    assume wa'': "wa'' \<in> write_actions E" "(ad, al) \<in> action_loc P E wa''"
    from `wa'' \<in> write_actions E` ra
    have "ra \<noteq> wa''" by(auto dest: read_actions_not_write_actions)
    show "E \<turnstile> wa'' \<le>a wa' \<or> E \<turnstile> ra \<le>a wa''"
    proof(rule disjCI)
      assume "\<not> E \<turnstile> ra \<le>a wa''"
      with total_onPD[OF total_action_order, of ra E wa''] 
        `ra \<noteq> wa''` `ra \<in> read_actions E` `wa'' \<in> write_actions E`
      have "E \<turnstile> wa'' \<le>a ra" by simp
      with wa'' have "wa'' \<in> Q" by(simp add: Q_def)
      with finQ show "E \<turnstile> wa'' \<le>a wa'"
        using `Q \<subseteq> actions E` unfolding wa'_def
        by(rule Max_torder_above[OF torder_action_order])
    qed
  qed
  thus ?thesis ..
qed


lemma mrw_before:
  assumes E: "E \<in> \<E>"
  and mrw: "P,E \<turnstile> r \<leadsto>mrw w"
  shows "w < r"
using mrw read_actions_not_write_actions[of r E]
apply cases
apply(erule action_orderE)
 apply(erule (1) new_action_before_read[OF E])
 apply(simp add: new_actions_for_def)
apply(cases "w = r")
apply auto
done

lemma action_order_write_readD:
  "\<lbrakk> E \<in> \<E>; E \<turnstile> w \<le>a r; r \<in> read_actions E; w \<in> write_actions E; adal \<in> action_loc P E r; adal \<in> action_loc P E w \<rbrakk>
  \<Longrightarrow> w < r"
apply(erule action_orderE)
 apply(frule (2) new_actionsI)
 apply(frule \<E>_new_same_addr_singleton[where adal=adal])
 apply(frule (2) \<E>_ex_new_action)
 apply blast
apply(cases "w=r")
 apply clarify
 apply(blast dest: read_actions_not_write_actions)
apply simp
done


lemma sequentially_consistent_most_recent_write_for:
  "E \<in> \<E> \<Longrightarrow> sequentially_consistent P (E, \<lambda>r. THE w. P,E \<turnstile> r \<leadsto>mrw w)"
by(rule sequentially_consistentI)(auto dest: most_recent_write_exists simp add: THE_most_recent_writeI)

lemma ta_seq_consist_imp_sequentially_consistent:
  assumes E: "E \<in> \<E>"
  and tsa_ok: "thread_start_actions_ok E"
  and seq: "ta_seq_consist P empty (lmap snd E)"
  shows "\<exists>ws. sequentially_consistent P (E, ws) \<and> P \<turnstile> (E, ws) \<surd>"
proof(intro exI conjI)
  def ws == "\<lambda>i. THE w. P,E \<turnstile> i \<leadsto>mrw w"
  from E show "sequentially_consistent P (E, ws)"
    unfolding ws_def by(rule sequentially_consistent_most_recent_write_for)
    
  show "P \<turnstile> (E, ws) \<surd>"
  proof(rule wf_execI)
    show "is_write_seen P E ws"
    proof(rule is_write_seenI)
      fix a ad al v
      assume a: "a \<in> read_actions E"
        and adal: "action_obs E a = NormalAction (ReadMem ad al v)"
      from most_recent_write_exists[OF E a]
      obtain w where mrw: "P,E \<turnstile> a \<leadsto>mrw w" ..
      hence w: "ws a = w" by(simp add: ws_def THE_most_recent_writeI)
      with mrw adal

      show "ws a \<in> write_actions E"
        and "(ad, al) \<in> action_loc P E (ws a)"
        and "\<not> P,E \<turnstile> a \<le>hb ws a"
        by(fastsimp elim!: most_recent_write_for.cases dest: happens_before_into_action_order antisymPD[OF antisym_action_order] read_actions_not_write_actions)+

      let ?between = "ltake (enat (a - Suc w)) (ldropn (Suc w) E)"
      let ?prefix = "ltake (enat w) E"
      let ?vs_prefix = "mrw_values P empty (map snd (list_of ?prefix))"

      from E mrw have "w < a" by(rule mrw_before)

      { fix v'
        assume new: "is_new_action (action_obs E w)"
          and vs': "?vs_prefix (ad, al) = \<lfloor>(v', True)\<rfloor>"
        from mrw_values_eq_SomeD[OF vs']
        obtain obs' wa obs'' where split: "map snd (list_of ?prefix) = obs' @ wa # obs''"
          and wa: "is_write_action wa"
          and adal': "(ad, al) \<in> action_loc_aux P wa"
          and new_wa: "\<not> is_new_action wa" by blast
        from split have "length (map snd (list_of ?prefix)) = Suc (length obs' + length obs'')" by simp
        hence len_prefix: "llength ?prefix = enat \<dots>" by(simp add: length_list_of_conv_the_enat min_enat1_conv_enat)
        with split have "nth (map snd (list_of ?prefix)) (length obs') = wa"
          and "enat (length obs') < llength ?prefix" by simp_all
        hence "snd (lnth ?prefix (length obs')) = wa" by(simp add: list_of_lmap[symmetric] del: list_of_lmap)
        hence wa': "action_obs E (length obs') = wa" and "enat (length obs') < llength E"
          using `enat (length obs') < llength ?prefix` by(auto simp add: action_obs_def lnth_ltake)
        with wa have "length obs' \<in> write_actions E" by(auto intro: write_actions.intros simp add: actions_def)
        from most_recent_write_recent[OF mrw _ this, of "(ad, al)"] adal adal' wa'
        have "E \<turnstile> length obs' \<le>a w \<or> E \<turnstile> a \<le>a length obs'" by simp
        hence False using new_wa new wa' adal len_prefix `w < a`
          by(auto elim!: action_orderE simp add: min_enat1_conv_enat split: enat.split_asm) 
      }
      hence mrw_value_w: "mrw_value P ?vs_prefix (snd (lnth E w)) (ad, al) =
                          \<lfloor>(value_written P E w (ad, al), \<not> is_new_action (action_obs E w))\<rfloor>"
        using `ws a \<in> write_actions E` `(ad, al) \<in> action_loc P E (ws a)` w
        by(cases "snd (lnth E w)" rule: mrw_value_cases)(fastsimp elim: write_actions.cases simp add: value_written_def action_obs_def)+
      have "mrw_values P (mrw_value P ?vs_prefix (snd (lnth E w))) (list_of (lmap snd ?between)) (ad, al) = \<lfloor>(value_written P E w (ad, al), \<not> is_new_action (action_obs E w))\<rfloor>"
      proof(subst mrw_values_no_write_unchanged)
        fix wa
        assume "wa \<in> set (list_of (lmap snd ?between))"
          and write_wa: "is_write_action wa"
          and adal_wa: "(ad, al) \<in> action_loc_aux P wa"
        hence wa: "wa \<in> lset (lmap snd ?between)" by simp
        from wa obtain i_wa where "wa = lnth (lmap snd ?between) i_wa"
          and i_wa: "enat i_wa < llength (lmap snd ?between)"
          unfolding lset_def by blast
        moreover hence i_wa_len: "enat (Suc (w + i_wa)) < llength E" by(cases "llength E") auto
        ultimately have wa': "wa = action_obs E (Suc (w + i_wa))"
          by(simp_all add: lnth_ltake action_obs_def add_ac)
        with write_wa i_wa_len have "Suc (w + i_wa) \<in> write_actions E"
          by(auto intro: write_actions.intros simp add: actions_def)
        from most_recent_write_recent[OF mrw _ this, of "(ad, al)"] adal adal_wa wa'
        have "E \<turnstile> Suc (w + i_wa) \<le>a w \<or> E \<turnstile> a \<le>a Suc (w + i_wa)" by(simp)
        hence "is_new_action wa \<and> \<not> is_new_action (action_obs E w)"
          using adal i_wa wa' by(auto elim: action_orderE)
        thus "case (mrw_value P ?vs_prefix (snd (lnth E w)) (ad, al)) of None \<Rightarrow> False | Some (v, b) \<Rightarrow> b \<and> is_new_action wa"
          unfolding mrw_value_w by simp
      qed(simp add: mrw_value_w)

      moreover

      from a have "a \<in> actions E" by simp
      hence "enat a < llength E" by(rule actionsE)
      with `w < a` have "enat (a - Suc w) < llength E - enat (Suc w)"
        by(cases "llength E") simp_all
      hence "E = lappend (lappend ?prefix (LCons (lnth E w) ?between)) (LCons (lnth (ldropn (Suc w) E) (a - Suc w)) (ldropn (Suc (a - Suc w)) (ldropn (Suc w) E)))"
        using `w < a` `enat a < llength E` unfolding lappend_assoc lappend_LCons
        apply(subst ldropn_Suc_conv_ldropn, simp)
        apply(subst lappend_ltake_enat_ldropn)
        apply(subst ldropn_Suc_conv_ldropn, simp add: less_trans[where y="enat a"])
        by simp
      hence E': "E = lappend (lappend ?prefix (LCons (lnth E w) ?between)) (LCons (lnth E a) (ldropn (Suc a) E))"
        using `w < a` `enat a < llength E` by simp
      
      from seq have "ta_seq_consist P (mrw_values P empty (list_of (lappend (lmap snd ?prefix) (LCons (snd (lnth E w)) (lmap snd ?between))))) (lmap snd (LCons (lnth E a) (ldropn (Suc a) E)))"
        by(subst (asm) E')(simp add: lmap_lappend_distrib ta_seq_consist_lappend)
      ultimately show "value_written P E (ws a) (ad, al) = v" using adal w
        by(clarsimp simp add: action_obs_def list_of_lappend list_of_LCons)

      (* assume "is_volatile P al" *)
      show "\<not> P,E \<turnstile> a \<le>so ws a" using `w < a` w adal by(auto elim!: action_orderE sync_orderE)

      fix a'
      assume a': "a' \<in> write_actions E" "(ad, al) \<in> action_loc P E a'"

      {
        presume "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a"
        with mrw adal a' have "a' = ws a" unfolding w
          by cases(fastsimp dest: antisymPD[OF antisym_action_order] read_actions_not_write_actions elim!: meta_allE[where x=a'])
        thus "a' = ws a" "a' = ws a" by -
      next
        assume "P,E \<turnstile> ws a \<le>hb a'" "P,E \<turnstile> a' \<le>hb a"
        thus "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a" using a' by(blast intro: happens_before_into_action_order)+
      next
        assume "is_volatile P al" "P,E \<turnstile> ws a \<le>so a'" "P,E \<turnstile> a' \<le>so a"
        thus "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a" by(auto elim: sync_orderE)
      }
    qed
  qed(rule tsa_ok)
qed

end

section {* Cut-and-update and sequentially consistent completion *}

inductive foldl_list_all2 ::
  "('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'a \<Rightarrow> bool"
for f and P and Q
where
  "foldl_list_all2 f P Q [] [] s"
| "\<lbrakk> Q x y s; P x y s \<Longrightarrow> foldl_list_all2 f P Q xs ys (f x y s) \<rbrakk> \<Longrightarrow> foldl_list_all2 f P Q (x # xs) (y # ys) s"

inductive_simps foldl_list_all2_simps [simp]:
  "foldl_list_all2 f P Q [] ys s"
  "foldl_list_all2 f P Q xs [] s"
  "foldl_list_all2 f P Q (x # xs) (y # ys) s"

inductive_simps foldl_list_all2_Cons1:
  "foldl_list_all2 f P Q (x # xs) ys s"

inductive_simps foldl_list_all2_Cons2:
  "foldl_list_all2 f P Q xs (y # ys) s"

definition eq_upto_seq_inconsist ::
  "'m prog \<Rightarrow> obs_event action list \<Rightarrow> obs_event action list \<Rightarrow> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool) \<Rightarrow> bool"
where
  "eq_upto_seq_inconsist P =
   foldl_list_all2 (\<lambda>ob ob' vs. mrw_value P vs ob) 
                   (\<lambda>ob ob' vs. case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = Some (v, b) | _ \<Rightarrow> True)
                   (\<lambda>ob ob' vs. if (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = Some (v, b) | _ \<Rightarrow> True) then ob = ob' else ob \<approx> ob')"

lemma eq_upto_seq_inconsist_simps:
  "eq_upto_seq_inconsist P [] obs' vs \<longleftrightarrow> obs' = []"
  "eq_upto_seq_inconsist P obs [] vs \<longleftrightarrow> obs = []"
  "eq_upto_seq_inconsist P (ob # obs) (ob' # obs') vs \<longleftrightarrow> 
   (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> 
      if (\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>) 
      then ob = ob' \<and> eq_upto_seq_inconsist P obs obs' (mrw_value P vs ob) 
      else ob \<approx> ob'
    | _ \<Rightarrow> ob = ob' \<and> eq_upto_seq_inconsist P obs obs' (mrw_value P vs ob))"
by(auto simp add: eq_upto_seq_inconsist_def split: action.split obs_event.split)

lemma eq_upto_seq_inconsist_Cons1:
  "eq_upto_seq_inconsist P (ob # obs) obs' vs \<longleftrightarrow>
   (\<exists>ob' obs''. obs' = ob' # obs'' \<and> 
      (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> 
         if (\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>) 
         then ob' = ob \<and> eq_upto_seq_inconsist P obs obs'' (mrw_value P vs ob)
         else ob \<approx> ob'
       | _ \<Rightarrow> ob' = ob \<and> eq_upto_seq_inconsist P obs obs'' (mrw_value P vs ob)))"
unfolding eq_upto_seq_inconsist_def
by(auto split: obs_event.split action.split simp add: foldl_list_all2_Cons1)

lemma eq_upto_seq_inconsist_appendD:
  assumes "eq_upto_seq_inconsist P (obs @ obs') obs'' vs"
  and "ta_seq_consist P vs (llist_of obs)"
  shows "length obs \<le> length obs''" (is ?thesis1)
  and "take (length obs) obs'' = obs" (is ?thesis2)
  and "eq_upto_seq_inconsist P obs' (drop (length obs) obs'') (mrw_values P vs obs)" (is ?thesis3)
using assms
by(induct obs arbitrary: obs'' vs)(auto split: action.split_asm obs_event.split_asm simp add: eq_upto_seq_inconsist_Cons1)

lemma ta_seq_consist_imp_eq_upto_seq_inconsist_refl:
  "ta_seq_consist P vs (llist_of obs) \<Longrightarrow> eq_upto_seq_inconsist P obs obs vs"
apply(induct obs arbitrary: vs)
apply(auto simp add: eq_upto_seq_inconsist_simps split: action.split obs_event.split)
done

context executions_sc begin

lemma ta_seq_consist_mrwI:
  assumes E: "E \<in> \<E>"
  and wf: "P \<turnstile> (E, ws) \<surd>"
  and mrw: "\<And>a. \<lbrakk> enat a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
  shows "ta_seq_consist P empty (lmap snd (ltake r E))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume i_len: "enat i < llength (lmap snd (ltake r E))"
    and E_i: "lnth (lmap snd (ltake r E)) i = NormalAction (ReadMem ad al v)"
  from i_len have "enat i < r" by simp
  from i_len have "i \<in> actions E" by(simp add: actions_def)
  moreover from E_i i_len have obs_i: "action_obs E i = NormalAction (ReadMem ad al v)"
    by(simp add: action_obs_def lnth_ltake)
  ultimately have read: "i \<in> read_actions E" ..
  with i_len have mrw_i: "P,E \<turnstile> i \<leadsto>mrw ws i" by(auto intro: mrw)
  with E have "ws i < i" by(rule mrw_before)

  from mrw_i obs_i obtain adal_w: "(ad, al) \<in> action_loc P E (ws i)"
    and adal_r: "(ad, al) \<in> action_loc P E i"
    and "write": "ws i \<in> write_actions E" by cases auto
  
  from wf have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
  from is_write_seenD[OF this read obs_i]
  have vw_v: "value_written P E (ws i) (ad, al) = v" by simp

  let ?vs = "mrw_values P empty (map snd (list_of (ltake (enat (ws i)) E)))"

  from `ws i < i` i_len have "enat (ws i) < llength (ltake (enat i) E)"
    by(simp add: less_trans[where y="enat i"])
  hence "ltake (enat i) E = lappend (ltake (enat (ws i)) (ltake (enat i) E)) (LCons (lnth (ltake (enat i) E) (ws i)) (ldropn (Suc (ws i)) (ltake (enat i) E)))"
    by(simp only: ldropn_Suc_conv_ldropn lappend_ltake_enat_ldropn)
  also have "\<dots> = lappend (ltake (enat (ws i)) E) (LCons (lnth E (ws i)) (ldropn (Suc (ws i)) (ltake (enat i) E)))"
    using `ws i < i` i_len `enat (ws i) < llength (ltake (enat i) E)` 
    by(simp add: lnth_ltake)(simp add: min_def)
  finally have r_E: "ltake (enat i) E = \<dots>" .

  have "mrw_values P empty (list_of (ltake (enat i) (lmap snd (ltake r E)))) (ad, al)
    = mrw_values P empty (map snd (list_of (ltake (enat i) E))) (ad, al)"
    using `enat i < r` by(auto simp add: min_def)
  also have "\<dots> = mrw_values P (mrw_value P ?vs (snd (lnth E (ws i)))) (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E)))) (ad, al)"
    by(subst r_E)(simp add: list_of_lappend)
  also have "\<dots> = mrw_value P ?vs (snd (lnth E (ws i))) (ad, al)"
  proof(rule mrw_values_no_write_unchanged)
    fix wa
    assume wa: "wa \<in> set (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))))"
      and "is_write_action wa" "(ad, al) \<in> action_loc_aux P wa"

    from wa obtain w where "w < length (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))))"
      and "map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))) ! w = wa"
      unfolding in_set_conv_nth by blast
    moreover hence "Suc (ws i + w) < i" (is "?w < _") using i_len 
      by(cases "llength E")(simp_all add: length_list_of_conv_the_enat)
    ultimately have obs_w': "action_obs E ?w = wa" using i_len
      by(simp add: action_obs_def lnth_ltake less_trans[where y="enat i"] add_ac)
    from `?w < i` i_len have "?w \<in> actions E"
      by(simp add: actions_def less_trans[where y="enat i"])
    with `is_write_action wa` obs_w' `(ad, al) \<in> action_loc_aux P wa`
    have write': "?w \<in> write_actions E" 
      and adal': "(ad, al) \<in> action_loc P E ?w"
      by(auto intro: write_actions.intros)
      
    from `?w < i` `i \<in> read_actions E` `?w \<in> actions E`
    have "E \<turnstile> ?w \<le>a i" by(auto simp add: action_order_def elim: read_actions.cases)

    from mrw_i adal_r write' adal'
    have "E \<turnstile> ?w \<le>a ws i \<or> E \<turnstile> i \<le>a ?w" by(rule most_recent_write_recent)
    hence "E \<turnstile> ?w \<le>a ws i"
    proof
      assume "E \<turnstile> i \<le>a ?w"
      with `E \<turnstile> ?w \<le>a i` have "?w = i" by(rule antisymPD[OF antisym_action_order])
      with write' read have False by(auto dest: read_actions_not_write_actions)
      thus ?thesis ..
    qed

    from adal_w "write" have "mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) \<noteq> None"
      by(cases "snd (lnth E (ws i))" rule: mrw_value_cases)
        (auto simp add: action_obs_def split: split_if_asm elim: write_actions.cases)
    then obtain b v where vb: "mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) = Some (v, b)" by auto
    moreover
    from `E \<turnstile> ?w \<le>a ws i` obs_w'
    have "is_new_action wa" "\<not> is_new_action (action_obs E (ws i))" by(auto elim!: action_orderE)
    from `\<not> is_new_action (action_obs E (ws i))` "write" adal_w
    obtain v' where "action_obs E (ws i) = NormalAction (WriteMem ad al v')"
      by(auto elim!: write_actions.cases is_write_action.cases)
    with vb have b by(simp add: action_obs_def)
    with `is_new_action wa` vb 
    show "case mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) of None \<Rightarrow> False | \<lfloor>(v, b)\<rfloor> \<Rightarrow> b \<and> is_new_action wa" by simp
  qed
  also {
    fix v
    assume "?vs (ad, al) = Some (v, True)"
      and "is_new_action (action_obs E (ws i))"
    
    from mrw_values_eq_SomeD[OF this(1)]
    obtain wa where "wa \<in> set (map snd (list_of (ltake (enat (ws i)) E)))"
      and "is_write_action wa"
      and "(ad, al) \<in> action_loc_aux P wa"
      and "\<not> is_new_action wa" by(fastsimp simp del: set_map)
    moreover then obtain w where w: "w < ws i"  and wa: "wa = snd (lnth E w)"
      unfolding in_set_conv_nth by(cases "llength E")(auto simp add: lnth_ltake length_list_of_conv_the_enat)
    ultimately have "w \<in> write_actions E" "action_obs E w = wa" "(ad, al) \<in> action_loc P E w"
      using `ws i \<in> write_actions E`
      by(auto intro!: write_actions.intros simp add: actions_def less_trans[where y="enat (ws i)"] action_obs_def elim!: write_actions.cases)
    with mrw_i adal_r have "E \<turnstile> w \<le>a ws i \<or> E \<turnstile> i \<le>a w" by -(rule most_recent_write_recent)
    hence False
    proof
      assume "E \<turnstile> w \<le>a ws i"
      moreover from `\<not> is_new_action wa` `is_new_action (action_obs E (ws i))` "write" w wa `w \<in> write_actions E`
      have "E \<turnstile> ws i \<le>a w" by(auto simp add: action_order_def action_obs_def)
      ultimately have "w = ws i" by(rule antisymPD[OF antisym_action_order])
      with `w < ws i` show False by simp
    next
      assume "E \<turnstile> i \<le>a w"
      moreover from `w \<in> write_actions E` `w < ws i` `ws i < i` read
      have "E \<turnstile> w \<le>a i" by(auto simp add: action_order_def elim: read_actions.cases)
      ultimately have "i = w" by(rule antisymPD[OF antisym_action_order])
      with `w < ws i` `ws i < i` show False by simp
    qed }
  then obtain b where "\<dots> = Some (v, b)" using vw_v "write" adal_w
    apply(atomize_elim)
    apply(auto simp add: action_obs_def value_written_def write_actions_iff)
    apply(erule is_write_action.cases)
    apply auto
    apply blast+
    done
  finally show "\<exists>b. mrw_values P empty (list_of (ltake (enat i) (lmap snd (ltake r E)))) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    by blast
qed

end

locale jmm_\<tau>multithreaded = \<tau>multithreaded +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l, 't, 'x, 'm, 'w, obs_event action) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> obs_event action list" 
  and \<tau>move :: "('l, 't, 'x, 'm, 'w, obs_event action) \<tau>moves" 
  fixes P :: "'md prog"
begin

primrec complete_sc_aux :: "(('l,'t,'x,'m,'w) state \<times> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool)) \<Rightarrow> 
  ((('t \<times> ('l, 't, 'x, 'm, 'w, obs_event action list) thread_action) \<times> 
    ('l,'t,'x,'m,'w) state \<times> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool)) + 
   ('l, 't, 'x, 'm, 'w) state option)"
where
  "complete_sc_aux (s, vs) =
   (if (\<exists>s'. \<tau>mredT^** s s' \<and> (\<forall>tta s''. \<not> redT s' tta s''))
    then Inr (Some (SOME s'. \<tau>mredT^** s s' \<and> (\<forall>tta s''. \<not> redT s' tta s'')))
    else if mthr.\<tau>diverge s then Inr None
    else let ((t, ta), s'') = 
             SOME ((t, ta), s''). \<exists>s'. \<tau>mredT^** s s' \<and> redT s' (t, ta) s'' \<and> \<not> m\<tau>move s' (t, ta) s'' \<and> 
                                       ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)
         in Inl ((t, ta), (s'', mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"

declare complete_sc_aux.simps [simp del]

definition complete_sc :: "('l,'t,'x,'m,'w) state \<Rightarrow> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool) \<Rightarrow> 
  ('t \<times> ('l, 't, 'x, 'm, 'w, obs_event action list) thread_action, ('l, 't, 'x, 'm, 'w) state option) tllist"
where "complete_sc s vs = tllist_corec (s, vs) complete_sc_aux"

definition sc_completion :: "('l, 't, 'x, 'm, 'w) state \<Rightarrow> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool) \<Rightarrow> bool"
where
  "sc_completion s vs \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m'.
       mthr.\<tau>rtrancl3p s ttas s' \<longrightarrow> ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow>
       \<not> \<tau>move (x, shr s') ta (x', m') \<longrightarrow>
       (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                      ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))"

lemma sc_completionD:
  "\<lbrakk> sc_completion s vs; mthr.\<tau>rtrancl3p s ttas s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))); 
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta; \<not> \<tau>move (x, shr s') ta (x', m') \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
unfolding sc_completion_def by blast

lemma sc_completionI:
  "(\<And>ttas s' t x ta x' m'. 
     \<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))); 
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta; \<not> \<tau>move (x, shr s') ta (x', m') \<rbrakk>
     \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))
  \<Longrightarrow> sc_completion s vs"
unfolding sc_completion_def by blast

lemma sc_completion_shift:
  assumes sc_c: "sc_completion s vs"
  and \<tau>Red: "\<tau>trsys.\<tau>rtrancl3p redT m\<tau>move s ttas s'"
  and sc: "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of ttas)))"
  shows "sc_completion s' (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
proof(rule sc_completionI)
  fix ttas' s'' t x ta x' m'
  assume \<tau>Red': "mthr.\<tau>rtrancl3p s' ttas' s''"
    and sc': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
    and red: "thr s'' t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s''\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok s'' t ta" 
      "\<not> \<tau>move (x, shr s'') ta (x', m')"
  from \<tau>Red \<tau>Red' have "mthr.\<tau>rtrancl3p s (ttas @ ttas') s''" by(rule mthr.\<tau>rtrancl3p_trans)
  moreover from sc sc' have "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ ttas'))))"
    apply(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
    apply(simp add: lconcat_llist_of[symmetric] lmap_llist_of[symmetric] lmap_compose[symmetric] o_def split_def del: lmap_llist_of lmap_compose)
    done
  ultimately
  show "\<exists>ta' x'' m''. t \<turnstile> \<langle>x, shr s''\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle> \<and> actions_ok s'' t ta' \<and> \<not> \<tau>move (x, shr s'') ta' (x'', m'') \<and>
         ta_seq_consist P (mrw_values P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
    using red unfolding foldl_append[symmetric] concat_append[symmetric] map_append[symmetric]
    by(rule sc_completionD[OF sc_c])
qed

lemma complete_sc_in_\<tau>Runs:
  assumes cau: "sc_completion s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "mthr.\<tau>Runs s (complete_sc s vs)"
proof -
  def s' \<equiv> s and vs' \<equiv> vs
  def ttas \<equiv> "complete_sc s' vs'"
  let ?ttas' = "\<lambda>ttas' :: ('t \<times> ('l,'t,'x,'m,'w,obs_event action list) thread_action) list.
               concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')"
  let "?vs ttas'" = "mrw_values P vs (?ttas' ttas')"
  from s'_def vs'_def
  have "mthr.\<tau>rtrancl3p s [] s'" "ta_seq_consist P vs (llist_of (?ttas' []))" "vs' = ?vs []"
    by(auto simp add: mthr.\<tau>rtrancl3p_Nil_eq_\<tau>moves)
  hence "\<exists>ttas'. ttas = complete_sc s' (?vs ttas') \<and> mthr.\<tau>rtrancl3p s ttas' s' \<and> ta_seq_consist P vs (llist_of (?ttas' ttas'))"
    unfolding ttas_def by blast
  thus "mthr.\<tau>Runs s' ttas"
  proof(coinduct s' ttas rule: mthr.\<tau>Runs.coinduct)
    case (\<tau>Runs s' ttas)
    then obtain ttas' where ttas: "ttas = complete_sc s' (?vs ttas')"
      and Red: "mthr.\<tau>rtrancl3p s ttas' s'"
      and sc: "ta_seq_consist P vs (llist_of (?ttas' ttas'))" by blast
    let "?halt s''" = "\<tau>mredT^** s' s'' \<and> (\<forall>tta s'''. \<not> redT s'' tta s''')"
    let "?diverge" = "mthr.\<tau>diverge s'"
    let "?proceed" = "\<lambda>(s'', (t', ta'), s'''). \<tau>mredT^** s' s'' \<and> redT s'' (t', ta') s''' \<and> \<not> m\<tau>move s'' (t', ta') s'''"

    show ?case
    proof(cases "\<exists>s''. ?halt s''")
      case True
      then obtain s'' where "?halt s''" ..
      hence "?halt (Eps ?halt)" by(rule someI)
      moreover from True have "ttas = TNil \<lfloor>Eps ?halt\<rfloor>" unfolding ttas complete_sc_def
        by(subst tllist_corec) (simp add: complete_sc_aux.simps)
      ultimately have ?Terminate by simp
      thus ?thesis by simp
    next
      case False
      note no_halt = this
      show ?thesis
      proof(cases "?diverge")
        case True
        with no_halt have "ttas = TNil None" unfolding ttas complete_sc_def
          by(subst tllist_corec)(simp add: complete_sc_aux.simps)
        thus ?thesis using True by simp
      next
        case False

        let ?proceed' = "\<lambda>((t', ta'), s'''). \<exists>s''. \<tau>mredT^** s' s'' \<and> redT s'' (t', ta') s''' \<and> \<not> m\<tau>move s'' (t', ta') s''' \<and> 
                        ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"

        from mthr.not_\<tau>diverge_to_no_\<tau>move[OF False]
        obtain s'' where s'_s'': "\<tau>mredT^** s' s''"
          and no_\<tau>: "\<And>s'''. \<not> \<tau>mredT s'' s'''" by blast
        from s'_s'' no_halt obtain t' ta' s''' where red: "s'' -t'\<triangleright>ta'\<rightarrow> s'''"
          by(auto simp del: split_paired_Ex split_paired_All)
        with no_\<tau>[of s'''] have "\<not> m\<tau>move s'' (t', ta') s'''" by auto
        from mthr.\<tau>rtrancl3p_trans[OF Red mthr.\<tau>rtrancl3p_Nil_eq_\<tau>moves[THEN iffD2, OF s'_s'']]
        have s_s'': "mthr.\<tau>rtrancl3p s ttas' s''" by simp

        from red obtain ta'' s'''' where "s'' -t'\<triangleright>ta''\<rightarrow> s''''"
          and "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)"
        proof(cases)
          case (redT_normal x x' m')
          note red = `t' \<turnstile> \<langle>x, shr s''\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>`
            and ts''t' = `thr s'' t' = \<lfloor>(x, no_wait_locks)\<rfloor>`
            and aok = `actions_ok s'' t' ta'`
            and s''' = `redT_upd s'' t' ta' x' m' s'''`
          with `\<not> m\<tau>move s'' (t', ta') s'''`
          have "\<not> \<tau>move (x, shr s'') ta' (x', m')"
            by(auto intro: m\<tau>move.intros)
          from sc_completionD[OF cau s_s'' sc ts''t' red aok this] False
          obtain ta'' x'' m'' where red': "t' \<turnstile> \<langle>x, shr s''\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
            and aok': "actions_ok s'' t' ta''"
            and sc': "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)" by blast
          from redT_updWs_total obtain ws' where "redT_updWs t' (wset s'') \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> ws'" ..
          then obtain s'''' where "redT_upd s'' t' ta'' x'' m'' s''''" by fastsimp
          with red' ts''t' aok' have "s'' -t'\<triangleright>ta''\<rightarrow> s''''" ..
          thus thesis using sc' by(rule that)
        next
          case redT_acquire
          thus thesis by(simp add: that[OF red] ta_seq_consist_convert_RA)
        qed
        moreover with no_\<tau>[of s''''] have "\<not> m\<tau>move s'' (t', ta'') s''''" by auto
        ultimately have "?proceed' ((t', ta''), s'''')"
          using s'_s'' by(auto simp del: split_paired_Ex)
        hence "?proceed' (Eps ?proceed')" by(rule someI)
        moreover with Red have "mthr.\<tau>rtrancl3p s (ttas' @ [fst (Eps ?proceed')]) (snd (Eps ?proceed'))"
          by(fastsimp simp add: split_beta elim: mthr.\<tau>rtrancl3p_snocI)
        moreover from no_halt False
        have "ttas = TCons (fst (Eps ?proceed')) (complete_sc (snd (Eps ?proceed')) (?vs (ttas' @ [fst (Eps ?proceed')])))"
          unfolding ttas complete_sc_def by(subst tllist_corec)(simp add: complete_sc_aux.simps split_beta)
        moreover from sc `?proceed' (Eps ?proceed')`
        have "ta_seq_consist P vs (llist_of (?ttas' (ttas' @ [fst (Eps ?proceed')])))"
          unfolding map_append concat_append lappend_llist_of_llist_of[symmetric] 
          by(subst ta_seq_consist_lappend)(auto simp add: split_def)
        ultimately have ?Proceed
          by(fastsimp intro: exI[where x="ttas' @ [fst (Eps ?proceed')]"] simp del: split_paired_Ex)
        thus ?thesis by simp
      qed
    qed
  qed
qed

lemma complete_sc_ta_seq_consist:
  assumes cau: "sc_completion s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of_tllist (complete_sc s vs))))"
proof -
  def vs' \<equiv> vs
  let ?obs = "\<lambda>ttas. lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of_tllist ttas))"
  def obs \<equiv> "?obs (complete_sc s vs)"
  def a \<equiv> "llist_of_tllist (complete_sc s vs')"
  let ?ttas' = "\<lambda>ttas' :: ('t \<times> ('l,'t,'x,'m,'w,obs_event action list) thread_action) list.
               concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')"
  let "?vs ttas'" = "mrw_values P vs (?ttas' ttas')"
  from vs'_def obs_def
  have "mthr.\<tau>rtrancl3p s [] s" "ta_seq_consist P vs (llist_of (?ttas' []))" "vs' = ?vs []"
    by(auto simp add: mthr.\<tau>rtrancl3p_Nil_eq_\<tau>moves)
  hence "\<exists>s' ttas'. obs = ?obs (complete_sc s' vs') \<and> mthr.\<tau>rtrancl3p s ttas' s' \<and> 
                    ta_seq_consist P vs (llist_of (?ttas' ttas')) \<and> vs' = ?vs ttas' \<and> 
                    a = llist_of_tllist (complete_sc s' vs')"
    unfolding obs_def vs'_def a_def by metis
  moreover have "wf (inv_image {(m, n). m < n} (llength \<circ> ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [])))"
    (is "wf ?R") by(rule wf_inv_image)(rule wellorder_class.wf)
  ultimately show "ta_seq_consist P vs' obs"
  proof(coinduct vs' obs a rule: ta_seq_consist_coinduct_append_wf)
    case (ta_seq_consist vs' obs a)
    then obtain s' ttas' where obs_def: "obs = ?obs (complete_sc s' (?vs ttas'))"
      and Red: "mthr.\<tau>rtrancl3p s ttas' s'"
      and sc: "ta_seq_consist P vs (llist_of (?ttas' ttas'))"
      and vs'_def: "vs' = ?vs ttas'" 
      and a_def: "a = llist_of_tllist (complete_sc s' vs')" by blast
 
    let "?halt s''" = "\<tau>mredT^** s' s'' \<and> (\<forall>tta s'''. \<not> redT s'' tta s''')"
    let "?diverge" = "mthr.\<tau>diverge s'"
    let "?proceed" = "\<lambda>(s'', (t', ta'), s'''). \<tau>mredT^** s' s'' \<and> redT s'' (t', ta') s''' \<and> \<not> m\<tau>move s'' (t', ta') s'''"
    show ?case
    proof(cases "(\<exists>s''. ?halt s'') \<or> ?diverge \<or> obs = LNil")
      case True
      hence "llist_of_tllist (complete_sc s' (?vs ttas')) = LNil \<or> obs = LNil"
        unfolding complete_sc_def obs_def
        by(subst tllist_corec)(auto simp add: complete_sc_aux.simps simp del: split_paired_Ex, blast)
      hence ?LNil unfolding obs_def by auto
      thus ?thesis ..
    next
      case False
      
      let ?proceed' = "\<lambda>((t', ta'), s'''). \<exists>s''. \<tau>mredT^** s' s'' \<and> redT s'' (t', ta') s''' \<and> \<not> m\<tau>move s'' (t', ta') s''' \<and> 
                                          ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      let ?tta = "fst (Eps ?proceed')"
      let ?s' = "snd (Eps ?proceed')"
      
      from False have no_halt: "\<not> (\<exists>s''. ?halt s'')" and no_diverge: "\<not> ?diverge" and "obs \<noteq> LNil" by blast+
      from mthr.not_\<tau>diverge_to_no_\<tau>move[OF no_diverge]
      obtain s'' where s'_s'': "\<tau>mredT^** s' s''"
        and no_\<tau>: "\<And>s'''. \<not> \<tau>mredT s'' s'''" by blast
      from s'_s'' no_halt obtain t' ta' s''' where red: "s'' -t'\<triangleright>ta'\<rightarrow> s'''"
        by(auto simp del: split_paired_Ex split_paired_All)
      with no_\<tau>[of s'''] have "\<not> m\<tau>move s'' (t', ta') s'''" by auto
      from mthr.\<tau>rtrancl3p_trans[OF Red mthr.\<tau>rtrancl3p_Nil_eq_\<tau>moves[THEN iffD2, OF s'_s'']]
      have s_s'': "mthr.\<tau>rtrancl3p s ttas' s''" by simp

      from red obtain ta'' s''''
        where "s'' -t'\<triangleright>ta''\<rightarrow> s''''"
        and "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)"
      proof(cases)
        case (redT_normal x x' m')
        note red = `t' \<turnstile> \<langle>x, shr s''\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>`
          and ts''t' = `thr s'' t' = \<lfloor>(x, no_wait_locks)\<rfloor>`
          and aok = `actions_ok s'' t' ta'`
          and s''' = `redT_upd s'' t' ta' x' m' s'''`
        with `\<not> m\<tau>move s'' (t', ta') s'''`
        have "\<not> \<tau>move (x, shr s'') ta' (x', m')"
          by(auto intro: m\<tau>move.intros)
        from sc_completionD[OF cau s_s'' sc ts''t' red aok this]
        obtain ta'' x'' m'' where red': "t' \<turnstile> \<langle>x, shr s''\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
          and aok': "actions_ok s'' t' ta''"
          and sc': "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)" by blast
        from redT_updWs_total obtain ws' where "redT_updWs t' (wset s'') \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> ws'" ..
        then obtain s'''' where "redT_upd s'' t' ta'' x'' m'' s''''" by fastsimp
        with red' ts''t' aok' have "s'' -t'\<triangleright>ta''\<rightarrow> s''''" ..
        thus thesis using sc' by(rule that)
      next
        case redT_acquire
        thus thesis by(simp add: that[OF red] ta_seq_consist_convert_RA)
      qed
      moreover with no_\<tau>[of s''''] have "\<not> m\<tau>move s'' (t', ta'') s''''" by auto
      ultimately have "?proceed' ((t', ta''), s'''')"
        using s'_s'' by(auto simp del: split_paired_Ex)
      hence "?proceed' (Eps ?proceed')" by(rule someI)
      show ?thesis
      proof(cases "obs = LNil")
        case True thus ?thesis ..
      next
        case False
        from no_halt no_diverge
        have csc_unfold: "complete_sc s' (?vs ttas') = TCons ?tta (complete_sc ?s' (?vs (ttas' @ [?tta])))"
          unfolding complete_sc_def by(subst tllist_corec)(simp add: complete_sc_aux.simps split_beta)
        hence "obs = lappend (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>) (?obs (complete_sc ?s' (?vs (ttas' @ [?tta]))))"
          using obs_def by(simp add: split_beta)
        moreover have "ta_seq_consist P vs' (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>)"
          using `?proceed' (Eps ?proceed')` vs'_def by(clarsimp simp add: split_beta)
        moreover {
          assume "llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub> = LNil"
          moreover from obs_def `obs \<noteq> LNil`
          have "lfinite (ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []) (llist_of_tllist (complete_sc s' (?vs ttas'))))"
            unfolding lfinite_ltakeWhile by(fastsimp simp add: split_def lconcat_eq_LNil)
          ultimately have "(llist_of_tllist (complete_sc ?s' (?vs (ttas' @ [?tta]))), a) \<in> ?R"
            unfolding a_def vs'_def csc_unfold
            by(clarsimp simp add: split_def)(auto simp add: lfinite_eq_range_llist_of) }
        moreover have "?obs (complete_sc ?s' (?vs (ttas' @ [?tta]))) = ?obs (complete_sc ?s' (mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>))))"
          unfolding vs'_def by(simp add: split_def)
        moreover from `?proceed' (Eps ?proceed')`
        have "mthr.\<tau>rtrancl3p s (ttas' @ [?tta]) ?s'"
          by(auto simp add: split_def intro: mthr.\<tau>rtrancl3p_snocI[OF Red])
        moreover from sc `?proceed' (Eps ?proceed')`
        have "ta_seq_consist P vs (llist_of (?ttas' (ttas' @ [?tta])))"
          by(clarsimp simp add: split_def ta_seq_consist_lappend lappend_llist_of_llist_of[symmetric] simp del: lappend_llist_of_llist_of)
        moreover have "mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>)) = ?vs (ttas' @ [?tta])" 
          unfolding vs'_def by(simp add: split_def)
        moreover have "llist_of_tllist (complete_sc ?s' (?vs (ttas' @ [?tta]))) =
          llist_of_tllist (complete_sc ?s' (mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>))))"
          unfolding vs'_def by(simp add: split_def)
        ultimately have "?lappend" by blast
        thus ?thesis ..
      qed
    qed
  qed
qed

lemma sequential_completion_\<tau>Runs:
  assumes "sc_completion s vs"
  and "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "\<exists>ttas. mthr.\<tau>Runs s ttas \<and> ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of_tllist ttas)))"
using complete_sc_ta_seq_consist[OF assms] complete_sc_in_\<tau>Runs[OF assms]
by blast


definition cut_and_update :: "('l, 't, 'x, 'm, 'w) state \<Rightarrow> (addr \<times> addr_loc \<rightharpoonup> val \<times> bool) \<Rightarrow> bool"
where
  "cut_and_update s vs \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m'.
      mthr.\<tau>rtrancl3p s ttas s' \<longrightarrow> ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
      thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow> 
      \<not> \<tau>move (x, shr s') ta (x', m') \<longrightarrow> 
   (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))))"

lemma cut_and_updateI[intro?]:
  "(\<And>ttas s' t x ta x' m'. 
     \<lbrakk> mthr.\<tau>rtrancl3p s ttas s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta;
       \<not> \<tau>move (x, shr s') ta (x', m') \<rbrakk>
      \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                       ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                       eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))))
    \<Longrightarrow> cut_and_update s vs"
unfolding cut_and_update_def by blast

lemma cut_and_updateD:
  "\<lbrakk> cut_and_update s vs; mthr.\<tau>rtrancl3p s ttas s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta; \<not> \<tau>move (x, shr s') ta (x', m') \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> \<not> \<tau>move (x, shr s') ta' (x'', m'') \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
unfolding cut_and_update_def by blast

lemma cut_and_update_imp_sc_completion:
  "cut_and_update s vs \<Longrightarrow> sc_completion s vs"
apply(rule sc_completionI)
apply(drule (6) cut_and_updateD)
apply blast
done

lemma sequential_completion:
  assumes cut_and_update: "cut_and_update s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  and \<tau>Red: "mthr.\<tau>rtrancl3p s ttas s'"
  and sc: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and red: "redT s' (t, ta) s''"
  and \<tau>: "\<not> m\<tau>move s' (t, ta) s''"
  shows
  "\<exists>ta' ttas'. mthr.\<tau>Runs s' (TCons (t, ta') ttas') \<and> 
     ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') (llist_of_tllist ttas'))))) \<and> 
     eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
proof -
  from red obtain ta' s''' 
    where red': "redT s' (t, ta') s'''"
    and \<tau>': "\<not> m\<tau>move s' (t, ta') s'''"
    and sc': "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') LNil))))"
    and eq: "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  proof cases
    case (redT_normal x x' m')
    note ts't = `thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>`
      and red = `t \<turnstile> \<langle>x, shr s'\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>`
      and aok = `actions_ok s' t ta`
      and s'' = `redT_upd s' t ta x' m' s''`
    with \<tau> have "\<not> \<tau>move (x, shr s') ta (x', m')" by(auto intro: m\<tau>move.intros)
    from cut_and_updateD[OF cut_and_update, OF \<tau>Red sc ts't red aok this]
    obtain ta' x'' m'' where red: "t \<turnstile> \<langle>x, shr s'\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      and sc': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      and eq: "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      and aok: "actions_ok s' t ta'" 
      and \<tau>': "\<not> \<tau>move (x, shr s') ta' (x'', m'')" by blast
    obtain ws''' where "redT_updWs t (wset s') \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> ws'''"
      using redT_updWs_total ..
    then obtain s''' where s''': "redT_upd s' t ta' x'' m'' s'''" by fastsimp
    with red `thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>` aok have "s' -t\<triangleright>ta'\<rightarrow> s'''" by(rule redT.redT_normal)
    moreover from \<tau>' ts't red s''' have "\<not> m\<tau>move s' (t, ta') s'''" by(auto elim: m\<tau>move.cases)
    moreover from sc sc'
    have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') LNil))))"
      by(auto simp add: lmap_lappend_distrib ta_seq_consist_lappend split_def lconcat_llist_of[symmetric] o_def list_of_lconcat)
    ultimately show thesis using eq by(rule that)
  next
    case (redT_acquire x ln n)
    hence "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta) LNil))))"
      and "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      using sc
      by(simp_all add: lmap_lappend_distrib ta_seq_consist_lappend split_def lconcat_llist_of[symmetric] o_def list_of_lconcat ta_seq_consist_convert_RA ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red \<tau> show thesis by(rule that)
  qed

  txt {* Now, find a sequentially consistent completion from @{term "s'''"} onwards. *}
  from red' \<tau>' have \<tau>Red'': "mthr.\<tau>rtrancl3p s' [(t, ta')] s'''"
    by(rule mthr.\<tau>rtrancl3p_step)(rule mthr.\<tau>rtrancl3p_refl)
  with \<tau>Red have \<tau>Red': "mthr.\<tau>rtrancl3p s (ttas @ [(t, ta')]) s'''" by(rule mthr.\<tau>rtrancl3p_trans)

  from sc sc'
  have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas @ [(t, ta')]))))"
    by(simp add: o_def split_def lappend_llist_of_llist_of[symmetric])
  with cut_and_update_imp_sc_completion[OF cut_and_update] \<tau>Red'
  have "sc_completion s''' (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta')]))))"
    by(rule sc_completion_shift)
  from sequential_completion_\<tau>Runs[OF this ta_seq_consist_convert_RA]
  obtain ttas' where \<tau>Runs: "\<tau>trsys.\<tau>Runs redT m\<tau>move s''' ttas'"
    and sc'': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta')])))) 
                                (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of_tllist ttas')))"
    by blast
  from mthr.\<tau>rtrancl3p_into_\<tau>Runs[OF \<tau>Red'' \<tau>Runs]
  have "mthr.\<tau>Runs s' (TCons (t, ta') ttas')" by simp
  moreover from sc sc' sc''
  have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') (llist_of_tllist ttas')))))"
    unfolding lmap_lappend_distrib lconcat_lappend by(simp add: o_def ta_seq_consist_lappend split_def list_of_lconcat)
  ultimately show ?thesis using eq by blast
qed

end

end