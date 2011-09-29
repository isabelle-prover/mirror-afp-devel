(*  Title:      JinjaThreads/MM/SC_Completion.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Combination of locales for heap operations and interleaving} *}

theory JMM_Framework imports
  JMM_Heap
  "../Framework/FWInitFinLift"
  "../Common/WellForm"
begin

lemma convert_new_thread_action_id [simp]: -- "Move to FWState"
  "convert_new_thread_action id = (id :: ('t, 'x, 'm) new_thread_action \<Rightarrow> ('t, 'x, 'm) new_thread_action)" (is ?thesis1)
  "convert_new_thread_action (\<lambda>x. x) = (id :: ('t, 'x, 'm) new_thread_action \<Rightarrow> ('t, 'x, 'm) new_thread_action)" (is ?thesis2)
proof -
  show ?thesis1 by(rule ext)(case_tac x, simp_all)
  thus ?thesis2 by(simp add: id_def)
qed

context heap begin

lemma init_fin_lift_state_start_state:
  "init_fin_lift_state s (start_state f P C M vs) = start_state (\<lambda>C M Ts T meth vs. (s, f C M Ts T meth vs)) P C M vs"
by(simp add: start_state_def init_fin_lift_state_def split_beta fun_eq_iff)

end

context allocated_heap begin

lemma mrw_addrs_lift_start_heap_obs:
  "mrw_addrs (mrw_values P vs (map snd (lift_start_obs start_tid start_heap_obs))) \<subseteq> mrw_addrs vs"
by(simp add: lift_start_obs_def o_def mrw_addrs_start_heap_obs)

end

context heap begin

lemma mrw_values_start_heap_obs_typeable:
  assumes wf: "wf_prog wf_md P"
  and mrws: "mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  shows "\<exists>T. P,start_heap \<turnstile> ad@al : T \<and> P,start_heap \<turnstile> v :\<le> T"
proof -
  from mrw_values_eq_SomeD[OF mrws]
  obtain obs' wa obs'' 
    where eq: "map snd (lift_start_obs start_tid start_heap_obs) = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  from `is_write_action wa` show ?thesis
  proof cases
    case (WriteMem ad' al' v')
    with vwa adal eq have "WriteMem ad al v \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
    thus ?thesis by(rule start_heap_write_typeable)
  next
    case (NewObj ad' C)
    with vwa adal eq have "NewObj ad C \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
    hence "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>"
      by(rule NewObj_start_heap_obsD[OF wf_prog_wf_syscls[OF wf]])
    thus ?thesis using adal vwa NewObj
      by(fastforce simp add: has_field_def intro: addr_loc_type.intros)
  next
    case (NewArr ad' T n)
    with vwa adal eq have "NewArr ad T n \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
    hence "typeof_addr start_heap ad = \<lfloor>Array T\<rfloor>"
      and "array_length start_heap ad = n" by(rule NewArr_start_heap_obsD)+
    thus ?thesis using adal vwa NewArr
      by(fastforce intro: addr_loc_type.intros simp add: has_field_def)
  qed
qed

lemma start_state_vs_conf:
  "wf_prog wf_md P \<Longrightarrow> vs_conf P start_heap (mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs)))"
by(rule vs_confI)(rule mrw_values_start_heap_obs_typeable)

end


section {* JMM traces for Jinja semantics *}

context multithreaded begin

inductive_set \<E> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> 'o) llist set"
  for \<sigma> :: "('l,'t,'x,'m,'w) state"
where
  "mthr.Runs \<sigma> E'
  \<Longrightarrow> lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') \<in> \<E> \<sigma>"

lemma actions_\<E>E_aux:
  fixes \<sigma> E'
  defines "E == lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
  assumes mthr: "mthr.Runs \<sigma> E'"
  and a: "enat a < llength E"
  obtains m n t ta
  where "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "enat m < llength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "lnth E' m = (t, ta)"
proof -
  from lnth_lconcat_conv[OF a[unfolded E_def], folded E_def]
  obtain m n
    where "lnth E a = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') m) n"
    and "enat n < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') m)"
    and "enat m < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and "enat a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat n"
    by blast
  moreover
  obtain t ta where "lnth E' m = (t, ta)" by(cases "lnth E' m")
  ultimately have E_a: "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
    and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and m: "enat m < llength E'"
    and a: "enat a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat n"
    by(simp_all add: lnth_llist_of)
  note a
  also have "(\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) = 
            setsum (enat \<circ> (\<lambda>i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) {..<m}"
    using m by(simp add: less_trans[where y="enat m"] split_beta)
  also have "\<dots> = enat (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
    by(subst setsum_hom)(simp_all add: zero_enat_def)
  finally have a: "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n" by simp
  with E_a n m show thesis using `lnth E' m = (t, ta)` by(rule that)
qed

lemma actions_\<E>E:
  assumes E: "E \<in> \<E> \<sigma>"
  and a: "enat a < llength E"
  obtains E' m n t ta
  where "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
  and "mthr.Runs \<sigma> E'"
  and "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "enat m < llength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "lnth E' m = (t, ta)"
proof -
  from E obtain E' ws
    where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and "mthr.Runs \<sigma> E'" by(rule \<E>.cases) blast
  from `mthr.Runs \<sigma> E'` a[unfolded E]
  show ?thesis
    by(rule actions_\<E>E_aux)(fold E, rule that[OF E `mthr.Runs \<sigma> E'`])
qed

end

context \<tau>multithreaded_wf begin

text {* Alternative characterisation for @{term "\<E>"} *}
lemma \<E>_conv_Runs:
  "\<E> \<sigma> = lconcat ` lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ` llist_of_tllist ` {E. mthr.\<tau>Runs \<sigma> E}"
  (is "?lhs = ?rhs")
proof(intro equalityI subsetI)
  fix E
  assume "E \<in> ?rhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and \<tau>Runs: "mthr.\<tau>Runs \<sigma> E'" by(blast)
  obtain E'' where E': "E' = tmap (\<lambda>(tls, s', tl, s''). tl) (sum_case (\<lambda>(tls, s'). \<lfloor>s'\<rfloor>) Map.empty) E''"
    and \<tau>Runs': "mthr.\<tau>Runs_table2 \<sigma> E''"
    using \<tau>Runs by(rule mthr.\<tau>Runs_into_\<tau>Runs_table2)
  have "mthr.Runs \<sigma> (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) 
                                      (LCons (case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil)))"
    (is "mthr.Runs _ ?E'''")
    using \<tau>Runs' by(rule mthr.\<tau>Runs_table2_into_Runs)
  moreover 
  let ?tail = "\<lambda>E''. case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls"
  {
    have "E = lconcat (lfilter (\<lambda>xs. xs \<noteq> LNil) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))"
      unfolding E by(simp add: lconcat_lfilter_neq_LNil)
    also have "\<dots> = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E''))))"
      by(simp add: E' lfilter_lmap lmap_compose[symmetric] o_def split_def)
    also
    have "(lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')),
           lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil)))) \<in>
          {(lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')),
           lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))
          |E''. \<exists>\<sigma>. mthr.\<tau>Runs_table2 \<sigma> E''}" 
      (is "_ \<in> ?r")
      using \<tau>Runs' by blast
    hence "lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')) = 
          lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil)))"
    proof(coinduct rule: llist_equalityI)
      case (Eqllist q)
      then obtain E'' \<sigma> 
        where q: "q = (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')), lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))"
        and \<tau>Runs': "mthr.\<tau>Runs_table2 \<sigma> E''"
        by blast
      show ?case
      proof(cases "fst q")
        case LNil
        hence "\<forall>(tls, s', (t, ta), s'') \<in> lset (llist_of_tllist E''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []"
          using q by(auto simp add: lfilter_empty_conv)
        hence "\<forall>(t, ta) \<in> lset (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []"
          by(cases "lfinite (llist_of_tllist E'')")(fastforce simp add: lset_lappend_lfinite split_beta lset_lconcat_lfinite lappend_inf mthr.silent_move2_def dest: mthr.\<tau>Runs_table2_silentsD[OF \<tau>Runs'] mthr.\<tau>Runs_table2_terminal_silentsD[OF \<tau>Runs'] mthr.\<tau>Runs_table2_terminal_inf_stepD[OF \<tau>Runs'] m\<tau>move_silentD inf_step_silentD silent_moves2_silentD split: sum.split_asm)+
        hence "lfilter (\<lambda>(t, ta). obs_a ta \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))) = LNil"
          by(simp add: lfilter_empty_conv split_beta)
        thus ?thesis using LNil q by simp
      next
        case (LCons tl tls')
        then obtain tls s' s'' tlsstlss' where tls': "tls' = lmap (\<lambda>(tls, s', tta, s''). tta) tlsstlss'"
          and filter: "lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) (llist_of_tllist E'') = LCons (tls, s', tl, s'') tlsstlss'"
          using q by(fastforce simp add: lmap_eq_LCons_conv)
        from lfilter_eq_LConsD[OF filter]
        obtain us vs where eq: "llist_of_tllist E'' = lappend us (LCons (tls, s', tl, s'') vs)"
          and fin: "lfinite us"
          and empty: "\<forall>(tls, s', (t, ta), s'')\<in>lset us. obs_a ta = []"
          and neq_empty: "obs_a (snd tl) \<noteq> []"
          and tlsstlss': "tlsstlss' = lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) vs"
          by(auto simp add: split_beta)
        from eq obtain E''' where E'': "E'' = lappendt us E'''" 
          and eq': "llist_of_tllist E''' = LCons (tls, s', tl, s'') vs"
          and terminal: "terminal E''' = terminal E''"
          unfolding llist_of_tllist_eq_lappend_conv by auto
        from \<tau>Runs' fin E'' obtain \<sigma>' where \<tau>Runs'': "mthr.\<tau>Runs_table2 \<sigma>' E'''"
          by(auto dest: mthr.\<tau>Runs_table2_lappendtD)
        then obtain \<sigma>'' E'''' where "mthr.\<tau>Runs_table2 \<sigma>'' E''''" "E''' = TCons (tls, s', tl, s'') E''''"
          using eq' by cases auto
        moreover from \<tau>Runs' E'' fin
        have "\<forall>(tls, s, tl, s')\<in>lset us. \<forall>(t, ta)\<in>set tls. ta = \<epsilon>"
          by(fastforce dest: mthr.\<tau>Runs_table2_silentsD m\<tau>move_silentD simp add: mthr.silent_move2_def)
        hence "lfilter (\<lambda>(t, ta). obs_a ta \<noteq> []) (lconcat (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) us)) = LNil"
          using empty by(auto simp add: lfilter_empty_conv lset_lconcat_lfinite split_beta)
        moreover from \<tau>Runs'' eq' have "snd ` set tls \<subseteq> {\<epsilon>}"
          by(cases)(fastforce dest: silent_moves2_silentD)+
        hence "[(t, ta)\<leftarrow>tls . obs_a ta \<noteq> []] = []"
          by(auto simp add: filter_empty_conv split_beta)
        ultimately have ?EqLCons
          using LCons q E'' fin tls' tlsstlss' filter eq' neq_empty
          by(fastforce simp add: lmap_lappend_distrib lappend_assoc lfilter_lappend_lfinite split_beta simp del: split_paired_Ex)
        thus ?thesis ..
      qed
    qed
    also have "lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) \<dots> = lfilter (\<lambda>obs. obs \<noteq> LNil) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))"
      unfolding lfilter_lmap by(simp add: o_def split_def)
    finally have "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?E''')"
      by(simp add: lconcat_lfilter_neq_LNil) }
  ultimately show "E \<in> ?lhs" by(blast intro: \<E>.intros)
next
  fix E
  assume "E \<in> ?lhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) E')"
    and Runs: "mthr.Runs \<sigma> E'" by(blast elim: \<E>.cases)
  from Runs obtain E'' where E': "E' = lmap (\<lambda>(s, tl, s'). tl) E''"
    and Runs': "mthr.Runs_table \<sigma> E''" by(rule mthr.Runs_into_Runs_table)
  have "mthr.\<tau>Runs \<sigma> (tmap (\<lambda>(s, tl, s'). tl) id (tfilter None (\<lambda>(s, tl, s'). \<not> m\<tau>move s tl s') (tllist_of_llist (Some (llast (LCons \<sigma> (lmap (\<lambda>(s, tl, s'). s') E'')))) E'')))"
    (is "mthr.\<tau>Runs _ ?E'''")
    using Runs' by(rule mthr.Runs_table_into_\<tau>Runs)
  moreover
  have "(\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> []) = (\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> [] \<and> \<not> m\<tau>move s (t, ta) s')"
    by(rule ext)(auto dest: m\<tau>move_silentD)
  hence "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (llist_of_tllist ?E'''))"
    unfolding E E'
    by(subst (1 2) lconcat_lfilter_neq_LNil[symmetric])(simp add: lfilter_lmap lfilter_lfilter o_def split_def)
  ultimately show "E \<in> ?rhs" by(blast)
qed

end

text {* Running threads have been started before *}

definition Status_no_wait_locks :: "('l,'t,status \<times> 'x) thread_info \<Rightarrow> bool"
where
  "Status_no_wait_locks ts \<longleftrightarrow> 
  (\<forall>t status x ln. ts t = \<lfloor>((status, x), ln)\<rfloor> \<longrightarrow> status \<noteq> Running \<longrightarrow> ln = no_wait_locks)"

lemma Status_no_wait_locks_PreStartD:
  "\<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((PreStart, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locks_FinishedD:
  "\<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((Finished, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locksI:
  "(\<And>t status x ln. \<lbrakk> ts t = \<lfloor>((status, x), ln)\<rfloor>; status = PreStart \<or> status = Finished \<rbrakk> \<Longrightarrow> ln = no_wait_locks)
  \<Longrightarrow> Status_no_wait_locks ts"
unfolding Status_no_wait_locks_def 
apply clarify
apply(case_tac status)
apply auto
done

context heap_base begin

lemma Status_no_wait_locks_start_state:
  "Status_no_wait_locks (thr (init_fin_lift_state status (start_state f P C M vs)))"
by(clarsimp simp add: Status_no_wait_locks_def init_fin_lift_state_def start_state_def split_beta)

end

context multithreaded_base begin

lemma init_fin_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  shows "Status_no_wait_locks (thr s')"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with ok show ?thesis
    by(auto intro!: Status_no_wait_locksI dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD split: split_if_asm)
next
  case redT_normal
  show ?thesis
  proof(rule Status_no_wait_locksI)
    fix t' status' x' ln'
    assume tst': "thr s' t' = \<lfloor>((status', x'), ln')\<rfloor>"
      and status: "status' = PreStart \<or> status' = Finished"
    show "ln' = no_wait_locks"
    proof(cases "thr s t'")
      case None
      with redT_normal tst' show ?thesis
        by(fastforce elim!: init_fin.cases dest: redT_updTs_new_thread simp add: final_thread.actions_ok_iff split: split_if_asm)
    next
      case (Some sxln)
      obtain status'' x'' ln'' 
        where [simp]: "sxln = ((status'', x''), ln'')" by(cases sxln) auto
      show ?thesis
      proof(cases "fst tta = t'")
        case True
        with redT_normal tst' status show ?thesis by(auto simp add: expand_finfun_eq fun_eq_iff)
      next
        case False
        with tst' redT_normal Some status have "status'' = status'" "ln'' = ln'" 
          by(force dest: redT_updTs_Some simp add: final_thread.actions_ok_iff)+
        with ok Some status show ?thesis
          by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      qed
    qed
  qed
qed

lemma init_fin_Running_InitialThreadAction:
  assumes redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "tta = (t, \<lbrace>InitialThreadAction\<rbrace>)"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with running not_running show ?thesis by(auto split: split_if_asm)
next
  case redT_normal
  show ?thesis
  proof(cases "thr s t")
    case None
    with redT_normal running not_running show ?thesis
      by(fastforce simp add: final_thread.actions_ok_iff elim: init_fin.cases dest: redT_updTs_new_thread split: split_if_asm)
  next
    case (Some a)
    with redT_normal running not_running show ?thesis
      apply(cases a)
      apply(auto simp add: final_thread.actions_ok_iff split: split_if_asm elim: init_fin.cases)
      apply((drule (1) redT_updTs_Some)?, fastforce)+
      done
  qed
qed

end

context if_multithreaded begin

lemma init_fin_Trsys_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and Trsys: "if.mthr.Trsys s ttas s'"
  shows "Status_no_wait_locks (thr s')"
using Trsys ok
by(induct)(blast dest: init_fin_preserve_Status_no_wait_locks)+

lemma init_fin_Trsys_Running_InitialThreadAction:
  assumes redT: "if.mthr.Trsys s ttas s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "(t, \<lbrace>InitialThreadAction\<rbrace>) \<in> set ttas"
using redT not_running running
proof(induct arbitrary: x' ln')
  case rtrancl3p_refl thus ?case by(fastforce)
next
  case (rtrancl3p_step s ttas s' tta s'') thus ?case
    by(cases "\<exists>x ln. thr s' t = \<lfloor>((Running, x), ln)\<rfloor>")(fastforce dest: init_fin_Running_InitialThreadAction)+
qed

end

locale heap_multithreaded =
  heap
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    P 
  + 
  mthr!: multithreaded final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"

  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'addr released_locks \<Rightarrow> ('addr, 'thread_id) obs_event list" 
  and P :: "'md prog"

sublocale heap_multithreaded < mthr!: if_multithreaded final r convert_RA
by(unfold_locales)

sublocale heap_multithreaded < "if"!: jmm_multithreaded
  mthr.init_fin_final mthr.init_fin "map NormalAction \<circ> convert_RA"
.

context heap_multithreaded begin

lemma thread_start_actions_ok_init_fin:
  assumes E: "E \<in> mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"
  shows "thread_start_actions_ok (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) E)"
  (is "thread_start_actions_ok ?E")
proof(rule thread_start_actions_okI)
  let ?start_heap_obs = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"
  fix a
  assume a: "a \<in> actions ?E"
    and a_new: "\<not> is_new_action (action_obs ?E a)"
  show "\<exists>i. i \<le> a \<and> action_obs ?E i = InitialThreadAction \<and> action_tid ?E i = action_tid ?E a"
  proof(cases "action_tid ?E a = start_tid")
    case True thus ?thesis
      by(auto simp add: lift_start_obs_def action_tid_def action_obs_def)
  next
    case False

    let ?a = "a - length ?start_heap_obs"

    from False have "a \<ge> length ?start_heap_obs"
      by(rule contrapos_np)(auto simp add: lift_start_obs_def action_tid_def lnth_LCons lnth_lappend1 split: nat.split)
    hence [simp]: "action_tid ?E a = action_tid E ?a" "action_obs ?E a = action_obs E ?a"
      by(simp_all add: action_tid_def lnth_lappend2 action_obs_def)

    from False have not_running: "\<And>x ln. thr ?start_state (action_tid E ?a) \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
      by(auto simp add: start_state_def split_beta init_fin_lift_state_def split: split_if_asm)
    
    from E obtain E' where E': "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
      and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)
    from a E' `a \<ge> length ?start_heap_obs`
    have enat_a: "enat ?a < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))"
      by(cases "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))")(auto simp add: actions_def)
    with \<tau>Runs obtain m n t ta
    where a_obs: "lnth (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')) (a - length ?start_heap_obs) = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
      and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" 
      and m: "enat m < llength E'"
      and a_conv: "?a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
      and E'_m: "lnth E' m = (t, ta)"
      by(rule mthr.if.actions_\<E>E_aux)
    from a_obs have [simp]: "action_tid E ?a = t" "action_obs E ?a = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n"
      by(simp_all add: E' action_tid_def action_obs_def)

    let ?E' = "ldropn (Suc m) E'"
    let ?m_E' = "ltake (enat m) E'"
    have E'_unfold: "E' = lappend (ltake (enat m) E') (LCons (lnth E' m) ?E')"
      unfolding ldropn_Suc_conv_ldropn[OF m] by simp
    hence "mthr.if.mthr.Runs ?start_state (lappend ?m_E' (LCons (lnth E' m) ?E'))"
      using \<tau>Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of ?m_E') \<sigma>'"
      and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' m) ?E')"
      by(rule mthr.if.mthr.Runs_lappendE) simp
    from \<tau>Runs' obtain \<sigma>''' where red_a: "mthr.if.redT \<sigma>' (t, ta) \<sigma>'''"
      and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>''' ?E'"
      unfolding E'_m by cases
    from red_a obtain status x ln where tst: "thr \<sigma>' t = \<lfloor>((status, x), ln)\<rfloor>" by cases auto
    show ?thesis
    proof(cases "status = PreStart \<or> status = Finished")
      case True
      have "Status_no_wait_locks (thr \<sigma>')"
        by(rule mthr.init_fin_Trsys_preserve_Status_no_wait_locks[OF _ \<sigma>_\<sigma>'])(rule Status_no_wait_locks_start_state)
      with True tst have "ln = no_wait_locks"
        by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      with red_a tst True have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [InitialThreadAction]" by(cases) auto
      hence "action_obs E ?a = InitialThreadAction" using a_obs n unfolding E'
        by(simp add: action_obs_def)
      thus ?thesis by(auto)
    next
      case False
      hence "status = Running" by(cases status) auto
      with tst mthr.init_fin_Trsys_Running_InitialThreadAction[OF \<sigma>_\<sigma>' not_running]
      have "(action_tid E ?a, \<lbrace>InitialThreadAction\<rbrace>) \<in> set (list_of (ltake (enat m) E'))"
        using a_obs E' by(auto simp add: action_tid_def)
      then obtain i where "i < m" "enat i < llength E'" 
        and nth_i: "lnth E' i = (action_tid E ?a, \<lbrace>InitialThreadAction\<rbrace>)"
        unfolding in_set_conv_nth 
        by(cases "llength E'")(auto simp add: length_list_of_conv_the_enat lnth_ltake)

      let ?i' = "\<Sum>i<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>"
      let ?i = "length ?start_heap_obs + ?i'"

      from `i < m` have "(\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = ?i' + (\<Sum>i=i..<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
      hence "?i' \<le> ?a" unfolding a_conv by simp
      hence "?i \<le> a" using `a \<ge> length ?start_heap_obs` by arith


      from `?i' \<le> ?a` have "enat ?i' < llength E" using enat_a E'
        by(simp add: le_less_trans[where y="enat ?a"])
      from lnth_lconcat_conv[OF this[unfolded E'], folded E']
      obtain k l 
        where nth_i': "lnth E ?i' = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') k) l"
        and l: "l < length \<lbrace>snd (lnth E' k)\<rbrace>\<^bsub>o\<^esub>"
        and k: "enat k < llength E'"
        and i_conv: "enat ?i' = (\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat l"
        by(fastforce simp add: split_beta)

      have "(\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) =
            (\<Sum>i<k. (enat \<circ> (\<lambda>i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(rule setsum_cong)(simp_all add: less_trans[where y="enat k"] split_beta k)
      also have "\<dots> = enat (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule setsum_hom)(simp_all add: zero_enat_def)
      finally have i_conv: "?i' = (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + l" using i_conv by simp

      have [simp]: "i = k"
      proof(rule ccontr)
        assume "i \<noteq> k"
        thus False unfolding neq_iff
        proof
          assume "i < k"
          hence "(\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with i_conv have "(\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" "l = 0" by simp_all
          moreover have "(\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `i < k`]) simp
          ultimately show False using nth_i by simp
        next
          assume "k < i"
          hence "?i' = (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst setsum_add_nat_ivl) simp_all
          with i_conv have "(\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" by simp
          moreover have "(\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (lnth E' k)\<rbrace>\<^bsub>o\<^esub>"
            by(subst setsum_head_upt_Suc[OF `k < i`]) simp
          ultimately show False using l by simp
        qed
      qed
      with l nth_i have [simp]: "l = 0" by simp
      
      hence "lnth E ?i' = (action_tid E ?a, InitialThreadAction)"
        using nth_i nth_i' k by simp
      with `?i \<le> a` show ?thesis
        by(auto simp add: action_tid_def action_obs_def lnth_lappend2)
    qed
  qed
qed

end

text {* In the subsequent locales, @{text "convert_RA"} refers to @{term "convert_RA"} and is no longer a parameter! *}

lemma convert_RA_not_write:
  "ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
by(auto simp add: convert_RA_def)

lemma ta_seq_consist_convert_RA:
  "ta_seq_consist P vs (llist_of ((map NormalAction \<circ> convert_RA) ln))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume "enat i < llength (llist_of ((map NormalAction \<circ> convert_RA) ln :: ('b, 'c) obs_event action list))"
    and "lnth (llist_of ((map NormalAction \<circ> convert_RA) ln :: ('b, 'c) obs_event action list)) i = NormalAction (ReadMem ad al v)"
  hence "ReadMem ad al v \<in> set (convert_RA ln :: ('b, 'c) obs_event list)"
    by(auto simp add: in_set_conv_nth)
  hence False by(auto simp add: convert_RA_def)
  thus "\<exists>b. mrw_values P vs (list_of (ltake (enat i) (llist_of ((map NormalAction \<circ> convert_RA) ln)))) (ad, al) = \<lfloor>(v, b)\<rfloor>" ..
qed

locale allocated_multithreaded =
  allocated_heap
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write 
    allocated
    P 
  + 
  mthr!: multithreaded final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"

  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and P :: "'md prog"
  +
  assumes red_allocated_mono: "t \<turnstile> (x, m) -ta\<rightarrow> (x', m') \<Longrightarrow> allocated m \<subseteq> allocated m'"
  and red_New_allocatedD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> allocated m' \<and> ad \<notin> allocated m"
  and red_allocated_NewD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); ad \<in> allocated m'; ad \<notin> allocated m \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and red_New_same_addr_same:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"


sublocale allocated_multithreaded < heap_multithreaded
  addr2thread_id thread_id2addr
  empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
  final r convert_RA P
by(unfold_locales)

context allocated_multithreaded begin

lemma redT_allocated_mono:
  assumes "mthr.redT \<sigma> (t, ta) \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms
by cases(auto dest: red_allocated_mono del: subsetI)

lemma RedT_allocated_mono:
  assumes "mthr.RedT \<sigma> ttas \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms unfolding mthr.RedT_def
by induct(auto dest!: redT_allocated_mono intro: subset_trans del: subsetI)

lemma init_fin_allocated_mono:
  "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m') \<Longrightarrow> allocated m \<subseteq> allocated m'"
by(cases rule: mthr.init_fin.cases)(auto dest: red_allocated_mono)

lemma init_fin_redT_allocated_mono:
  assumes "mthr.if.redT \<sigma> (t, ta) \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms
by cases(auto dest: init_fin_allocated_mono del: subsetI)

lemma init_fin_RedT_allocated_mono:
  assumes "mthr.if.RedT \<sigma> ttas \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms unfolding mthr.if.RedT_def
by induct(auto dest!: init_fin_redT_allocated_mono intro: subset_trans del: subsetI)

lemma init_fin_red_New_allocatedD:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> allocated m' \<and> ad \<notin> allocated m"
using assms
by cases(auto dest: red_New_allocatedD)

lemma init_fin_red_allocated_NewD:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "ad \<in> allocated m'" "ad \<notin> allocated m"
  shows "\<exists>CTn. NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by(cases)(auto dest!: red_allocated_NewD)

lemma init_fin_red_New_same_addr_same:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (NewHeapElem a CTn)" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NormalAction (NewHeapElem a CTn')" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "i = j"
using assms
by cases(auto dest: red_New_same_addr_same)

lemma init_fin_redT_allocated_NewHeapElemD:
  assumes  "mthr.if.redT s (t, ta) s'"
  and "ad \<in> allocated (shr s')"
  and "ad \<notin> allocated (shr s)"
  shows "\<exists>CTn. NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by(cases)(auto dest: init_fin_red_allocated_NewD)

lemma init_fin_RedT_allocated_NewHeapElemD:
  assumes "mthr.if.RedT s ttas s'"
  and "ad \<in> allocated (shr s')"
  and "ad \<notin> allocated (shr s)"
  shows "\<exists>t ta CTn. (t, ta) \<in> set ttas \<and> NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
proof(induct rule: mthr.if.RedT_induct')
  case refl thus ?case by simp
next
  case (step ttas s' t ta s'') thus ?case
    by(cases "ad \<in> allocated (shr s')")(fastforce simp del: split_paired_Ex dest: init_fin_redT_allocated_NewHeapElemD)+
qed

lemma \<E>_new_actions_for_unique:
  assumes E: "E \<in> lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"
  and a: "a \<in> new_actions_for P E adal"
  and a': "a' \<in> new_actions_for P E adal"
  shows "a = a'"
using a a'
proof(induct a a' rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le a a')
  note a = `a \<in> new_actions_for P E adal`
    and a' = `a' \<in> new_actions_for P E adal`
    and a_a' = `a \<le> a'`
  obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  
  let ?init_obs = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"

  have distinct: "distinct (filter (\<lambda>obs. \<exists>a CTn. obs = NormalAction (NewHeapElem a CTn)) (map snd ?init_obs))"
    unfolding start_heap_obs_def
    by(fastforce intro: inj_onI intro!: distinct_filter simp add: distinct_map distinct_zipI1 distinct_initialization_list)

  from start_addrs_allocated
  have dom_start_state: "{a. \<exists>CTn. NormalAction (NewHeapElem a CTn) \<in> snd ` set ?init_obs} \<subseteq> allocated (shr ?start_state)"
    by(fastforce simp add: init_fin_lift_state_conv_simps shr_start_state dest: NewHeapElem_start_heap_obs_start_addrsD subsetD)
  
  show ?case
  proof(cases "a' < length ?init_obs")
    case True
    with a' adal E obtain t_a' CTn_a'
      where CTn_a': "?init_obs ! a' = (t_a', NormalAction (NewHeapElem ad CTn_a'))"
      by(cases "?init_obs ! a'")(fastforce elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from True a_a' have len_a: "a < length ?init_obs" by simp
    with a adal E obtain t_a CTn_a
      where CTn_a: "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
      by(cases "?init_obs ! a")(fastforce elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from CTn_a CTn_a' True len_a
    have "NormalAction (NewHeapElem ad CTn_a') \<in> snd ` set ?init_obs"
      and "NormalAction (NewHeapElem ad CTn_a) \<in> snd ` set ?init_obs" unfolding set_conv_nth
      by(fastforce intro: rev_image_eqI)+
    hence [simp]: "CTn_a' = CTn_a" using distinct_start_addrs'
      by(auto simp add: in_set_conv_nth distinct_conv_nth start_heap_obs_def start_addrs_def) blast
    from distinct_filterD[OF distinct, of a' a "NormalAction (NewHeapElem ad CTn_a)"] len_a True CTn_a CTn_a'
    show "a = a'" by simp
  next
    case False
    obtain n where n: "length ?init_obs = n" by blast
    with False have "n \<le> a'" by simp
    
    from E obtain E'' where E: "E = lappend (llist_of ?init_obs) E''"
      and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
      and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)
    
    from E E'' a' n `n \<le> a'` adal have a': "a' - n \<in> new_actions_for P E'' adal"
      by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)
    
    from a' have "a' - n \<in> actions E''" by(auto elim: new_actionsE)
    hence "enat (a' - n) < llength E''" by(rule actionsE)
    with \<tau>Runs obtain a'_m a'_n t_a' ta_a'
      where E_a': "lnth E'' (a' - n) = (t_a', \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n)"
      and a'_n: "a'_n < length \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>" and a'_m: "enat a'_m < llength E'"
      and a'_conv: "a' - n = (\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a'_n"
      and E'_a'_m: "lnth E' a'_m = (t_a', ta_a')"
      unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
    from a' have "is_new_action (action_obs E'' (a' - n))"
      and "(ad, al) \<in> action_loc P E'' (a' - n)"
      unfolding adal by(auto elim: new_actionsE)
    then obtain CTn'
      where "action_obs E'' (a' - n) = NormalAction (NewHeapElem ad CTn')"
      by cases(fastforce)+
    hence New_ta_a': "\<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NormalAction (NewHeapElem ad CTn')"
      using E_a' a'_n unfolding action_obs_def by simp

    show ?thesis
    proof(cases "a < n")
      case True
      with a adal E n obtain t_a CTn_a where "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
        by(cases "?init_obs ! a")(fastforce elim!: is_new_action.cases simp add: action_obs_def lnth_lappend1 new_actions_for_def)+

      with subsetD[OF dom_start_state, of ad] n True
      have a_shr_\<sigma>: "ad \<in> allocated (shr ?start_state)"
        by(fastforce simp add: set_conv_nth intro: rev_image_eqI)
      
      have E'_unfold': "E' = lappend (ltake (enat a'_m) E') (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E'))"
        unfolding ldropn_Suc_conv_ldropn[OF a'_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat a'_m) E') (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E')))"
        using \<tau>Runs by simp

      then obtain \<sigma>'
        where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat a'_m) E')) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E'))"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''
        where red_a': "mthr.if.redT \<sigma>' (t_a', ta_a') \<sigma>''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' (ldropn (Suc a'_m) E')"
        unfolding E'_a'_m by cases
      from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a' obtain x_a' x'_a' m'_a' 
        where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>') ta_a' (x'_a', m'_a')"
        and \<sigma>''': "redT_upd \<sigma>' t_a' ta_a' x'_a' m'_a' \<sigma>''"
        and ts_t_a': "thr \<sigma>' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a' X_a' X'_a'
        where x_a': "x_a' = (Running, X_a')"
        and x'_a': "x'_a' = (Running, X'_a')"
        and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
        and red''_a': "t_a' \<turnstile> \<langle>X_a', shr \<sigma>'\<rangle> -ta'_a'\<rightarrow> \<langle>X'_a', m'_a'\<rangle>"
        by cases fastforce+
      
      from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
        and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a' have allocated_ad': "ad \<notin> allocated (shr \<sigma>')"
        by(auto dest: red_New_allocatedD)
      
      have "allocated (shr ?start_state) \<subseteq> allocated (shr \<sigma>')"
        using \<sigma>_\<sigma>' unfolding mthr.if.RedT_def[symmetric] by(rule init_fin_RedT_allocated_mono)
      hence False using allocated_ad' a_shr_\<sigma> by blast
      thus ?thesis ..
    next
      case False
      hence "n \<le> a" by simp

      from E E'' a n `n \<le> a` adal have a: "a - n \<in> new_actions_for P E'' adal"
        by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)

      from a have "a - n \<in> actions E''" by(auto elim: new_actionsE)
      hence "enat (a - n) < llength E''" by(rule actionsE)

      with \<tau>Runs obtain a_m a_n t_a ta_a 
        where E_a: "lnth E'' (a - n) = (t_a, \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n)"
        and a_n: "a_n < length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>" and a_m: "enat a_m < llength E'"
        and a_conv: "a - n = (\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a_n"
        and E'_a_m: "lnth E' a_m = (t_a, ta_a)"
        unfolding E' by(rule mthr.if.actions_\<E>E_aux)
  
      from a have "is_new_action (action_obs E'' (a - n))" 
        and "(ad, al) \<in> action_loc P E'' (a - n)" 
        unfolding adal by(auto elim: new_actionsE)
      then obtain CTn where "action_obs E'' (a - n) = NormalAction (NewHeapElem ad CTn)"
        by cases(fastforce)+
      hence New_ta_a: " \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NormalAction (NewHeapElem ad CTn)"
        using E_a a_n unfolding action_obs_def by simp
      
      let ?E' = "ldropn (Suc a_m) E'"
  
      have E'_unfold: "E' = lappend (ltake (enat a_m) E') (LCons (lnth E' a_m) ?E')"
        unfolding ldropn_Suc_conv_ldropn[OF a_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat a_m) E') (LCons (lnth E' a_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat a_m) E')) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' a_m) ?E')"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''
        where red_a: "mthr.if.redT \<sigma>' (t_a, ta_a) \<sigma>''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' ?E'"
        unfolding E'_a_m by cases
      from New_ta_a a_n have "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a obtain x_a x'_a m'_a 
        where red'_a: "mthr.init_fin t_a (x_a, shr \<sigma>') ta_a (x'_a, m'_a)"
        and \<sigma>''': "redT_upd \<sigma>' t_a ta_a x'_a m'_a \<sigma>''"
        and ts_t_a: "thr \<sigma>' t_a = \<lfloor>(x_a, no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>`
      obtain ta'_a X_a X'_a
        where x_a: "x_a = (Running, X_a)"
        and x'_a: "x'_a = (Running, X'_a)"
        and ta_a: "ta_a = convert_TA_initial (convert_obs_initial ta'_a)"
        and red''_a: "t_a \<turnstile> (X_a, shr \<sigma>') -ta'_a\<rightarrow> (X'_a, m'_a)"
        by cases fastforce+
      from ta_a New_ta_a a_n have New_ta'_a: "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NewHeapElem ad CTn"
        and a_n': "a_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn \<in> set \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a have allocated_m'_a_ad: "ad \<in> allocated m'_a"
        by(auto dest: red_New_allocatedD)
      
      have "a_m \<le> a'_m"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "a'_m < a_m" by simp
        hence "(\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a'_m..<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          by(simp add: setsum_upto_add_nat)
        hence "a' - n < a - n" using `a'_m < a_m` a'_n E'_a'_m unfolding a_conv a'_conv
          by(subst (asm) setsum_head_upt_Suc) simp_all
        with a_a' show False by simp
      qed
  
      have a'_less: "a' - n < (a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence a'_greater: "(a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> \<le> a' - n" by simp
        
        have "a_m < a'_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          with `a_m \<le> a'_m` have "a_m = a'_m" by simp
          with a'_greater a_n a'_n E'_a'_m E'_a_m show False
            unfolding a_conv a'_conv by simp
        qed
        hence a'_m_a_m: "enat (a'_m - Suc a_m) < llength ?E'" using a'_m
          by(cases "llength E'") simp_all
        from `a_m < a'_m` a'_m E'_a'_m
        have E'_a'_m': "lnth ?E' (a'_m - Suc a_m) = (t_a', ta_a')" by simp
    
        have E'_unfold': "?E' = lappend (ltake (enat (a'_m - Suc a_m)) ?E') (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E'))"
          unfolding ldropn_Suc_conv_ldropn[OF a'_m_a_m] lappend_ltake_enat_ldropn ..
        hence "mthr.if.mthr.Runs \<sigma>'' (lappend (ltake (enat (a'_m - Suc a_m)) ?E') (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E')))"
          using \<tau>Runs'' by simp
        then obtain \<sigma>'''
          where \<sigma>''_\<sigma>''': "mthr.if.mthr.Trsys \<sigma>'' (list_of (ltake (enat (a'_m - Suc a_m)) ?E')) \<sigma>'''"
          and \<tau>Runs''': "mthr.if.mthr.Runs \<sigma>''' (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E'))"
          by(rule mthr.if.mthr.Runs_lappendE) simp
        from \<tau>Runs''' obtain \<sigma>''''
          where red_a': "mthr.if.redT \<sigma>''' (t_a', ta_a') \<sigma>''''"
          and \<tau>Runs'''': "mthr.if.mthr.Runs \<sigma>'''' (ldropn (Suc (a'_m - Suc a_m)) ?E')"
          unfolding E'_a'_m' by cases
        from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
          unfolding in_set_conv_nth by blast
        with red_a' obtain x_a' x'_a' m'_a' 
          where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>''') ta_a' (x'_a', m'_a')"
          and \<sigma>'''''': "redT_upd \<sigma>''' t_a' ta_a' x'_a' m'_a' \<sigma>''''"
          and ts_t_a': "thr \<sigma>''' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
          by cases auto
        from red'_a' `NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>`
        obtain ta'_a' X_a' X'_a' 
          where x_a': "x_a' = (Running, X_a')"
          and x'_a': "x'_a' = (Running, X'_a')"
          and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
          and red''_a': "t_a' \<turnstile> (X_a', shr \<sigma>''') -ta'_a'\<rightarrow> (X'_a', m'_a')"
          by cases fastforce+
        from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
          and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
        hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
        with red''_a' have allocated_ad': "ad \<notin> allocated (shr \<sigma>''')"
          by(auto dest: red_New_allocatedD)
    
        have "allocated m'_a = allocated (shr \<sigma>'')" using \<sigma>''' by auto
        also have "\<dots> \<subseteq> allocated (shr \<sigma>''')"
          using \<sigma>''_\<sigma>''' unfolding mthr.if.RedT_def[symmetric] by(rule init_fin_RedT_allocated_mono)
        finally have "ad \<in> allocated (shr \<sigma>''')" using allocated_m'_a_ad by blast
        with allocated_ad' show False by contradiction
      qed
      
      from `a_m \<le> a'_m` have [simp]: "a_m = a'_m"
      proof(rule le_antisym)
        show "a'_m \<le> a_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence "a_m < a'_m" by simp
          hence "(\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a_m..<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            by(simp add: setsum_upto_add_nat)
          with a'_less `a_m < a'_m` E'_a_m a_n a'_n show False
            unfolding a'_conv a_conv by(subst (asm) setsum_head_upt_Suc) simp_all
        qed
      qed
      with E'_a_m E'_a'_m have [simp]: "t_a' = t_a" "ta_a' = ta_a" by simp_all
      from New_ta_a' a'_n ta_a have a'_n': "a'_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>"
        and New_ta'_a': "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'" by auto
      with red''_a New_ta'_a a_n' have "a'_n = a_n"
        by(auto dest: red_New_same_addr_same)
      with `a_m = a'_m` have "a - n = a' - n" unfolding a_conv a'_conv by simp
      thus ?thesis using `n \<le> a` `n \<le> a'` by simp
    qed
  qed
qed

end


text {* Knowledge of addresses of a multithreaded state *}

fun ka_Val :: "'addr val \<Rightarrow> 'addr set"
where
  "ka_Val (Addr a) = {a}"
| "ka_Val _ = {}"

fun new_obs_addr :: "('addr, 'thread_id) obs_event \<Rightarrow> 'addr set"
where
  "new_obs_addr (ReadMem ad al (Addr ad')) = {ad'}"
| "new_obs_addr (NewObj ad C) = {ad}"
| "new_obs_addr (NewArr ad T n) = {ad}"
| "new_obs_addr _ = {}"

lemma new_obs_addr_cases[consumes 1, case_names ReadMem NewHeapElem, cases set]:
  assumes "ad \<in> new_obs_addr ob"
  obtains ad' al where "ob = ReadMem ad' al (Addr ad)"
  | CTn where "ob = NewHeapElem ad CTn"
using assms
by(cases ob rule: new_obs_addr.cases) auto

definition new_obs_addrs :: "('addr, 'thread_id) obs_event list \<Rightarrow> 'addr set"
where
  "new_obs_addrs obs = (\<Union>new_obs_addr ` set obs)"

fun new_obs_addr_if :: "('addr, 'thread_id) obs_event action \<Rightarrow> 'addr set"
where
  "new_obs_addr_if (NormalAction a) = new_obs_addr a"
| "new_obs_addr_if _ = {}"

definition new_obs_addrs_if :: "('addr, 'thread_id) obs_event action list \<Rightarrow> 'addr set"
where 
  "new_obs_addrs_if obs = (\<Union>new_obs_addr_if ` set obs)"

lemma ka_Val_subset_new_obs_Addr_ReadMem:
  "ka_Val v \<subseteq> new_obs_addr (ReadMem ad al v)"
by(cases v) simp_all

lemma typeof_ka: "typeof v \<noteq> None \<Longrightarrow> ka_Val v = {}"
by(cases v) simp_all

lemma ka_Val_undefined_value [simp]:
  "ka_Val undefined_value = {}"
apply(cases "undefined_value :: 'a val")
apply(bestsimp simp add: undefined_value_not_Addr dest: subst)+
done

locale known_addrs_base =
  fixes known_addrs :: "'t \<Rightarrow> 'x \<Rightarrow> 'addr set"
begin

definition known_addrs_thr :: "('l, 't, 'x) thread_info \<Rightarrow> 'addr set"
where "known_addrs_thr ts = (\<Union>t \<in> dom ts. known_addrs t (fst (the (ts t))))"

definition known_addrs_state :: "('l,'t,'x,'m,'w) state \<Rightarrow> 'addr set"
where "known_addrs_state s = known_addrs_thr (thr s)"

lemma known_addrs_state_simps [simp]:
  "known_addrs_state (ls, (ts, m), ws) = known_addrs_thr ts"
by(simp add: known_addrs_state_def)

lemma known_addrs_thr_cases[consumes 1, case_names known_addrs, cases set: known_addrs_thr]:
  assumes "ad \<in> known_addrs_thr ts"
  obtains t x ln where "ts t = \<lfloor>(x, ln)\<rfloor>" "ad \<in> known_addrs t x"
using assms
by(auto simp add: known_addrs_thr_def ran_def)

lemma known_addrs_stateI:
  "\<lbrakk> ad \<in> known_addrs t x; thr s t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> ad \<in> known_addrs_state s"
by(fastforce simp add: known_addrs_state_def known_addrs_thr_def intro: rev_bexI)

fun known_addrs_if :: "'t \<Rightarrow> status \<times> 'x \<Rightarrow> 'addr set"
where "known_addrs_if t (s, x) = known_addrs t x"

end

locale if_known_addrs_base = 
  known_addrs_base known_addrs 
  +
  multithreaded_base final r convert_RA
  for known_addrs :: "'t \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 't, 'x, 'heap, 'addr, 'obs) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and convert_RA :: "'addr released_locks \<Rightarrow> 'obs list"

sublocale if_known_addrs_base < "if"!: known_addrs_base known_addrs_if .

locale known_addrs =
  allocated_multithreaded
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    allocated
    final r
    P 
  +
  if_known_addrs_base known_addrs final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"

  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and known_addrs :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and P :: "'md prog"
  +
  assumes red_known_addrs_new:
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>
  \<Longrightarrow> known_addrs t x' \<subseteq> known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and red_known_addrs_new_thread:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> known_addrs t' x'' \<subseteq> known_addrs t x"
  and red_read_knows_addr:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> known_addrs t x"
  and red_write_knows_addr:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad' \<in> known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  -- "second possibility necessary for @{term heap_clone}"
  and red_hext_incr: "t \<turnstile> (x, m) -ta\<rightarrow> (x', m') \<Longrightarrow> m \<unlhd> m'"
begin

notation mthr.redT_syntax1 ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)

lemma if_red_known_addrs_new: 
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  shows "known_addrs_if t x' \<subseteq> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by cases(auto dest!: red_known_addrs_new simp add: new_obs_addrs_if_def new_obs_addrs_def)

lemma if_red_known_addrs_new_thread:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "known_addrs_if t' x'' \<subseteq> known_addrs_if t x"
using assms
by cases(fastforce dest: red_known_addrs_new_thread)+

lemma if_red_read_knows_addr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> known_addrs_if t x"
using assms
by cases(fastforce dest: red_read_knows_addr)+

lemma if_red_write_knows_addr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = NormalAction (WriteMem ad al (Addr ad'))" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad' \<in> known_addrs_if t x \<or> ad' \<in> new_obs_addrs_if (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using assms
by cases(auto dest: red_write_knows_addr simp add: new_obs_addrs_if_def new_obs_addrs_def take_map)

lemma if_redT_known_addrs_new:
  assumes redT: "mthr.if.redT s (t, ta) s'"
  shows "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using redT
proof(cases)
  case redT_acquire thus ?thesis
    by(cases s)(fastforce simp add: if.known_addrs_thr_def split: split_if_asm intro: rev_bexI)
next
  case (redT_normal x x' m)
  note red = `t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m)`
  show ?thesis
  proof
    fix ad
    assume "ad \<in> if.known_addrs_state s'"
    hence "ad \<in> if.known_addrs_thr (thr s')" by(simp add: if.known_addrs_state_def)
    then obtain t' x'' ln'' where ts't': "thr s' t' = \<lfloor>(x'', ln'')\<rfloor>" 
      and ad: "ad \<in> known_addrs_if t' x''"
      by(rule if.known_addrs_thr_cases)
    show "ad \<in> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    proof(cases "thr s t'")
      case None
      with redT_normal `thr s' t' = \<lfloor>(x'', ln'')\<rfloor>`
      obtain m'' where "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(fastforce dest: redT_updTs_new_thread split: split_if_asm)
      with red have "known_addrs_if t' x'' \<subseteq> known_addrs_if t x" by(rule if_red_known_addrs_new_thread)
      also have "\<dots> \<subseteq> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
      finally have "ad \<in> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" using ad by blast
      thus ?thesis using `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` by(blast intro: if.known_addrs_stateI)
    next
      case (Some xln)
      show ?thesis
      proof(cases "t = t'")
        case True
        with redT_normal ts't' if_red_known_addrs_new[OF red] ad
        have "ad \<in> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by auto
        thus ?thesis using `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>` by(blast intro: if.known_addrs_stateI)
      next
        case False
        with ts't' redT_normal ad Some show ?thesis
          by(fastforce dest: redT_updTs_Some[where ts="thr s" and t=t'] intro: if.known_addrs_stateI)
      qed
    qed
  qed
qed

lemma if_redT_read_knows_addr:
  assumes redT: "mthr.if.redT s (t, ta) s'"
  and read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> if.known_addrs_state s"
using redT
proof(cases)
  case redT_acquire thus ?thesis using read by auto
next
  case (redT_normal x x' m')
  with if_red_read_knows_addr[OF `t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m')` read]
  show ?thesis
    by(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def intro: bexI[where x=t])
qed

lemma init_fin_redT_known_addrs_subset:
  assumes "mthr.if.redT s (t, ta) s'"
  shows "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> known_addrs_if t (fst (the (thr s' t)))"
using assms
apply(cases)
 apply(rule subsetI)
 apply(clarsimp simp add: if.known_addrs_thr_def split: split_if_asm)
 apply(rename_tac status x status' x' m' a ws' t'' status'' x'' ln'')
 apply(case_tac "thr s t''")
  apply(drule (2) redT_updTs_new_thread)
  apply clarsimp
  apply(drule (1) if_red_known_addrs_new_thread)
  apply simp
  apply(drule (1) subsetD)
  apply(rule_tac x="(status, x)" in if.known_addrs_stateI)
   apply(simp)
  apply simp
 apply(frule_tac t="t''" in redT_updTs_Some, assumption)
 apply clarsimp
 apply(rule_tac x="(status'', x'')" in if.known_addrs_stateI)
  apply simp
 apply simp
apply(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def split: split_if_asm)
done

lemma init_fin_hext_incr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  shows "m \<unlhd> m'"
using assms
by(cases)(auto intro: red_hext_incr)

lemma init_fin_redT_hext_incr:
  assumes "mthr.if.redT s (t, ta) s'"
  shows "shr s \<unlhd> shr s'"
using assms
by(cases)(auto dest: init_fin_hext_incr)

lemma init_fin_RedT_hext_incr:
  assumes "mthr.if.RedT s ttas s'"
  shows "shr s \<unlhd> shr s'"
using assms
by(induct rule: mthr.if.RedT_induct')(blast dest: init_fin_redT_hext_incr intro: hext_trans)+

lemma redT_ta_seq_consist_known_addrs_allocated:
  assumes red: "mthr.if.redT s (t, ta) s'"
  and tasc: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and ka: "if.known_addrs_state s \<subseteq> allocated (shr s)"
  and vs: "mrw_addrs vs \<subseteq> allocated (shr s)"
  shows "if.known_addrs_state s' \<subseteq> allocated (shr s')" (is "?thesis1")
  and "mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> allocated (shr s')" (is "?thesis2")
proof -
  have "?thesis1 \<and> ?thesis2" using red
  proof(cases)
    case (redT_acquire x ln n)
    hence "if.known_addrs_state s' = if.known_addrs_state s"
      by(auto 4 4 simp add: if.known_addrs_state_def if.known_addrs_thr_def split: split_if_asm dest: bspec)
    also note ka 
    also from redT_acquire have "shr s = shr s'" by simp
    finally have "if.known_addrs_state s' \<subseteq> allocated (shr s')" .
    moreover have "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = vs" using redT_acquire
      by(auto simp add: fun_eq_iff intro!: mrw_values_no_write_unchanged dest: convert_RA_not_write)
    ultimately show ?thesis using vs by(simp add: `shr s = shr s'`)
  next
    case (redT_normal x x' m')
    note red = `t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m')`
      and tst = `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`
    have allocated_subset: "allocated (shr s) \<subseteq> allocated (shr s')"
      using `mthr.if.redT s (t, ta) s'` by(rule init_fin_redT_allocated_mono)
    with vs have vs': "mrw_addrs vs \<subseteq> allocated (shr s')" by blast
    { fix obs obs'
      assume "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs @ obs'"
      moreover with tasc have "ta_seq_consist P vs (llist_of obs)"
        by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
      ultimately have "mrw_addrs (mrw_values P vs obs) \<union> new_obs_addrs_if obs \<subseteq> allocated (shr s')" 
        (is "?concl obs")
      proof(induct obs arbitrary: obs' rule: rev_induct)
        case Nil thus ?case using vs' by(simp add: new_obs_addrs_if_def)
      next
        case (snoc ob obs)
        note ta = `\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = (obs @ [ob]) @ obs'`
        note tasc = `ta_seq_consist P vs (llist_of (obs @ [ob]))`
        from snoc have IH: "?concl obs"
          by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
        hence "?concl (obs @ [ob])"
        proof(cases "ob" rule: mrw_value_cases)
          case (1 ad' al v)
          note ob = `ob = NormalAction (WriteMem ad' al v)`
          with ta have Write: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! length obs = NormalAction (WriteMem ad' al v)" by simp
          show ?thesis
          proof
            fix ad''
            assume "ad'' \<in> mrw_addrs (mrw_values P vs (obs @ [ob])) \<union> new_obs_addrs_if (obs @ [ob])"
            hence "ad'' \<in> mrw_addrs (mrw_values P vs obs) \<union> new_obs_addrs_if obs \<or> v = Addr ad''"
              by(auto simp add: ob mrw_addrs_def ran_def new_obs_addrs_if_def split: split_if_asm)
            thus "ad'' \<in> allocated (shr s')"
            proof
              assume "ad'' \<in> mrw_addrs (mrw_values P vs obs) \<union> new_obs_addrs_if obs"
              also note IH finally show ?thesis .
            next
              assume v: "v = Addr ad''"
              with Write have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! length obs = NormalAction (WriteMem ad' al (Addr ad''))" by simp
              with red have "ad'' \<in> known_addrs_if t x \<or> ad'' \<in> new_obs_addrs_if (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
                by(rule if_red_write_knows_addr)(simp add: ta)
              thus ?thesis
              proof
                assume "ad'' \<in> known_addrs_if t x"
                hence "ad'' \<in> if.known_addrs_state s" using tst by(rule if.known_addrs_stateI)
                with ka allocated_subset show ?thesis by blast
              next
                assume "ad'' \<in> new_obs_addrs_if (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
                with ta have "ad'' \<in> new_obs_addrs_if obs" by simp
                with IH show ?thesis by blast
              qed
            qed
          qed
        next
          case (2 ad C)

          hence ob: "ob = NormalAction (NewObj ad C)" by simp
          hence "mrw_addrs (mrw_values P vs (obs @ [ob])) \<subseteq> mrw_addrs (mrw_values P vs obs)"
            by(auto simp add: mrw_addrs_def ran_def default_val_not_Addr Addr_not_default_val image_Collect split del: option.splits)
          moreover from ob ta have "NormalAction (NewHeapElem ad (Class_type C)) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
          from init_fin_red_New_allocatedD[OF red this] have "ad \<in> allocated m'" ..
          with redT_normal have "ad \<in> allocated (shr s')" by auto
          ultimately show ?thesis using IH ob by(auto simp add: new_obs_addrs_if_def)
        next
          case (3 ad T n)
          note ob = `ob = NormalAction (NewArr ad T n)`
          hence "mrw_addrs (mrw_values P vs (obs @ [ob])) \<subseteq> mrw_addrs (mrw_values P vs obs)"
            by(auto simp add: mrw_addrs_def ran_def default_val_not_Addr Addr_not_default_val image_Collect split del: option.splits)
          moreover from ob ta have "NormalAction (NewHeapElem ad (Array_type T n)) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
          from init_fin_red_New_allocatedD[OF red this] have "ad \<in> allocated m'" ..
          with redT_normal have "ad \<in> allocated (shr s')" by auto
          ultimately show ?thesis using IH ob by(auto simp add: new_obs_addrs_if_def)
        next
          case (5 ad al v)
          note ob = `ob = NormalAction (ReadMem ad al v)`
          { fix ad'
            assume v: "v = Addr ad'"
            with tasc ob obtain b where mrw: "mrw_values P vs obs (ad, al) = \<lfloor>(Addr ad', b)\<rfloor>"
              by(auto simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend simp del: lappend_llist_of_llist_of)
            hence "ad' \<in> mrw_addrs (mrw_values P vs obs)"
              by(fastforce simp add: mrw_addrs_def ran_def intro: rev_image_eqI)
            with IH have "ad' \<in> allocated (shr s')" by blast }
          with ob IH show ?thesis by(cases v)(simp_all add: new_obs_addrs_if_def)
        qed(simp_all add: new_obs_addrs_if_def)
        thus ?case by simp
      qed }
    note this[of "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" "[]"]
    moreover have "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
      using `mthr.if.redT s (t, ta) s'` by(rule if_redT_known_addrs_new)
    ultimately show ?thesis using ka allocated_subset by blast
  qed
  thus ?thesis1 ?thesis2 by simp_all
qed


lemma RedT_ta_seq_consist_known_addrs_allocated:
  assumes red: "mthr.if.RedT s ttas s'"
  and tasc: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and ka: "if.known_addrs_state s \<subseteq> allocated (shr s)"
  and vs: "mrw_addrs vs \<subseteq> allocated (shr s)"
  shows "if.known_addrs_state s' \<subseteq> allocated (shr s')" (is "?thesis1 s'")
  and "mrw_addrs (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<subseteq> allocated (shr s')" (is "?thesis2 s' ttas")
proof -
  from red tasc have "?thesis1 s' \<and> ?thesis2 s' ttas"
  proof(induct rule: mthr.if.RedT_induct')
    case refl thus ?case using ka vs by simp
  next
    case (step ttas s' t ta s'')
    hence "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      and "?thesis1 s'" "?thesis2 s' ttas"
      by(simp_all add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
    from redT_ta_seq_consist_known_addrs_allocated[OF `mthr.if.redT s' (t, ta) s''` this]
    show ?case by simp
  qed
  thus "?thesis1 s'" "?thesis2 s' ttas" by simp_all
qed

lemma read_ex_NewHeapElem [consumes 5, case_names start Red]:
  assumes RedT: "mthr.if.RedT (init_fin_lift_state status (start_state f P C M vs)) ttas s"
  and red: "mthr.if.redT s (t, ta) s'"
  and read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and sc: "ta_seq_consist P empty (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and known: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  obtains (start) CTn where "NewHeapElem ad CTn \<in> set start_heap_obs"
  | (Red) ttas' s'' t' ta' s''' ttas'' CTn
  where "mthr.if.RedT (init_fin_lift_state status (start_state f P C M vs)) ttas' s''"
  and "mthr.if.redT s'' (t', ta') s'''"
  and "mthr.if.RedT s''' ttas'' s"
  and "ttas = ttas' @ (t', ta') # ttas''"
  and "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
proof -
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"
  let ?obs_prefix = "lift_start_obs start_tid start_heap_obs"
  let ?vs_start = "mrw_values P empty (map snd ?obs_prefix)"

  from sc have "ta_seq_consist P (mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs))) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    by(simp add: ta_seq_consist_lappend lappend_llist_of_llist_of[symmetric] del: lappend_llist_of_llist_of)
  with RedT have "if.known_addrs_state s \<subseteq> allocated (shr s)"
  proof(rule RedT_ta_seq_consist_known_addrs_allocated)
    show "if.known_addrs_state ?start_state \<subseteq> allocated (shr ?start_state)"
      using known
      by(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def start_state_def init_fin_lift_state_def split_beta split: split_if_asm)
    
    have "mrw_addrs ?vs_start \<subseteq> mrw_addrs empty" by(rule mrw_addrs_lift_start_heap_obs)
    thus "mrw_addrs ?vs_start \<subseteq> allocated (shr ?start_state)" by simp
  qed
  also from red read obtain x_ra x'_ra m'_ra 
    where red'_ra: "t \<turnstile> (x_ra, shr s) -ta\<rightarrow>i (x'_ra, m'_ra)"
    and s': "redT_upd s t ta x'_ra m'_ra s'"
    and ts_t: "thr s t = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
    by cases auto
  from red'_ra read
  have "ad \<in> known_addrs_if t x_ra" by(rule if_red_read_knows_addr)
  hence "ad \<in> if.known_addrs_state s" using ts_t by(rule if.known_addrs_stateI)
  finally have "ad \<in> allocated (shr s)" .

  show ?thesis
  proof(cases "ad \<in> allocated start_heap")
    case True
    then obtain CTn where "NewHeapElem ad CTn \<in> set start_heap_obs"
      unfolding start_addrs_allocated by(blast dest: start_addrs_NewHeapElem_start_heap_obsD)
    thus ?thesis by(rule start)
  next
    case False
    hence "ad \<notin> allocated (shr ?start_state)" by(simp add: start_state_def split_beta shr_init_fin_lift_state)
    with RedT `ad \<in> allocated (shr s)` obtain t' ta' CTn
      where tta: "(t', ta') \<in> set ttas"
      and new: "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
      by(blast dest: init_fin_RedT_allocated_NewHeapElemD)
    from tta obtain ttas' ttas'' where ttas: "ttas = ttas' @ (t', ta') # ttas''" by(auto dest: split_list)
    with RedT obtain s'' s''' 
      where "mthr.if.RedT ?start_state ttas' s''"
      and "mthr.if.redT s'' (t', ta') s'''"
      and "mthr.if.RedT s''' ttas'' s"
      unfolding mthr.if.RedT_def by(auto elim!: rtrancl3p_appendE dest!: converse_rtrancl3p_step)
    thus thesis using ttas new by(rule Red)
  qed
qed

end

locale known_addrs_typing =
  known_addrs
    addr2thread_id thread_id2addr
    empty_heap new_obj new_arr typeof_addr array_length heap_read heap_write
    allocated known_addrs
    final r P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"

  and empty_heap :: "'heap"
  and new_obj :: "'heap \<Rightarrow> cname \<Rightarrow> ('heap \<times> 'addr option)"
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ('heap \<times> 'addr option)"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> ty"
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and known_addrs :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and wfx :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'md prog"
  +
  assumes wfs_ta_seq_consist_invar:
  "\<lbrakk> mthr.redT s (t, ta) s'; ts_ok wfx (thr s) (shr s); 
     vs_conf P (shr s) vs; ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<rbrakk>
  \<Longrightarrow> ts_ok wfx (thr s') (shr s') \<and> vs_conf P (shr s') (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and red_read_typeable:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T. P,m \<turnstile> ad@al : T"
  and red_NewObjD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; NewObj ad C \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr m' ad = \<lfloor>Class C\<rfloor>"
  and red_NewArrD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; NewArr ad T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr m' ad = \<lfloor>T\<lfloor>\<rceil>\<rfloor> \<and> array_length m' ad = n"
begin

lemma if_redT_ta_seq_consist_invar:
  assumes red: "mthr.if.redT s (t, ta) s'"
  and ts_ok: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" 
  and vs: "vs_conf P (shr s) vs"
  shows "ts_ok (init_fin_lift wfx) (thr s') (shr s')" (is ?thesis1)
  and "vs_conf P (shr s') (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" (is ?thesis2)
proof -
  let ?s = "\<lambda>s. (locks s, (\<lambda>t. Option.map (\<lambda>((status, x), ln). (x, ln)) (thr s t), shr s), wset s, interrupts s)"
  
  from ts_ok have ts_ok': "ts_ok wfx (thr (?s s)) (shr (?s s))" by(auto intro!: ts_okI dest: ts_okD)
  from vs have vs': "vs_conf P (shr (?s s)) vs" by simp

  from red have "?thesis1 \<and> ?thesis2"
  proof(cases)
    case (redT_normal x x' m)
    note tst = `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`
    from `t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m)`
    show ?thesis 
    proof(cases)
      case (NormalAction X TA X')
      from `ta = convert_TA_initial (convert_obs_initial TA)` `mthr.if.actions_ok s t ta`
      have "mthr.actions_ok (?s s) t TA"
        by(auto elim: rev_iffD1[OF _ thread_oks_ts_change] cond_action_oks_final_change)

      with tst NormalAction `redT_upd s t ta x' m s'` have "mthr.redT (?s s) (t, TA) (?s s')"
        using map_redT_updTs[of snd "thr s" "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"]
        by(auto intro!: mthr.redT.intros simp add: split_def map_pair_def o_def fun_eq_iff)
      moreover note ts_ok' vs'
      moreover from `ta = convert_TA_initial (convert_obs_initial TA)` have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>" by(auto)
      with sc have "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>))" by simp
      ultimately have "ts_ok wfx (thr (?s s')) (shr (?s s')) \<and> vs_conf P (shr (?s s')) (mrw_values P vs (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>))"
        by(rule wfs_ta_seq_consist_invar)
      thus ?thesis using `\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>` by(auto intro!: ts_okI dest: ts_okD)
    next
      case InitialThreadAction
      with redT_normal ts_ok' vs show ?thesis
        by(auto 4 3 intro!: ts_okI dest: ts_okD split: split_if_asm)
    next
      case ThreadFinishAction
      with redT_normal ts_ok' vs show ?thesis
        by(auto 4 3 intro!: ts_okI dest: ts_okD split: split_if_asm)
    qed
  next
    case (redT_acquire x ln l)
    have "mrw_values P vs (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list)) = vs"
      by(auto simp add: convert_RA_not_write fun_eq_iff intro!: mrw_values_no_write_unchanged)
    thus ?thesis using vs ts_ok redT_acquire by(auto 4 3 intro!: ts_okI dest: ts_okD split: split_if_asm)
  qed
  thus ?thesis1 ?thesis2 by(rule conjunct1 conjunct2)+
qed
      
lemma if_RedT_ta_seq_consist_invar:
  assumes red: "mthr.if.RedT s ttas s'"
  and tsok: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and vs: "vs_conf P (shr s) vs"
  shows "ts_ok (init_fin_lift wfx) (thr s') (shr s')" (is ?thesis1)
  and "vs_conf P (shr s') (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))" (is ?thesis2)
using red tsok sc vs unfolding mthr.if.RedT_def
proof(induct arbitrary: vs rule: rtrancl3p_converse_induct')
  case refl
  case 1 thus ?case by -
  case 2 thus ?case by simp
next
  case (step s tta s' ttas)
  obtain t ta where tta: "tta = (t, ta)" by(cases tta)

  case 1
  hence sc1: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    and sc2: "ta_seq_consist P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lconcat_llist_of[symmetric] lmap_llist_of[symmetric] lmap_compose[symmetric] o_def llist_of.simps lmap_LCons lconcat_LCons tta
    by(simp_all add: ta_seq_consist_lappend list_of_lconcat o_def)
  from if_redT_ta_seq_consist_invar[OF step(2)[unfolded tta] _ sc1] 1 step.hyps(3)[of "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] sc2
  show ?case by simp

  case 2
  hence sc1: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    and sc2: "ta_seq_consist P (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lconcat_llist_of[symmetric] lmap_llist_of[symmetric] lmap_compose[symmetric] o_def llist_of.simps lmap_LCons lconcat_LCons tta
    by(simp_all add: ta_seq_consist_lappend list_of_lconcat o_def)
  from if_redT_ta_seq_consist_invar[OF step(2)[unfolded tta] _ sc1] 2 step.hyps(4)[of "mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] sc2
  show ?case by(simp add: tta o_def)
qed

lemma executions_sc:
  assumes wf: "wf_syscls P"
  and ok: "start_heap_ok"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and vs_conf_start: "vs_conf P start_heap (mrw_values P empty (map NormalAction start_heap_obs))"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows
  "executions_sc (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))) P"
  (is "executions_sc ?E P")
proof
  fix E a adal a'
  assume "E \<in> ?E" "a \<in> new_actions_for P E adal" "a' \<in> new_actions_for P E adal"
  thus "a = a'" by(rule \<E>_new_actions_for_unique)
next

  let ?obs_prefix = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"

  fix E ra adal
  assume E: "E \<in> ?E"
    and "ra \<in> read_actions E"
    and "adal \<in> action_loc P E ra"
    and sc: "ta_seq_consist P empty (ltake (enat ra) (lmap snd E))"
  moreover obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  ultimately obtain v where ra: "action_obs E ra = NormalAction (ReadMem ad al v)"
    and ra_len: "enat ra < llength E"
    by(cases "lnth E ra")(fastforce elim!: read_actions.cases actionsE)

  from E obtain E'' where E: "E = lappend (llist_of ?obs_prefix) E''"
    and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto
  from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)

  have ra_len': "length ?obs_prefix \<le> ra"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "ra < length ?obs_prefix" by simp
    moreover with ra ra_len E obtain ra' ad al v 
      where "start_heap_obs ! ra' = ReadMem ad al v" "ra' < length start_heap_obs"
      by(cases ra)(auto simp add: lnth_LCons lnth_lappend1 action_obs_def lift_start_obs_def)
    ultimately have "ReadMem ad al v \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
    thus False by(simp add: start_heap_obs_not_Read)
  qed
  let ?n = "length ?obs_prefix"
  from ra ra_len ra_len' E have "enat (ra - ?n) < llength E''"
    and ra_obs: "action_obs E'' (ra - ?n) = NormalAction (ReadMem ad al v)"
    by(cases "llength E''", auto simp add: action_obs_def lnth_lappend2)
  
  from \<tau>Runs `enat (ra - ?n) < llength E''` obtain ra_m ra_n t_ra ta_ra 
    where E_ra: "lnth E'' (ra - ?n) = (t_ra, \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub> ! ra_n)"
    and ra_n: "ra_n < length \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>" and ra_m: "enat ra_m < llength E'"
    and ra_conv: "ra - ?n = (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + ra_n"
    and E'_ra_m: "lnth E' ra_m = (t_ra, ta_ra)"
    unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
  let ?E' = "ldropn (Suc ra_m) E'"
    
  have E'_unfold: "E' = lappend (ltake (enat ra_m) E') (LCons (lnth E' ra_m) ?E')"
    unfolding ldropn_Suc_conv_ldropn[OF ra_m] by simp
  hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat ra_m) E') (LCons (lnth E' ra_m) ?E'))"
    using \<tau>Runs by simp
  then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat ra_m) E')) \<sigma>'"
    and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' ra_m) ?E')"
    by(rule mthr.if.mthr.Runs_lappendE) simp
  from \<tau>Runs' obtain \<sigma>'' where red_ra: "mthr.if.redT \<sigma>' (t_ra, ta_ra) \<sigma>''"
    and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' ?E'"
    unfolding E'_ra_m by cases

  from E_ra ra_n ra_obs have "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>"
    by(auto simp add: action_obs_def in_set_conv_nth)
  with red_ra obtain x_ra x'_ra m'_ra 
    where red'_ra: "mthr.init_fin t_ra (x_ra, shr \<sigma>') ta_ra (x'_ra, m'_ra)"
    and \<sigma>'': "redT_upd \<sigma>' t_ra ta_ra x'_ra m'_ra \<sigma>''"
    and ts_t_a: "thr \<sigma>' t_ra = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
    by cases auto
  from red'_ra `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>`
  obtain ta'_ra X_ra X'_ra
    where x_ra: "x_ra = (Running, X_ra)"
    and x'_ra: "x'_ra = (Running, X'_ra)"
    and ta_ra: "ta_ra = convert_TA_initial (convert_obs_initial ta'_ra)"
    and red''_ra: "t_ra \<turnstile> (X_ra, shr \<sigma>') -ta'_ra\<rightarrow> (X'_ra, m'_ra)"
    by cases fastforce+

  from `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>` ta_ra 
  have "ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>" by auto

  from wfx_start have wfx_start: "ts_ok (init_fin_lift wfx) (thr ?start_state) (shr ?start_state)"
    by(simp add: start_state_def split_beta)

  from sc ra_len'
  have "ta_seq_consist P (mrw_values P empty (map snd ?obs_prefix))
    (lmap snd (ltake (enat (ra - ?n)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))))"
    unfolding E E' by(simp add: ltake_lappend2 lmap_lappend_distrib ta_seq_consist_lappend)
  also note ra_conv also note plus_enat_simps(1)[symmetric]
  also have "enat (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<ra_m. enat (length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))"
    by(subst setsum_hom[symmetric])(simp_all add: zero_enat_def)
  also have "\<dots> = (\<Sum>i<ra_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i))"
    using ra_m by-(rule setsum_cong[OF refl], simp add: le_less_trans[where y="enat ra_m"] split_beta)
  also note ltake_plus_conv_lappend also note lconcat_ltake[symmetric]
  also note lmap_lappend_distrib
  also note ta_seq_consist_lappend
  finally have "ta_seq_consist P (mrw_values P empty (map snd ?obs_prefix)) (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of (list_of (ltake (enat ra_m) E'))))))"
    by(simp add: split_def)
  hence sc': "ta_seq_consist P (mrw_values P empty (map snd ?obs_prefix)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat ra_m) E')))))"
    unfolding lmap_lconcat lmap_compose[symmetric] o_def lconcat_llist_of[symmetric] lmap_llist_of[symmetric]
    by(simp add: split_beta o_def)

  from vs_conf_start have vs_conf_start: "vs_conf P (shr ?start_state) (mrw_values P empty (map snd ?obs_prefix))"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta lift_start_obs_def o_def)
  with \<sigma>_\<sigma>' wfx_start sc' have "ts_ok (init_fin_lift wfx) (thr \<sigma>') (shr \<sigma>')"
    unfolding mthr.if.RedT_def[symmetric] by(rule if_RedT_ta_seq_consist_invar)
  with ts_t_a have "wfx t_ra X_ra (shr \<sigma>')" unfolding x_ra by(auto dest: ts_okD)

  with red''_ra `ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>`
  obtain T' where type_adal: "P,shr \<sigma>' \<turnstile> ad@al : T'" by(auto dest: red_read_typeable)

  from sc ra_len' have "ta_seq_consist P empty (llist_of (map snd ?obs_prefix))"
    unfolding E by(simp add: ltake_lappend2 lmap_lappend_distrib ta_seq_consist_lappend)
  with sc' have sc'': "ta_seq_consist P Map.empty (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat ra_m) E')))))"
    by(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)

  from \<sigma>_\<sigma>' red_ra `NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>` sc'' ka
  show "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
    unfolding mthr.if.RedT_def[symmetric]
  proof(cases rule: read_ex_NewHeapElem)
    case (start CTn)
    then obtain n where n: "start_heap_obs ! n = NewHeapElem ad CTn" 
      and len: "n < length start_heap_obs"
      unfolding in_set_conv_nth by blast
    from len have "Suc n \<in> actions E" unfolding E by(simp add: actions_def enat_less_enat_plusI)
    moreover
    from \<sigma>_\<sigma>' have hext: "start_heap \<unlhd> shr \<sigma>'" unfolding mthr.if.RedT_def[symmetric]
      by(auto dest!: init_fin_RedT_hext_incr simp add: start_state_def split_beta init_fin_lift_state_conv_simps)

    have "adal \<in> action_loc P E (Suc n)"
    proof(cases "CTn")
      case (Class_type C)[simp]
      with start have "typeof_addr start_heap ad = \<lfloor>Class C\<rfloor>"
        by(auto dest: NewObj_start_heap_obsD[OF wf])
      with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>Class C\<rfloor>" by(rule typeof_addr_hext_mono)
      with type_adal show ?thesis using n len unfolding E adal
        by cases(auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    next
      case (Array_type U si)[simp]
      with start have "typeof_addr start_heap ad = \<lfloor>Array U\<rfloor>"
        and "array_length start_heap ad = si" by(auto dest: NewArr_start_heap_obsD)
      with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>Array U\<rfloor>" "array_length (shr \<sigma>') ad = si"
        by(auto dest: hext_arrD)
      with type_adal show ?thesis using n len unfolding E adal
        by cases(auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def dest: has_field_decl_above)
    qed
    moreover have "is_new_action (action_obs E (Suc n))" using n len unfolding E
      by(simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    ultimately have "Suc n \<in> new_actions_for P E adal" by(rule new_actionsI)
    moreover have "Suc n < ra" using ra_len' len by(simp)
    ultimately show ?thesis by blast
  next
    case (Red ttas' s'' t' ta' s''' ttas'' CTn)
    from `mthr.if.RedT s''' ttas'' \<sigma>'` have hext: "shr s''' \<unlhd> shr \<sigma>'" by(rule init_fin_RedT_hext_incr)
    
    from `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>`
    obtain obs obs' where obs: "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = obs @ NormalAction (NewHeapElem ad CTn) # obs'"
      by(auto dest: split_list)
    
    let ?wa = "?n + length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs"
    have "enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas' @ [(t', ta')]))))"
      using obs by simp
    also have "\<dots> = llength (lconcat (lmap llist_of (lmap (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas' @ [(t', ta')])))))"
      by(simp del: map_map map_append add: lconcat_llist_of)
    also have "\<dots> \<le> llength (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas' @ (t', ta') # ttas''))))"
      by(auto simp add: o_def split_def intro: lprefix_llist_ofI intro!: lprefix_lconcatI lprefix_llength_le)
    also note len_less = calculation
    have "\<dots> \<le> (\<Sum>i<ra_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E') i))"
      unfolding `list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''`[symmetric]
      by(simp add: ltake_lmap[symmetric] lconcat_ltake del: ltake_lmap)
    also have "\<dots> = enat (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)" using ra_m
      by(subst setsum_hom[symmetric, where f="enat"])(auto intro: setsum_cong simp add: zero_enat_def less_trans[where y="enat ra_m"] split_beta)
    also have "\<dots> \<le> enat (ra - ?n)" unfolding ra_conv by simp
    finally have wa_ra: "?wa < ra" by simp
    with ra_len have "?wa \<in> actions E" by(cases "llength E")(simp_all add: actions_def)
    moreover
    from `mthr.if.redT s'' (t', ta') s'''` `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>`
    obtain x_wa x_wa' where ts''t': "thr s'' t' = \<lfloor>(x_wa, no_wait_locks)\<rfloor>"
      and red_wa: "mthr.init_fin t' (x_wa, shr s'') ta' (x_wa', shr s''')"
      by(cases) fastforce+

    from sc'
    have "ta_seq_consist P (mrw_values P empty (map snd ?obs_prefix)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
      unfolding `list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''`
      by(simp add: lappend_llist_of_llist_of[symmetric] lmap_lappend_distrib ta_seq_consist_lappend del: lappend_llist_of_llist_of)
    with `mthr.if.RedT ?start_state ttas' s''` wfx_start 
    have "ts_ok (init_fin_lift wfx) (thr s'') (shr s'')"
      using vs_conf_start by(rule if_RedT_ta_seq_consist_invar)
    with ts''t' have wfxt': "wfx t' (snd x_wa) (shr s'')" by(cases x_wa)(auto dest: ts_okD)

    {
      have "action_obs E ?wa = 
        snd (lnth (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')) (length (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs))"
        unfolding E E' by(simp add: action_obs_def lnth_lappend2)
      also from `enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < enat (ra - length (lift_start_obs start_tid start_heap_obs))` `enat (ra - ?n) < llength E''`
      have "\<dots> = lnth (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E')) (length (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs)"
        unfolding E'
        by(subst lnth_lmap[symmetric, where f=snd])(erule (1) less_trans, simp add: lmap_lconcat lmap_compose[symmetric] o_def split_def del: lmap_compose)
      also from len_less
      have "enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < llength (lconcat (ltake (enat ra_m) (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E')))"
        unfolding `list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''`[symmetric]
        by(simp add: ltake_lmap[symmetric] del: ltake_lmap)
      note lnth_lconcat_ltake[OF this, symmetric]
      also note ltake_lmap
      also have "ltake (enat ra_m) E' = llist_of (list_of (ltake (enat ra_m) E'))" by(simp)
      also note `list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''`
      also note lmap_llist_of also have "(\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) = llist_of \<circ> (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
        by(simp add: o_def split_def)
      also note map_map[symmetric] also note lconcat_llist_of
      also note lnth_llist_of 
      also have "concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas' @ (t', ta') # ttas'')) ! (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) = NormalAction (NewHeapElem ad CTn)"
        by(simp add: nth_append obs)
      finally have "action_obs E ?wa = NormalAction (NewHeapElem ad CTn)" .
    }
    note wa_obs = this

    have "adal \<in> action_loc P E ?wa"
    proof(cases "CTn")
      case (Class_type C)[simp]
      with red_wa have "typeof_addr (shr s''') ad = \<lfloor>Class C\<rfloor>"
        using wfxt' `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>` by cases(auto dest: red_NewObjD)
      with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>Class C\<rfloor>" by(rule typeof_addr_hext_mono)
      with type_adal show ?thesis using wa_obs unfolding E adal
        by cases (auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    next
      case (Array_type U si)[simp]
      from red_wa have "typeof_addr (shr s''') ad = \<lfloor>Array U\<rfloor> \<and> array_length (shr s''') ad = si" 
        using wfxt' `NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>` by cases(auto dest: red_NewArrD)
      with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>Array U\<rfloor>" "array_length (shr \<sigma>') ad = si"
        by(auto dest: hext_arrD)
      with type_adal show ?thesis using wa_obs unfolding E adal
        by cases(auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def dest: has_field_decl_above)
    qed
    moreover have "is_new_action (action_obs E ?wa)" using wa_obs by simp
    ultimately have "?wa \<in> new_actions_for P E adal" by(rule new_actionsI)
    thus ?thesis using wa_ra by blast
  qed
qed

lemma red_known_addrs_mrw_addrs_dom_vs:
  assumes red: "t \<turnstile> (x, h) -ta\<rightarrow> (x', h')"
  and sc: "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and dom_vs: "(\<Union>a \<in> known_addrs t x \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,h \<turnstile> a@al : T}) \<subseteq> dom vs"
  and dom_typeof_addr: "known_addrs t x \<union> mrw_addrs vs \<subseteq> dom (typeof_addr h)"
  and wfx: "wfx t x h"
  shows "(\<Union>a \<in> known_addrs t x' \<union> mrw_addrs (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)). {(a, al) | al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" (is ?thesis1)
  and "known_addrs t x' \<union> mrw_addrs (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<subseteq> dom (typeof_addr h')" (is ?thesis2)
proof -
  from red have hext: "h \<unlhd> h'" by(rule red_hext_incr)

  have dom_vs': "(\<Union>a \<in> known_addrs t x \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom vs"
  proof(rule UN_least)
    fix a
    assume a: "a \<in> known_addrs t x \<union> mrw_addrs vs"
    with dom_typeof_addr obtain T where "typeof_addr h a = \<lfloor>T\<rfloor>" by blast
    moreover note typeof_addr_eq_Some_conv[OF this]
    ultimately have "{(a, al)|al. \<exists>T. P,h' \<turnstile> a@al : T} = {(a, al)|al. \<exists>T. P,h \<turnstile> a@al : T}" using hext
      by(fastforce elim!: addr_loc_type.cases intro: addr_loc_type.intros dest: hext_arrD hext_objD)
    also from dom_vs a have "\<dots> \<subseteq> dom vs" by blast
    finally show "{(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T} \<subseteq> dom vs" .
  qed

  from dom_typeof_addr hext_dom_typeof_addr_subset[OF hext]
  have dom_typeof_addr': "known_addrs t x \<union> mrw_addrs vs \<subseteq> dom (typeof_addr h')"
    by(rule subset_trans)

  { fix obs obs'
    assume ta: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs @ obs'"
    hence "(\<Union>a \<in> new_obs_addrs obs \<union> mrw_addrs (mrw_values P vs (map NormalAction obs)). {(a, al) | al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs (map NormalAction obs)) \<and> new_obs_addrs obs \<union> mrw_addrs (mrw_values P vs (map NormalAction obs)) \<subseteq> dom (typeof_addr h')"
      (is "?concl1 obs \<and> ?concl2 obs")
    proof(induct obs arbitrary: obs' rule: rev_induct)
      case Nil thus ?case using dom_vs' dom_typeof_addr' by(simp add: new_obs_addrs_def)
    next
      case (snoc ob obs)
      let ?vs = "mrw_values P vs (map NormalAction obs)"
      let ?vs' = "mrw_values P vs (map NormalAction (obs @ [ob]))"
      from `\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = (obs @ [ob]) @ obs'` have ta: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs @ ob # obs'" by simp
      hence dom_vs: "?concl1 obs"
        and dom_typeof_addr: "?concl2 obs" by(rule conjunct1[OF snoc.hyps] conjunct2[OF snoc.hyps])+
      thus ?case
      proof(cases "NormalAction ob" rule: mrw_value_cases)
        case (1 ad al v)
        hence ob: "ob = WriteMem ad al v" by simp
        with ta have "write": "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! length obs = WriteMem ad al v" "length obs < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp_all
        from dom_vs have "(\<Union>a\<in>new_obs_addrs obs. {(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom ?vs" by simp
        also have "\<dots> \<subseteq> dom ?vs'" by simp(rule mrw_value_dom_mono)
        also have "(\<Union>a\<in> mrw_addrs ?vs'. {(a, al) |al. \<exists>b. P,h' \<turnstile> a@al : b}) \<subseteq> dom ?vs'" 
        proof(rule UN_least)
          fix a
          assume "a \<in> mrw_addrs ?vs'"
          hence "v = Addr a \<or> a \<in> mrw_addrs ?vs" using ob
            by(auto simp add: mrw_addrs_def ran_def split: split_if_asm)
          hence "{(a, al) |al. \<exists>b. P,h' \<turnstile> a@al : b} \<subseteq> dom ?vs"
          proof
            assume v: "v = Addr a"
            from red "write" have "a \<in> known_addrs t x \<or> a \<in> new_obs_addrs (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
              unfolding v by(rule red_write_knows_addr)
            thus ?thesis
            proof
              assume "a \<in> known_addrs t x"
              hence "{(a, al) |al. \<exists>b. P,h' \<turnstile> a@al : b} \<subseteq> dom vs" using dom_vs' by blast
              also have "\<dots> \<subseteq> dom ?vs" by(rule mrw_values_dom_mono)
              finally show ?thesis .
            next
              assume "a \<in> new_obs_addrs (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
              hence "a \<in> new_obs_addrs obs" by(simp add: ta)
              with dom_vs show ?thesis by blast
            qed
          next
            assume "a \<in> mrw_addrs (mrw_values P vs (map NormalAction obs))"
            with dom_vs show ?thesis by blast
          qed
          also note `\<dots> \<subseteq> dom ?vs'`
          finally show "{(a, al) |al. \<exists>b. P,h' \<turnstile> a@al : b} \<subseteq> dom ?vs'" .
        qed
        ultimately have "?concl1 (obs @ [ob])" by(simp add: ob new_obs_addrs_def del: fun_upd_apply)
        moreover
        have "mrw_addrs ?vs' \<subseteq> dom (typeof_addr h')"
        proof
          fix a
          assume "a \<in> mrw_addrs ?vs'"
          hence "v = Addr a \<or> a \<in> mrw_addrs ?vs" using ob
            by(auto simp add: mrw_addrs_def ran_def split: split_if_asm)
          thus "a \<in> dom (typeof_addr h')"
          proof
            assume v: "v = Addr a"
            from red "write" have "a \<in> known_addrs t x \<or> a \<in> new_obs_addrs (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
              unfolding v by(rule red_write_knows_addr)
            thus ?thesis using dom_typeof_addr' dom_typeof_addr by(auto simp add: ta)
          next
            assume "a \<in> mrw_addrs ?vs"
            with dom_typeof_addr show ?thesis by blast
          qed
        qed
        with dom_typeof_addr have "?concl2 (obs @ [ob])" by(simp add: ob new_obs_addrs_def del: fun_upd_apply)
        ultimately show ?thesis ..
      next
        case (5 ad al v)
        hence ob: "ob = ReadMem ad al v" by simp
        with dom_vs dom_typeof_addr show ?thesis
        proof(cases v)
          case (Addr a)
          from sc ta ob obtain b where "?vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
            by(auto simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend simp del: lappend_llist_of_llist_of)
          with Addr have a: "a \<in> mrw_addrs ?vs" by(fastforce simp add: mrw_addrs_def ran_def intro: rev_image_eqI)
          hence "{(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T} \<subseteq> dom ?vs" using dom_vs by blast
          also have "\<dots> \<subseteq> dom ?vs'" by(simp)(rule mrw_value_dom_mono)
          finally have "?concl1 (obs @ [ob])" using ob Addr dom_vs by(simp add: new_obs_addrs_def)
          moreover
          from a dom_typeof_addr have "?concl2 (obs @ [ob])" using ob Addr by(auto simp add: new_obs_addrs_def)
          ultimately show ?thesis ..
        qed(simp_all add: new_obs_addrs_def)
      next
        case (2 a C)
        hence ob: "ob = NewObj a C" by simp
        with ta have "NewObj a C \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
        with red wfx have a: "typeof_addr h' a = \<lfloor>Class C\<rfloor>" by(rule red_NewObjD)
        have "mrw_addrs ?vs' \<subseteq> mrw_addrs ?vs" unfolding ob
          by(auto simp add: mrw_addrs_def ran_def default_val_not_Addr Addr_not_default_val image_Collect split_paired_Ex split del: option.splits split: split_if_asm)
        note Complete_Lattices.UN_mono[OF Un_mono[OF subset_refl this] subset_refl]
        also note dom_vs
        also have "dom ?vs \<subseteq> dom ?vs'" by(simp)(rule mrw_value_dom_mono)
        also from a ob have "{(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T} \<subseteq> dom ?vs'" by(fastforce elim!: addr_loc_type.cases)
        ultimately have "?concl1 (obs @ [ob])" using ob by(simp add: new_obs_addrs_def del: fun_upd_apply)
        moreover {
          note `mrw_addrs ?vs' \<subseteq> mrw_addrs ?vs`
          also have "mrw_addrs ?vs \<subseteq> dom (typeof_addr h')" using dom_typeof_addr by blast
          finally have "?concl2 (obs @ [ob])" using dom_typeof_addr a ob by(simp add: new_obs_addrs_def domIff)
        }
        ultimately show ?thesis ..
      next
        case (3 a T n)
        hence ob: "ob = NewArr a T n" by simp
        with ta have "NewArr a T n \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
        with red wfx have a: "typeof_addr h' a = \<lfloor>Array T\<rfloor>" "array_length h' a = n" by(blast dest: red_NewArrD)+
        have "mrw_addrs ?vs' \<subseteq> mrw_addrs ?vs" unfolding ob
          by(auto simp add: mrw_addrs_def ran_def default_val_not_Addr Addr_not_default_val image_Collect split_paired_Ex split del: option.splits)
        note Complete_Lattices.UN_mono[OF Un_mono[OF subset_refl this] subset_refl]
        also note dom_vs
        also have "dom ?vs \<subseteq> dom ?vs'" by(simp)(rule mrw_value_dom_mono)
        also from a ob have "{(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T} \<subseteq> dom ?vs'"
          by(auto elim!: addr_loc_type.cases)(frule has_field_decl_above, fastforce)+
        ultimately have "?concl1 (obs @ [ob])" using ob by(simp add: new_obs_addrs_def del: fun_upd_apply)
        moreover {
          note `mrw_addrs ?vs' \<subseteq> mrw_addrs ?vs`
          also have "mrw_addrs ?vs \<subseteq> dom (typeof_addr h')" using dom_typeof_addr by blast
          finally have "?concl2 (obs @ [ob])" using dom_typeof_addr a ob by(simp add: new_obs_addrs_def domIff)
        }
        ultimately show ?thesis ..
      qed(simp_all add: new_obs_addrs_def)
    qed }
  note this[of "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" "[]", unfolded append_Nil2, OF refl]
  note dom_vs'' = this[THEN conjunct1] and typeof_addr'' = this[THEN conjunct2]

  have x': "known_addrs t x' \<subseteq> known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    using red by(rule red_known_addrs_new)
  hence "(\<Union>a\<in>known_addrs t x' \<union> mrw_addrs (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)). {(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq>
  (\<Union>a\<in>known_addrs t x. {(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T}) \<union> (\<Union>a\<in>new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<union> mrw_addrs (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)). {(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T})" by blast
  also {
    have "(\<Union>a\<in>known_addrs t x. {(a, al) |al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom vs" using dom_vs' by blast
    also have "\<dots> \<subseteq> dom (mrw_values P vs (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" by(rule mrw_values_dom_mono)
    also note Un_mono[OF calculation dom_vs''] }
  also note Un_absorb
  finally show ?thesis1 .

  from x' dom_typeof_addr' typeof_addr'' show ?thesis2 by blast
qed

lemma init_fin_red_known_addrs_mrw_addrs_dom_vs:
  assumes red: "t \<turnstile> (x, h) -ta\<rightarrow>i (x', h')"
  and sc: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and dom_vs: "(\<Union>a \<in> known_addrs_if t x \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,h \<turnstile> a@al : T}) \<subseteq> dom vs"
  and dom_typeof_addr: "known_addrs_if t x \<union> mrw_addrs vs \<subseteq> dom (typeof_addr h)"
  and wfx: "init_fin_lift wfx t x h"
  shows "(\<Union>a \<in> known_addrs_if t x' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>). {(a, al) | al. \<exists>T. P,h' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" (is ?thesis1)
  and "known_addrs_if t x' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> dom (typeof_addr h')" (is ?thesis2)
proof -
  from red dom_vs dom_typeof_addr have "?thesis1 \<and> ?thesis2"
  proof(cases)
    case (NormalAction X TA X')
    hence "t \<turnstile> \<langle>X, h\<rangle> -TA\<rightarrow> \<langle>X', h'\<rangle>" "ta_seq_consist P vs (llist_of (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>))"
      "(\<Union>a \<in> known_addrs t X \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,h \<turnstile> a@al : T}) \<subseteq> dom vs"
      "known_addrs t X \<union> mrw_addrs vs \<subseteq> dom (typeof_addr h)"
      "wfx t X h"
      using sc dom_vs dom_typeof_addr wfx by simp_all
    from red_known_addrs_mrw_addrs_dom_vs[OF this] NormalAction
    show ?thesis by simp
  qed auto
  thus ?thesis1 ?thesis2 by(rule conjunct1 conjunct2)+
qed

lemma if_redT_known_addrs_mrw_addrs_dom_vs:
  assumes redT: "mthr.if.redT s (t, ta) s'"
  and sc: "ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and dom_vs: "(\<Union>a \<in> if.known_addrs_state s \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs"
  and dom_typeof_addr: "if.known_addrs_state s \<union> mrw_addrs vs \<subseteq> dom (typeof_addr (shr s))"
  and wt: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  shows "(\<Union>a \<in> if.known_addrs_state s' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>). {(a, al) | al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" (is ?thesis1)
  and "if.known_addrs_state s' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> dom (typeof_addr (shr s'))" (is ?thesis2)
proof -
  note [iff del] = domIff

  from redT dom_vs dom_typeof_addr have "?thesis1 \<and> ?thesis2"
  proof(cases)
    case (redT_normal x x' m')
    note tst = `thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>`
    note red = `t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m')`
    note s' = `redT_upd s t ta x' m' s'`

    from wt tst have wfx: "init_fin_lift wfx t x (shr s)" by(cases x)(auto dest!: ts_okD)

    from tst have kasub: "known_addrs_if t x \<subseteq> if.known_addrs_state s" by(auto intro: if.known_addrs_stateI)
    note Un_mono[OF this]
    hence "(\<Union>a\<in>known_addrs_if t x \<union> mrw_addrs vs. {(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> (\<Union>a \<in> if.known_addrs_state s \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T})"
      by(rule Complete_Lattices.UN_mono) simp_all
    also note dom_vs
    finally have dom_vs': "(\<Union>a\<in>known_addrs_if t x \<union> mrw_addrs vs. {(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs" .
    
    from kasub dom_typeof_addr
    have "known_addrs_if t x \<union> mrw_addrs vs \<subseteq> dom (typeof_addr (shr s))" by blast
    with `mthr.init_fin t (x, shr s) ta (x', m')` sc dom_vs'
    have dom_vs'': "(\<Union>a\<in>known_addrs_if t x' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>). {(a, al) |al. \<exists>T. P,m' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      and dom_typeof_addr'': "known_addrs_if t x' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> dom (typeof_addr m')"
      using wfx by(rule init_fin_red_known_addrs_mrw_addrs_dom_vs)+

    from red have hext: "shr s \<unlhd> m'" by(rule init_fin_hext_incr)

    have "(\<Union>a\<in>if.known_addrs_state s' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>). {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> (\<Union>a\<in>known_addrs_if t x' \<union> mrw_addrs (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<union> if.known_addrs_state s. {(a, al) |al. \<exists>T. P,m' \<turnstile> a@al : T})"
      using init_fin_redT_known_addrs_subset[OF redT] s'
      by-(rule Complete_Lattices.UN_mono, auto)
    also note UN_Un
    also note Un_mono[OF dom_vs'' subset_refl]
    also have "(\<Union>a\<in>if.known_addrs_state s. {(a, al) |al. \<exists>T. P,m' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" 
    proof(rule UN_least)
      fix a
      assume a: "a \<in> if.known_addrs_state s"
      with dom_typeof_addr obtain T where "typeof_addr (shr s) a = \<lfloor>T\<rfloor>" by(auto iff: domIff)
      moreover note typeof_addr_eq_Some_conv[OF this]
      ultimately have "{(a, al)|al. \<exists>T. P,m' \<turnstile> a@al : T} = {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}" using hext
        by(fastforce elim!: addr_loc_type.cases intro: addr_loc_type.intros dest: hext_arrD hext_objD)
      also from dom_vs a have "\<dots> \<subseteq> dom vs" by blast
      also have "dom vs \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" by(rule mrw_values_dom_mono)
      finally show "{(a, al) |al. \<exists>T. P,m' \<turnstile> a@al : T} \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" .
    qed
    note Un_mono[OF subset_refl this]
    also note Un_absorb finally have ?thesis1 .
    moreover
    from init_fin_redT_known_addrs_subset[OF redT] s' dom_typeof_addr dom_typeof_addr'' 
      hext_dom_typeof_addr_subset[OF hext]
    have ?thesis2
      by(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def split: split_if_asm)(blast, drule subsetD, auto)
    ultimately show ?thesis ..
  next
    case (redT_acquire x ln n)
    have "dom vs \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" by(rule mrw_values_dom_mono)
    with dom_vs
    have "(\<Union>a\<in>if.known_addrs_state s \<union> mrw_addrs vs. {(a, al) |al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      by(rule subset_trans)
    also have "if.known_addrs_state s = if.known_addrs_state s'"
      using redT_acquire by(auto 4 3 simp add: if.known_addrs_thr_def if.known_addrs_state_def split: split_if_asm dest: bspec iff: domIff)
    moreover have "vs = mrw_values P vs (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list))"
      by(rule sym)(auto simp add: convert_RA_not_write fun_eq_iff intro!: mrw_values_no_write_unchanged)
    ultimately show ?thesis using redT_acquire dom_typeof_addr by auto
  qed
  thus ?thesis1 ?thesis2 by(rule conjunct1 conjunct2)+
qed

lemma if_RedT_known_addrs_mrw_addrs_dom_vs:
  assumes redT: "mthr.if.RedT s ttas s'"
  and sc: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and dom_vs: "(\<Union>a \<in> if.known_addrs_state s \<union> mrw_addrs vs. {(a, al)|al. \<exists>T. P,shr s \<turnstile> a@al : T}) \<subseteq> dom vs"
  and dom_typeof_addr: "if.known_addrs_state s \<union> mrw_addrs vs \<subseteq> dom (typeof_addr (shr s))"
  and wt: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and vs: "vs_conf P (shr s) vs"
  shows "(\<Union>a \<in> if.known_addrs_state s' \<union> mrw_addrs (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))). {(a, al) | al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))" (is ?thesis1)
  and "if.known_addrs_state s' \<union> mrw_addrs (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<subseteq> dom (typeof_addr (shr s'))" (is ?thesis2)
proof -
  from redT sc have "?thesis1 \<and> ?thesis2"
  proof(induct rule: mthr.if.RedT_induct')
    case refl thus ?case using dom_vs dom_typeof_addr wt by simp
  next
    case (step ttas s' t ta s'')
    let ?vs = "mrw_values P vs (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas))"
    from `ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta)]))))`
    have sc1: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, a). \<lbrace>a\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      and sc2: "ta_seq_consist P ?vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      unfolding lconcat_llist_of[symmetric] lmap_llist_of[symmetric] lmap_compose[symmetric] o_def lappend_llist_of_llist_of[symmetric] lmap_lappend_distrib
      by(simp_all add: ta_seq_consist_lappend list_of_lconcat o_def)
    note `mthr.if.redT s' (t, ta) s''` sc2
    moreover
    from sc1 have "(\<Union>a\<in>if.known_addrs_state s' \<union> mrw_addrs ?vs. {(a, al) |al. \<exists>T. P,shr s' \<turnstile> a@al : T}) \<subseteq> dom ?vs"
      and "if.known_addrs_state s' \<union> mrw_addrs ?vs \<subseteq> dom (typeof_addr (shr s'))"
      by(rule conjunct1[OF step(2)] conjunct2[OF step(2)])+
    moreover from `mthr.if.RedT s ttas s'` wt sc1 vs
    have "ts_ok (init_fin_lift wfx) (thr s') (shr s')" by(rule if_RedT_ta_seq_consist_invar)
    ultimately have "(\<Union>a\<in>if.known_addrs_state s'' \<union> mrw_addrs (mrw_values P ?vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>). {(a, al) |al. \<exists>T. P,shr s'' \<turnstile> a@al : T}) \<subseteq> dom (mrw_values P ?vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      and "if.known_addrs_state s'' \<union> mrw_addrs (mrw_values P ?vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> dom (typeof_addr (shr s''))"
      by(rule if_redT_known_addrs_mrw_addrs_dom_vs)+
    thus ?case by simp
  qed
  thus ?thesis1 ?thesis2 by(rule conjunct1 conjunct2)+
qed


lemma executions:
  fixes status f C M vs
  defines "\<E> \<equiv> lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
                  mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"
  assumes cut_and_update:
    "if.cut_and_update
       (init_fin_lift_state status (start_state f P C M vs))
       (mrw_values P empty (map snd (lift_start_obs start_tid start_heap_obs)))"
    (is "if.cut_and_update ?start_state (mrw_values _ _ (map _ ?start_heap_obs))")
  and wf: "wf_syscls P"
  and ok: "start_heap_ok"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and vs: "vs_conf P start_heap (mrw_values P Map.empty (map NormalAction start_heap_obs))"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows "executions \<E> P" (is "executions ?\<E> _")
proof -
  let ?\<E> = "lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"
  interpret jmm!: executions_sc "?\<E>" P
    using wf ok wfx_start vs ka by(rule executions_sc)

  let ?n = "length ?start_heap_obs"
  let ?\<E>' = "lappend (llist_of ?start_heap_obs) ` mthr.if.\<E> ?start_state"

  show ?thesis unfolding \<E>_def
  proof
    fix E ws r
    assume E: "E \<in> ?\<E>'"
      and wf: "P \<turnstile> (E, ws) \<surd>"
      and mrw: "\<And>a. \<lbrakk> a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
    show "\<exists>E'\<in>?\<E>'. \<exists>ws'. P \<turnstile> (E', ws') \<surd> \<and> ltake (enat r) E = ltake (enat r) E' \<and>
                           sequentially_consistent P (E', ws') \<and>
                           action_tid E r = action_tid E' r \<and> action_obs E r \<approx> action_obs E' r \<and>
                           (r \<in> actions E \<longrightarrow> r \<in> actions E')"
    proof(cases "\<exists>r'. r' \<in> read_actions E \<and> r \<le> r'")
      case False
      have "sequentially_consistent P (E, ws)"
      proof(rule sequentially_consistentI)
        fix a
        assume "a \<in> read_actions E"
        with False have "a < r" by auto
        thus "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw)
      qed
      moreover have "action_obs E r \<approx> action_obs E r" by(rule sim_action_refl)
      ultimately show ?thesis using wf E by blast
    next
      case True
      let ?P = "\<lambda>r'. r' \<in> read_actions E \<and> r \<le> r'"
      let ?r = "Least ?P"
      from True obtain r' where r': "?P r'" by blast
      hence r: "?P ?r" by(rule LeastI)
      {
        fix a
        assume "a < ?r" "a \<in> read_actions E"
        have "P,E \<turnstile> a \<leadsto>mrw ws a"
        proof(cases "a < r")
          case True
          thus ?thesis using `a \<in> read_actions E` by(rule mrw)
        next
          case False
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `a < ?r` have False by simp
          thus ?thesis ..
        qed }
      note mrw' = this

      from E obtain E'' where E: "E = lappend (llist_of ?start_heap_obs) E''"
        and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto

      from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
        and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'"
        by(rule mthr.if.\<E>.cases)

      have r_len: "length ?start_heap_obs \<le> ?r"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?r < length ?start_heap_obs" by simp
        moreover with r E obtain t ad al v where "?start_heap_obs ! ?r = (t, NormalAction (ReadMem ad al v))"
          by(cases "?start_heap_obs ! ?r")(fastforce elim!: read_actions.cases simp add: actions_def action_obs_def lnth_lappend1)
        ultimately have "(t, NormalAction (ReadMem ad al v)) \<in> set ?start_heap_obs" unfolding in_set_conv_nth by blast
        thus False by(auto simp add: start_heap_obs_not_Read)
      qed
      let ?n = "length ?start_heap_obs"
      from r r_len E have r: "?r - ?n \<in> read_actions E''"
        by(fastforce elim!: read_actions.cases simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)
      
      from r have "?r - ?n \<in> actions E''" by(auto)
      hence "enat (?r - ?n) < llength E''" by(rule actionsE)
      with \<tau>Runs obtain r_m r_n t_r ta_r 
        where E_r: "lnth E'' (?r - ?n) = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
        and r_n: "r_n < length \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and r_m: "enat r_m < llength E'"
        and r_conv: "?r - ?n = (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n"
        and E'_r_m: "lnth E' r_m = (t_r, ta_r)"
        unfolding E' by(rule mthr.if.actions_\<E>E_aux)

      let ?E' = "ldropn (Suc r_m) E'"
      let ?r_m_E' = "ltake (enat r_m) E'"
      have E'_unfold: "E' = lappend (ltake (enat r_m) E') (LCons (lnth E' r_m) ?E')"
        unfolding ldropn_Suc_conv_ldropn[OF r_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend ?r_m_E' (LCons (lnth E' r_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of ?r_m_E') \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' r_m) ?E')"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''' where red_ra: "mthr.if.redT \<sigma>' (t_r, ta_r) \<sigma>'''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>''' ?E'"
        unfolding E'_r_m by cases

      let ?vs = "mrw_values P empty (map snd ?start_heap_obs)"
      { fix a
        assume "enat a < enat ?r"
          and "a \<in> read_actions E"
        have "a < r"
        proof(rule ccontr)
          assume "\<not> a < r"
          with `a \<in> read_actions E` have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with `enat a < enat ?r` show False by simp
        qed
        hence "P,E \<turnstile> a \<leadsto>mrw ws a" using `a \<in> read_actions E` by(rule mrw) }
      with `E \<in> ?\<E>'` wf have "ta_seq_consist P empty (lmap snd (ltake (enat ?r) E))"
        by(rule jmm.ta_seq_consist_mrwI)

      hence start_sc: "ta_seq_consist P empty (llist_of (map snd ?start_heap_obs))"
        and "ta_seq_consist P ?vs (lmap snd (ltake (enat (?r - ?n)) E''))"
        using `?n \<le> ?r` unfolding E ltake_lappend lmap_lappend_distrib
        by(simp_all add: ta_seq_consist_lappend o_def)

      note this(2) also from r_m
      have r_m_sum_len_eq: "(\<Sum>i<r_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) = enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(subst setsum_hom[symmetric, where f=enat])(auto simp add: zero_enat_def split_def less_trans[where y="enat r_m"] intro: setsum_cong)
      hence "ltake (enat (?r - ?n)) E'' = 
            lappend (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')) 
                    (ltake (enat r_n) (ldrop (enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E''))"
        unfolding ltake_lmap[symmetric] lconcat_ltake r_conv plus_enat_simps(1)[symmetric] ltake_plus_conv_lappend
        unfolding E' by simp
      finally have "ta_seq_consist P ?vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')))"
        and sc_ta_r: "ta_seq_consist P (mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))) (lmap snd (ltake (enat r_n) (ldropn (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'')))"
        unfolding lmap_lappend_distrib by(simp_all add: ta_seq_consist_lappend split_def)
      note this(1) also
      have "lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (enat r_m) E')))
            = llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E')))"
        unfolding lmap_lconcat lmap_compose[symmetric] o_def split_def lconcat_llist_of[symmetric] map_map lmap_llist_of[symmetric]
        by simp
      finally have "ta_seq_consist P ?vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))" .
      from if.sequential_completion[OF cut_and_update ta_seq_consist_convert_RA \<sigma>_\<sigma>'[folded mthr.if.RedT_def] this red_ra]
      obtain ta' ttas' 
        where "mthr.if.mthr.Runs \<sigma>' (LCons (t_r, ta') ttas')"
        and sc: "ta_seq_consist P (mrw_values P empty (map snd ?start_heap_obs)) 
                   (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') ttas'))))"
          and eq_ta: "eq_upto_seq_inconsist P \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P ?vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))"
          by blast

      let ?E_sc' = "lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') ttas')"
      let ?E_sc'' = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?E_sc')"
      let ?E_sc = "lappend (llist_of ?start_heap_obs) ?E_sc''"

      from \<sigma>_\<sigma>' `mthr.if.mthr.Runs \<sigma>' (LCons (t_r, ta') ttas')`
      have "mthr.if.mthr.Runs ?start_state ?E_sc'" by(rule mthr.if.mthr.Trsys_into_Runs)
      hence "?E_sc'' \<in> mthr.if.\<E> ?start_state" by(rule mthr.if.\<E>.intros)
      hence "?E_sc \<in> ?\<E>" by(rule imageI)
      moreover from `?E_sc'' \<in> mthr.if.\<E> ?start_state`
      have tsa_ok: "thread_start_actions_ok ?E_sc" by(rule thread_start_actions_ok_init_fin) 
        
      from sc have "ta_seq_consist P empty (lmap snd ?E_sc)"
        by(simp add: lmap_lappend_distrib o_def lmap_lconcat lmap_compose[symmetric] split_def ta_seq_consist_lappend start_sc del: lmap_compose)
      from jmm.ta_seq_consist_imp_sequentially_consistent[OF `?E_sc \<in> ?\<E>` tsa_ok this]
      obtain ws_sc where "sequentially_consistent P (?E_sc, ws_sc)"
        and "P \<turnstile> (?E_sc, ws_sc) \<surd>" unfolding start_heap_obs_def[symmetric] by blast
      moreover {
        have enat_sum_r_m_eq: "enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))"
          by(auto intro: setsum_cong simp add: less_trans[OF _ r_m] lnth_ltake llength_lconcat_lfinite_conv_sum setsum_hom[symmetric, where f=enat] zero_enat_def[symmetric] split_beta)
        also have "\<dots> \<le> llength E''" unfolding E'
          by(blast intro: lprefix_llength_le lprefix_lconcatI lmap_lprefix)
        finally have r_m_E: "ltake (enat (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))) E = ltake (enat (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))) ?E_sc"
          by(simp add: ltake_lappend lappend_eq_lappend_conv lmap_lappend_distrib r_m_sum_len_eq ltake_lmap[symmetric] min_def zero_enat_def[symmetric] E E' lconcat_ltake ltake_all del: ltake_lmap)

        have drop_r_m_E: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E = lappend (llist_of (map (Pair t_r) \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ldropn (Suc r_m) E')))"
          (is "_ = ?drop_r_m_E") using E'_r_m unfolding E E'
          by(subst (2) E'_unfold)(simp add: ldropn_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric])

        have drop_r_m_E_sc: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) ?E_sc =
          lappend (llist_of (map (Pair t_r) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas'))"
          by(simp add: ldropn_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric])

        let ?vs_r_m = "mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))"
        note sc_ta_r also
        from drop_r_m_E have "ldropn (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'' = ?drop_r_m_E"
          unfolding E by(simp add: ldropn_lappend2)
        also have "lmap snd (ltake (enat r_n) \<dots>) = llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)" using r_n
          by(simp add: ltake_lappend lmap_lappend_distrib ltake_lmap[symmetric] take_map o_def zero_enat_def[symmetric] del: ltake_lmap)
        finally have sc_ta_r: "ta_seq_consist P ?vs_r_m (llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))" .
        note eq_ta
        also have "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" by simp
        finally have "eq_upto_seq_inconsist P (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs_r_m"
          by(simp add: list_of_lconcat split_def o_def map_concat)
        from eq_upto_seq_inconsist_appendD[OF this sc_ta_r]
        have r_n': "r_n \<le> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
          and take_r_n_eq: "take r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
          and eq_r_n: "eq_upto_seq_inconsist P (drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) (drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (mrw_values P ?vs_r_m (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"
          using r_n by(simp_all add: min_def)
        from r_conv `?n \<le> ?r` have r_conv': "?r = (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) + r_n" by simp
        from r_n' r_n take_r_n_eq r_m_E drop_r_m_E drop_r_m_E_sc
        have take_r'_eq: "ltake (enat ?r) E = ltake (enat ?r) ?E_sc" unfolding r_conv'
          apply(subst (1 2) plus_enat_simps(1)[symmetric])
          apply(subst (1 2) ltake_plus_conv_lappend)
          apply(simp add: lappend_eq_lappend_conv ltake_lappend1 take_map)
          done
        hence take_r_eq: "ltake (enat r) E = ltake (enat r) ?E_sc"
          by(rule ltake_eq_ltake_antimono)(simp add: `?P ?r`)
        
        from eq_r_n nth_drop'[OF r_n, symmetric]
        have "drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<noteq> []" by(auto simp add: eq_upto_seq_inconsist_simps)
        hence r_n': "r_n < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by simp
        hence eq_r_n: "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n \<approx> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n"
          using eq_r_n nth_drop'[OF r_n, symmetric] nth_drop'[OF r_n', symmetric]
          by(simp add: eq_upto_seq_inconsist_simps split: action.split_asm obs_event.split_asm split_if_asm)
        obtain tid_eq: "action_tid E r = action_tid ?E_sc r" 
          and obs_eq: "action_obs E r \<approx> action_obs ?E_sc r"
        proof(cases "r < ?r")
          case True
          { from True have "action_tid E r = action_tid (ltake (enat ?r) E) r"
              by(simp add: action_tid_def lnth_ltake)
            also note take_r'_eq
            also have "action_tid (ltake (enat ?r) ?E_sc) r = action_tid ?E_sc r"
              using True by(simp add: action_tid_def lnth_ltake)
            finally have "action_tid E r = action_tid ?E_sc r" . }
          moreover
          { from True have "action_obs E r = action_obs (ltake (enat ?r) E) r"
              by(simp add: action_obs_def lnth_ltake)
            also note take_r'_eq
            also have "action_obs (ltake (enat ?r) ?E_sc) r = action_obs ?E_sc r"
              using True by(simp add: action_obs_def lnth_ltake)
            finally have "action_obs E r \<approx> action_obs ?E_sc r" by simp }
          ultimately show thesis by(rule that)
        next
          case False
          with `?P ?r` have r_eq: "r = ?r" by simp
          hence "lnth E r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)" using E_r r_conv' E by(simp add: lnth_lappend2)
          moreover have "lnth ?E_sc r = (t_r, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n)" using `?n \<le> ?r` r_n'
            by(subst r_eq)(simp add: r_conv lnth_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric] lnth_lappend1 del: length_lift_start_obs)
          ultimately have "action_tid E r = action_tid ?E_sc r" "action_obs E r \<approx> action_obs ?E_sc r"
            using eq_r_n by(simp_all add: action_tid_def action_obs_def)
          thus thesis by(rule that)
        qed
        
        have "enat r < enat ?n + llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil))))"
          using `?P ?r` r_n' unfolding lmap_lappend_distrib
          by(simp add: enat_sum_r_m_eq[symmetric] r_conv')
        also have "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil)))) \<le> llength ?E_sc''"
          by(rule lprefix_llength_le[OF lprefix_lconcatI])(simp add: lmap_lprefix)
        finally have "r \<in> actions ?E_sc" by(simp add: actions_def add_left_mono)
        note this tid_eq obs_eq take_r_eq }
      ultimately show ?thesis by blast
    qed
  qed(rule \<E>_new_actions_for_unique)
qed

end

end
