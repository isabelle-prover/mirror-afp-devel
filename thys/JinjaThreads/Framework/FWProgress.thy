(*  Title:      JinjaThreads/Framework/FWProgress.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Progress theorem for the multithreaded semantics} *}

theory FWProgress imports FWSemantics begin

context multithreaded begin

definition must_lock :: "'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ \<wrong>" [0,0] 81) where
  "must_lock \<equiv> (\<lambda>x m. \<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)))"

lemma must_lockI:
  "(\<And>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> \<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<Longrightarrow> \<langle>x, m\<rangle> \<wrong>"
by(clarsimp simp add: must_lock_def)

lemma must_lockE:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>; \<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(simp only: must_lock_def)

lemma must_lockD:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>; \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk> \<Longrightarrow> \<exists>l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
apply(erule must_lockE)
by(fastsimp)



definition can_lock :: "'x \<Rightarrow> 'm \<Rightarrow> 'l set \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ _/ \<wrong>" [0,0,0] 81) where 
  "can_lock \<equiv> (\<lambda>x m L. \<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> (L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"

lemma can_lockI:
  "\<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<rbrakk> \<Longrightarrow> \<langle>x, m\<rangle> L \<wrong>"
apply(cases ta)
apply(fastsimp simp add: can_lock_def)
done

lemma can_lockE:
  "\<lbrakk> \<langle>x, m\<rangle> L \<wrong>; (\<And>ta x' m'. \<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<rbrakk> \<Longrightarrow> Q) \<rbrakk> \<Longrightarrow> Q"
by(clarsimp simp add: can_lock_def)


definition must_lock' :: "'x \<Rightarrow> 'm \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ \<wrong>'" [0,0] 81) where
  "must_lock' \<equiv> (\<lambda>x m. \<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. must_acquire_lock (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)))"

lemma must_lock'I:
  "(\<And>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<Longrightarrow> \<exists>l. must_acquire_lock (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<Longrightarrow> \<langle>x, m\<rangle> \<wrong>'"
by(clarsimp simp add: must_lock'_def)

lemma must_lock'E:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>'; \<forall>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<longrightarrow> (\<exists>l. must_acquire_lock (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(simp only: must_lock'_def)

lemma must_lock'D:
  "\<lbrakk> \<langle>x, m\<rangle> \<wrong>'; \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk> \<Longrightarrow> \<exists>l. must_acquire_lock (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
apply(erule must_lock'E)
by(fastsimp)



definition can_lock' :: "'x \<Rightarrow> 'm \<Rightarrow> 'l set \<Rightarrow> bool" ("\<langle>_,/ _\<rangle>/ _/ \<wrong>'" [0,0,0] 81) where 
  "can_lock' \<equiv> (\<lambda>x m L. \<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> (L = collect_locks' \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>))"

lemma can_lock'I:
  "\<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; L = collect_locks' \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<rbrakk> \<Longrightarrow> \<langle>x, m\<rangle> L \<wrong>'"
apply(cases ta)
apply(fastsimp simp add: can_lock'_def)
done

lemma can_lock'E:
  "\<lbrakk> \<langle>x, m\<rangle> L \<wrong>'; (\<And>ta x' m'. \<lbrakk> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; L = collect_locks' \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<rbrakk> \<Longrightarrow> Q) \<rbrakk> \<Longrightarrow> Q"
by(clarsimp simp add: can_lock'_def)

lemma can_lock_can_lock'_eq: 
  "(\<exists>L. \<langle>x, m\<rangle> L \<wrong>) \<longleftrightarrow> (\<exists>L. \<langle>x, m\<rangle> L \<wrong>')"
by(auto intro: can_lock'I can_lockI elim!: can_lock'E can_lockE)

definition wf_red_precond :: "('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<Rightarrow> 'm \<Rightarrow> bool" where
  "wf_red_precond ls ts m \<equiv>
   \<forall>t x ta x' m'. ts t = \<lfloor>x\<rfloor> \<and> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>
              \<longrightarrow> (\<exists>ta' x' m'. \<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle> \<and> thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>
                              \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)"

lemma wf_red_precondI:
  "(\<And>t x ta x' m'. \<lbrakk> ts t = \<lfloor>x\<rfloor>; \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk> 
                   \<Longrightarrow> \<exists>ta' x' m'. \<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle> \<and> thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>
                                  \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)
   \<Longrightarrow> wf_red_precond ls ts m"
apply(auto simp add: wf_red_precond_def)
done

lemma wf_red_precondD:
  "\<lbrakk> wf_red_precond ls ts m; ts t = \<lfloor>x\<rfloor>; \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<rbrakk>
  \<Longrightarrow> \<exists>ta' x' m'. \<langle>x, m\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle> \<and> thread_oks ts m' \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> lock_ok_las' ls t \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub>
               \<and> collect_locks' \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
apply(unfold wf_red_precond_def)
by(blast)

end


locale final_thread = multithreaded +
  fixes final :: "'x \<Rightarrow> bool"
  assumes final_no_red: "final x \<Longrightarrow> \<not> ((x, m), ta, x', m') \<in> r" begin

lemma final_no_redT: 
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; thr s t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> \<not> final x"
by(auto elim!: redT.cases dest!: final_no_red)

definition ls_ts_final_ok :: "('l,'t) locks \<Rightarrow> ('t,'x) thread_info \<Rightarrow> bool" where
  "ls_ts_final_ok \<equiv> (\<lambda>ls ts. \<forall>l. case ls l of None     \<Rightarrow> True
                                      | \<lfloor>(t, n)\<rfloor>  \<Rightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x)"

lemma ls_ts_final_okI:
  "(\<And>l t n. ls l = \<lfloor>(t, n)\<rfloor> \<Longrightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x) \<Longrightarrow> ls_ts_final_ok ls ts"
  by(auto simp add: ls_ts_final_ok_def)

lemma ls_ts_final_okE:
  "\<lbrakk> ls_ts_final_ok ls ts; (\<And>l t n. ls l = \<lfloor>(t, n)\<rfloor> \<Longrightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by(force simp add: ls_ts_final_ok_def)

lemma ls_ts_final_okD:
  "\<lbrakk> ls_ts_final_ok ls ts; ls l = \<lfloor>(t, n)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x"
apply(auto simp add: ls_ts_final_ok_def)
done

definition all_final_except :: "('t,'x) thread_info \<Rightarrow> 't set \<Rightarrow> bool" where
  "all_final_except ts M \<equiv> \<forall>t\<in>(UNIV - M). (case (ts t) of None \<Rightarrow> True | \<lfloor>x\<rfloor> \<Rightarrow> final x)"

lemma all_final_except_mono:
  "A \<subseteq> B \<Longrightarrow> all_final_except ts A \<longrightarrow> all_final_except ts B"
by(auto simp add: all_final_except_def)

end

locale progress = multithreaded + final_thread begin

coinductive_set deadlocked :: "('c,'d,'a,'b,'e) state \<Rightarrow> 'd set"
  for s :: "('c,'d,'a,'b,'e) state"
  where
  deadlockedLock:
    "\<lbrakk> thr s t = \<lfloor>x\<rfloor>; \<langle>x, shr s\<rangle> \<wrong>; \<langle>x, shr s\<rangle> L \<wrong>;
       \<forall>L. \<langle>x, shr s\<rangle> L \<wrong> \<longrightarrow> (\<exists>t'. (t' \<in> deadlocked s \<or> (\<exists>x. thr s t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t \<and> (\<exists>l \<in> L. has_lock (locks s l) t')) \<rbrakk>
     \<Longrightarrow> t \<in> deadlocked s"

| deadlockedWait:
    "\<lbrakk> thr s t = \<lfloor>x\<rfloor>; all_final_except (thr s) (deadlocked s); wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> t \<in> deadlocked s"
monos all_final_except_mono

lemma red_no_deadlock: 
  assumes P: "s -t\<triangleright>ta\<rightarrow> s'"
  shows "t \<notin> deadlocked s"
proof(rule notI)
  assume dead: "t \<in> deadlocked s"
  obtain las tas was where ta: "ta = (las, tas, was)" by (cases ta, auto)
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by (cases s, auto)
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  from ta s s' P obtain x x'
    where Pe: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
    and est: "ts t = \<lfloor>x\<rfloor>"
    and lot: "lock_ok_las ls t las"
    and cct: "thread_oks ts m' tas"
    and wst: "ws t = None"
    by(auto elim: redT.cases)
  show False
  proof(cases "all_final_except ts (deadlocked s) \<and> (\<exists>w. ws t = \<lfloor>w\<rfloor>)")
    case True with wst show ?thesis by simp
  next
    case False
    with dead est s
    have mle: "\<langle>x, m\<rangle> \<wrong>"
      and excle: "\<exists>L. \<langle>x, m\<rangle> L \<wrong>"
      and cledead: "\<forall>L. \<langle>x, m\<rangle> L \<wrong> \<longrightarrow> (\<exists>t'. (t' \<in> deadlocked (ls, (ts, m), ws) \<or> (\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t \<and> (\<exists>l\<in>L. has_lock (ls l) t'))"
      by - (erule deadlocked.cases, fastsimp+)+
    from Pe mle ta have "\<exists>l. Lock \<in> set (las l)"
      by(auto dest!: must_lockD)
    then obtain l where tal: "Lock \<in> set (las l)" by blast
    from Pe tal ta have "\<langle>x, m\<rangle> collect_locks las \<wrong>" by(auto intro!: can_lockI)
    with cledead s have "\<exists>t'. (t' \<in> deadlocked s \<or> (\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t \<and> (\<exists>l\<in>collect_locks las. has_lock (ls l) t')" by simp
    then obtain t' l' where t't: "t' \<noteq> t" and ltas: "l' \<in> collect_locks las" and hlt': "has_lock (ls l') t'" by blast
    from lot ltas have "may_lock (ls l') t"
      by(auto elim!: collect_locksE lock_ok_las_may_lock)
    with hlt' have "t' = t" by - (rule has_lock_may_lock_t_eq)
    with t't show False by contradiction
  qed
qed


lemma no_deadlocked_ex_not_waiting:
  assumes t'ndead: "t' \<notin> deadlocked s"
  and est': "thr s t' = \<lfloor>x\<rfloor>"
  and nfin: "\<not> final x"
  and loes: "lock_thread_ok (locks s) (thr s)"
  shows "\<exists>t x. thr s t = \<lfloor>x\<rfloor> \<and> \<not> final x \<and> wset s t = None
               \<and> (\<langle>x, shr s\<rangle> \<wrong> \<and> (\<exists>L. \<langle>x, shr s\<rangle> L \<wrong>)
                  \<longrightarrow> (\<exists>L. \<langle>x, shr s\<rangle> L \<wrong> \<and> (\<forall>l\<in>L. may_lock (locks s l) t)))"
using t'ndead
proof(rule contrapos_np)
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by (cases s, auto)
  assume "\<not> (\<exists>t x. thr s t = \<lfloor>x\<rfloor> \<and> \<not> final x \<and> wset s t = None \<and> (\<langle>x, shr s\<rangle> \<wrong> \<and> (\<exists>L. \<langle>x, shr s\<rangle> L \<wrong>) \<longrightarrow> (\<exists>L. \<langle>x, shr s\<rangle> L \<wrong> \<and> (\<forall>l\<in>L. may_lock (locks s l) t))))"
  with s have a:
    "\<And>t x. \<lbrakk> ts t = \<lfloor>x\<rfloor>; \<not> final x; ws t = None \<rbrakk> 
           \<Longrightarrow> \<langle>x, m\<rangle> \<wrong> \<and> (\<exists>L. \<langle>x, m\<rangle> L \<wrong>) \<and> (\<forall>L. \<langle>x, m\<rangle> L \<wrong> \<longrightarrow> (\<exists>l\<in>L. \<not> may_lock (ls l) t))"
    by(force)
  show "t' \<in> deadlocked s"
  proof(rule deadlocked.coinduct)
    show "t' \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)}"
      using est' nfin s by auto
  next
    fix z
    assume z: "z \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)}"
    then obtain x' where esz: "ts z = \<lfloor>x'\<rfloor>" by blast
    show "(\<exists>t x L. z = t \<and> thr s t = \<lfloor>x\<rfloor> \<and>
                           \<langle>x, shr s\<rangle> \<wrong> \<and>
                           \<langle>x, shr s\<rangle> L \<wrong> \<and>
                           (\<forall>L. \<langle>x, shr s\<rangle> L \<wrong> \<longrightarrow>
                                (\<exists>t'. ((t' \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)} \<or> t' \<in> deadlocked s) \<or> (\<exists>x. thr s t' = \<lfloor>x\<rfloor> \<and> final x)) \<and>
                                      t' \<noteq> t \<and> (\<exists>l\<in>L. has_lock (locks s l) t')))) \<or>
        (\<exists>t x w. z = t \<and> thr s t = \<lfloor>x\<rfloor> \<and>
                           all_final_except (thr s) {z. z \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)} \<or> z \<in> deadlocked s} \<and> wset s t = \<lfloor>w\<rfloor>)"
    proof(cases "ws z")
      case None
      with z esz have nfine: "\<not> final x'" by(auto)
      with None esz s have mle: "\<langle>x', m\<rangle> \<wrong>"
	and cle: "\<exists>L. \<langle>x', m\<rangle> L \<wrong>"
	and clemle: "\<forall>L. \<langle>x', m\<rangle> L \<wrong> \<longrightarrow> (\<exists>l\<in>L. \<not> may_lock (ls l) z)"
	by -(fastsimp dest: a)+
      from cle obtain L where "\<langle>x', m\<rangle> L \<wrong>" by blast
      with clemle have "\<exists>l\<in>L. \<not> may_lock (ls l) z" by auto
      then obtain l
	where lL: "l \<in> L"
	and nmll: "\<not> may_lock (ls l) z" by blast
      hence "\<exists>t''. t'' \<noteq> z \<and> has_lock (ls l) t''"
	by(simp add: not_may_lock_conv)
      then obtain t''
	where tt'': "t'' \<noteq> z"
	and hlt'': "has_lock (ls l) t''"
	by blast
      show ?thesis
      proof(rule disjI1)
	{ fix L'
	  assume "\<langle>x', m\<rangle> L' \<wrong>"
	  with clemle have "\<exists>l\<in>L'. \<not> may_lock (ls l) z" by simp
	  then obtain l'
	    where l'L': "l' \<in> L'"
	    and nmll': "\<not> may_lock (ls l') z"
	    by blast
	  hence "\<exists>t''. z \<noteq> t'' \<and> has_lock (ls l') t''"
	    by(auto simp add: not_may_lock_conv)
	  then obtain t'' n
	    where tt'': "z \<noteq> t''"
	    and hl't'': "has_lock (ls l') t''" by blast
	  from loes hl't'' s have b: "\<exists>x''. ts t'' = \<lfloor>x''\<rfloor>"
	    by(auto elim!: has_lockE dest!: lock_thread_okD)
	  then obtain x'' where tst'': "ts t'' = \<lfloor>x''\<rfloor>" by blast
	  with s have "(t'' \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)} \<or> t'' \<in> deadlocked s) \<or> (\<exists>x. thr s t'' = \<lfloor>x\<rfloor> \<and> final x)"
	    by(cases "final x''", auto)
	  with hl't'' tt'' l'L'
	  have "\<exists>t'. ((t' \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)} \<or> t' \<in> deadlocked s) \<or> (\<exists>x. thr s t' = \<lfloor>x\<rfloor> \<and> final x))
                   \<and> t' \<noteq> z \<and> (\<exists>l\<in>L'. has_lock (ls l) t')"
	    by(fastsimp) }
	thus "\<exists>t x L. z = t \<and> thr s t = \<lfloor>x\<rfloor> \<and>
                    \<langle>x, shr s\<rangle> \<wrong> \<and>
                    \<langle>x, shr s\<rangle> L \<wrong> \<and>
                    (\<forall>L. \<langle>x, shr s\<rangle> L \<wrong> \<longrightarrow>
                         (\<exists>t'. ((t' \<in> {t. \<exists>x. ts t = \<lfloor>x\<rfloor> \<and> ((\<exists>w. ws t = \<lfloor>w\<rfloor>) \<or> \<not> final x)} \<or> t' \<in> deadlocked s) \<or> (\<exists>x. thr s t' = \<lfloor>x\<rfloor> \<and> final x)) \<and>
                               t' \<noteq> t \<and> (\<exists>l\<in>L. has_lock (locks s l) t')))"
	  using esz mle cle s
	  by force
      qed
    next
      case (Some w)
      with esz s show ?thesis 
	by -(rule disjI2, clarsimp simp add: all_final_except_def)
    qed
  qed 
qed

definition wf_progress :: "('d,'a) thread_info \<Rightarrow> 'b \<Rightarrow> bool" where
  "wf_progress ts m \<equiv> \<forall>t x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x \<longrightarrow> (\<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>)"

lemma wf_progressI:
  "(\<And>t x. \<lbrakk> ts t = \<lfloor>x\<rfloor>; \<not> final x \<rbrakk> \<Longrightarrow> \<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>) \<Longrightarrow> wf_progress ts m"
apply(auto simp add: wf_progress_def)
done

lemma wf_progressE:
  "\<lbrakk> wf_progress ts m; \<forall>t x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x \<longrightarrow> (\<exists>ta x' m'. \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
apply(auto simp add: wf_progress_def)
done

lemma redT_progress:
  assumes est: "thr s t = \<lfloor>x\<rfloor>"
  and nfine: "\<not> final x"
  and ndead: "t \<notin> deadlocked s"
  and progress: "wf_progress (thr s) (shr s)"
  and loes: "lock_thread_ok (locks s) (thr s)"
  and conform: "wf_red_precond (locks s) (thr s) (shr s)"
  shows "\<exists>t' ta' s'. s -t'\<triangleright>ta'\<rightarrow> s'"
proof -
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by (cases s, auto)
  with conform have conform': "wf_red_precond ls ts m" by simp
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  note no_deadlocked_ex_not_waiting[OF ndead est nfine loes]
  with s have "\<exists>t x. ts t = \<lfloor>x\<rfloor> \<and> \<not> final x \<and> ws t = None
                     \<and>  (\<langle>x, m\<rangle> \<wrong> \<and> (\<exists>L. \<langle>x, m\<rangle> L \<wrong>)
                          \<longrightarrow> (\<exists>L. \<langle>x, m\<rangle> L \<wrong> \<and> (\<forall>l\<in>L. may_lock (ls l) t)))"
    by simp
  then obtain t' x' 
    where est': "ts t' = \<lfloor>x'\<rfloor>"
    and nfine': "\<not> final x'"
    and wst': "ws t' = None"
    and mlclml: "\<lbrakk> \<langle>x', m\<rangle> \<wrong>; \<exists>L. \<langle>x', m\<rangle> L \<wrong> \<rbrakk> \<Longrightarrow> \<exists>L. \<langle>x', m\<rangle> L \<wrong> \<and> (\<forall>l\<in>L. may_lock (ls l) t')"
    by blast
  from est' nfine' progress s have "\<exists>ta x'' m''. \<langle>x', m\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>"
    by(auto elim: wf_progressE)
  then obtain x'' m'' ta'
    where red: "\<langle>x', m\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
    by blast
  hence cl: "\<langle>x', m\<rangle> collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<wrong>"
    by(auto intro: can_lockI)
  { assume ml: "\<langle>x', m\<rangle> \<wrong>"
    with cl obtain L
      where cl': "\<langle>x', m\<rangle> L \<wrong>"
      and mayl: "\<forall>l\<in>L. may_lock (ls l) t'"
      by(blast dest: mlclml)
    from cl' have "\<exists>ta''' x''' m'''. \<langle>x', m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle> \<and> L = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
      by (fastsimp elim!: can_lockE del: equalityI)
    then obtain ta''' x''' m'''
      where red'': "\<langle>x', m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
      and L: "L = collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
      by blast
    from wf_red_precondD[OF conform' _ red'', OF est']
    obtain ta'' x'' m''
      where red': "\<langle>x', m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
      and cct: "thread_oks ts m'' \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
      and lot: "lock_ok_las' ls t' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>"
      by blast
    from collect L mayl have "\<forall>l\<in>collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>. may_lock (ls l) t'"
      by auto
    with lot have "\<forall>l\<in>collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>. may_lock (ls l) t'"
      by - (rule lock_ok_las'_collect_locks'_may_lock)
    with lot have "lock_ok_las ls t' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      by -(rule lock_ok_las'_collect_locks_lock_ok_las)
    moreover
    obtain s' where s': "s' = redT_upd (ls, (ts(t' \<mapsto> x''), m''), ws) t' ta''" by auto
    ultimately
    have "s -t'\<triangleright>ta''\<rightarrow> s'" using red' cct est' wst' s
      by(auto intro!: redT.intros)
    hence ?thesis by blast }
  moreover
  { assume ml: "\<not> \<langle>x', m\<rangle> \<wrong>"
    hence "\<exists>ta x'' m'. \<langle>x', m\<rangle> -ta\<rightarrow> \<langle>x'', m'\<rangle> \<and> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = {}"
      by(auto simp add: collect_locks_def must_lock_def)
    then obtain ta''' x''' m'''
      where red'': "\<langle>x', m\<rangle> -ta'''\<rightarrow> \<langle>x''', m'''\<rangle>"
      and collect'': "collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub> = {}" by blast
    from wf_red_precondD[OF conform' _ red'', OF est']
    obtain ta'' x'' m''
      where red': "\<langle>x', m\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
      and cct: "thread_oks ts m'' \<lbrace>ta''\<rbrace>\<^bsub>t\<^esub>"
      and lot: "lock_ok_las' ls t' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      and collect: "collect_locks' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta'''\<rbrace>\<^bsub>l\<^esub>" by blast
    from collect collect'' lot
    have "\<forall>l\<in>collect_locks \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>. may_lock (ls l) t'"
      apply -
      apply(erule lock_ok_las'_collect_locks'_may_lock)
      by auto
    with lot have "lock_ok_las ls t' \<lbrace>ta''\<rbrace>\<^bsub>l\<^esub>"
      by -(rule lock_ok_las'_collect_locks_lock_ok_las)
    moreover
    obtain s' where s': "s' = redT_upd (ls, (ts(t' \<mapsto> x''), m''), ws) t' ta''" by auto
    ultimately
    have "s -t'\<triangleright>ta''\<rightarrow> s'" using red' cct est' wst' s
      by(auto intro!: redT.intros)
    hence ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma redT_deadlocked_subset:
  assumes  Red: "s -t\<triangleright>ta\<rightarrow> s'"
  and mlpres: "\<And>t x. \<lbrakk> thr s t = \<lfloor>x\<rfloor>; \<langle>x, shr s\<rangle> \<wrong> \<rbrakk> \<Longrightarrow> \<langle>x, shr s'\<rangle> \<wrong>"
  and clpres: "\<And>t x L. \<lbrakk> thr s t = \<lfloor>x\<rfloor>; \<langle>x, shr s\<rangle> L \<wrong>; L \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>L. \<langle>x, shr s'\<rangle> L \<wrong>"
  and clserp: "\<And>t x L. \<lbrakk> thr s t = \<lfloor>x\<rfloor>; \<langle>x, shr s'\<rangle> L \<wrong>; L \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>L'. L' \<subseteq> L \<and> \<langle>x, shr s\<rangle> L' \<wrong>"
  shows "deadlocked s \<subseteq> deadlocked s'"
proof(rule subsetI)
  fix t'
  assume t'dead: "t' \<in> deadlocked s"
  obtain las tas was where ta: "ta = (las, tas, was)" by (cases ta, auto)
  obtain ls ts m ws where s: "s = (ls, (ts, m), ws)" by (cases s, auto)
  obtain ls' ts' m' ws' where s': "s' = (ls', (ts', m'), ws')" by (cases s', auto)
  from ta s s' Red obtain x x'
    where red: "\<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
    and est: "ts t = \<lfloor>x\<rfloor>"
    and lot: "lock_ok_las ls t las"
    and cct: "thread_oks ts m' tas"
    and wst: "ws t = None"
    and ws': "ws' = redT_updWs ws t was"
    and es': "ts' = redT_updTs (ts(t \<mapsto> x')) tas"
    and ls': "ls' = redT_updLs ls t las"
    by(auto elim!: redT.cases)
  from Red have tndead: "t \<notin> deadlocked s"
    by(auto dest: red_no_deadlock)
  with t'dead have t't: "t' \<noteq> t" by auto
  from red have "\<not> final x"
    apply -
    apply(erule contrapos_pn)
    by(rule final_no_red)
  with tndead est s have nafe: "\<not> all_final_except ts (deadlocked s)"
    apply(clarsimp simp add: all_final_except_def)
    apply(rule_tac x="t" in bexI, auto)
    done
  show "t' \<in> deadlocked s'"
  proof(rule deadlocked.coinduct)
    show "t' \<in> deadlocked s" by(rule t'dead)
  next
    fix t''
    assume t''dead: "t'' \<in> deadlocked s"
    with nafe s
    have "\<exists>x. ts t'' = \<lfloor>x\<rfloor> \<and> \<langle>x, m\<rangle> \<wrong> \<and> (\<exists>L. \<langle>x, m\<rangle> L \<wrong>) \<and>
	          (\<forall>L. \<langle>x, m\<rangle> L \<wrong> \<longrightarrow> (\<exists>t'. (t' \<in> deadlocked s \<or> (\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t'' \<and> (\<exists>l\<in>L. has_lock (ls l) t')))"
      by(auto elim!: deadlocked.cases)
    then obtain X
      where est'': "ts t'' = \<lfloor>X\<rfloor>"
      and msE: "\<langle>X, m\<rangle> \<wrong>"
      and excsE: "\<exists>L. \<langle>X, m\<rangle> L \<wrong>"
      and csexdead: "\<forall>L. \<langle>X, m\<rangle> L \<wrong> \<longrightarrow> (\<exists>t'. (t' \<in> deadlocked s \<or> (\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t'' \<and> (\<exists>l\<in>L. has_lock (ls l) t'))"
      by(blast)
    from t''dead Red have t''t: "t'' \<noteq> t"
      by(auto dest: red_no_deadlock)
    with Red est'' s s' have es't'': "ts' t'' = \<lfloor>X\<rfloor>"
      by(auto elim!: redT_ts_Some_inv)
    show "(\<exists>t x L. t'' = t \<and> thr s' t = \<lfloor>x\<rfloor> \<and>
                          \<langle>x, shr s'\<rangle> \<wrong> \<and>
                          \<langle>x, shr s'\<rangle> L \<wrong> \<and>
                          (\<forall>L. \<langle>x, shr s'\<rangle> L \<wrong> \<longrightarrow>
                               (\<exists>t'. ((t' \<in> deadlocked s \<or> t' \<in> deadlocked s') \<or> (\<exists>x. thr s' t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t \<and> (\<exists>l\<in>L. has_lock (locks s' l) t')))) \<or>
        (\<exists>t x w. t'' = t \<and> thr s' t = \<lfloor>x\<rfloor> \<and> all_final_except (thr s') {x. x \<in> deadlocked s \<or> x \<in> deadlocked s'} \<and> wset s' t = \<lfloor>w\<rfloor>)"
    proof -
      note es't''
      moreover
      from excsE obtain L where clL: "\<langle>X, m\<rangle> L \<wrong>" by blast
      then obtain X' M' ta
	where red': "\<langle>X, m\<rangle> -ta\<rightarrow> \<langle>X', M'\<rangle>"
	and L: "L = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
	by(auto elim: can_lockE)
      from msE L red' have Lnempty: "L \<noteq> {}"
	by(auto dest!: must_lockD simp add: collect_locks_def)
      with est'' clL have clL': "\<exists>L. \<langle>X, m'\<rangle> L \<wrong>"
	by(rule clpres[simplified s s', simplified])
      moreover
      from est'' msE have msE': "\<langle>X, m'\<rangle> \<wrong>"
	by(rule mlpres[simplified s s', simplified])
      moreover
      have "\<forall>L. \<langle>X, m'\<rangle> L \<wrong> \<longrightarrow> (\<exists>t'. ((t' \<in> deadlocked s \<or> t' \<in> deadlocked s') \<or> (\<exists>x. thr s' t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t'' \<and> (\<exists>l\<in>L. has_lock (ls' l) t'))"
      proof(rule allI, rule impI)
 	fix L
	assume clL'': "\<langle>X, m'\<rangle> L \<wrong>"
	with msE' have "L \<noteq> {}"
	  by(auto elim!: can_lockE dest!: must_lockD simp add: collect_locks_def)
	with clL'' est'' have "\<exists>L'. L' \<subseteq> L \<and> \<langle>X, m\<rangle> L' \<wrong>"
	  by -(rule clserp[simplified s s', simplified])
	then obtain L'
 	  where clL': "\<langle>X, m\<rangle> L' \<wrong>"
	  and LL': "L' \<subseteq> L" by blast
	with csexdead obtain t' l'
	  where t'dead: "t' \<in> deadlocked s \<or> (\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x)"
	  and t't'': "t' \<noteq> t''"
	  and exlL: "\<exists>l\<in>L'. has_lock (ls l) t'"
	  by blast
	from exlL obtain l
	  where lL: "l \<in> L'"
	  and hll: "has_lock (ls l) t'"
	  by blast
	from t'dead Red s have tt': "t \<noteq> t'"
	  by(auto dest: red_no_deadlock final_no_redT)
 	from lot have "lock_actions_ok (ls l) t (las l)"
 	  by(simp add: lock_ok_las_def)
 	with tt' ls' hll have hl't': "has_lock (ls' l) t'"
 	  by(auto simp add: has_lock_has_locks_conv 
 	                    lock_actions_ok_has_locks_upd_locks_eq_has_locks
                            redT_updLs_def)
 	from lL LL' have lL: "l \<in> L" by auto
	from t'dead show "\<exists>t'. ((t' \<in> deadlocked s \<or> t' \<in> deadlocked s') \<or> (\<exists>x. thr s' t' = \<lfloor>x\<rfloor> \<and> final x)) \<and> t' \<noteq> t'' \<and> (\<exists>l\<in>L. has_lock (ls' l) t')"
	proof(rule disjE)
	  assume "t' \<in> deadlocked s"
	  with t't'' hl't' lL show ?thesis by blast
	next
	  assume "\<exists>x. ts t' = \<lfloor>x\<rfloor> \<and> final x"
	  then obtain x''
	    where tst': "ts t' = \<lfloor>x''\<rfloor>"
	    and finalx'': "final x''" by blast
	  with est red have "t' \<noteq> t" by(auto dest: final_no_red)
	  with tst' es' cct have "ts' t' = \<lfloor>x''\<rfloor>"
	    by(auto intro!: redT_updTs_Some simp add: redT_updTs_upd[OF _ cct, OF est, symmetric])
	  with finalx'' t't'' s' hl't' lL 
	  show ?thesis by(auto)
	qed
      qed
      ultimately show ?thesis using s' by simp
    qed
  qed
qed


end

end
