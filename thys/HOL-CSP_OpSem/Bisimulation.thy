theory Bisimulation
  imports OpSemLocale
begin




section \<open>Bisimulation\<close>

subsection \<open>LTS\<close>

subsubsection \<open>Definition\<close>

locale LTS =
  fixes S :: \<open>'\<alpha> set\<close>                      \<comment>\<open>set of states\<close>
  (*   and     \<tau>_rel  :: \<open>'\<alpha> rel\<close>             \<comment>\<open>relation  of \<open>\<tau>\<close> transitions\<close> *)
    and event_rels :: \<open>'\<beta> event \<Rightarrow> '\<alpha> rel\<close> \<comment>\<open>relations of transitions for events\<close>
  \<comment> \<open>Of course for processes we will instantiate \<^typ>\<open>'\<alpha>\<close> with
     \<^typ>\<open>'\<alpha> process\<close> and \<^typ>\<open>'\<beta>\<close> with \<^typ>\<open>'\<alpha>\<close>.\<close>
(* assumes Domain_\<tau>_rel : \<open>Domain \<tau>_rel \<subseteq> S\<close>     
  and    Range_\<tau>_rel :  \<open>Range \<tau>_rel \<subseteq> S\<close> *)
assumes  Domain_event_rels : \<open>Domain (event_rels e) \<subseteq> S\<close>     
    and  Range_event_rels :  \<open>Range (event_rels e) \<subseteq> S\<close>
begin

inductive trace_trans\<^sub>L\<^sub>T\<^sub>S :: \<open>['\<alpha>, '\<beta> trace, '\<alpha>] \<Rightarrow> bool\<close>
  where Nil  : \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P [] P\<close>
  |     tick : \<open>(P, Q) \<in> event_rels \<checkmark> \<Longrightarrow> trace_trans\<^sub>L\<^sub>T\<^sub>S P [\<checkmark>] Q\<close>
  |     Cons : \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S Q s R \<Longrightarrow> (P, Q) \<in> event_rels (ev e) \<Longrightarrow> trace_trans\<^sub>L\<^sub>T\<^sub>S P (ev e # s) R\<close>

definition Traces\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> \<Rightarrow> '\<beta> trace set\<close>
  where \<open>Traces\<^sub>L\<^sub>T\<^sub>S P \<equiv> {s. \<exists>Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q}\<close>

(* 
not working, we had to define trace_trans\<^sub>L\<^sub>T\<^sub>S first
inductive_set Traces\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace set\<close> (\<open>\<T>\<^sub>L\<^sub>T\<^sub>S\<close>)
  for P :: \<open>'\<alpha> process\<close>
  where  Nil_trace : \<open>[] \<in> \<T>\<^sub>L\<^sub>T\<^sub>S P\<close>
  |     tick_trace : \<open>P \<in> Domain (event_rels \<checkmark>) \<Longrightarrow> [\<checkmark>] \<in> \<T>\<^sub>L\<^sub>T\<^sub>S P\<close> 
  |       ev_trace : \<open>s \<in> \<T>\<^sub>L\<^sub>T\<^sub>S P \<Longrightarrow> (Q, P) \<in> events_rels (ev e) \<Longrightarrow> ev e # s \<in> \<T>\<^sub>L\<^sub>T\<^sub>S Q\<close>
 *)


definition initials\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> \<Rightarrow> '\<beta> event set\<close> (* (\<open>(_\<^sup>0\<^sub>L\<^sub>T\<^sub>S)\<close> [1000] 999), conflict with P\<^sup>0*)
  where \<open>initials\<^sub>L\<^sub>T\<^sub>S P \<equiv> {e. [e] \<in> Traces\<^sub>L\<^sub>T\<^sub>S P}\<close>


lemma trace_trans\<^sub>L\<^sub>T\<^sub>S_imp_ftF: \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q \<Longrightarrow> ftF s\<close>
  by (induct rule: trace_trans\<^sub>L\<^sub>T\<^sub>S.induct) (simp_all add: ftF_butlast)

lemma ftF_Traces\<^sub>L\<^sub>T\<^sub>S: \<open>s \<in> Traces\<^sub>L\<^sub>T\<^sub>S P \<Longrightarrow> ftF s\<close>
  unfolding Traces\<^sub>L\<^sub>T\<^sub>S_def by simp (elim exE trace_trans\<^sub>L\<^sub>T\<^sub>S_imp_ftF)



paragraph \<open>Characterizations for \<^const>\<open>trace_trans\<^sub>L\<^sub>T\<^sub>S\<close>\<close>

lemma trace_trans\<^sub>L\<^sub>T\<^sub>S_iff :
  \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P [] Q \<longleftrightarrow> P = Q\<close>
  \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P [f] Q \<longleftrightarrow> (P, Q) \<in> event_rels f\<close>
  \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P (ev e # s) R \<longleftrightarrow> (\<exists>Q. (P, Q) \<in> event_rels (ev e) \<and> trace_trans\<^sub>L\<^sub>T\<^sub>S Q s R)\<close>
  \<open>tF s \<Longrightarrow> trace_trans\<^sub>L\<^sub>T\<^sub>S P (s @ [f]) R \<longleftrightarrow> (\<exists>Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q \<and> (Q, R) \<in> event_rels f)\<close>
  \<open>ftF (s @ t) \<Longrightarrow> trace_trans\<^sub>L\<^sub>T\<^sub>S P (s @ t) R \<longleftrightarrow> (\<exists>Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q \<and> trace_trans\<^sub>L\<^sub>T\<^sub>S Q t R)\<close>
proof -
  show f1 : \<open>\<And>P Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P [] Q \<longleftrightarrow> P = Q\<close>
   and f2 : \<open>\<And>P Q f. trace_trans\<^sub>L\<^sub>T\<^sub>S P [f] Q \<longleftrightarrow> (P, Q) \<in> event_rels f\<close>
   and f3 : \<open>\<And>P Q' e s R. trace_trans\<^sub>L\<^sub>T\<^sub>S P (ev e # s) R \<longleftrightarrow>
                          (\<exists>Q. (P, Q) \<in> event_rels (ev e) \<and> trace_trans\<^sub>L\<^sub>T\<^sub>S Q s R)\<close>
    by (metis list.distinct(1) trace_trans\<^sub>L\<^sub>T\<^sub>S.simps,
        solves \<open>subst trace_trans\<^sub>L\<^sub>T\<^sub>S.simps, simp,
                metis event.exhaust neq_Nil_conv trace_trans\<^sub>L\<^sub>T\<^sub>S.simps\<close>,
        solves \<open>subst trace_trans\<^sub>L\<^sub>T\<^sub>S.simps, auto\<close>)

  show f5 : \<open>ftF (s @ t) \<Longrightarrow>
             trace_trans\<^sub>L\<^sub>T\<^sub>S P (s @ t) R \<longleftrightarrow> (\<exists>Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q \<and> trace_trans\<^sub>L\<^sub>T\<^sub>S Q t R)\<close> for t
  proof (induct s arbitrary: P Q)
    case Nil
    show ?case by (simp add: f1)
  next
    case (Cons e s P)
    from Cons.prems 
    consider \<open>e = \<checkmark>\<close> and \<open>s = []\<close> and \<open>t = []\<close> | \<open>\<exists>x. e = ev x\<close>
      by (cases e; simp add: ftF_butlast split: if_split_asm)
    thus ?case
    proof cases
      show \<open>e = \<checkmark> \<Longrightarrow> s = [] \<Longrightarrow> t = [] \<Longrightarrow> ?case\<close> by (simp add: f1 f2)
    next
      show \<open>\<exists>x. e = ev x \<Longrightarrow> ?case\<close>
        by (elim exE, simp add: f3)
           (metis Cons.hyps Cons.prems append.right_neutral ftF_append
                  ftF_mono tF_Cons trace_trans\<^sub>L\<^sub>T\<^sub>S_imp_ftF)
    qed
  qed

  show \<open>tF s \<Longrightarrow> trace_trans\<^sub>L\<^sub>T\<^sub>S P (s @ [f]) R \<longleftrightarrow>
        (\<exists>Q. trace_trans\<^sub>L\<^sub>T\<^sub>S P s Q \<and> (Q, R) \<in> event_rels f)\<close>
    by (simp add: f2 f5 ftF_butlast)
qed


lemma initials\<^sub>L\<^sub>T\<^sub>S_def_bis: \<open>initials\<^sub>L\<^sub>T\<^sub>S P = {e. P \<in> Domain (event_rels e)}\<close>
  by (auto simp add: initials\<^sub>L\<^sub>T\<^sub>S_def Traces\<^sub>L\<^sub>T\<^sub>S_def trace_trans\<^sub>L\<^sub>T\<^sub>S_iff(2))


subsubsection \<open>Simulation on LTS\<close>

definition Simulation\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> rel \<Rightarrow> bool\<close> (\<open>Sim\<^sub>L\<^sub>T\<^sub>S\<close>)
  where \<open>Sim\<^sub>L\<^sub>T\<^sub>S r \<equiv>
         \<forall>P Q P' e. (P, Q) \<in> r \<longrightarrow> P' \<in> Domain r \<longrightarrow> (P, P') \<in> event_rels e \<longrightarrow>
                    (\<exists>Q' \<in> Range r. (Q, Q') \<in> event_rels e \<and> (e \<noteq> \<checkmark> \<longrightarrow> (P', Q') \<in> r))\<close>

lemma Simulation\<^sub>L\<^sub>T\<^sub>SI :
  \<open>\<lbrakk>\<And>P Q P'. (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> (P, P') \<in> event_rels \<checkmark> \<Longrightarrow> \<exists>Q'\<in>Range r. (Q, Q') \<in> event_rels \<checkmark>;
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> (P, P') \<in> event_rels (ev e) \<Longrightarrow> \<exists>Q'. (Q, Q') \<in> event_rels (ev e) \<and> (P', Q') \<in> r\<rbrakk>
   \<Longrightarrow> Sim\<^sub>L\<^sub>T\<^sub>S r\<close>
  unfolding Simulation\<^sub>L\<^sub>T\<^sub>S_def by (metis Range.intros event.exhaust)

lemma Simulation\<^sub>L\<^sub>T\<^sub>SD1 : \<open>Sim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> (P, P') \<in> event_rels \<checkmark> \<Longrightarrow> \<exists>Q'\<in>Range r. (Q, Q') \<in> event_rels \<checkmark>\<close>
  and Simulation\<^sub>L\<^sub>T\<^sub>SD2 : \<open>Sim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> (P, P') \<in> event_rels (ev e) \<Longrightarrow> \<exists>Q'. (Q, Q') \<in> event_rels (ev e) \<and> (P', Q') \<in> r\<close>
  unfolding Simulation\<^sub>L\<^sub>T\<^sub>S_def by blast+


lemma Simulation\<^sub>L\<^sub>T\<^sub>S_Id_on: \<open>Sim\<^sub>L\<^sub>T\<^sub>S (Id_on A)\<close>
  by (rule Simulation\<^sub>L\<^sub>T\<^sub>SI) blast+


paragraph \<open>Composition of Simulations\<close>

lemma Simulation\<^sub>L\<^sub>T\<^sub>S_relcomp : \<open>Sim\<^sub>L\<^sub>T\<^sub>S (r O s)\<close> if \<open>Sim\<^sub>L\<^sub>T\<^sub>S r\<close> and \<open>Sim\<^sub>L\<^sub>T\<^sub>S s\<close> and \<open>Range r = Domain s\<close>
\<comment>\<open>At first glance \<^prop>\<open>Range r \<subseteq> Domain s\<close> is enough, but we actually
   need the equality to recover \<^term>\<open>Range (r O s)\<close> for \<^term>\<open>event_rels \<checkmark>\<close> case.\<close>
proof (rule Simulation\<^sub>L\<^sub>T\<^sub>SI)
  fix P R P'
  assume \<open>(P, R) \<in> r O s\<close> \<open>P' \<in> Domain (r O s)\<close> \<open>(P, P') \<in> event_rels \<checkmark>\<close>
  from \<open>(P, R) \<in> r O s\<close> obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>P' \<in> Domain (r O s)\<close> have \<open>P' \<in> Domain r\<close> by blast
  from Simulation\<^sub>L\<^sub>T\<^sub>SD1[OF \<open>Sim\<^sub>L\<^sub>T\<^sub>S r\<close> \<open>(P, Q) \<in> r\<close> \<open>P' \<in> Domain r\<close> \<open>(P, P') \<in> event_rels \<checkmark>\<close>]
  obtain Q' where \<open>Q' \<in> Range r\<close> \<open>(Q, Q') \<in> event_rels \<checkmark>\<close> by blast
  from \<open>Q' \<in> Range r\<close> \<open>Range r = Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
  from Simulation\<^sub>L\<^sub>T\<^sub>SD1[OF \<open>Sim\<^sub>L\<^sub>T\<^sub>S s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q' \<in> Domain s\<close> \<open>(Q, Q') \<in> event_rels \<checkmark>\<close>]
  obtain R' where \<open>R' \<in> Range s\<close> \<open>(R, R') \<in> event_rels \<checkmark>\<close> by blast
  show \<open>\<exists>R'\<in>Range (r O s). (R, R') \<in> event_rels \<checkmark>\<close>
  proof (rule bexI)
    from \<open>(R, R') \<in> event_rels \<checkmark>\<close> show \<open>(R, R') \<in> event_rels \<checkmark>\<close> .
  next
    show \<open>R' \<in> Range (r O s)\<close>
      by (metis (no_types) Domain_iff Range_iff \<open>R' \<in> Range s\<close>
                           relcomp.relcompI \<open>Range r = Domain s\<close>)
  qed
next
  fix P R e P'
  assume \<open>(P, R) \<in> r O s\<close> \<open>P' \<in> Domain (r O s)\<close> \<open>(P, P') \<in> event_rels (ev e)\<close>
  from \<open>(P, R) \<in> r O s\<close> obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>P' \<in> Domain (r O s)\<close> have \<open>P' \<in> Domain r\<close> by blast
  from Simulation\<^sub>L\<^sub>T\<^sub>SD2[OF \<open>Sim\<^sub>L\<^sub>T\<^sub>S r\<close> \<open>(P, Q) \<in> r\<close> \<open>P' \<in> Domain r\<close> \<open>(P, P') \<in> event_rels (ev e)\<close>]
  obtain Q' where \<open>(Q, Q') \<in> event_rels (ev e)\<close> \<open>(P', Q') \<in> r\<close> by blast
  from \<open>(P', Q') \<in> r\<close> \<open>Range r = Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
  from Simulation\<^sub>L\<^sub>T\<^sub>SD2[OF \<open>Sim\<^sub>L\<^sub>T\<^sub>S s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q' \<in> Domain s\<close> \<open>(Q, Q') \<in> event_rels (ev e)\<close>]
  obtain R' where \<open>(R, R') \<in> event_rels (ev e)\<close> \<open>(Q', R') \<in> s\<close> by blast
  with \<open>(P', Q') \<in> r\<close> \<open>(Q', R') \<in> s\<close>
  show \<open>\<exists>R'. (R, R') \<in> event_rels (ev e) \<and> (P', R') \<in> r O s\<close> by blast
qed



paragraph \<open>Characterization with trace_trans\<close>

lemma Simulation\<^sub>L\<^sub>T\<^sub>S_iff_trace_trans\<^sub>L\<^sub>T\<^sub>S:
  \<open>Sim\<^sub>L\<^sub>T\<^sub>S r \<longleftrightarrow> (\<forall>P Q P' s. (P, Q) \<in> r \<longrightarrow> P' \<in> Domain r \<longrightarrow> trace_trans P s P' \<longrightarrow>
                           (\<exists>Q' \<in> Range r. trace_trans Q s Q' \<and> (tF s \<longrightarrow> (P', Q') \<in> r)))\<close>
proof (intro iffI allI impI Simulation\<^sub>L\<^sub>T\<^sub>SI)

  oops


paragraph \<open>Traces of Simulation\<close>

lemma Simulation\<^sub>L\<^sub>T\<^sub>S_susbet_Traces\<^sub>L\<^sub>T\<^sub>S: \<open>Traces\<^sub>L\<^sub>T\<^sub>S P \<subseteq> Traces\<^sub>L\<^sub>T\<^sub>S Q\<close>
  if \<open>Sim\<^sub>L\<^sub>T\<^sub>S r\<close> and \<open>(P, Q) \<in> r\<close>
  and \<open>\<forall>P P' e. P \<in> Domain r \<longrightarrow> (P, P') \<in> event_rels e \<longrightarrow> P' \<in> Domain r\<close>
proof (rule subsetI)
  fix s
  assume \<open>s \<in> Traces\<^sub>L\<^sub>T\<^sub>S P\<close>
  then obtain P' where \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S P s P'\<close> unfolding Traces\<^sub>L\<^sub>T\<^sub>S_def by blast
  from this and \<open>(P, Q) \<in> r\<close> have \<open>\<exists>Q'. trace_trans\<^sub>L\<^sub>T\<^sub>S Q s Q'\<close>
  proof (induct s arbitrary: P Q)
    case Nil
    show ?case by (simp add: trace_trans\<^sub>L\<^sub>T\<^sub>S_iff(1))
  next
    case (Cons e s)
    consider \<open>e = \<checkmark>\<close> and \<open>s = []\<close> | \<open>\<exists>x. e = ev x\<close>
      by (metis Cons.prems(1) butlast.simps(2) event.exhaust
                ftF_butlast tF_Cons trace_trans\<^sub>L\<^sub>T\<^sub>S_imp_ftF)
    thus ?case
    proof cases
      show \<open>e = \<checkmark> \<Longrightarrow> s = [] \<Longrightarrow> \<exists>a. trace_trans\<^sub>L\<^sub>T\<^sub>S Q (e # s) a\<close>
        by (metis Cons.prems Domain.DomainI Simulation\<^sub>L\<^sub>T\<^sub>SD1
                  that(1, 3) trace_trans\<^sub>L\<^sub>T\<^sub>S_iff(2))
    next
      assume \<open>\<exists>x. e = ev x\<close>
      then obtain x where \<open>e = ev x\<close> ..
      with Cons.prems(1) trace_trans\<^sub>L\<^sub>T\<^sub>S_iff(3) obtain Q'
        where \<open>(P, Q') \<in> event_rels (ev x)\<close> \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S Q' s P'\<close> by blast
      have \<open>Q' \<in> Domain r\<close> by (metis Cons.prems(2) Domain.DomainI \<open>(P, Q') \<in> event_rels (ev x)\<close> that(3))
      from Simulation\<^sub>L\<^sub>T\<^sub>SD2[OF \<open>Sim\<^sub>L\<^sub>T\<^sub>S r\<close> \<open>(P, Q) \<in> r\<close> this \<open>(P, Q') \<in> event_rels (ev x)\<close>]
      obtain Q'' where \<open>(Q, Q'') \<in> event_rels (ev x)\<close> \<open>(Q', Q'') \<in> r\<close> by blast
      with \<open>trace_trans\<^sub>L\<^sub>T\<^sub>S Q' s P'\<close> Cons.hyps show ?case
        by (simp add: \<open>e = ev x\<close> trace_trans\<^sub>L\<^sub>T\<^sub>S_iff(3)) blast
    qed
  qed

  thus \<open>s \<in> Traces\<^sub>L\<^sub>T\<^sub>S Q\<close> by (simp add: Traces\<^sub>L\<^sub>T\<^sub>S_def)
qed
  
     


subsubsection \<open>Bisimulation on LTS\<close>

definition Bisimulation\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> rel \<Rightarrow> bool\<close> (\<open>Bisim\<^sub>L\<^sub>T\<^sub>S\<close>)
  where \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<equiv> Sim\<^sub>L\<^sub>T\<^sub>S r \<and> Sim\<^sub>L\<^sub>T\<^sub>S (r\<inverse>)\<close>

(* lemma Bisimulation\<^sub>L\<^sub>T\<^sub>S_def_bis : 
  \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<longleftrightarrow> (\<forall>P Q P' e. (P, Q) \<in> r \<longrightarrow> P' \<in> Domain r \<longrightarrow> (P, P') \<in> event_rels e \<longleftrightarrow>
                             (\<exists>Q' \<in> Range r. (Q, Q') \<in> event_rels e \<and> (e \<noteq> \<checkmark> \<longrightarrow> (P', Q') \<in> r)))\<close>
  unfolding Bisimulation\<^sub>L\<^sub>T\<^sub>S_def Simulation\<^sub>L\<^sub>T\<^sub>S_def sym_def converseD by (auto simp add: subset_iff)
 *)

lemma Bisimulation\<^sub>L\<^sub>T\<^sub>SI :
  \<open>Sim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> Sim\<^sub>L\<^sub>T\<^sub>S (r\<inverse>) \<Longrightarrow> Bisim\<^sub>L\<^sub>T\<^sub>S r\<close>
  by (simp add: Bisimulation\<^sub>L\<^sub>T\<^sub>S_def)

lemma Bisimulation\<^sub>L\<^sub>T\<^sub>SD1 : \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> Sim\<^sub>L\<^sub>T\<^sub>S r\<close>
  and Bisimulation\<^sub>L\<^sub>T\<^sub>SD2 : \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> Sim\<^sub>L\<^sub>T\<^sub>S (r\<inverse>)\<close>
  by (simp_all add: Bisimulation\<^sub>L\<^sub>T\<^sub>S_def)


lemma Bisimulation\<^sub>L\<^sub>T\<^sub>S_Id_on: \<open>Bisim\<^sub>L\<^sub>T\<^sub>S (Id_on A)\<close>
  by (simp add: Bisimulation\<^sub>L\<^sub>T\<^sub>S_def Simulation\<^sub>L\<^sub>T\<^sub>S_Id_on)

lemma Bisimulation\<^sub>L\<^sub>T\<^sub>S_converse_iff_Bisimulation\<^sub>L\<^sub>T\<^sub>S [simp]: \<open>Bisim\<^sub>L\<^sub>T\<^sub>S (r\<inverse>) \<longleftrightarrow> Bisim\<^sub>L\<^sub>T\<^sub>S r\<close>
  by (rule iffI) (simp_all add: Bisimulation\<^sub>L\<^sub>T\<^sub>S_def)


lemma Bisimulation\<^sub>L\<^sub>T\<^sub>S_relcomp :
  \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> Bisim\<^sub>L\<^sub>T\<^sub>S s \<Longrightarrow> Range r = Domain s \<Longrightarrow> Bisim\<^sub>L\<^sub>T\<^sub>S (r O s)\<close>
  by (rule Bisimulation\<^sub>L\<^sub>T\<^sub>SI)
     (simp_all add: Simulation\<^sub>L\<^sub>T\<^sub>S_relcomp Bisimulation\<^sub>L\<^sub>T\<^sub>SD1 Bisimulation\<^sub>L\<^sub>T\<^sub>SD2 converse_relcomp)



paragraph \<open>Traces of Bisimulation\<close>

lemma Biimulation\<^sub>L\<^sub>T\<^sub>S_eq_Traces\<^sub>L\<^sub>T\<^sub>S: \<open>Traces\<^sub>L\<^sub>T\<^sub>S P = Traces\<^sub>L\<^sub>T\<^sub>S Q\<close>
  if \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r\<close> and \<open>(P, Q) \<in> r\<close>
  and \<open>\<forall>P P' e. P \<in> Domain r \<longrightarrow> (P, P') \<in> event_rels e \<longrightarrow> P' \<in> Domain r\<close>
  and \<open>\<forall>P P' e. P \<in> Range  r \<longrightarrow> (P, P') \<in> event_rels e \<longrightarrow> P' \<in> Range  r\<close>
proof (rule subset_antisym)
  from \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r\<close>[THEN Bisimulation\<^sub>L\<^sub>T\<^sub>SD1] \<open>(P, Q) \<in> r\<close> that(3)
  show \<open>Traces\<^sub>L\<^sub>T\<^sub>S P \<subseteq> Traces\<^sub>L\<^sub>T\<^sub>S Q\<close> by (rule Simulation\<^sub>L\<^sub>T\<^sub>S_susbet_Traces\<^sub>L\<^sub>T\<^sub>S)
next
  from \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r\<close>[THEN Bisimulation\<^sub>L\<^sub>T\<^sub>SD2] \<open>(P, Q) \<in> r\<close>[THEN converseI]
  show \<open>Traces\<^sub>L\<^sub>T\<^sub>S Q \<subseteq> Traces\<^sub>L\<^sub>T\<^sub>S P\<close>
    by (rule Simulation\<^sub>L\<^sub>T\<^sub>S_susbet_Traces\<^sub>L\<^sub>T\<^sub>S) (simp add: that(4))
qed

(* 
corollary (in AfterExt) Bisimulation_imp_eq_T: \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
  using Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e by blast


lemma (in OpSemTransitions) Bisimulation_imp_ev_trans:
  \<open>Bisim r \<Longrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close>
  by (metis BisimulationD1 Simulation_Bisimulation Simulation_imp_ev_trans Un_iff)

 *)

subsection \<open>Bisimilar and Bisimilarity\<close>

definition Bisimilar\<^sub>L\<^sub>T\<^sub>S :: \<open>['\<alpha>, '\<alpha>] \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50)
  where \<open>P \<sim> Q \<equiv> \<exists>r. Bisim\<^sub>L\<^sub>T\<^sub>S r \<and> (P, Q) \<in> r\<close>

lemma Bisimilar\<^sub>L\<^sub>T\<^sub>SI : \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P \<sim> Q\<close>
  by (auto simp add: Bisimilar\<^sub>L\<^sub>T\<^sub>S_def)

lemma Bisimilar\<^sub>L\<^sub>T\<^sub>SE :
  assumes \<open>P \<sim> Q\<close>
  obtains r where \<open>Bisim\<^sub>L\<^sub>T\<^sub>S r\<close> and \<open>(P, Q) \<in> r\<close>
  using assms unfolding Bisimilar\<^sub>L\<^sub>T\<^sub>S_def by blast


abbreviation Bisimilarity\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> rel\<close> (\<open>\<B>\<^sub>L\<^sub>T\<^sub>S\<close>)
  where \<open>\<B>\<^sub>L\<^sub>T\<^sub>S \<equiv> {(P, Q). P \<sim> Q}\<close>


lemma Bisimulation\<^sub>L\<^sub>T\<^sub>S_Bisimilarity\<^sub>L\<^sub>T\<^sub>S: \<open>Bisim\<^sub>L\<^sub>T\<^sub>S \<B>\<^sub>L\<^sub>T\<^sub>S\<close>
proof (rule Bisimulation\<^sub>L\<^sub>T\<^sub>SI)
  show \<open>Sim\<^sub>L\<^sub>T\<^sub>S \<B>\<^sub>L\<^sub>T\<^sub>S\<close>
  proof (rule Simulation\<^sub>L\<^sub>T\<^sub>SI)
    show \<open>(P, Q) \<in> \<B>\<^sub>L\<^sub>T\<^sub>S \<Longrightarrow> P' \<in> Domain \<B>\<^sub>L\<^sub>T\<^sub>S \<Longrightarrow> (P, P') \<in> event_rels \<checkmark>
          \<Longrightarrow> \<exists>Q'\<in>Range \<B>\<^sub>L\<^sub>T\<^sub>S. (Q, Q') \<in> event_rels \<checkmark>\<close> for P Q P'

      oops
      apply (auto simp add: Bisimilar\<^sub>L\<^sub>T\<^sub>S_def Bisimulation\<^sub>L\<^sub>T\<^sub>S_def Simulation\<^sub>L\<^sub>T\<^sub>S_def)
      sledgehammer
  oops
  apply (intro Bisimulation\<^sub>L\<^sub>T\<^sub>SI Simulation\<^sub>L\<^sub>T\<^sub>SI)
  apply (simp_all add: )
  sledgehammer
  
  show \<open>(P, Q) \<in> \<B> \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close> for P Q
    by (simp, elim BisimilarE BisimulationE, blast)
next
  fix P Q e
  assume \<open>(P, Q) \<in> \<B>\<close> \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>(P, Q) \<in> \<B>\<close> BisimilarE obtain r where \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> by blast
  show \<open>(P after e, Q after e) \<in> \<B>\<close>
  proof (clarify, rule BisimilarI)
    from \<open>Bisim r\<close> show \<open>Bisim r\<close> .
  next
    from \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
    show \<open>(P after e, Q after e) \<in> r\<close> by (fact BisimulationD2)
  qed
qed


lemma Bisimilarity_contains_Bisimulation: \<open>Bisim r \<Longrightarrow> r \<subseteq> \<B>\<close>
  using BisimilarI by blast
  

lemma Bisimilarity_is_maximal: \<open>r = \<B> \<longleftrightarrow> Bisim r \<and> (\<forall>s. Bisim s \<longrightarrow> s \<subseteq> r)\<close>
  using Bisimulation_Bisimilarity Bisimilarity_contains_Bisimulation by blast


(* voir si on a envie plus tard de faire une locale pour restreindre les noeuds *)
lemma Bisimilarity_is_equivalence_relation: \<open>equiv UNIV \<B>\<close>
proof (rule equivI)
  show \<open>refl \<B>\<close>
    by (meson Bisimilarity_contains_Bisimulation
              Bisimulation_Id IdI reflI subset_eq)
next
  show \<open>sym \<B>\<close>
    by (metis Bisimilarity_contains_Bisimulation Bisimulation_Bisimilarity
              Bisimulation_iff_Bisimulation_converse Un_absorb2 sym_Un_converse)
next
  from BisimilarI Bisimulation_Bisimilarity Bisimulation_relcomp
  show \<open>trans \<B>\<close> by (intro transI) blast
qed







end




context OpSemTransitions
begin


section \<open>Bisimulation\<close>

subsection \<open>Simulation\<close>

definition Simulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Sim\<close>)
  where \<open>Sim r \<equiv> \<forall>P Q P'. (P, Q) \<in> r \<longrightarrow> P' \<in> Domain r \<longrightarrow>
                 (P \<leadsto>\<^sub>\<checkmark> P' \<longrightarrow> (\<exists>Q'\<in>Range r. Q \<leadsto>\<^sub>\<checkmark> Q')) \<and>
                 (\<forall>e. P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r))\<close>
  (* add [] \<in> \<D> P \<longrightarrow> [] \<in> \<D> Q ? *)

lemma SimulationI :
  \<open>\<lbrakk>\<And>P Q P'. (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> \<exists>Q'\<in>Range r. Q \<leadsto>\<^sub>\<checkmark> Q';
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<rbrakk>
   \<Longrightarrow> Sim r\<close>
  by (simp add: Simulation_def)

lemma SimulationD1 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> \<exists>Q'\<in>Range r. Q \<leadsto>\<^sub>\<checkmark> Q'\<close>
  and SimulationD2 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P'\<in>Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  by (simp_all add: Simulation_def)

lemma SimulationE: 
(* see how to write this lemma, not working at all  *)
  assumes \<open>Sim r\<close> and \<open>(P, Q) \<in> r\<close> and \<open>P'\<in>Domain r\<close>
  obtains Q' where \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> Q \<leadsto>\<^sub>\<checkmark> Q'\<close>
      and \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  using assms unfolding Simulation_def by blast


paragraph \<open>Examples of Simulations (especially with refinements)\<close>

lemma Simulation_Id: \<open>Sim Id\<close> (* \<open>Id_on\<close> if we go for the locale *)
  using \<tau>_trans_eq by (intro SimulationI) blast+

method show_Simulation_converse_le uses hyp1 hyps2_3 =
  rule SimulationI, simp_all add: AfterExt_def,
  use \<tau>_trans_eq hyp1 in blast,
  meson \<tau>_trans_eq in_mono hyp1 hyps2_3

lemma Simulation_converse_leF: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_F hyps2_3 : mono_After_F trans_F)

lemma Simulation_converse_leT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_T hyps2_3 : mono_After_T trans_T)

lemma Simulation_converse_leFD: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F\<^sub>D P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_FD hyps2_3 : mono_After_FD trans_FD)

lemma Simulation_converse_leDT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>D\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_DT hyps2_3 : mono_After_DT trans_DT)



paragraph \<open>Composition of Simulations\<close>

lemma Simulation_relcomp : \<open>Sim (r O s)\<close> if \<open>Sim r\<close> and \<open>Sim s\<close> and \<open>Range r = Domain s\<close>
\<comment>\<open>At first glance \<^prop>\<open>Range r \<subseteq> Domain s\<close> is enough, but we actually
   need the equality to recover \<^term>\<open>Range (r O s)\<close> for \<open>(\<leadsto>\<^sub>\<checkmark>)\<close> case.\<close>
proof (rule SimulationI)
  fix P R P'
  assume \<open>(P, R) \<in> r O s\<close> \<open>P' \<in> Domain (r O s)\<close> \<open>P \<leadsto>\<^sub>\<checkmark> P'\<close>
  from \<open>(P, R) \<in> r O s\<close> obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>P' \<in> Domain (r O s)\<close> have \<open>P' \<in> Domain r\<close> by blast
  from SimulationD1[OF \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^sub>\<checkmark> P'\<close>]
  obtain Q' where \<open>Q' \<in> Range r\<close> \<open>Q \<leadsto>\<^sub>\<checkmark> Q'\<close> by blast
  from \<open>Q' \<in> Range r\<close> \<open>Range r = Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
  from SimulationD1[OF \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q' \<in> Domain s\<close> \<open>Q \<leadsto>\<^sub>\<checkmark> Q'\<close>]
  obtain R' where \<open>R' \<in> Range s\<close> \<open>R \<leadsto>\<^sub>\<checkmark> R'\<close> by blast
  show \<open>\<exists>R'\<in>Range (r O s). R \<leadsto>\<^sub>\<checkmark> R'\<close>
  proof (rule bexI)
    from \<open>R \<leadsto>\<^sub>\<checkmark> R'\<close> show \<open>R \<leadsto>\<^sub>\<checkmark> R'\<close> .
  next
    show \<open>R' \<in> Range (r O s)\<close>
      by (metis (no_types) Domain_iff Range_iff \<open>R' \<in> Range s\<close>
                           relcomp.relcompI \<open>Range r = Domain s\<close>)
  qed
next
  fix P R e P'
  assume \<open>(P, R) \<in> r O s\<close> \<open>P' \<in> Domain (r O s)\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>
  from \<open>(P, R) \<in> r O s\<close> obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>P' \<in> Domain (r O s)\<close> have \<open>P' \<in> Domain r\<close> by blast
  from SimulationD2[OF \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>]
  obtain Q' where \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close> by blast
  from \<open>(P', Q') \<in> r\<close> \<open>Range r = Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
  
  from SimulationD2[OF \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q' \<in> Domain s\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>]
  obtain R' where \<open>R \<leadsto>\<^bsub>e\<^esub> R'\<close> \<open>(Q', R') \<in> s\<close> by blast
  with \<open>(P', Q') \<in> r\<close> \<open>(Q', R') \<in> s\<close>
  show \<open>\<exists>R'. R \<leadsto>\<^bsub>e\<^esub> R' \<and> (P', R') \<in> r O s\<close> by blast
qed



paragraph \<open>Initials and Traces on a LTS\<close>

text \<open>The LTS is not necessarily complete, in the sense that
      we may only access to some of the initials, some of the traces \<open>\<dots>\<close>\<close>

definition initlats\<^sub>L\<^sub>T\<^sub>S :: \<open>'\<alpha> process set \<Rightarrow> '\<alpha> process \<Rightarrow> '\<alpha>\<close>
  where \<open>initlats\<^sub>L\<^sub>T\<^sub>S S P \<equiv> \<close>
lemma \<open>\<close>
  


lemma (in AfterExt) Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :
  \<open>Sim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
proof (intro iffI allI impI)
  fix P Q
  assume \<open>Sim r\<close>
  hence * : \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
            \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow>
             (P after e, Q after e) \<in> r\<close> for P Q e by (meson SimulationE)+
  have \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q \<and> (tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close> for s
  proof (induct s rule: rev_induct)
    case Nil
    thus ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    from append_T_imp_tF snoc.prems(2) have f1 : \<open>tF s\<close> by blast
    with snoc.hyps snoc.prems is_processT3_ST
    have f2 : \<open>s \<in> \<T> Q\<close> \<open>(P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r\<close> by blast+
    from f2(2) have f3 : \<open>(P after\<^sub>\<T> s)\<^sup>0 \<subseteq> (Q after\<^sub>\<T> s)\<^sup>0\<close> by (fact "*"(1))
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(2) have f4 : \<open>e \<in> (P after\<^sub>\<T> s)\<^sup>0\<close> by blast
    from f3 f4 have f5 : \<open>e \<in> (Q after\<^sub>\<T> s)\<^sup>0\<close> by auto
    show ?case
    proof (intro conjI impI)
      from f5 show \<open>s @ [e] \<in> \<T> Q\<close> by (simp add: initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq f1 f2(1))
    next
      assume \<open>tF (s @ [e])\<close>
      then obtain x where \<open>e = ev x\<close> by (cases e; simp)
      show \<open>(P after\<^sub>\<T> (s @ [e]), Q after\<^sub>\<T> (s @ [e])) \<in> r\<close> 
        by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc \<open>e = ev x\<close> AfterExt_def)
           (fact "*"(2)[OF f2(2) f3 f4[simplified \<open>e = ev x\<close>]])
    qed
  qed
  thus \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P \<subseteq> \<T> Q \<and> (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
    by (simp add: subset_iff)
next
  assume * : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
  show \<open>Sim r\<close> 
  proof (rule SimulationI)
    fix P Q
    from "*"[rule_format, of P Q] show \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      by (simp add: anti_mono_initials_T trace_refine_def)
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close>
    from \<open>ev e \<in> P\<^sup>0\<close> have \<open>[ev e] \<in> \<T> P\<close> by (simp add: initials_def)
    from "*"[rule_format, OF \<open>(P, Q) \<in> r\<close>, THEN conjunct2, rule_format, OF this]
    show \<open>(P after e, Q after e) \<in> r\<close> by (simp add: AfterExt_def)
  qed
qed



lemma (in OpSemTransitions) Simulation_imp_ev_trans:
  \<open>(\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
          (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close> if \<open>Sim r\<close>
proof (intro iffI allI impI conjI)
  from \<open>Sim r\<close> show \<open>(P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q
    by (elim SimulationE) blast
next
  fix P Q e
  assume \<open>(P, Q) \<in> r\<close> and \<open>ev e \<in> P\<^sup>0\<close>
  with \<open>Sim r\<close> SimulationD1 SimulationD2 have \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>(P after e, Q after e) \<in> r\<close> by simp_all
  have \<open>P \<leadsto>\<^bsub>e\<^esub> P after e\<close> by (meson \<open>ev e \<in> P\<^sup>0\<close> \<tau>_trans_eq ev_trans_is)
  moreover have \<open>Q \<leadsto>\<^bsub>e\<^esub> Q after e\<close>
    by (metis \<tau>_trans_eq ev_trans_is \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close> subset_eq)
  ultimately show \<open>\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
    using \<open>(P after e, Q after e) \<in> r\<close> by blast
qed


(* next
  assume hyp : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r))\<close>
  show \<open>Sim r\<close>
  proof (intro SimulationI subsetI)
    show \<open>e \<in> Q\<^sup>0\<close> if \<open>(P, Q) \<in> r\<close> and \<open>e \<in> P\<^sup>0\<close> for P Q e
      by (metis hyp[rule_format, OF that(1)] event.exhaust that(2))
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> and \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> and \<open>ev e \<in> P\<^sup>0\<close>
    from this(1, 3) hyp obtain P' Q' where \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close> by blast
    thus \<open>(P after e, Q after e) \<in> r\<close> sledgehammer
  oops
  proof 
    find_theorems name: ome name: I *)
    



subsection \<open>Bisimulation\<close>

definition Bisimulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Bisim\<close>)
  where \<open>Bisim r \<equiv> Sim r \<and> Sim (r\<inverse>)\<close>

lemma Bisimulation_def_bis : 
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> P\<^sup>0 = Q\<^sup>0 \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (P after e, Q after e) \<in> r))\<close>
  unfolding Bisimulation_def Simulation_def sym_def converseD by (auto simp add: subset_iff)


lemma BisimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0;
    \<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<rbrakk>
   \<Longrightarrow> Bisim r\<close>
  by (simp add: Bisimulation_def_bis)

lemma BisimulationD1 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
  and BisimulationD2 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  by (simp_all add: Bisimulation_def_bis)

lemma BisimulationE : 
  assumes \<open>Bisim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
      and \<open>\<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  using assms unfolding Bisimulation_def_bis by blast


lemma Bisimulation_Id: \<open>Bisim Id\<close>
  by (rule BisimulationI) simp_all

lemma Bisimulation_iff_Bisimulation_converse: \<open>Bisim r \<longleftrightarrow> Bisim (r\<inverse>)\<close>
  by (intro iffI BisimulationI; elim BisimulationE, simp)

lemma Simulation_Bisimulation: \<open>Bisim r \<Longrightarrow> Sim r\<close>
  by (elim BisimulationE, rule SimulationI; simp)


lemma Bisimulation_relcomp : \<open>Bisim r \<Longrightarrow> Bisim s \<Longrightarrow> Bisim (r O s)\<close>
  unfolding Bisimulation_def by (metis Simulation_relcomp converse_relcomp)


lemma (in AfterExt) Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P = \<T> Q \<and>
                      (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
  unfolding Bisimulation_def by (simp add: Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e) blast


corollary (in AfterExt) Bisimulation_imp_eq_T: \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
  using Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e by blast


lemma (in OpSemTransitions) Bisimulation_imp_ev_trans:
  \<open>Bisim r \<Longrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close>

  oops
  by (metis BisimulationD1 Simulation_Bisimulation Simulation_imp_ev_trans Un_iff)



subsection \<open>Bisimilar and Bisimilarity\<close>

definition Bisimilar :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50)
  where \<open>P \<sim> Q \<equiv> \<exists>r. Bisim r \<and> (P, Q) \<in> r\<close>

lemma BisimilarI : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P \<sim> Q\<close>
  by (auto simp add: Bisimilar_def)

lemma BisimilarE :
  assumes \<open>P \<sim> Q\<close>
  obtains r where \<open>Bisim r\<close> and \<open>(P, Q) \<in> r\<close>
  using assms unfolding Bisimilar_def by blast


abbreviation Bisimilarity :: \<open>'\<alpha> process rel\<close> (\<open>\<B>\<close>)
  where \<open>\<B> \<equiv> {(P, Q). P \<sim> Q}\<close>


lemma Bisimulation_Bisimilarity: \<open>Bisim \<B>\<close>
proof (rule BisimulationI)
  show \<open>(P, Q) \<in> \<B> \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close> for P Q
    by (simp, elim BisimilarE BisimulationE, blast)
next
  fix P Q e
  assume \<open>(P, Q) \<in> \<B>\<close> \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>(P, Q) \<in> \<B>\<close> BisimilarE obtain r where \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> by blast
  show \<open>(P after e, Q after e) \<in> \<B>\<close>
  proof (clarify, rule BisimilarI)
    from \<open>Bisim r\<close> show \<open>Bisim r\<close> .
  next
    from \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
    show \<open>(P after e, Q after e) \<in> r\<close> by (fact BisimulationD2)
  qed
qed


lemma Bisimilarity_contains_Bisimulation: \<open>Bisim r \<Longrightarrow> r \<subseteq> \<B>\<close>
  using BisimilarI by blast
  

lemma Bisimilarity_is_maximal: \<open>r = \<B> \<longleftrightarrow> Bisim r \<and> (\<forall>s. Bisim s \<longrightarrow> s \<subseteq> r)\<close>
  using Bisimulation_Bisimilarity Bisimilarity_contains_Bisimulation by blast


(* voir si on a envie plus tard de faire une locale pour restreindre les noeuds *)
lemma Bisimilarity_is_equivalence_relation: \<open>equiv UNIV \<B>\<close>
proof (rule equivI)
  show \<open>refl \<B>\<close>
    by (meson Bisimilarity_contains_Bisimulation
              Bisimulation_Id IdI reflI subset_eq)
next
  show \<open>sym \<B>\<close>
    by (metis Bisimilarity_contains_Bisimulation Bisimulation_Bisimilarity
              Bisimulation_iff_Bisimulation_converse Un_absorb2 sym_Un_converse)
next
  from BisimilarI Bisimulation_Bisimilarity Bisimulation_relcomp
  show \<open>trans \<B>\<close> by (intro transI) blast
qed
















(* section \<open>Bisimulation\<close>

context After
begin

subsection \<open>Simulation\<close>

definition Simulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Sim\<close>)
  where \<open>Sim r \<equiv> \<forall>P Q. (P, Q) \<in> r \<longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (P after e, Q after e) \<in> r)\<close>
  (* add [] \<in> \<D> P \<longrightarrow> [] \<in> \<D> Q ? *)

lemma SimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0;
    \<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<rbrakk>
   \<Longrightarrow> Sim r\<close>
  by (simp add: Simulation_def)

lemma SimulationD1 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
  and SimulationD2 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  by (simp_all add: Simulation_def)

lemma SimulationE: 
  assumes \<open>Sim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      and \<open>\<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  using assms unfolding Simulation_def by blast


lemma Simulation_Id: \<open>Sim Id\<close> (* \<open>Id_on\<close> if we go for the locale *)
  by (rule SimulationI) simp_all


lemma Simulation_relcomp : \<open>Sim (r O s)\<close> if \<open>Sim r\<close> and \<open>Sim s\<close>
proof (rule SimulationI)
  show \<open>(P, R) \<in> r O s \<Longrightarrow> P\<^sup>0 \<subseteq> R\<^sup>0\<close> for P R
  proof (elim relcompE, clarify)
    fix Q x
    assume \<open>(P, Q) \<in> r\<close> and \<open>(Q, R) \<in> s\<close> and \<open>x \<in> P\<^sup>0\<close>
    from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> have \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> by (fact SimulationD1)
    with \<open>x \<in> P\<^sup>0\<close> have \<open>x \<in> Q\<^sup>0\<close> by (fact set_rev_mp)
    also have \<open>Q\<^sup>0 \<subseteq> R\<^sup>0\<close> using \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> by (fact SimulationD1)
    finally show \<open>x \<in> R\<^sup>0\<close> .
  qed
next
  show \<open>(P, R) \<in> r O s \<Longrightarrow> P\<^sup>0 \<subseteq> R\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, R after e) \<in> r O s\<close> for P R e
  proof (elim relcompE, clarify)
    fix Q
    assume \<open>ev e \<in> P\<^sup>0\<close> and \<open>(P, Q) \<in> r\<close> and \<open>(Q, R) \<in> s\<close>
    show \<open>(P after e, R after e) \<in> r O s\<close>
    proof (rule relcompI)
      from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
      show \<open>(P after e, Q after e) \<in> r\<close> by (fact SimulationD2)
    next
      from \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> set_mp[OF SimulationD1[OF \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close>] \<open>ev e \<in> P\<^sup>0\<close>]
      show \<open>(Q after e, R after e) \<in> s\<close> by (fact SimulationD2)
    qed
  qed
qed


lemma (in AfterExt) Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :
  \<open>Sim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
proof (intro iffI allI impI)
  fix P Q
  assume \<open>Sim r\<close>
  hence * : \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
            \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow>
             (P after e, Q after e) \<in> r\<close> for P Q e by (meson SimulationE)+
  have \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q \<and> (tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close> for s
  proof (induct s rule: rev_induct)
    case Nil
    thus ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    from append_T_imp_tF snoc.prems(2) have f1 : \<open>tF s\<close> by blast
    with snoc.hyps snoc.prems is_processT3_ST
    have f2 : \<open>s \<in> \<T> Q\<close> \<open>(P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r\<close> by blast+
    from f2(2) have f3 : \<open>(P after\<^sub>\<T> s)\<^sup>0 \<subseteq> (Q after\<^sub>\<T> s)\<^sup>0\<close> by (fact "*"(1))
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(2) have f4 : \<open>e \<in> (P after\<^sub>\<T> s)\<^sup>0\<close> by blast
    from f3 f4 have f5 : \<open>e \<in> (Q after\<^sub>\<T> s)\<^sup>0\<close> by auto
    show ?case
    proof (intro conjI impI)
      from f5 show \<open>s @ [e] \<in> \<T> Q\<close> by (simp add: initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq f1 f2(1))
    next
      assume \<open>tF (s @ [e])\<close>
      then obtain x where \<open>e = ev x\<close> by (cases e; simp)
      show \<open>(P after\<^sub>\<T> (s @ [e]), Q after\<^sub>\<T> (s @ [e])) \<in> r\<close> 
        by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc \<open>e = ev x\<close> AfterExt_def)
           (fact "*"(2)[OF f2(2) f3 f4[simplified \<open>e = ev x\<close>]])
    qed
  qed
  thus \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P \<subseteq> \<T> Q \<and> (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
    by (simp add: subset_iff)
next
  assume * : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
  show \<open>Sim r\<close> 
  proof (rule SimulationI)
    fix P Q
    from "*"[rule_format, of P Q] show \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      by (simp add: anti_mono_initials_T trace_refine_def)
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close>
    from \<open>ev e \<in> P\<^sup>0\<close> have \<open>[ev e] \<in> \<T> P\<close> by (simp add: initials_def)
    from "*"[rule_format, OF \<open>(P, Q) \<in> r\<close>, THEN conjunct2, rule_format, OF this]
    show \<open>(P after e, Q after e) \<in> r\<close> by (simp add: AfterExt_def)
  qed
qed



lemma (in OpSemTransitions) Simulation_imp_ev_trans:
  \<open>(\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
          (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close> if \<open>Sim r\<close>
proof (intro iffI allI impI conjI)
  from \<open>Sim r\<close> show \<open>(P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q
    by (elim SimulationE) blast
next
  fix P Q e
  assume \<open>(P, Q) \<in> r\<close> and \<open>ev e \<in> P\<^sup>0\<close>
  with \<open>Sim r\<close> SimulationD1 SimulationD2 have \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>(P after e, Q after e) \<in> r\<close> by simp_all
  have \<open>P \<leadsto>\<^bsub>e\<^esub> P after e\<close> by (meson \<open>ev e \<in> P\<^sup>0\<close> \<tau>_trans_eq ev_trans_is)
  moreover have \<open>Q \<leadsto>\<^bsub>e\<^esub> Q after e\<close>
    by (metis \<tau>_trans_eq ev_trans_is \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close> subset_eq)
  ultimately show \<open>\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
    using \<open>(P after e, Q after e) \<in> r\<close> by blast
qed


(* next
  assume hyp : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r))\<close>
  show \<open>Sim r\<close>
  proof (intro SimulationI subsetI)
    show \<open>e \<in> Q\<^sup>0\<close> if \<open>(P, Q) \<in> r\<close> and \<open>e \<in> P\<^sup>0\<close> for P Q e
      by (metis hyp[rule_format, OF that(1)] event.exhaust that(2))
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> and \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> and \<open>ev e \<in> P\<^sup>0\<close>
    from this(1, 3) hyp obtain P' Q' where \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close> by blast
    thus \<open>(P after e, Q after e) \<in> r\<close> sledgehammer
  oops
  proof 
    find_theorems name: ome name: I *)
    



subsection \<open>Bisimulation\<close>

definition Bisimulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Bisim\<close>)
  where \<open>Bisim r \<equiv> Sim r \<and> Sim (r\<inverse>)\<close>

lemma Bisimulation_def_bis : 
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> P\<^sup>0 = Q\<^sup>0 \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (P after e, Q after e) \<in> r))\<close>
  unfolding Bisimulation_def Simulation_def sym_def converseD by (auto simp add: subset_iff)


lemma BisimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0;
    \<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<rbrakk>
   \<Longrightarrow> Bisim r\<close>
  by (simp add: Bisimulation_def_bis)

lemma BisimulationD1 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
  and BisimulationD2 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  by (simp_all add: Bisimulation_def_bis)

lemma BisimulationE : 
  assumes \<open>Bisim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
      and \<open>\<And>P Q e. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (P after e, Q after e) \<in> r\<close>
  using assms unfolding Bisimulation_def_bis by blast


lemma Bisimulation_Id: \<open>Bisim Id\<close>
  by (rule BisimulationI) simp_all

lemma Bisimulation_iff_Bisimulation_converse: \<open>Bisim r \<longleftrightarrow> Bisim (r\<inverse>)\<close>
  by (intro iffI BisimulationI; elim BisimulationE, simp)

lemma Simulation_Bisimulation: \<open>Bisim r \<Longrightarrow> Sim r\<close>
  by (elim BisimulationE, rule SimulationI; simp)


lemma Bisimulation_relcomp : \<open>Bisim r \<Longrightarrow> Bisim s \<Longrightarrow> Bisim (r O s)\<close>
  unfolding Bisimulation_def by (metis Simulation_relcomp converse_relcomp)


lemma (in AfterExt) Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P = \<T> Q \<and>
                      (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
  unfolding Bisimulation_def by (simp add: Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e) blast


corollary (in AfterExt) Bisimulation_imp_eq_T: \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
  using Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e by blast


lemma (in OpSemTransitions) Bisimulation_imp_ev_trans:
  \<open>Bisim r \<Longrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close>
  by (metis BisimulationD1 Simulation_Bisimulation Simulation_imp_ev_trans Un_iff)



subsection \<open>Bisimilar and Bisimilarity\<close>

definition Bisimilar :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50)
  where \<open>P \<sim> Q \<equiv> \<exists>r. Bisim r \<and> (P, Q) \<in> r\<close>

lemma BisimilarI : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P \<sim> Q\<close>
  by (auto simp add: Bisimilar_def)

lemma BisimilarE :
  assumes \<open>P \<sim> Q\<close>
  obtains r where \<open>Bisim r\<close> and \<open>(P, Q) \<in> r\<close>
  using assms unfolding Bisimilar_def by blast


abbreviation Bisimilarity :: \<open>'\<alpha> process rel\<close> (\<open>\<B>\<close>)
  where \<open>\<B> \<equiv> {(P, Q). P \<sim> Q}\<close>


lemma Bisimulation_Bisimilarity: \<open>Bisim \<B>\<close>
proof (rule BisimulationI)
  show \<open>(P, Q) \<in> \<B> \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close> for P Q
    by (simp, elim BisimilarE BisimulationE, blast)
next
  fix P Q e
  assume \<open>(P, Q) \<in> \<B>\<close> \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>(P, Q) \<in> \<B>\<close> BisimilarE obtain r where \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> by blast
  show \<open>(P after e, Q after e) \<in> \<B>\<close>
  proof (clarify, rule BisimilarI)
    from \<open>Bisim r\<close> show \<open>Bisim r\<close> .
  next
    from \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
    show \<open>(P after e, Q after e) \<in> r\<close> by (fact BisimulationD2)
  qed
qed


lemma Bisimilarity_contains_Bisimulation: \<open>Bisim r \<Longrightarrow> r \<subseteq> \<B>\<close>
  using BisimilarI by blast
  

lemma Bisimilarity_is_maximal: \<open>r = \<B> \<longleftrightarrow> Bisim r \<and> (\<forall>s. Bisim s \<longrightarrow> s \<subseteq> r)\<close>
  using Bisimulation_Bisimilarity Bisimilarity_contains_Bisimulation by blast


(* voir si on a envie plus tard de faire une locale pour restreindre les noeuds *)
lemma Bisimilarity_is_equivalence_relation: \<open>equiv UNIV \<B>\<close>
proof (rule equivI)
  show \<open>refl \<B>\<close>
    by (meson Bisimilarity_contains_Bisimulation
              Bisimulation_Id IdI reflI subset_eq)
next
  show \<open>sym \<B>\<close>
    by (metis Bisimilarity_contains_Bisimulation Bisimulation_Bisimilarity
              Bisimulation_iff_Bisimulation_converse Un_absorb2 sym_Un_converse)
next
  from BisimilarI Bisimulation_Bisimilarity Bisimulation_relcomp
  show \<open>trans \<B>\<close> by (intro transI) blast
qed


 *)




section \<open>Bisimulation\<close>

context OpSemTransitions
begin

subsection \<open>Simulation\<close>

paragraph \<open>Definition\<close>

definition Simulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Sim\<close>)
  where \<open>Sim r \<equiv> \<forall>P Q. (P, Q) \<in> r \<longrightarrow>
                 (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                 (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P')) \<and>
                 (\<forall>P' e. P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r))\<close>
  (* add [] \<in> \<D> P \<longrightarrow> [] \<in> \<D> Q ? *)

lemma SimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0;
    \<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P');
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow>
                (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)\<rbrakk> \<Longrightarrow> Sim r\<close> 
  by (simp add: Simulation_def Domain_iff)

lemma SimulationD1 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
  and SimulationD2 : \<open>Sim r \<Longrightarrow> P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
  and SimulationD3 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  by (simp_all add: Simulation_def subset_iff)
     (metis event.exhaust, blast)

lemma SimulationE: 
  assumes \<open>Sim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      and \<open>\<And>P Q e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
      and \<open>\<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  using SimulationD1 SimulationD2 SimulationD3 \<open>Sim r\<close> by fast


paragraph \<open>Examples of Simulations (especially with refinements)\<close>

lemma Simulation_Id: \<open>Sim Id\<close> (* \<open>Id_on\<close> if we go for the locale *)
  using \<tau>_trans_eq by (intro SimulationI) blast+

method show_Simulation_converse_le uses hyp1 hyps2_3 =
  rule SimulationI, simp_all add: AfterExt_def,
  use hyp1 in blast,
  use \<tau>_trans_eq in blast,
  meson \<tau>_trans_eq in_mono hyp1 hyps2_3

lemma Simulation_converse_leF: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_F hyps2_3 : mono_After_F trans_F)

lemma Simulation_converse_leT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_T hyps2_3 : mono_After_T trans_T)

lemma Simulation_converse_leFD: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F\<^sub>D P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_FD hyps2_3 : mono_After_FD trans_FD)

lemma Simulation_converse_leDT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>D\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_DT hyps2_3 : mono_After_DT trans_DT)


lemma \<open>Sim (UNIV \<times> {\<bottom>})\<close>
  by (rule SimulationI; simp add: initials_BOT AfterExt_BOT \<tau>_trans_eq)
     (rule bexI, rule \<tau>_trans_eq, simp add: Domain_iff)



paragraph \<open>Elaborated Properties\<close>

lemma Simulation_relcomp : \<open>Sim (r O s)\<close> if \<open>Sim r\<close> and \<open>Sim s\<close> and \<open>Range r \<subseteq> Domain s\<close>
proof (rule SimulationI)
  show \<open>(P, Q) \<in> r O s \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q
    by (elim relcompE) (metis Pair_inject SimulationD1 subsetD \<open>Sim r\<close> \<open>Sim s\<close>)
next
  fix P e
  assume \<open>P \<in> Domain (r O s)\<close> and \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>P \<in> Domain (r O s)\<close> obtain R where \<open>(P, R) \<in> r O s\<close> unfolding Domain_iff by blast
  then obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close> SimulationD2 obtain P'
    where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> by blast
  with \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close> SimulationD3 obtain Q'
    where \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close> by blast
  with \<open>Range r \<subseteq> Domain s\<close> have \<open>ev e \<in> Q\<^sup>0\<close> \<open>Q' \<in> Domain s\<close> by auto
  from  \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>Q' \<in> Domain s\<close> SimulationD3
  obtain R' where \<open>R \<leadsto>\<^bsub>e\<^esub> R'\<close> \<open>(Q', R') \<in> s\<close> by blast
  from \<open>(P', Q') \<in> r\<close> \<open>(Q', R') \<in> s\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> show \<open>\<exists>P'\<in>Domain (r O s). P \<leadsto>\<^bsub>e\<^esub> P'\<close> by blast
next
  show \<open>(P, R) \<in> r O s \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> P' \<in> Domain (r O s) \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> 
        \<exists>R'. R \<leadsto>\<^bsub>e\<^esub> R' \<and> (P', R') \<in> r O s\<close> for P R e P'
  proof (elim relcompE, clarify)
    fix Q Q''
    assume \<open>ev e \<in> P\<^sup>0\<close> \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> \<open>(P', Q'') \<in> r\<close> \<open>P afterExt ev e \<leadsto>\<^sub>\<tau> P'\<close>
    obtain Q' where \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close>
      by (meson DomainI SimulationD3 \<open>(P', Q'') \<in> r\<close> \<open>(P, Q) \<in> r\<close>
                \<open>P afterExt ev e \<leadsto>\<^sub>\<tau> P'\<close> \<open>Sim r\<close> \<open>ev e \<in> P\<^sup>0\<close>)
    from \<open>(P', Q') \<in> r\<close> \<open>Range r \<subseteq> Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
    from SimulationD3 \<open>(Q, R) \<in> s\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>Q' \<in> Domain s\<close> \<open>Sim s\<close>
    obtain R' where \<open>R \<leadsto>\<^bsub>e\<^esub> R'\<close> \<open>(Q', R') \<in> s\<close> by blast
    with \<open>(P', Q') \<in> r\<close> show \<open>\<exists>R'. R \<leadsto>\<^bsub>e\<^esub> R' \<and> (P', R') \<in> r O s\<close> by blast
  qed
qed


lemma \<tau>_trans_imp_leT_imp_Simulation_iff_trace_trans :
  \<open>Sim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow>
                    (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^sup>*s P')) \<and>
                    (\<forall>P' s. tF s \<longrightarrow> P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^sup>*s P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^sup>*s Q' \<and> (P', Q') \<in> r)))\<close>
 (*  if \<tau>_trans_imp_leT : \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close> *)
proof (intro iffI ballI allI impI conjI)
  from SimulationD1 show \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q by blast
next
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*s P'\<close> if \<open>Sim r\<close> for P Q s
  proof (induct s arbitrary: P Q rule: rev_induct)
    show \<open>(P, Q) \<in> r \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> \<exists>x\<in>Domain r. P \<leadsto>\<^sup>*[] x\<close> for P Q
      by (meson Domain.DomainI \<tau>_trans_eq trace_\<tau>_trans)
  next
    fix e s P Q
    assume   hyp : \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*s P'\<close> for P Q
    assume prems : \<open>(P, Q) \<in> r\<close> \<open>s @ [e] \<in> \<T> P\<close> \<open>tF (s @ [e])\<close>
    from prems(3) obtain x where \<open>e = ev x\<close> by (cases e; simp)
    from hyp is_processT3_ST prems tF_append
    obtain P' where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^sup>*s P'\<close> by blast
    have \<open>P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> P'\<close> using T_imp_trace_trans_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans
                                       \<open>P \<leadsto>\<^sup>*s P'\<close> is_processT3_ST prems(2) by blast
    moreover have \<open>ev x \<in> (P after\<^sub>\<T> s)\<^sup>0\<close>
      using \<open>e = ev x\<close> initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e prems(2) by blast
    ultimately have \<open>P after\<^sub>\<T> (s @ [ev x]) \<leadsto>\<^sub>\<tau> P' afterExt ev x\<close>
      apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc) 
      oops
      find_theorems \<tau>_trans name: mono

      using \<open>P \<leadsto>\<^sup>*s P'\<close> \<tau>_trans_imp_leT trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans_if_\<tau>_trans_imp_leT by blast
    from \<open>Sim r\<close> obtain P'' where \<open>\<close>
      thm SimulationD2

      find_theorems After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e trace_trans

    thm 

(*     find_theorems ev_trans \<T>
    have \<open>ev x \<in> P'\<^sup>0\<close>
      find_theorems trace_trans \<T>
      oops
      find_theorems \<open>\<close>
    obtain 

    thm SimulationD2[OF \<open>Sim r\<close> \<open>P' \<in> Domain r\<close> ]
    have \<open>\<close>
    oops
 

 *)
    show \<open>\<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*(s @ [e]) P'\<close>
      sledgehammer
    
     apply (meson Domain.DomainI \<tau>_trans_eq trace_\<tau>_trans)
    sledgehammer
    using SimulationD1 by blast
  fix P Q
  assume \<open>Sim r\<close>
  hence * : \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
            \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow>
             (P after e, Q after e) \<in> r\<close> for P Q e by (meson SimulationE)+
  have \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q \<and> (tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close> for s
  proof (induct s rule: rev_induct)
    case Nil
    thus ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    from append_T_imp_tF snoc.prems(2) have f1 : \<open>tF s\<close> by blast
    with snoc.hyps snoc.prems is_processT3_ST
    have f2 : \<open>s \<in> \<T> Q\<close> \<open>(P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r\<close> by blast+
    from f2(2) have f3 : \<open>(P after\<^sub>\<T> s)\<^sup>0 \<subseteq> (Q after\<^sub>\<T> s)\<^sup>0\<close> by (fact "*"(1))
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(2) have f4 : \<open>e \<in> (P after\<^sub>\<T> s)\<^sup>0\<close> by blast
    from f3 f4 have f5 : \<open>e \<in> (Q after\<^sub>\<T> s)\<^sup>0\<close> by auto
    show ?case
    proof (intro conjI impI)
      from f5 show \<open>s @ [e] \<in> \<T> Q\<close> by (simp add: initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq f1 f2(1))
    next
      assume \<open>tF (s @ [e])\<close>
      then obtain x where \<open>e = ev x\<close> by (cases e; simp)
      show \<open>(P after\<^sub>\<T> (s @ [e]), Q after\<^sub>\<T> (s @ [e])) \<in> r\<close> 
        by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc \<open>e = ev x\<close> AfterExt_def)
           (fact "*"(2)[OF f2(2) f3 f4[simplified \<open>e = ev x\<close>]])
    qed
  qed
  thus \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P \<subseteq> \<T> Q \<and> (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
    by (simp add: subset_iff)
next
  assume * : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
  show \<open>Sim r\<close> 
  proof (rule SimulationI)
    fix P Q
    from "*"[rule_format, of P Q] show \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      by (simp add: anti_mono_initials_T trace_refine_def)
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close>
    from \<open>ev e \<in> P\<^sup>0\<close> have \<open>[ev e] \<in> \<T> P\<close> by (simp add: initials_def)
    from "*"[rule_format, OF \<open>(P, Q) \<in> r\<close>, THEN conjunct2, rule_format, OF this]
    show \<open>(P after e, Q after e) \<in> r\<close> by (simp add: AfterExt_def)
  qed
qed
  oops





subsection \<open>Bisimulation\<close>

definition Bisimulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Bisim\<close>)
  where \<open>Bisim r \<equiv> Sim r \<and> Sim (r\<inverse>)\<close>


lemma BisimulationI : \<open>Sim r \<Longrightarrow> Sim (r\<inverse>) \<Longrightarrow> Bisim r\<close>
  by (simp add: Bisimulation_def)

lemma BisimulationD1 : \<open>Bisim r \<Longrightarrow> Sim r\<close>
  and BisimulationD2 : \<open>Bisim r \<Longrightarrow> Sim (r\<inverse>)\<close>
  by (simp_all add: Bisimulation_def)

lemma BisimulationE :
  assumes \<open>Bisim r\<close>
  obtains \<open>Sim r\<close> and \<open>Sim (r\<inverse>)\<close>
  using BisimulationD1 BisimulationD2 \<open>Bisim r\<close> by presburger


lemma Bisimulation_def_bis : 
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow>
               (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
               (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P'\<in>Domain r. P \<leadsto>\<^bsub>e\<^esub> P')) \<and>
               (\<forall>e. ev e \<in> Q\<^sup>0 \<longrightarrow> (\<exists>Q'\<in>Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q')) \<and>
               (\<forall>P' e. P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)) \<and>
               (\<forall>Q' e. Q' \<in> Range  r \<longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<longrightarrow> (\<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r)))\<close>
  unfolding Bisimulation_def Simulation_def by simp blast

lemma BisimulationI_bis :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0;
    \<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^bsub>e\<^esub> P';
    \<And>Q e. Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q'\<in>Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q';
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r;
    \<And>P Q e Q'. (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<rbrakk>
   \<Longrightarrow> Bisim r\<close>
  by (simp add: Bisimulation_def_bis) blast
 
lemma BisimulationD1_bis : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
  and BisimulationD2_bis : \<open>Bisim r \<Longrightarrow> P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
  and BisimulationD3_bis : \<open>Bisim r \<Longrightarrow> Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q' \<in> Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  and BisimulationD4_bis : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  and BisimulationD5_bis : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<close>
  unfolding Bisimulation_def
  by (use SimulationD1 in blast) (use SimulationD2 SimulationD3 in blast)+

lemma BisimulationE_bis : 
  assumes \<open>Bisim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
      and \<open>\<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
      and \<open>\<And>Q e. Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q' \<in> Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
      and \<open>\<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
      and \<open>\<And>P Q e Q'. (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<close>
  using BisimulationD1_bis BisimulationD2_bis BisimulationD3_bis 
        BisimulationD4_bis BisimulationD5_bis \<open>Bisim r\<close> by presburger



paragraph \<open>Examples of Bisimulations (especially with refinements)\<close>

lemma Bisimulation_Id: \<open>Bisim Id\<close>
  by (simp add: Bisimulation_def Simulation_Id)

(* method show_Simulation_converse_le uses hyp1 hyps2_3 =
  rule SimulationI, simp_all add: AfterExt_def,
  use hyp1 in blast,
  use \<tau>_trans_eq in blast,
  meson \<tau>_trans_eq in_mono hyp1 hyps2_3 *)



lemma  eqF_iff : \<open>\<F> P = \<F> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F Q \<and> Q \<sqsubseteq>\<^sub>F P\<close>
  and  eqT_iff : \<open>\<T> P = \<T> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>T Q \<and> Q \<sqsubseteq>\<^sub>T P\<close>
  and eqDT_iff : \<open>\<T> P = \<T> Q \<and> \<D> P = \<D> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<and> Q \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  unfolding trace_divergence_refine_def failure_refine_def
            trace_refine_def divergence_refine_def by auto

lemma Bisimulation_eqF: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Bisim {(P, Q). \<F> P = \<F> Q}\<close>
  unfolding Bisimulation_def 


  oops
  apply (rule BisimulationI, simp_all add: AfterExt_def)
      apply (metis anti_mono_initials_F failure_refine_def subset_iff)
  sledgehammer
  using \<tau>_trans_eq apply blast
  sledgehammer defer sledgehammer defer sledgehammer
  unfolding Bisimulation_def apply (intro conjI)
  sledgehammer
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_F hyps2_3 : mono_After_F trans_F)

lemma Bisimulation_eqT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_T hyps2_3 : mono_After_T trans_T)

lemma Bisimulation_eqFD: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F\<^sub>D P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_FD hyps2_3 : mono_After_FD trans_FD)

lemma Bisimulation_eqDT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>D\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_DT hyps2_3 : mono_After_DT trans_DT)




lemma Bisimulation_iff_Bisimulation_converse: \<open>Bisim r \<longleftrightarrow> Bisim (r\<inverse>)\<close>
  by (intro iffI BisimulationI; elim BisimulationE, simp)


lemma Bisimulation_relcomp : \<open>Bisim r \<Longrightarrow> Bisim s \<Longrightarrow> Range r = Domain s \<Longrightarrow> Bisim (r O s)\<close>
  by (simp add: Bisimulation_def Simulation_relcomp converse_relcomp)


(* 
lemma (in AfterExt) Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P = \<T> Q \<and>
                      (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
  unfolding Bisimulation_def by (simp add: Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e) blast

 *)


lemma \<open>(\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q) \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> {ev e # s| s. s \<in> \<T> P'} \<subseteq> \<T> P\<close>
  apply (auto simp add: AfterExt_def)
  by (meson T_trace_trans_reality_check ev_trans_is trace_trans_iff(3))



(* TODO: modifier la gestion de \<checkmark> dans la def de Simulation *)

find_theorems After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e trace_trans 


lemma 
  \<open>\<forall>i < n. P i \<in> Domain r \<Longrightarrow> \<forall>i < n. P i \<leadsto>\<^bsub>f i\<^esub> P (Suc i) \<Longrightarrow> [ev (f i). i \<leftarrow> [0..<n]] \<in> \<T> (P 0)\<close>
  if \<open>Sim r\<close>
proof (induct n)
  case 0
  then show ?case by (simp add: Nil_elem_T)
next
  case (Suc n)
  have \<open>[ev (f i). i \<leftarrow> [0..<n]] \<in> \<T> (P 0)\<close>
    using Suc.hyps Suc.prems(1, 2) less_Suc_eq by presburger
  have \<open>P n \<in> Domain r\<close> \<open>ev (f n) \<in> (P n)\<^sup>0\<close>
    apply (simp add: Suc.prems(1))
    by (simp add: Suc.prems(2))
    show ?case
      using SimulationD2[OF \<open>Sim r\<close> \<open>P n \<in> Domain r\<close> \<open>ev (f n) \<in> (P n)\<^sup>0\<close>]

      apply simp
      

      oops
    
    sorry
qed


lemma \<open>P \<leadsto>\<^sup>*s P' \<Longrightarrow> P \<in> Domain r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> s \<in> \<T> P\<close> if \<open>Sim r\<close>
proof (induct s arbitrary: P P')
  show \<open>\<And>P. [] \<in> \<T> P\<close> by (simp add: Nil_elem_T)
next
  fix e s P P'
  assume hyp : \<open>P \<leadsto>\<^sup>*s P' \<Longrightarrow> P \<in> Domain r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> s \<in> \<T> P\<close> for P P'
  assume prems : \<open>P \<leadsto>\<^sup>*e # s P'\<close> \<open>P \<in> Domain r\<close> \<open>P' \<in> Domain r\<close>
  show \<open>e # s \<in> \<T> P\<close>
  proof (cases e)
    assume \<open>e = \<checkmark>\<close>
    with trace_trans.simps prems(1) have \<open>s = []\<close> by blast
    with \<open>e = \<checkmark>\<close> prems(1) show  \<open>e # s \<in> \<T> P\<close>
      by (simp add: initials_def trace_trans_iff(2))
  next
    fix x
    assume \<open>e = ev x\<close>
    obtain Q where \<open>P \<leadsto>\<^bsub>x\<^esub> Q\<close> \<open>Q \<leadsto>\<^sup>*s P'\<close>
      using \<open>e = ev x\<close> prems(1) trace_trans_iff(3) by blast


    show \<open>e # s \<in> \<T> P\<close>
      sorry
  qed
qed
      
    oops
  case (trace_tick_trans P P')
  then show ?case unfolding initials_def by simp
next
  case (trace_Cons_ev_trans P e P' s P'')
  obtain P''' where \<open>P''' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>
    using trace_Cons_ev_trans.hyps(1) trace_Cons_ev_trans.prems(2) by blast
    
  term ?case
  have \<open>s \<in> \<T> P'''\<close> sledgehammer
  then show ?case sorry
qed
  case Nil
  then show ?case sorry
next
  case (snoc e s)
  have \<open>tF s\<close> sle 

  thm trace_trans_iff(4)

  oops
  show ?case 
  obtain P' where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^sup>*s P'\<close>
    using append_single_T_imp_tF is_processT3_ST snoc.hyps snoc.prems(1, 3) by blast
  from \<open>Sim r\<close> \<open>P' \<in> Domain r\<close> SimulationD2
  
  then show ?case sorry
qed


lemma \<open>s \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*s Q \<Longrightarrow> Q\<^sup>0 \<subseteq> (P after\<^sub>\<T> s)\<^sup>0\<close>
  by (simp add: T_imp_trace_trans_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans \<tau>_trans_anti_mono_initials)

lemma Simulation_imp_converse_leT : \<open>Q \<sqsubseteq>\<^sub>T P\<close> if \<open>Sim r\<close> and \<open>(P, Q) \<in> r\<close>
proof -
  from \<open>(P, Q) \<in> r\<close> have \<open>s \<in> \<T> P \<Longrightarrow> (\<exists>t \<in> \<T> Q. s \<le> t)\<close> for s
  proof (induct s arbitrary: Q rule: rev_induct)
    from Nil_elem_T show \<open>\<And>Q. (\<exists>t \<in> \<T> Q. [] \<le> t)\<close> by blast
  next
    case (snoc e s)
    from is_processT3_ST snoc.hyps snoc.prems
    obtain t where \<open>t \<in> \<T> Q\<close> \<open>s \<le> t\<close> by blast
    have \<open>e \<in> (P after\<^sub>\<T> s)\<^sup>0\<close> using initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(1) by auto
    
    then show ?case sorry
  qed
  thus \<open>Q \<sqsubseteq>\<^sub>T P\<close> unfolding trace_refine_def using is_processT3_ST_pref by blast
qed



lemma Simulation_imp_eqT: \<open>\<T> P = \<T> Q\<close> if \<open>Bisim r\<close> and \<open>(P, Q) \<in> r\<close>
proof -
  from Simulation_imp_converse_leT[OF \<open>Bisim r\<close>[THEN BisimulationD1] \<open>(P, Q) \<in> r\<close>]
  have \<open>Q \<sqsubseteq>\<^sub>T P\<close> .
  from Simulation_imp_converse_leT[OF \<open>Bisim r\<close>[THEN BisimulationD2]]
  have \<open>P \<sqsubseteq>\<^sub>T Q\<close> by (simp add: that(2))
  from \<open>P \<sqsubseteq>\<^sub>T Q\<close> \<open>Q \<sqsubseteq>\<^sub>T P\<close> show \<open>\<T> P = \<T> Q\<close>
    unfolding trace_refine_def by simp
qed




  oops
  (* preuve par contradiction ? *)

end end


lemma \<tau>_trans_imp_leT_imp_Bisimulation_imp_eqT: \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
  if \<tau>_trans_imp_leT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close> and \<open>Bisim r\<close>
proof (subst set_eq_iff, intro allI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<longleftrightarrow> s \<in> \<T> Q\<close> for s
  proof (induct s arbitrary: P Q)
    show \<open>(P, Q) \<in> r \<Longrightarrow> [] \<in> \<T> P \<longleftrightarrow> [] \<in> \<T> Q\<close> for P Q
      by (simp add: Nil_elem_T)
  next
    have * : \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> {ev e # s| s. s \<in> \<T> P'} \<subseteq> \<T> P\<close> for P e P'
      by (simp add: AfterExt_def subset_iff)
         (metis (no_types, lifting) T_After T_trace_trans_reality_check
                \<tau>_trans_imp_leT \<tau>_trans_trace_trans mem_Collect_eq)

    fix e s P Q
    assume hyp : \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<longleftrightarrow> s \<in> \<T> Q\<close> for P Q
    assume \<open>(P, Q) \<in> r\<close>
    from BisimulationD1[OF \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close>] have \<open>P\<^sup>0 = Q\<^sup>0\<close> .
    show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
    proof (cases \<open>e \<in> P\<^sup>0\<close>)
      from \<open>P\<^sup>0 = Q\<^sup>0\<close> Cons_in_T_imp_elem_initials
      show \<open>e \<notin> P\<^sup>0 \<Longrightarrow> e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close> by blast
    next
      assume \<open>e \<in> P\<^sup>0\<close>
      show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
      proof (cases e)
        assume \<open>e = \<checkmark>\<close>
        with \<open>P\<^sup>0 = Q\<^sup>0\<close> show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
          by (metis butlast.simps(2) ftF_butlast initials_def
                    is_processT2_TR mem_Collect_eq tF_Cons)
      next
        fix x
        assume \<open>e = ev x\<close>
        with \<open>e \<in> P\<^sup>0\<close> \<open>P\<^sup>0 = Q\<^sup>0\<close> have \<open>ev x \<in> P\<^sup>0\<close> \<open>ev x \<in> Q\<^sup>0\<close> by simp_all
  
        with \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> BisimulationD2 BisimulationD3
        obtain P' Q' where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>x\<^esub> P'\<close> \<open>Q' \<in> Range r\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q'\<close> by blast

        with \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> BisimulationD4 BisimulationD5
        obtain P'' Q'' where \<open>P \<leadsto>\<^bsub>x\<^esub> P''\<close> \<open>(P'', Q') \<in> r\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q''\<close> \<open>(P', Q'') \<in> r\<close> by blast

        from \<open>Bisim r\<close> \<open>(P'', Q') \<in> r\<close> \<open>(P', Q'') \<in> r\<close> hyp
        have \<open>s \<in> \<T> P'' \<longleftrightarrow> s \<in> \<T> Q'\<close> \<open>s \<in> \<T> P' \<longleftrightarrow> s \<in> \<T> Q''\<close> by simp_all

        from \<open>P \<leadsto>\<^bsub>x\<^esub> P'\<close> \<open>P \<leadsto>\<^bsub>x\<^esub> P''\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q'\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q''\<close> "*" 
        have $ : \<open>{ev x # s| s. s \<in> \<T> P' } \<subseteq> \<T> P\<close> \<open>{ev x # s| s. s \<in> \<T> Q' } \<subseteq> \<T> Q\<close>
                 \<open>{ev x # s| s. s \<in> \<T> P''} \<subseteq> \<T> P\<close> \<open>{ev x # s| s. s \<in> \<T> Q''} \<subseteq> \<T> Q\<close> by simp_all

        
      

        

        thus \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
          
          
      thm BisimulationD4 BisimulationD5


      thm BisimulationD2
proof (unfold trace_refine_def, rule subsetI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q\<close> for s
  proof (induct s arbitrary: P Q) (* induct length s ? *)
    case Nil
    then show ?case by (simp add: Nil_elem_T)
  next
    case (Cons e s)
    show ?case
    proof (cases e)
      assume \<open>e = \<checkmark>\<close>
      hence \<open>s = []\<close> by (metis Cons.prems(2) append_Cons tF_Cons
                               append_single_T_imp_tF list_nonMt_append)
      show \<open>e # s \<in> \<T> Q\<close>
        sledgehammer
      show \<open>e = \<checkmark> \<Longrightarrow> e # s \<in> \<T> Q\<close> sledgehammer
    from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> have \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> by (fact SimulationD1)
    from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> SimulationD2 obtain P' where \<open>Domain ?r. ?P \<leadsto>\<^bsub>?e\<^esub> P'\<close>
    thm SimulationD2
    thm SimulationD3
    thm SimulationD1
    thm SimulationE
    then show ?case sorry
  qed




lemma Bisimulation_imp_eqT: \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
proof (intro subset_antisym subsetI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q\<close> if \<open>Bisim r\<close> for r P Q s
  proof (induct s arbitrary: Q rule: rev_induct)
    case Nil
    then show ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    then show ?case sorry
  qed
    sorry
  with Bisimulation_iff_Bisimulation_converse
  show \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> s \<in> \<T> P\<close> for s by blast
qed
    using  by blast
  using Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e by blast


lemma (in OpSemTransitions) Bisimulation_imp_ev_trans:
  \<open>Bisim r \<Longrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close>
  by (metis BisimulationD1 Simulation_Bisimulation Simulation_imp_ev_trans Un_iff)



subsection \<open>Bisimilar and Bisimilarity\<close>

definition Bisimilar :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50)
  where \<open>P \<sim> Q \<equiv> \<exists>r. Bisim r \<and> (P, Q) \<in> r\<close>

lemma BisimilarI : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P \<sim> Q\<close>
  by (auto simp add: Bisimilar_def)

lemma BisimilarE :
  assumes \<open>P \<sim> Q\<close>
  obtains r where \<open>Bisim r\<close> and \<open>(P, Q) \<in> r\<close>
  using assms unfolding Bisimilar_def by blast


abbreviation Bisimilarity :: \<open>'\<alpha> process rel\<close> (\<open>\<B>\<close>)
  where \<open>\<B> \<equiv> {(P, Q). P \<sim> Q}\<close>


lemma Bisimulation_Bisimilarity: \<open>Bisim \<B>\<close>
proof (rule BisimulationI)
  show \<open>(P, Q) \<in> \<B> \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close> for P Q
    by (simp, elim BisimilarE BisimulationE, blast)
next
  fix P Q e
  assume \<open>(P, Q) \<in> \<B>\<close> \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>(P, Q) \<in> \<B>\<close> BisimilarE obtain r where \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> by blast
  show \<open>(P after e, Q after e) \<in> \<B>\<close>
  proof (clarify, rule BisimilarI)
    from \<open>Bisim r\<close> show \<open>Bisim r\<close> .
  next
    from \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
    show \<open>(P after e, Q after e) \<in> r\<close> by (fact BisimulationD2)
  qed
qed


lemma Bisimilarity_contains_Bisimulation: \<open>Bisim r \<Longrightarrow> r \<subseteq> \<B>\<close>
  using BisimilarI by blast
  

lemma Bisimilarity_is_maximal: \<open>r = \<B> \<longleftrightarrow> Bisim r \<and> (\<forall>s. Bisim s \<longrightarrow> s \<subseteq> r)\<close>
  using Bisimulation_Bisimilarity Bisimilarity_contains_Bisimulation by blast


(* voir si on a envie plus tard de faire une locale pour restreindre les noeuds *)
lemma Bisimilarity_is_equivalence_relation: \<open>equiv UNIV \<B>\<close>
proof (rule equivI)
  show \<open>refl \<B>\<close>
    by (meson Bisimilarity_contains_Bisimulation
              Bisimulation_Id IdI reflI subset_eq)
next
  show \<open>sym \<B>\<close>
    by (metis Bisimilarity_contains_Bisimulation Bisimulation_Bisimilarity
              Bisimulation_iff_Bisimulation_converse Un_absorb2 sym_Un_converse)
next
  from BisimilarI Bisimulation_Bisimilarity Bisimulation_relcomp
  show \<open>trans \<B>\<close> by (intro transI) blast
qed




end

subsection \<open>\<open>\<tau>\<close> transition equivalence\<close>

context OpSemTransitions
begin

inductive \<tau>_trans_clos :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<tau>\<^sup>+\<close> 50)
  where \<open>P \<leadsto>\<^sub>\<tau>\<^sup>+ P\<close>
  |     \<open>P \<leadsto>\<^sub>\<tau>\<^sup>+ Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> R \<Longrightarrow> P \<leadsto>\<^sub>\<tau>\<^sup>+ R\<close>


lemma \<open>transp (\<leadsto>\<^sub>\<tau>\<^sup>+)\<close>
  sledgehammer



find_theorems \<open>?P\<^sup>+\<close> trans

definition 



lemma \<open>(\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
          (\<forall>P' e. P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close> if \<open>Sim r\<close>

  oops






end



end





lemma \<open>Bisimulation bisim \<Longrightarrow> \<bottom> P \<in> bisim \<Longrightarrow> P = \<bottom>\<close>
  oops



lemma \<open>Bisimulation bisim \<Longrightarrow> bisim P Q \<longleftrightarrow> bisim Q P\<close>
  oops



(* section \<open>Bisimulation\<close>

context OpSemTransitions
begin

subsection \<open>Simulation\<close>

paragraph \<open>Definition\<close>

definition sim_on :: \<open>['\<alpha> process rel, '\<alpha> process set] \<Rightarrow> bool\<close>
  where \<open>sim_on r S \<equiv> \<forall>P Q. (P, Q) \<in> r \<longrightarrow>
                      (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P')) \<and>
                      (\<forall>P' e. P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r))\<close>
  (* add [] \<in> \<D> P \<longrightarrow> [] \<in> \<D> Q ? *)

lemma SimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0;
    \<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P');
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow>
                (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)\<rbrakk> \<Longrightarrow> Sim r\<close> 
  by (simp add: Simulation_def Domain_iff)

lemma SimulationD1 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
  and SimulationD2 : \<open>Sim r \<Longrightarrow> P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
  and SimulationD3 : \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  by (simp_all add: Simulation_def subset_iff)
     (metis event.exhaust, blast)

lemma SimulationE: 
  assumes \<open>Sim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      and \<open>\<And>P Q e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
      and \<open>\<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  using SimulationD1 SimulationD2 SimulationD3 \<open>Sim r\<close> by fast


paragraph \<open>Examples of Simulations (especially with refinements)\<close>

lemma Simulation_Id: \<open>Sim Id\<close> (* \<open>Id_on\<close> if we go for the locale *)
  using \<tau>_trans_eq by (intro SimulationI) blast+

method show_Simulation_converse_le uses hyp1 hyps2_3 =
  rule SimulationI, simp_all add: AfterExt_def,
  use hyp1 in blast,
  use \<tau>_trans_eq in blast,
  meson \<tau>_trans_eq in_mono hyp1 hyps2_3

lemma Simulation_converse_leF: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_F hyps2_3 : mono_After_F trans_F)

lemma Simulation_converse_leT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_T hyps2_3 : mono_After_T trans_T)

lemma Simulation_converse_leFD: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F\<^sub>D P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_FD hyps2_3 : mono_After_FD trans_FD)

lemma Simulation_converse_leDT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>D\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_DT hyps2_3 : mono_After_DT trans_DT)
 

paragraph \<open>Elaborated Properties\<close>

lemma Simulation_relcomp : \<open>Sim (r O s)\<close> if \<open>Sim r\<close> and \<open>Sim s\<close> and \<open>Range r \<subseteq> Domain s\<close>
proof (rule SimulationI)
  show \<open>(P, Q) \<in> r O s \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q
    by (elim relcompE) (metis Pair_inject SimulationD1 subsetD \<open>Sim r\<close> \<open>Sim s\<close>)
next
  fix P e
  assume \<open>P \<in> Domain (r O s)\<close> and \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>P \<in> Domain (r O s)\<close> obtain R where \<open>(P, R) \<in> r O s\<close> unfolding Domain_iff by blast
  then obtain Q where \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> by blast
  from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close> SimulationD2 obtain P'
    where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> by blast
  with \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close> SimulationD3 obtain Q'
    where \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close> by blast
  with \<open>Range r \<subseteq> Domain s\<close> have \<open>ev e \<in> Q\<^sup>0\<close> \<open>Q' \<in> Domain s\<close> by auto
  from  \<open>Sim s\<close> \<open>(Q, R) \<in> s\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>Q' \<in> Domain s\<close> SimulationD3
  obtain R' where \<open>R \<leadsto>\<^bsub>e\<^esub> R'\<close> \<open>(Q', R') \<in> s\<close> by blast
  from \<open>(P', Q') \<in> r\<close> \<open>(Q', R') \<in> s\<close> \<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> show \<open>\<exists>P'\<in>Domain (r O s). P \<leadsto>\<^bsub>e\<^esub> P'\<close> by blast
next
  show \<open>(P, R) \<in> r O s \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> P' \<in> Domain (r O s) \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> 
        \<exists>R'. R \<leadsto>\<^bsub>e\<^esub> R' \<and> (P', R') \<in> r O s\<close> for P R e P'
  proof (elim relcompE, clarify)
    fix Q Q''
    assume \<open>ev e \<in> P\<^sup>0\<close> \<open>(P, Q) \<in> r\<close> \<open>(Q, R) \<in> s\<close> \<open>(P', Q'') \<in> r\<close> \<open>P afterExt ev e \<leadsto>\<^sub>\<tau> P'\<close>
    obtain Q' where \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>(P', Q') \<in> r\<close>
      by (meson DomainI SimulationD3 \<open>(P', Q'') \<in> r\<close> \<open>(P, Q) \<in> r\<close>
                \<open>P afterExt ev e \<leadsto>\<^sub>\<tau> P'\<close> \<open>Sim r\<close> \<open>ev e \<in> P\<^sup>0\<close>)
    from \<open>(P', Q') \<in> r\<close> \<open>Range r \<subseteq> Domain s\<close> have \<open>Q' \<in> Domain s\<close> by blast
    from SimulationD3 \<open>(Q, R) \<in> s\<close> \<open>Q \<leadsto>\<^bsub>e\<^esub> Q'\<close> \<open>Q' \<in> Domain s\<close> \<open>Sim s\<close>
    obtain R' where \<open>R \<leadsto>\<^bsub>e\<^esub> R'\<close> \<open>(Q', R') \<in> s\<close> by blast
    with \<open>(P', Q') \<in> r\<close> show \<open>\<exists>R'. R \<leadsto>\<^bsub>e\<^esub> R' \<and> (P', R') \<in> r O s\<close> by blast
  qed
qed


lemma \<tau>_trans_imp_leT_imp_Simulation_iff_trace_trans :
  \<open>Sim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow>
                    (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (\<exists>P' \<in> Domain r. P \<leadsto>\<^sup>*s P')) \<and>
                    (\<forall>P' s. tF s \<longrightarrow> P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^sup>*s P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^sup>*s Q' \<and> (P', Q') \<in> r)))\<close>
 (*  if \<tau>_trans_imp_leT : \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close> *)
proof (intro iffI ballI allI impI conjI)
  from SimulationD1 show \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<Longrightarrow> \<checkmark> \<in> Q\<^sup>0\<close> for P Q by blast
next
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*s P'\<close> if \<open>Sim r\<close> for P Q s
  proof (induct s arbitrary: P Q rule: rev_induct)
    show \<open>(P, Q) \<in> r \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> \<exists>x\<in>Domain r. P \<leadsto>\<^sup>*[] x\<close> for P Q
      by (meson Domain.DomainI \<tau>_trans_eq trace_\<tau>_trans)
  next
    fix e s P Q
    assume   hyp : \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> tF s \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*s P'\<close> for P Q
    assume prems : \<open>(P, Q) \<in> r\<close> \<open>s @ [e] \<in> \<T> P\<close> \<open>tF (s @ [e])\<close>
    from prems(3) obtain x where \<open>e = ev x\<close> by (cases e; simp)
    from hyp is_processT3_ST prems tF_append
    obtain P' where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^sup>*s P'\<close> by blast
    have \<open>P after\<^sub>\<T> s \<leadsto>\<^sub>\<tau> P'\<close> using T_imp_trace_trans_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans
                                       \<open>P \<leadsto>\<^sup>*s P'\<close> is_processT3_ST prems(2) by blast
    moreover have \<open>ev x \<in> (P after\<^sub>\<T> s)\<^sup>0\<close>
      using \<open>e = ev x\<close> initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e prems(2) by blast
    ultimately have \<open>P after\<^sub>\<T> (s @ [ev x]) \<leadsto>\<^sub>\<tau> P' afterExt ev x\<close>
      apply (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc) 
      oops
      find_theorems \<tau>_trans name: mono

      using \<open>P \<leadsto>\<^sup>*s P'\<close> \<tau>_trans_imp_leT trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans_if_\<tau>_trans_imp_leT by blast
    from \<open>Sim r\<close> obtain P'' where \<open>\<close>
      thm SimulationD2

      find_theorems After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e trace_trans

    thm 

(*     find_theorems ev_trans \<T>
    have \<open>ev x \<in> P'\<^sup>0\<close>
      find_theorems trace_trans \<T>
      oops
      find_theorems \<open>\<close>
    obtain 

    thm SimulationD2[OF \<open>Sim r\<close> \<open>P' \<in> Domain r\<close> ]
    have \<open>\<close>
    oops
 

 *)
    show \<open>\<exists>P'\<in>Domain r. P \<leadsto>\<^sup>*(s @ [e]) P'\<close>
      sledgehammer
    
     apply (meson Domain.DomainI \<tau>_trans_eq trace_\<tau>_trans)
    sledgehammer
    using SimulationD1 by blast
  fix P Q
  assume \<open>Sim r\<close>
  hence * : \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
            \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0 \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow>
             (P after e, Q after e) \<in> r\<close> for P Q e by (meson SimulationE)+
  have \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q \<and> (tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close> for s
  proof (induct s rule: rev_induct)
    case Nil
    thus ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    from append_T_imp_tF snoc.prems(2) have f1 : \<open>tF s\<close> by blast
    with snoc.hyps snoc.prems is_processT3_ST
    have f2 : \<open>s \<in> \<T> Q\<close> \<open>(P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r\<close> by blast+
    from f2(2) have f3 : \<open>(P after\<^sub>\<T> s)\<^sup>0 \<subseteq> (Q after\<^sub>\<T> s)\<^sup>0\<close> by (fact "*"(1))
    from initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e snoc.prems(2) have f4 : \<open>e \<in> (P after\<^sub>\<T> s)\<^sup>0\<close> by blast
    from f3 f4 have f5 : \<open>e \<in> (Q after\<^sub>\<T> s)\<^sup>0\<close> by auto
    show ?case
    proof (intro conjI impI)
      from f5 show \<open>s @ [e] \<in> \<T> Q\<close> by (simp add: initials_def T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq f1 f2(1))
    next
      assume \<open>tF (s @ [e])\<close>
      then obtain x where \<open>e = ev x\<close> by (cases e; simp)
      show \<open>(P after\<^sub>\<T> (s @ [e]), Q after\<^sub>\<T> (s @ [e])) \<in> r\<close> 
        by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc \<open>e = ev x\<close> AfterExt_def)
           (fact "*"(2)[OF f2(2) f3 f4[simplified \<open>e = ev x\<close>]])
    qed
  qed
  thus \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P \<subseteq> \<T> Q \<and> (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
    by (simp add: subset_iff)
next
  assume * : \<open>\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P \<subseteq> \<T> Q \<and>
                    (\<forall>s\<in>\<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r)\<close>
  show \<open>Sim r\<close> 
  proof (rule SimulationI)
    fix P Q
    from "*"[rule_format, of P Q] show \<open>(P, Q) \<in> r \<Longrightarrow> P\<^sup>0 \<subseteq> Q\<^sup>0\<close>
      by (simp add: anti_mono_initials_T trace_refine_def)
  next
    fix P Q e
    assume \<open>(P, Q) \<in> r\<close> \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> \<open>ev e \<in> P\<^sup>0\<close>
    from \<open>ev e \<in> P\<^sup>0\<close> have \<open>[ev e] \<in> \<T> P\<close> by (simp add: initials_def)
    from "*"[rule_format, OF \<open>(P, Q) \<in> r\<close>, THEN conjunct2, rule_format, OF this]
    show \<open>(P after e, Q after e) \<in> r\<close> by (simp add: AfterExt_def)
  qed
qed
  oops





subsection \<open>Bisimulation\<close>

definition Bisimulation :: \<open>'\<alpha> process rel \<Rightarrow> bool\<close> (\<open>Bisim\<close>)
  where \<open>Bisim r \<equiv> Sim r \<and> Sim (r\<inverse>)\<close>

thm Simulation_def[of r]

lemma Bisimulation_def_bis : 
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow>
               (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
               (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> (\<exists>P'\<in>Domain r. P \<leadsto>\<^bsub>e\<^esub> P')) \<and>
               (\<forall>e. ev e \<in> Q\<^sup>0 \<longrightarrow> (\<exists>Q'\<in>Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q')) \<and>
               (\<forall>P' e. P' \<in> Domain r \<longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)) \<and>
               (\<forall>Q' e. Q' \<in> Range  r \<longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<longrightarrow> (\<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r)))\<close>
  unfolding Bisimulation_def Simulation_def by simp blast

lemma BisimulationI :
  \<open>\<lbrakk>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> \<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0;
    \<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P'\<in>Domain r. P \<leadsto>\<^bsub>e\<^esub> P';
    \<And>Q e. Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q'\<in>Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q';
    \<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r;
    \<And>P Q e Q'. (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<rbrakk>
   \<Longrightarrow> Bisim r\<close>
  by (simp add: Bisimulation_def_bis) blast
 
lemma BisimulationD1 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
  and BisimulationD2 : \<open>Bisim r \<Longrightarrow> P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
  and BisimulationD3 : \<open>Bisim r \<Longrightarrow> Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q' \<in> Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  and BisimulationD4 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
  and BisimulationD5 : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<close>
  unfolding Bisimulation_def
  by (use SimulationD1 in blast) (use SimulationD2 SimulationD3 in blast)+

lemma BisimulationE : 
  assumes \<open>Bisim r\<close>
  obtains \<open>\<And>P Q. (P, Q) \<in> r \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close>
      and \<open>\<And>P e. P \<in> Domain r \<Longrightarrow> ev e \<in> P\<^sup>0 \<Longrightarrow> \<exists>P' \<in> Domain r. P \<leadsto>\<^bsub>e\<^esub> P'\<close>
      and \<open>\<And>Q e. Q \<in> Range  r \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> \<exists>Q' \<in> Range  r. Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
      and \<open>\<And>P Q e P'. (P, Q) \<in> r \<Longrightarrow> P' \<in> Domain r \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> \<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r\<close>
      and \<open>\<And>P Q e Q'. (P, Q) \<in> r \<Longrightarrow> Q' \<in> Range  r \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> \<exists>P'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> (P', Q') \<in> r\<close>
  using BisimulationD1 BisimulationD2 BisimulationD3 
        BisimulationD4 BisimulationD5 \<open>Bisim r\<close> by presburger



paragraph \<open>Examples of Bisimulations (especially with refinements)\<close>

lemma Bisimulation_Id: \<open>Bisim Id\<close>
  by (simp add: Bisimulation_def Simulation_Id)

(* method show_Simulation_converse_le uses hyp1 hyps2_3 =
  rule SimulationI, simp_all add: AfterExt_def,
  use hyp1 in blast,
  use \<tau>_trans_eq in blast,
  meson \<tau>_trans_eq in_mono hyp1 hyps2_3 *)



lemma  eqF_iff : \<open>\<F> P = \<F> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>F Q \<and> Q \<sqsubseteq>\<^sub>F P\<close>
  and  eqT_iff : \<open>\<T> P = \<T> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>T Q \<and> Q \<sqsubseteq>\<^sub>T P\<close>
  and eqDT_iff : \<open>\<T> P = \<T> Q \<and> \<D> P = \<D> Q \<longleftrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<and> Q \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  unfolding trace_divergence_refine_def failure_refine_def
            trace_refine_def divergence_refine_def by auto

lemma Bisimulation_eqF: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Bisim {(P, Q). \<F> P = \<F> Q}\<close>
  unfolding Bisimulation_def 


  oops
  apply (rule BisimulationI, simp_all add: AfterExt_def)
      apply (metis anti_mono_initials_F failure_refine_def subset_iff)
  sledgehammer
  using \<tau>_trans_eq apply blast
  sledgehammer defer sledgehammer defer sledgehammer
  unfolding Bisimulation_def apply (intro conjI)
  sledgehammer
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_F hyps2_3 : mono_After_F trans_F)

lemma Bisimulation_eqT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_T hyps2_3 : mono_After_T trans_T)

lemma Bisimulation_eqFD: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>F\<^sub>D P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_FD hyps2_3 : mono_After_FD trans_FD)

lemma Bisimulation_eqDT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Sim {(P, Q). Q \<sqsubseteq>\<^sub>D\<^sub>T P}\<close>
  by (show_Simulation_converse_le hyp1 : anti_mono_initials_DT hyps2_3 : mono_After_DT trans_DT)




lemma Bisimulation_iff_Bisimulation_converse: \<open>Bisim r \<longleftrightarrow> Bisim (r\<inverse>)\<close>
  by (intro iffI BisimulationI; elim BisimulationE, simp)

lemma Simulation_Bisimulation: \<open>Bisim r \<Longrightarrow> Sim r\<close>
  by (elim BisimulationE, rule SimulationI; simp)

lemma Bisimulation_relcomp : \<open>Bisim r \<Longrightarrow> Bisim s \<Longrightarrow> Range r = Domain s \<Longrightarrow> Bisim (r O s)\<close>
  by (simp add: Bisimulation_def Simulation_relcomp converse_relcomp)


(* 
lemma (in AfterExt) Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>Bisim r \<longleftrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> \<T> P = \<T> Q \<and>
                      (\<forall>s \<in> \<T> P. tF s \<longrightarrow> (P after\<^sub>\<T> s, Q after\<^sub>\<T> s) \<in> r))\<close>
  unfolding Bisimulation_def by (simp add: Simulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e) blast

 *)


lemma \<open>(\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q) \<Longrightarrow> P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> {ev e # s| s. s \<in> \<T> P'} \<subseteq> \<T> P\<close>
  apply (auto simp add: AfterExt_def)
  by (meson T_trace_trans_reality_check ev_trans_is trace_trans_iff(3))


lemma \<open>Sim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q\<close>
  (* preuve par contradiction ? *)


lemma \<tau>_trans_imp_leT_imp_Bisimulation_imp_eqT: \<open>(P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
  if \<tau>_trans_imp_leT: \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close> and \<open>Bisim r\<close>
proof (subst set_eq_iff, intro allI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<longleftrightarrow> s \<in> \<T> Q\<close> for s
  proof (induct s arbitrary: P Q)
    show \<open>(P, Q) \<in> r \<Longrightarrow> [] \<in> \<T> P \<longleftrightarrow> [] \<in> \<T> Q\<close> for P Q
      by (simp add: Nil_elem_T)
  next
    have * : \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> {ev e # s| s. s \<in> \<T> P'} \<subseteq> \<T> P\<close> for P e P'
      by (simp add: AfterExt_def subset_iff)
         (metis (no_types, lifting) T_After T_trace_trans_reality_check
                \<tau>_trans_imp_leT \<tau>_trans_trace_trans mem_Collect_eq)

    fix e s P Q
    assume hyp : \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<longleftrightarrow> s \<in> \<T> Q\<close> for P Q
    assume \<open>(P, Q) \<in> r\<close>
    from BisimulationD1[OF \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close>] have \<open>P\<^sup>0 = Q\<^sup>0\<close> .
    show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
    proof (cases \<open>e \<in> P\<^sup>0\<close>)
      from \<open>P\<^sup>0 = Q\<^sup>0\<close> Cons_in_T_imp_elem_initials
      show \<open>e \<notin> P\<^sup>0 \<Longrightarrow> e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close> by blast
    next
      assume \<open>e \<in> P\<^sup>0\<close>
      show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
      proof (cases e)
        assume \<open>e = \<checkmark>\<close>
        with \<open>P\<^sup>0 = Q\<^sup>0\<close> show \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
          by (metis butlast.simps(2) ftF_butlast initials_def
                    is_processT2_TR mem_Collect_eq tF_Cons)
      next
        fix x
        assume \<open>e = ev x\<close>
        with \<open>e \<in> P\<^sup>0\<close> \<open>P\<^sup>0 = Q\<^sup>0\<close> have \<open>ev x \<in> P\<^sup>0\<close> \<open>ev x \<in> Q\<^sup>0\<close> by simp_all
  
        with \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> BisimulationD2 BisimulationD3
        obtain P' Q' where \<open>P' \<in> Domain r\<close> \<open>P \<leadsto>\<^bsub>x\<^esub> P'\<close> \<open>Q' \<in> Range r\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q'\<close> by blast

        with \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> BisimulationD4 BisimulationD5
        obtain P'' Q'' where \<open>P \<leadsto>\<^bsub>x\<^esub> P''\<close> \<open>(P'', Q') \<in> r\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q''\<close> \<open>(P', Q'') \<in> r\<close> by blast

        from \<open>Bisim r\<close> \<open>(P'', Q') \<in> r\<close> \<open>(P', Q'') \<in> r\<close> hyp
        have \<open>s \<in> \<T> P'' \<longleftrightarrow> s \<in> \<T> Q'\<close> \<open>s \<in> \<T> P' \<longleftrightarrow> s \<in> \<T> Q''\<close> by simp_all

        from \<open>P \<leadsto>\<^bsub>x\<^esub> P'\<close> \<open>P \<leadsto>\<^bsub>x\<^esub> P''\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q'\<close> \<open>Q \<leadsto>\<^bsub>x\<^esub> Q''\<close> "*" 
        have $ : \<open>{ev x # s| s. s \<in> \<T> P' } \<subseteq> \<T> P\<close> \<open>{ev x # s| s. s \<in> \<T> Q' } \<subseteq> \<T> Q\<close>
                 \<open>{ev x # s| s. s \<in> \<T> P''} \<subseteq> \<T> P\<close> \<open>{ev x # s| s. s \<in> \<T> Q''} \<subseteq> \<T> Q\<close> by simp_all

        
      

        

        thus \<open>e # s \<in> \<T> P \<longleftrightarrow> e # s \<in> \<T> Q\<close>
          sledgehammer
          
      thm BisimulationD4 BisimulationD5


      thm BisimulationD2
proof (unfold trace_refine_def, rule subsetI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q\<close> for s
  proof (induct s arbitrary: P Q) (* induct length s ? *)
    case Nil
    then show ?case by (simp add: Nil_elem_T)
  next
    case (Cons e s)
    show ?case
    proof (cases e)
      assume \<open>e = \<checkmark>\<close>
      hence \<open>s = []\<close> by (metis Cons.prems(2) append_Cons tF_Cons
                               append_single_T_imp_tF list_nonMt_append)
      show \<open>e # s \<in> \<T> Q\<close>
        sledgehammer
      show \<open>e = \<checkmark> \<Longrightarrow> e # s \<in> \<T> Q\<close> sledgehammer
    from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> have \<open>P\<^sup>0 \<subseteq> Q\<^sup>0\<close> by (fact SimulationD1)
    from \<open>Sim r\<close> \<open>(P, Q) \<in> r\<close> SimulationD2 obtain P' where \<open>Domain ?r. ?P \<leadsto>\<^bsub>?e\<^esub> P'\<close>
    thm SimulationD2
    thm SimulationD3
    thm SimulationD1
    thm SimulationE
    then show ?case sorry
  qed




lemma Bisimulation_imp_eqT: \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> \<T> P = \<T> Q\<close>
proof (intro subset_antisym subsetI)
  show \<open>(P, Q) \<in> r \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> s \<in> \<T> Q\<close> if \<open>Bisim r\<close> for r P Q s
  proof (induct s arbitrary: Q rule: rev_induct)
    case Nil
    then show ?case by (simp add: Nil_elem_T)
  next
    case (snoc e s)
    then show ?case sorry
  qed
    sorry
  with Bisimulation_iff_Bisimulation_converse
  show \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> s \<in> \<T> Q \<Longrightarrow> s \<in> \<T> P\<close> for s by blast
qed
    using  by blast
  using Bisimulation_iff_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e by blast


lemma (in OpSemTransitions) Bisimulation_imp_ev_trans:
  \<open>Bisim r \<Longrightarrow> (\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longleftrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
                      (\<forall>e. ev e \<in> P\<^sup>0 \<union> Q\<^sup>0 \<longrightarrow> (\<exists>P' Q'. P \<leadsto>\<^bsub>e\<^esub> P' \<and> Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close>
  by (metis BisimulationD1 Simulation_Bisimulation Simulation_imp_ev_trans Un_iff)



subsection \<open>Bisimilar and Bisimilarity\<close>

definition Bisimilar :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50)
  where \<open>P \<sim> Q \<equiv> \<exists>r. Bisim r \<and> (P, Q) \<in> r\<close>

lemma BisimilarI : \<open>Bisim r \<Longrightarrow> (P, Q) \<in> r \<Longrightarrow> P \<sim> Q\<close>
  by (auto simp add: Bisimilar_def)

lemma BisimilarE :
  assumes \<open>P \<sim> Q\<close>
  obtains r where \<open>Bisim r\<close> and \<open>(P, Q) \<in> r\<close>
  using assms unfolding Bisimilar_def by blast


abbreviation Bisimilarity :: \<open>'\<alpha> process rel\<close> (\<open>\<B>\<close>)
  where \<open>\<B> \<equiv> {(P, Q). P \<sim> Q}\<close>


lemma Bisimulation_Bisimilarity: \<open>Bisim \<B>\<close>
proof (rule BisimulationI)
  show \<open>(P, Q) \<in> \<B> \<Longrightarrow> P\<^sup>0 = Q\<^sup>0\<close> for P Q
    by (simp, elim BisimilarE BisimulationE, blast)
next
  fix P Q e
  assume \<open>(P, Q) \<in> \<B>\<close> \<open>ev e \<in> P\<^sup>0\<close>
  from \<open>(P, Q) \<in> \<B>\<close> BisimilarE obtain r where \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> by blast
  show \<open>(P after e, Q after e) \<in> \<B>\<close>
  proof (clarify, rule BisimilarI)
    from \<open>Bisim r\<close> show \<open>Bisim r\<close> .
  next
    from \<open>Bisim r\<close> \<open>(P, Q) \<in> r\<close> \<open>ev e \<in> P\<^sup>0\<close>
    show \<open>(P after e, Q after e) \<in> r\<close> by (fact BisimulationD2)
  qed
qed


lemma Bisimilarity_contains_Bisimulation: \<open>Bisim r \<Longrightarrow> r \<subseteq> \<B>\<close>
  using BisimilarI by blast
  

lemma Bisimilarity_is_maximal: \<open>r = \<B> \<longleftrightarrow> Bisim r \<and> (\<forall>s. Bisim s \<longrightarrow> s \<subseteq> r)\<close>
  using Bisimulation_Bisimilarity Bisimilarity_contains_Bisimulation by blast


(* voir si on a envie plus tard de faire une locale pour restreindre les noeuds *)
lemma Bisimilarity_is_equivalence_relation: \<open>equiv UNIV \<B>\<close>
proof (rule equivI)
  show \<open>refl \<B>\<close>
    by (meson Bisimilarity_contains_Bisimulation
              Bisimulation_Id IdI reflI subset_eq)
next
  show \<open>sym \<B>\<close>
    by (metis Bisimilarity_contains_Bisimulation Bisimulation_Bisimilarity
              Bisimulation_iff_Bisimulation_converse Un_absorb2 sym_Un_converse)
next
  from BisimilarI Bisimulation_Bisimilarity Bisimulation_relcomp
  show \<open>trans \<B>\<close> by (intro transI) blast
qed




end

subsection \<open>\<open>\<tau>\<close> transition equivalence\<close>

context OpSemTransitions
begin

inductive \<tau>_trans_clos :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<tau>\<^sup>+\<close> 50)
  where \<open>P \<leadsto>\<^sub>\<tau>\<^sup>+ P\<close>
  |     \<open>P \<leadsto>\<^sub>\<tau>\<^sup>+ Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> R \<Longrightarrow> P \<leadsto>\<^sub>\<tau>\<^sup>+ R\<close>


lemma \<open>transp (\<leadsto>\<^sub>\<tau>\<^sup>+)\<close>
  sledgehammer



find_theorems \<open>?P\<^sup>+\<close> trans

definition 



lemma \<open>(\<forall>P Q. (P, Q) \<in> r \<longrightarrow> (\<checkmark> \<in> P\<^sup>0 \<longrightarrow> \<checkmark> \<in> Q\<^sup>0) \<and>
          (\<forall>P' e. P \<leadsto>\<^bsub>e\<^esub> P' \<longrightarrow> (\<exists>Q'. Q \<leadsto>\<^bsub>e\<^esub> Q' \<and> (P', Q') \<in> r)))\<close> if \<open>Sim r\<close>

  oops





 *)
end



end





lemma \<open>Bisimulation bisim \<Longrightarrow> \<bottom> P \<in> bisim \<Longrightarrow> P = \<bottom>\<close>
  oops



lemma \<open>Bisimulation bisim \<Longrightarrow> bisim P Q \<longleftrightarrow> bisim Q P\<close>
  oops


















end








term \<open>refl_on\<close>

find_theorems name: clos

find_theorems \<open>_ :: ('\<alpha> set \<Rightarrow> '\<alpha> list set)\<close>


term \<open>relcompp\<close>


find_theorems name: \<tau>_trans name: event_trans

\<comment> \<open>Do we really want @{thm [show_question_marks = false]
                            OpSemLocale.OpSemTransitionsLocale.\<tau>_trans_event_trans
                            OpSemLocale.OpSemTransitionsLocale.event_trans_\<tau>_trans} ??? 

Probably yes because of the definition of event_trans, but not that clear... \<close>

section \<open>Definition of a labelled transition system\<close>

locale LTS =
  fixes S :: \<open>'\<beta> set\<close>                \<comment>\<open>set of states\<close>
    and A :: \<open>'\<alpha> set\<close>                \<comment>\<open>set of actions\<close>
    and trans_rel :: \<open>'\<alpha> \<Rightarrow> '\<beta> rel\<close> \<comment>\<open>transition relation\<close>
  (*   and s\<^sub>0 :: '\<beta>                     \<comment>\<open>initial state\<close> *)
   (*  and Relations :: \<open>['\<beta>, '\<alpha>, '\<beta>] \<Rightarrow> bool\<close>  \<comment>\<open>relations between nodes\<close> *)            
(* assumes s\<^sub>0_inside_S: \<open>s\<^sub>0 \<in> S\<close> *)
assumes trans_rel_Domain_subset_of_S: \<open>Domain (trans_rel a) \<subseteq> S\<close>
begin



abbreviation trans_rel_arrow_notation :: \<open>['\<beta>, '\<alpha>, '\<beta>] \<Rightarrow> bool\<close> (\<open>_/ \<midarrow> _ \<rightarrow>/ _\<close> [50, 3, 51] 50)
  where \<open>trans_rel_arrow_notation \<equiv> \<lambda>s\<^sub>0 a s\<^sub>1. (s\<^sub>0, s\<^sub>1) \<in> trans_rel a\<close>

term \<open>s \<midarrow> a \<rightarrow> t\<close>

abbreviation A_star  (\<open>A\<^sup>*\<close>) where \<open>A\<^sup>* \<equiv> lists A\<close>

inductive find_a_name :: \<open>['\<beta>, '\<alpha> list, '\<beta>] \<Rightarrow> bool\<close> (\<open>_/ \<midarrow>\<midarrow> _ \<longrightarrow>/ _\<close> [50, 3, 51] 50)
  where  Nil: \<open>s \<in> S \<Longrightarrow> s \<midarrow>\<midarrow> [] \<longrightarrow> s\<close>
  |     snoc: \<open>s \<midarrow>\<midarrow> \<sigma> \<longrightarrow> t \<Longrightarrow> t \<midarrow> a \<rightarrow> u \<Longrightarrow> s \<midarrow>\<midarrow> \<sigma> @ [a] \<longrightarrow> u\<close>

\<comment>\<open>useful ?\<close>
lemma find_a_name_imp_inside_S: \<open>s \<midarrow>\<midarrow> \<sigma> \<longrightarrow> t \<Longrightarrow> s \<in> S\<close>
  by (induct rule: find_a_name.induct; simp)
  


lemma find_a_name_explicit:
  \<open>s \<midarrow>\<midarrow> \<sigma> \<longrightarrow> t \<longleftrightarrow> 
   (\<forall>i < length \<sigma>. \<sigma> ! i \<in> A) \<and>
   (\<exists>f. f 0 = s \<and> f (length \<sigma>) = t \<and>
        (\<forall>i \<le> length \<sigma>. f i \<in> S) \<and>
        (\<forall>i < length \<sigma>. f i \<midarrow> \<sigma> ! i \<rightarrow> f (Suc i)))\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI)
  show \<open>?lhs \<Longrightarrow> ?rhs\<close>
  proof (induct rule: find_a_name.induct)
    case (Nil s)
    thus ?case by auto
  next
    case (snoc s \<sigma> t a u)

    oops
    from "snoc.hyps"(2) obtain f
      where * : \<open>f 0 = s\<close> \<open>f (length \<sigma>) = t\<close> 
                \<open>\<forall>i\<le>length \<sigma>. f i \<in> S\<close>
                \<open>(\<forall>i<length \<sigma>. f i \<midarrow> \<sigma> ! i \<rightarrow> f (Suc i))\<close> by blast
    show ?case
    proof (intro conjI)
      show \<open>\<forall>i<length (\<sigma> @ [a]). (\<sigma> @ [a]) ! i \<in> A\<close>
        by (simp add: nth_append "snoc.hyps"(2, 4))
    next
      define g where \<open>g i \<equiv> if i = Suc (length \<sigma>) then u else f i\<close> for i
      show \<open>\<exists>f. f 0 = s \<and> f (length (\<sigma> @ [a])) = u \<and>
                (\<forall>i\<le>length (\<sigma> @ [a]). f i \<in> S) \<and> 
                (\<forall>i<length (\<sigma> @ [a]). f i \<midarrow> (\<sigma> @ [a]) ! i \<rightarrow> f (Suc i))\<close>
      proof (intro exI)
        show \<open>g 0 = s \<and> g (length (\<sigma> @ [a])) = u \<and>
              (\<forall>i\<le>length (\<sigma> @ [a]). g i \<in> S) \<and>
              (\<forall>i<length (\<sigma> @ [a]). g i \<midarrow> (\<sigma> @ [a]) ! i \<rightarrow> g (Suc i))\<close>
          unfolding g_def apply (simp add: "snoc.hyps"(3, 5) "*" nth_append)
          using "*"(2) "snoc.hyps"(5) less_SucE by blast
      qed
    qed
  qed
next
  show \<open>?rhs \<Longrightarrow> ?lhs\<close>
    apply (elim conjE exE, induct \<sigma> arbitrary: s t rule: rev_induct; simp)
    by (simp add: find_a_name.intros(1))
       (metis find_a_name.intros(2) less_Suc_eq less_Suc_eq_le nth_append nth_append_length)
qed


\<comment>\<open>See if we want to add this in the inductive def \<close>
lemma find_a_name_Cons:
  \<open>s \<midarrow>\<midarrow> \<sigma> \<longrightarrow> t \<Longrightarrow> u \<in> S \<Longrightarrow> a \<in> A \<Longrightarrow> u \<midarrow> a \<rightarrow> s \<Longrightarrow> u \<midarrow>\<midarrow> a # \<sigma> \<longrightarrow> t\<close>
  apply (induct rule: find_a_name.induct)
  by (metis find_a_name.Nil self_append_conv2 snoc) 
     (metis append_Cons snoc)
  



end


definition is_strong_Bisimulation :: \<open>['\<beta>, '\<beta>] \<Rightarrow> bool\<close>
  where \<open>is_strong_Bisimulation R \<equiv>
         (\<forall>n\<^sub>1 \<in> Nodes. \<forall>n\<^sub>2 \<in> Nodes. \<forall>m\<^sub>1 \<in> Nodes.
          n\<^sub>1 R n\<^sub>2)\<close> (* voir la notation *)


end








datatype '\<alpha> label = event \<open>'\<alpha> event\<close> | \<tau>

locale CSP_LTS = LTS Nodes N\<^sub>0 Relations
  for Nodes :: \<open>'\<alpha> process set\<close>
  and N\<^sub>0 :: \<open>'\<alpha> process\<close>
  and Relations :: \<open>['\<alpha> process, '\<alpha> label, '\<alpha> process] \<Rightarrow> bool\<close>
                  (\<open>_/ \<midarrow>_\<rightarrow>/ _\<close> [50, 3, 51] 50)
begin

term \<open>N \<midarrow>a\<rightarrow> N'\<close>


end



                



