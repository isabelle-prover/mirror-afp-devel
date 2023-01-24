section \<open>Singletape Turing Machines\<close>

theory Singletape_TM
  imports
    TM_Common 
begin

text \<open>Turing machines can be either defined via a datatype or via a locale.
  We use TMs with left endmarker and dedicated accepting and rejecting state from
  which no further transitions are allowed. Deterministic TMs can be partial.\<close>

datatype ('q,'a)tm = TM 
  (Q_tm: "'q set")   (* Q - states *)
  "'a set"   (* Sigma - input alphabet *)
  (\<Gamma>_tm: "'a set")   (* Gamma - tape alphabet *)
  'a         (* blank *)
  'a         (* left endmarker *)
  "('q \<times> 'a \<times> 'q \<times> 'a \<times> dir) set" (* transitions \<delta> *)
  'q         (* start state *)
  'q         (* accept state *)
  'q         (* reject state *) 

datatype ('a, 'q) st_config = Config\<^sub>S
  "'q"         (* state *)
  "nat \<Rightarrow> 'a"  (* tape content *)
  "nat"        (* tape position *)

locale singletape_tm =
  fixes 
    Q :: "'q set" and
    \<Sigma> :: "'a set" and
    \<Gamma> :: "'a set" and
    blank :: 'a and
    LE :: 'a and
    \<delta> :: "('q \<times> 'a \<times> 'q \<times> 'a \<times> dir) set" and
    s :: 'q and
    t :: 'q and
    r :: 'q 
  assumes
    fin_Q: "finite Q" and
    fin_\<Gamma>: "finite \<Gamma>" and
    \<Sigma>_sub_\<Gamma>: "\<Sigma> \<subseteq> \<Gamma>" and
    sQ: "s \<in> Q" and
    tQ: "t \<in> Q" and
    rQ: "r \<in> Q" and
    blank: "blank \<in> \<Gamma>" "blank \<notin> \<Sigma>" and
    LE: "LE \<in> \<Gamma>" "LE \<notin> \<Sigma>" and
    tr: "t \<noteq> r" and
    \<delta>_set: "\<delta> \<subseteq> (Q - {t,r}) \<times> \<Gamma> \<times> Q \<times> \<Gamma> \<times> UNIV" and
    \<delta>LE: "(q, LE, q', a', d) \<in> \<delta> \<Longrightarrow> a' = LE \<and> d \<in> {dir.N,dir.R}"
begin

lemma \<delta>: assumes "(q,a,q',b,d) \<in> \<delta>" 
  shows "q \<in> Q" "a \<in> \<Gamma>" "q' \<in> Q" "b \<in> \<Gamma>" 
  using assms \<delta>_set by auto

lemma fin\<Sigma>: "finite \<Sigma>" 
  using fin_\<Gamma> \<Sigma>_sub_\<Gamma> by (metis finite_subset)

lemmas tm = sQ \<Sigma>_sub_\<Gamma> blank(1) LE(1)

fun valid_config :: "('a, 'q) st_config \<Rightarrow> bool" where
  "valid_config (Config\<^sub>S q w n) = (q \<in> Q \<and> range w \<subseteq> \<Gamma>)"

definition init_config :: "'a list  \<Rightarrow> ('a,'q)st_config" where
  "init_config w = (Config\<^sub>S s (\<lambda> n. if n = 0 then LE else if n \<le> length w then w ! (n-1) else blank) 0)" 

lemma valid_init_config: "set w \<subseteq> \<Sigma> \<Longrightarrow> valid_config (init_config w)" 
  unfolding init_config_def valid_config.simps using tm by (force simp: set_conv_nth)

inductive_set step :: "('a, 'q) st_config rel" where
  step: "(q, ts n, q', a, dir) \<in> \<delta> \<Longrightarrow>
  (Config\<^sub>S q ts n, Config\<^sub>S q' (ts(n := a)) (go_dir dir n)) \<in> step"

lemma stepI: "(q, a, q', b, dir) \<in> \<delta> \<Longrightarrow> ts n = a \<Longrightarrow> ts' = ts(n := b) \<Longrightarrow> n' = go_dir dir n \<Longrightarrow> q1 = q \<Longrightarrow> q2 = q'
  \<Longrightarrow> (Config\<^sub>S q1 ts n, Config\<^sub>S q2 ts' n') \<in> step" 
  using step[of q ts n q' b dir] by auto

lemma valid_step: assumes step: "(\<alpha>,\<beta>) \<in> step" 
  and val: "valid_config \<alpha>"  
shows "valid_config \<beta>"
  using step
proof (cases rule: step.cases)
  case (step q ts n q' a dir)
  from \<delta>[OF step(3)] val
  show ?thesis unfolding step(1-2) by auto
qed

definition Lang :: "'a list set" where
  "Lang = {w . set w \<subseteq> \<Sigma> \<and> (\<exists> w' n. (init_config w, Config\<^sub>S t w' n) \<in> step^*)}"

definition deterministic where 
  "deterministic = (\<forall> q a p1 b1 d1 p2 b2 d2. (q,a,p1,b1,d1) \<in> \<delta> \<longrightarrow> (q,a,p2,b2,d2) \<in> \<delta> \<longrightarrow> (p1,b1,d1) = (p2,b2,d2))" 

definition upper_time_bound :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "upper_time_bound f = (\<forall> w c n. set w \<subseteq> \<Sigma> \<longrightarrow> (init_config w, c) \<in> step^^n \<longrightarrow> n \<le> f (length w))" 
end

fun valid_tm :: "('q,'a)tm \<Rightarrow> bool" where 
  "valid_tm (TM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = singletape_tm Q \<Sigma> \<Gamma> bl le \<delta> s t r" 

fun Lang_tm :: "('q,'a)tm \<Rightarrow> 'a list set" where
  "Lang_tm (TM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = singletape_tm.Lang \<Sigma> bl le \<delta> s t" 

fun det_tm :: "('q,'a)tm \<Rightarrow> bool" where
  "det_tm (TM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = singletape_tm.deterministic \<delta>" 

fun upperb_time_tm :: "('q,'a)tm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "upperb_time_tm (TM Q \<Sigma> \<Gamma> bl le \<delta> s t r) f = singletape_tm.upper_time_bound \<Sigma> bl le \<delta> s f" 

context singletape_tm
begin

text \<open>A deterministic step (in a potentially non-determistic TM) is a step without alternatives.
  This will be useful in the translation of multitape TMs. The simulation is mostly deterministic, and
  only at very specific points it is non-determistic, namely at the points where the multitape-TM transition
  is chosen.\<close>

inductive_set dstep :: "('a, 'q) st_config rel" where
  dstep: "(q, ts n, q', a, dir) \<in> \<delta> \<Longrightarrow>
    (\<And> q1' a1 dir1. (q, ts n, q1', a1, dir1) \<in> \<delta> \<Longrightarrow> (q1',a1,dir1) = (q',a,dir)) \<Longrightarrow>
  (Config\<^sub>S q ts n, Config\<^sub>S q' (ts(n := a)) (go_dir dir n)) \<in> dstep"

lemma dstepI: "(q, a, q', b, dir) \<in> \<delta> \<Longrightarrow> ts n = a \<Longrightarrow> ts' = ts(n := b) \<Longrightarrow> n' = go_dir dir n \<Longrightarrow> q1 = q \<Longrightarrow> q2 = q'
  \<Longrightarrow> (\<And> q'' b' dir'. (q, a, q'', b', dir') \<in> \<delta> \<Longrightarrow> (q'', b', dir') = (q',b,dir))
  \<Longrightarrow> (Config\<^sub>S q1 ts n, Config\<^sub>S q2 ts' n') \<in> dstep" 
  using dstep[of q ts n q' b dir] by blast

lemma dstep_step: "dstep \<subseteq> step" 
proof 
  fix st
  assume dstep: "st \<in> dstep" 
  obtain s t where st: "st = (s,t)" by force
  have "(s,t) \<in> step" using dstep[unfolded st]
  proof (cases rule: dstep.cases)
    case 1: (dstep q ts n q' a dir)
    show ?thesis unfolding 1(1-2) by (rule stepI[OF 1(3)], auto)
  qed
  thus "st \<in> step" using st by auto
qed

lemma dstep_inj: assumes "(x,y) \<in> dstep" 
  and "(x,z) \<in> step" 
shows "z = y" 
  using assms(2)
proof (cases)
  case 1: (step q ts n p a d)
  show ?thesis using assms(1) unfolding 1(1)
  proof cases
    case 2: (dstep p' a' d')
    from 2(3)[OF 1(3)] have id: "p' = p" "a' = a" "d' = d" by auto
    show ?thesis unfolding 1 2 id ..
  qed
qed

lemma dsteps_inj: assumes "(x,y) \<in> dstep^^n" 
  and "(x,z) \<in> step^^m" 
  and "\<not> (\<exists> u. (z,u) \<in> step)" 
shows "\<exists> k. m = n + k \<and> (y,z) \<in> step^^k" 
  using assms(1-2)
proof (induct n arbitrary: m x)
  case (Suc n m x)
  from Suc(2) obtain x' where step: "(x,x') \<in> dstep" and steps: "(x',y) \<in> dstep^^n" by (metis relpow_Suc_E2)
  from step dstep_step have "(x,x') \<in> step" by auto
  with assms(3) have "x \<noteq> z" by auto
  with Suc(3) obtain mm where m: "m = Suc mm" by (cases m, auto)
  from Suc(3)[unfolded this] obtain x'' where step': "(x,x'') \<in> step" and steps': "(x'',z) \<in> step^^mm" by (metis relpow_Suc_E2)
  from dstep_inj[OF step step'] have x'': "x'' = x'" by auto
  from Suc(1)[OF steps steps'[unfolded x'']] obtain k where mm: "mm = n + k" and steps: "(y, z) \<in> step ^^ k" by auto
  thus ?case unfolding m mm by auto
qed auto

lemma dsteps_inj': assumes "(x,y) \<in> dstep^^n" 
  and "(x,z) \<in> step^^m" 
  and "m \<ge> n" 
shows "\<exists> k. m = n + k \<and> (y,z) \<in> step^^k" 
  using assms(1-3)
proof (induct n arbitrary: m x)
  case (Suc n m x)
  from Suc(2) obtain x' where step: "(x,x') \<in> dstep" and steps: "(x',y) \<in> dstep^^n" by (metis relpow_Suc_E2)
  from step dstep_step have "(x,x') \<in> step" by auto
  with Suc obtain mm where m: "m = Suc mm" by (cases m, auto)
  from Suc(3)[unfolded this] obtain x'' where step': "(x,x'') \<in> step" and steps': "(x'',z) \<in> step^^mm" by (metis relpow_Suc_E2)
  from dstep_inj[OF step step'] have x'': "x'' = x'" by auto
  from Suc(1)[OF steps steps'[unfolded x'']] m Suc obtain k where mm: "mm = n + k" and steps: "(y, z) \<in> step ^^ k" by auto
  thus ?case unfolding m mm by auto
qed auto
end
end
