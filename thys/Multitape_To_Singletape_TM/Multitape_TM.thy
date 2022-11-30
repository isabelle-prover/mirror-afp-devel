section \<open>Multitape Turing Machines\<close>

theory Multitape_TM
  imports
    TM_Common 
begin

text \<open>Turing machines can be either defined via a datatype or via a locale.
  We use TMs with left endmarker and dedicated accepting and rejecting state from
  which no further transitions are allowed. Deterministic TMs can be partial.

  Having multiple tapes, tape positions, directions, etc. is modelled via functions 
  of type @{typ "'k \<Rightarrow> 'whatever"} for some finite index type @{typ "'k :: finite"}.

  The input will always be provided on the first tape, indexed by @{term "0 :: 'k :: zero"}.\<close>

datatype ('q,'a,'k)mttm = MTTM 
  (Q_tm: "'q set")   (* Q - states *)
  "'a set"   (* Sigma - input alphabet *)
  (\<Gamma>_tm: "'a set")   (* Gamma - tape alphabet *)
  'a         (* blank *)
  'a         (* left endmarker *)
  "('q \<times> ('k \<Rightarrow> 'a) \<times> 'q \<times> ('k \<Rightarrow> 'a) \<times> ('k \<Rightarrow> dir)) set" (* transitions \<delta> *)
  'q         (* start state *)
  'q         (* accept state *)
  'q         (* reject state *) 

datatype ('a,'q,'k) mt_config = Config\<^sub>M
  (mt_state: 'q)                  (* state *)
  "'k \<Rightarrow> nat \<Rightarrow> 'a"        (* k tape contents *)
  (mt_pos: "'k \<Rightarrow> nat")    (* k tape positions *)

locale multitape_tm =
  fixes 
    Q :: "'q set" and
    \<Sigma> :: "'a set" and
    \<Gamma> :: "'a set" and
    blank :: 'a and
    LE :: 'a and
    \<delta> :: "('q \<times> ('k \<Rightarrow> 'a) \<times> 'q \<times> ('k \<Rightarrow> 'a) \<times> ('k :: {finite,zero} \<Rightarrow> dir)) set" and
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
    \<delta>_set: "\<delta> \<subseteq> (Q - {t,r}) \<times> (UNIV \<rightarrow> \<Gamma>) \<times> Q \<times> (UNIV \<rightarrow> \<Gamma>) \<times> (UNIV \<rightarrow> UNIV)" and
    \<delta>LE: "(q, a, q', a', d) \<in> \<delta> \<Longrightarrow> a k = LE \<Longrightarrow> a' k = LE \<and> d k \<in> {dir.N,dir.R}"
begin

lemma \<delta>: assumes "(q,a,q',b,d) \<in> \<delta>" 
  shows "q \<in> Q" "a k \<in> \<Gamma>" "q' \<in> Q" "b k \<in> \<Gamma>" 
  using assms \<delta>_set by auto

lemma fin_\<Sigma>: "finite \<Sigma>" 
  using fin_\<Gamma> \<Sigma>_sub_\<Gamma> by (metis finite_subset)

lemma fin_\<delta>: "finite \<delta>" 
  by (intro finite_subset[OF \<delta>_set] finite_cartesian_product fin_funcsetI, insert fin_Q fin_\<Gamma>, auto)

lemmas tm = sQ \<Sigma>_sub_\<Gamma> blank(1) LE(1)

fun valid_config :: "('a, 'q, 'k) mt_config \<Rightarrow> bool" where
  "valid_config (Config\<^sub>M q w n) = (q \<in> Q \<and> (\<forall> k. range (w k) \<subseteq> \<Gamma>) \<and> (\<forall> k. w k 0 = LE))"

definition init_config :: "'a list  \<Rightarrow> ('a,'q,'k)mt_config" where
  "init_config w = (Config\<^sub>M s (\<lambda> k n. if n = 0 then LE else if k = 0 \<and> n \<le> length w then w ! (n-1) else blank) (\<lambda> _. 0))" 

lemma valid_init_config: "set w \<subseteq> \<Sigma> \<Longrightarrow> valid_config (init_config w)" 
  unfolding init_config_def valid_config.simps using tm by (force simp: set_conv_nth)

inductive_set step :: "('a, 'q, 'k) mt_config rel" where
  step: "(q, (\<lambda> k. ts k (n k)), q', a, dir) \<in> \<delta> \<Longrightarrow>
  (Config\<^sub>M q ts n, Config\<^sub>M q' (\<lambda> k. (ts k)(n k := a k)) (\<lambda> k. go_dir (dir k) (n k))) \<in> step"

lemma valid_step: assumes step: "(\<alpha>,\<beta>) \<in> step" 
  and val: "valid_config \<alpha>"  
shows "valid_config \<beta>"
  using step
proof (cases rule: step.cases)
  case (step q ts n q' a dir)
  from \<delta>[OF step(3)] val \<delta>LE step(3)
  show ?thesis unfolding step(1-2) by fastforce
qed

definition Lang :: "'a list set" where
  "Lang = {w . set w \<subseteq> \<Sigma> \<and> (\<exists> w' n. (init_config w, Config\<^sub>M t w' n) \<in> step^*)}"

definition deterministic where 
  "deterministic = (\<forall> q a p1 b1 d1 p2 b2 d2. (q,a,p1,b1,d1) \<in> \<delta> \<longrightarrow> (q,a,p2,b2,d2) \<in> \<delta> \<longrightarrow> (p1,b1,d1) = (p2,b2,d2))" 

definition upper_time_bound :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "upper_time_bound f = (\<forall> w c n. set w \<subseteq> \<Sigma> \<longrightarrow> (init_config w, c) \<in> step^^n \<longrightarrow> n \<le> f (length w))" 
end


fun valid_mttm :: "('q,'a,'k :: {finite,zero})mttm \<Rightarrow> bool" where 
  "valid_mttm (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = multitape_tm Q \<Sigma> \<Gamma> bl le \<delta> s t r" 

fun Lang_mttm :: "('q,'a,'k :: {finite,zero})mttm \<Rightarrow> 'a list set" where
  "Lang_mttm (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = multitape_tm.Lang \<Sigma> bl le \<delta> s t" 

fun det_mttm :: "('q,'a,'k :: {finite,zero})mttm \<Rightarrow> bool" where
  "det_mttm (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r) = multitape_tm.deterministic \<delta>" 

fun upperb_time_mttm :: "('q,'a,'k :: {finite, zero})mttm \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "upperb_time_mttm (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r) f = multitape_tm.upper_time_bound \<Sigma> bl le \<delta> s f" 


end
