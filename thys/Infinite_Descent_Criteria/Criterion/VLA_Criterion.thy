(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

section "Equivalent Criteria for Infinite Descent"

text "This subsection concerns two families of alternative criteria that are logically equivalent to
Infinite Descent, and are used as the basis for decision procedures. While these criteria are
already well-established, we provide the first mechanization within the
sloped graph locale, and formal proofs of their soundness and completeness relative to the
locale-level InfiniteDescent predicate."

subsection "Automata-based criteria"

text \<open>The first family of criteria reduces Infinite Descent to a language inclusion problem by interpreting (descending) ipaths as words in an \(\omega\)-regular language~\cite{LeeJB01,Brotherston:PhD,Simpson17Fossacs,InfiniteDescent}.
We formalize two approaches for constructing this interpretation, which (following the terminology of~\cite{InfiniteDescent})
we refer to as the `vertex-language' and `slope-language' criteria, respectively.\<close>


subsubsection "Vertex-language Criterion"
theory VLA_Criterion
  imports "../Sloped_Graphs"
          "../Buchi_Preliminaries"
begin


context Sloped_Graph 
begin
(*Representing the transitions for the NBA:*)
(**1: In the initial state and can self loop, i.e. \<Delta>_trans(q\<^sub>0, v) = {q\<^sub>0} - v can idle **)
(*is a self loop necessary? 
  No, infact it causes the equality to be false... 
      a valid run "NBA.run Paut\<^sub>V (x ||| r) q\<^sub>0" 
      doesn't necessarily imply "alw (holds2 edge) x", unless we are guaranteed to transition out of q\<^sub>0 immediately*)

(**2: Transition into the the graph from q\<^sub>0 (the path auto has states as vertices, thus the graph is represented 1 for 1, with the addition of q0)**)
(**3: Transition within the graph, using edges (note since q\<^sub>0 is outside the set of Nodes, we cannot retransition back to q\<^sub>0)**)

(*Imagine the state transition to look like the graph, where the edges from a state are labelled with the vertex it is visiting*)
(*NB: the parameters of this function are inverted for the nba datatype*)
abbreviation q\<^sub>0 where "q\<^sub>0 \<equiv> None"
(*PATH AUTOMATON*)
fun \<Delta>_trans :: "'node \<Rightarrow> 'node option \<Rightarrow> 'node option set" where
  "\<Delta>_trans tr (Some s) = (if edge s tr \<and> {s, tr} \<subseteq> Node then {Some tr} else {})"|
  "\<Delta>_trans tr q\<^sub>0 = (if tr \<in> Node then {Some tr} else {})"

lemma \<Delta>_trans_q\<^sub>0:"l \<in> Node \<Longrightarrow> Some l \<in> \<Delta>_trans l q\<^sub>0" by auto

lemma \<Delta>_trans_edge:"edge s tr \<Longrightarrow> {s, tr} \<subseteq> Node \<Longrightarrow> (Some tr) \<in> \<Delta>_trans tr (Some s)" by auto

lemma \<Delta>_trans_elim:
  assumes "r \<in> \<Delta>_trans x q"
  obtains (EdgeCase) "\<exists>q'. q = Some q' \<and> edge q' x \<and> {q', x} \<subseteq> Node \<and> r = (Some x)"
        | (InitCase) "q = q\<^sub>0" "x \<in> Node" "r = (Some x)"
proof -
  have "r \<in> \<Delta>_trans x q" using assms by assumption
  then consider 
    (EdgeCase) "\<exists>q'. q = Some q' \<and> edge q' x \<and> {q', x} \<subseteq> Node \<and> r = (Some x)" |
    (InitCase) "q = q\<^sub>0 \<and> x \<in> Node \<and> r = (Some x)"
     by(cases q, auto split: if_splits)
  then show thesis using that by (cases, auto)
qed

(*Sanity check with the \<Delta>_trans in the paper, 
  the sets of transitions as before*)
lemma "\<Delta>_trans l s = 
       {s'. s = q\<^sub>0 \<and> s' = (Some l) \<and> l \<in> Node} \<union>
       {s' . \<exists>q'. s = Some q' \<and> s' = (Some l) \<and> edge q' l \<and> {q', l} \<subseteq> Node}"
  by(cases s, auto)

definition Paut\<^sub>V :: "('node, 'node option) nba" where
  "Paut\<^sub>V = nba 
    Node
    {q\<^sub>0}
    \<Delta>_trans
    (\<lambda>s. the s \<in> Node)"

lemmas Paut\<^sub>V_defs = Paut\<^sub>V_def \<Delta>_trans.simps
lemma Paut\<^sub>V_alpha[simp]:"nba.alphabet Paut\<^sub>V = Node" unfolding Paut\<^sub>V_def by auto
lemma Paut\<^sub>V_accept[simp]:"nba.accepting Paut\<^sub>V = (\<lambda>s. the s \<in> Node)" unfolding Paut\<^sub>V_def by auto
lemma Paut\<^sub>V_init[simp]: "nba.initial Paut\<^sub>V = {q\<^sub>0}" unfolding Paut\<^sub>V_def by auto
lemma Paut\<^sub>V_initp[intro]:"p \<in> nba.initial Paut\<^sub>V \<longleftrightarrow> p = q\<^sub>0" by auto
lemma Paut\<^sub>V_trans[simp]:"nba.transition Paut\<^sub>V a b = \<Delta>_trans a b" unfolding Paut\<^sub>V_def by auto

lemmas Paut\<^sub>V_trans' = Paut\<^sub>V_trans \<Delta>_trans.simps


(*The language of the path automaton represents all ipaths*)
lemma Paut\<^sub>V_lang:"NBA.language Paut\<^sub>V = {nd. ipath nd}" 
proof(safe)
  fix x 
  show "x \<in> NBA.language Paut\<^sub>V \<Longrightarrow> local.ipath x"
  proof(erule nba.language_elim, unfold ipath_def Paut\<^sub>V_initp Paut\<^sub>V_accept, safe)
    fix r p i
    assume run:"NBA.run Paut\<^sub>V (x ||| r) q\<^sub>0" and accept:"infs (\<lambda>s. the s \<in> Node) r"

    have "sset x \<subseteq> Node" using streams_sset[OF nba.run_alphabet[OF run]] by auto

    thus "alw (holdsS Node) x" by (simp add: alw_holdsS_iff_snth subsetD)

    show "alw (holds2 edge) x" 
    proof (coinduct rule:alw_coinduct[of "\<lambda>x. \<exists>r q. NBA.run Paut\<^sub>V (x ||| r) q"],safe)   
      fix x'::"'node stream"
      fix r'::"'node option stream"
      fix q 


      show "\<exists>r q. NBA.run Paut\<^sub>V (x ||| r) q" using run streams_sset[OF nba.run_alphabet[OF run]] by auto
      
      show "NBA.run Paut\<^sub>V (x' ||| r') q \<Longrightarrow> holds2 edge x'" 
        apply(unfold szip_unfold[of x' r'], erule NBA.nba.run_scons_elim[of Paut\<^sub>V], safe) 
        apply(unfold Paut\<^sub>V_alpha Paut\<^sub>V_trans szip_unfold[of "stl x'"]) 
        apply(erule NBA.nba.run_scons_elim[of Paut\<^sub>V])
        by(cases q, auto split: if_splits)

      {assume "\<not> alw (holds2 edge) (stl x')" "NBA.run Paut\<^sub>V (x' ||| r') q"
       then show"\<exists>r q. NBA.run Paut\<^sub>V (stl x' ||| r) q"
       by(cases "(x' ||| r')", auto simp: stl_sset subset_iff split: if_splits)}
   
    qed
  qed
  show "ipath x \<Longrightarrow> x \<in> NBA.language Paut\<^sub>V"
  proof(rule nba.language[of q\<^sub>0 _ x "smap Some x"])
    fix x 
    assume ipath:"ipath x"

    hence x1_prop:"Some (shd x) \<in> \<Delta>_trans (shd x) q\<^sub>0" "shd x \<in> Node" 
      using \<Delta>_trans_q\<^sub>0 alw_holdsS_iff_snth snth_0 ipath sset_ipath by force+

    show "q\<^sub>0 \<in> nba.initial Paut\<^sub>V" by auto

    define F_valid:: "('node \<times> 'node option) stream \<Rightarrow> 'node option \<Rightarrow> bool" where
      "F_valid \<equiv> (\<lambda>r p. \<exists>r1. r = (r1 ||| smap Some r1) \<and> ipath r1 \<and> Some (shd r1) \<in> \<Delta>_trans (shd r1) p)"

    have FF:"F_valid (x ||| smap Some x) q\<^sub>0" using x1_prop ipath  by(auto simp: F_valid_def)

    thm "nba.run_coinduct"
    thus "NBA.run Paut\<^sub>V (x ||| smap Some x) q\<^sub>0"
      apply(coinduct rule: nba.run_coinduct[of F_valid])
      apply(unfold Paut\<^sub>V_alpha Paut\<^sub>V_trans fst_def snd_def F_valid_def,safe)
      subgoal using sset_ipath by auto
      subgoal by simp
      subgoal for _ _ _ _ r1 apply(intro exI[of _ "stl r1"] conjI, safe)
        subgoal by auto
        subgoal using ipath_stl by auto
        unfolding stream.map_sel(1)
        apply(rule \<Delta>_trans_edge) 
          subgoal unfolding ipath_iff_snth by(erule allE[of _ 0], auto) 
          subgoal by (metis R_ne insert_subset sset_ipath stream.collapse stream.set)  . . 
 
      show "infs (nba.accepting Paut\<^sub>V) (q\<^sub>0 ## smap Some x)" 
        unfolding alw_ev_scons apply(rule infs_all)
        using ipath sset_ipath[OF ipath] unfolding ipath_iff_snth 
        by (auto)
  qed
qed
(*TRACE AUTO*)
fun \<Delta>_trans' :: "'node \<Rightarrow> ('node \<times> 'pos \<times> slope) option \<Rightarrow> 
                  ('node \<times> 'pos \<times> slope) option set" where
  "\<Delta>_trans' v' (Some tr) = (case tr of (v, p, s) \<Rightarrow> {Some (v', p', s')| p' s'. RR (v, p) (v', p') s'})"|
  "\<Delta>_trans' v' q\<^sub>0 = (if v' \<in> Node then {q\<^sub>0} \<union> {Some (v', p', s')| p' s'. p' \<in> PosOf v' \<and> s' = Main} else {})"


fun fsnd where "fsnd (v,p,s) = (v, p)"

lemma q\<^sub>0'_notDecr:"third r = Decr \<Longrightarrow> \<not> (Some r) \<in> \<Delta>_trans' x q\<^sub>0" by(auto simp:   split: if_splits)

lemma \<Delta>_trans_q\<^sub>0'I:"v \<in> Node \<Longrightarrow> q\<^sub>0 \<in> \<Delta>_trans' v q\<^sub>0" by auto 

lemma \<Delta>_trans'_intro:
  assumes "v' \<in> Node"
  assumes "tr = q\<^sub>0 \<Longrightarrow> x = q\<^sub>0  \<or> (\<exists>p' s'. x = Some (v', p', s') \<and> p' \<in> PosOf v' \<and> s' = Main)"
  assumes "tr \<noteq> q\<^sub>0 \<Longrightarrow> (\<exists> p' s'. x = Some (v', p', s') \<and> RR (fst(the tr), second(the tr)) (v', p') s')"
  shows "x \<in> \<Delta>_trans' v' tr"
  using assms by (cases tr, auto)

lemma \<Delta>_trans'_elim:
  assumes "v' \<in> \<Delta>_trans' v\<^sub>t q"
  obtains 
    (\<Delta>_trans\<^sub>1) "q = q\<^sub>0" "v\<^sub>t \<in> Node" "v' = q\<^sub>0"
  | (\<Delta>_trans\<^sub>2) "q = q\<^sub>0" "v\<^sub>t \<in> Node" "\<exists>v'' p' s'. v' = Some (v'', p',s') \<and> p' \<in> PosOf v'' \<and> s' = Main \<and> v\<^sub>t = v''"
  | (\<Delta>_trans\<^sub>3) "\<exists>v p s v'' p' s'. q = Some (v, p, s) \<and> v' = Some (v'', p',s') \<and> RR (v, p) (v'', p') s' \<and> v\<^sub>t = v''" "v\<^sub>t \<in> Node"
proof -
  from assms consider 
    (\<Delta>_trans\<^sub>1) "q = q\<^sub>0 \<and> v\<^sub>t \<in> Node \<and> v' = q\<^sub>0" 
  | (\<Delta>_trans\<^sub>2) "\<exists>v'' p' s'. q = q\<^sub>0 \<and> v\<^sub>t \<in> Node \<and> v' = Some (v'', p',s') \<and> p' \<in> PosOf v'' \<and> s' = Main \<and> v\<^sub>t = v''"
  | (\<Delta>_trans\<^sub>3) "\<exists>v p s v'' p' s'. q = Some (v, p, s) \<and> v' = Some (v'', p',s') \<and> RR (v, p) (v'', p') s' \<and> v\<^sub>t = v'' \<and> v\<^sub>t \<in> Node"
    using RR_PosOf by(cases q, auto split: if_splits)
  then show thesis using that by cases auto
qed

lemma \<Delta>_trans'_elim_q\<^sub>0'_target:
  assumes "q\<^sub>0 \<in> \<Delta>_trans' v a" 
  obtains "q\<^sub>0 = a" "v \<in> Node"  
  using assms by(cases a,auto split: if_splits)

lemma \<Delta>_trans'_elim_q\<^sub>0':
  assumes "v' \<in> \<Delta>_trans' v\<^sub>t q\<^sub>0"
  obtains 
    (\<Delta>_trans\<^sub>1) "v\<^sub>t \<in> Node" "v' = q\<^sub>0"
  | (\<Delta>_trans\<^sub>2) "v\<^sub>t \<in> Node" "second (the v') \<in> PosOf (fst (the v'))" "third (the v') = Main" "v\<^sub>t = fst (the v')"
proof -
  from assms consider 
    (\<Delta>_trans\<^sub>1) "v\<^sub>t \<in> Node \<and> v' = q\<^sub>0" 
  | (\<Delta>_trans\<^sub>2) "v\<^sub>t \<in> Node \<and> second (the v') \<in> PosOf (fst (the v')) \<and> third (the v') = Main \<and> v\<^sub>t = fst (the v')"
    using RR_PosOf by(auto  split: if_splits)
  then show thesis using that by cases auto
qed

(*If we transition from a state which is not q\<^sub>0, then we can never return*)
lemma q\<^sub>0'_notReachable:"q \<noteq> q\<^sub>0 \<Longrightarrow> v' \<in> \<Delta>_trans' v q \<Longrightarrow> v' \<noteq> q\<^sub>0" by(cases v', cases q, auto)

lemma \<Delta>_trans'_v_eq:"v' \<noteq> q\<^sub>0 \<Longrightarrow> v' \<in> \<Delta>_trans' v q \<Longrightarrow> fst (the v') = v"
  apply(cases v')
  subgoal by(cases q, auto)
  subgoal by(cases q, auto split: if_splits) .

lemma \<Delta>_trans'_Decr_not_q\<^sub>0:"Some (v, p, Decr) \<in> \<Delta>_trans' vs q \<Longrightarrow> \<exists>v' p s. q = Some (v',p,s) \<and> vs = v "
  by(cases q, auto split: if_splits)

(*If we transition to a state v' which is decreasing, then RR x y Decr*)
lemma \<Delta>_trans'_DecrRR:
              "v' \<noteq> None \<Longrightarrow>
               fst (the v') \<in> Node \<Longrightarrow>
               second (the v') \<in> PosOf (fst (the v')) \<Longrightarrow>
               third (the v') = Decr \<Longrightarrow> v' \<in> \<Delta>_trans' v q \<Longrightarrow> 
               RR (fst (the q), second (the q)) (fst (the v'), second (the v')) Decr \<and> fst (the v') = v \<and> (fst (the q) \<in> Node \<and> second (the q) \<in> PosOf (fst (the q)) \<and> (third (the q) = Decr \<or> third (the q) = Main))"
  apply(cases v')
  subgoal by (cases q, auto split:if_splits)
  apply(erule \<Delta>_trans'_elim) using  RR_PosOf slope.exhaust by (auto,meson slope.exhaust) 

lemma \<Delta>_trans'_DecrRR':
              "Some (v',p',Decr) \<in> \<Delta>_trans' v q \<Longrightarrow> 
                v' \<in> Node \<Longrightarrow> p' \<in> PosOf v' \<Longrightarrow>
               RR (fst (the q), second (the q)) (v', p') Decr \<and> v' = v \<and> (fst (the q) \<in> Node \<and> second (the q) \<in> PosOf (fst (the q)))"
  using \<Delta>_trans'_DecrRR[of "Some (v',p',Decr)"] by auto

(*From a decreasing state, we only transition via RR*)
lemma \<Delta>_trans'_ProgDRR:
              "q \<noteq> q\<^sub>0 \<Longrightarrow>
               fst (the q) \<in> Node \<Longrightarrow> second (the q) \<in> PosOf (fst (the q)) \<Longrightarrow> third (the q) = Decr \<Longrightarrow> 
               v' \<in> \<Delta>_trans' v q \<Longrightarrow>
               RR (fst (the q), second (the q)) (fst (the v'), second (the v')) (third (the v')) \<and> (third (the v') = Main \<or> third (the v') = Decr) \<and> v' \<noteq> q\<^sub>0"
  apply(cases v')
  subgoal by( cases q, auto split:if_splits)
  apply(erule \<Delta>_trans'_elim) by auto 

lemma \<Delta>_trans'_ProgMRR:
              "q \<noteq> q\<^sub>0 \<Longrightarrow>
               v' \<in> \<Delta>_trans' v q \<Longrightarrow>
               RR (fst (the q), second (the q)) (fst (the v'), second (the v')) (third (the v')) \<and> (third (the v') = Main \<or> third (the v') = Decr) \<and> v' \<noteq> q\<^sub>0"
  apply(cases v')
  subgoal by( cases q, auto split:if_splits)
  apply(erule \<Delta>_trans'_elim) by auto 

lemma \<Delta>_trans'_ProgMRR'_Main:
              "x \<in> Node \<Longrightarrow> y \<in> PosOf x \<Longrightarrow> 
               Some (x',y',Main) \<in> \<Delta>_trans' x' (Some (x,y,z)) \<Longrightarrow>
               RR (x, y) (x', y') Main"
  using \<Delta>_trans'_ProgMRR[of "Some (x,y,z)" "Some (x',y',Main)" x'] slope.exhaust by auto


(*What the states should be, per the paper:*)
definition Q'_states::"('node \<times> 'pos \<times> slope) option set" where 
"Q'_states \<equiv> {q\<^sub>0} \<union> {Some (v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v}"


definition F_valid::"('node \<times> 'pos \<times> slope) option \<Rightarrow> bool" where 
"F_valid \<equiv> \<lambda>s.  \<exists>r1 r2. s = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1"


definition Taut\<^sub>V :: "('node, ('node \<times> 'pos \<times> slope) option) nba" where
  "Taut\<^sub>V = nba 
    Node
    {q\<^sub>0}
    \<Delta>_trans'
    F_valid"


lemma RR_red:"(\<forall>n\<ge>Suc 0. RR (r1 !! n, Ps !! n) (stl r1 !! n, stl Ps !! n) (stl Ss !! n)) \<longleftrightarrow>
       (\<forall>n. RR (stl r1 !! n, stl Ps !! n) (stl(stl r1) !! n, stl(stl Ps) !! n) (stl(stl Ss) !! n))"
  apply standard
subgoal by auto
  subgoal apply(rule allI)
    subgoal for n by(cases n, auto) . .
lemma Taut\<^sub>V_alpha[simp]:"nba.alphabet Taut\<^sub>V = Node" unfolding Taut\<^sub>V_def by auto
lemma Taut\<^sub>V_accept[simp]:"nba.accepting Taut\<^sub>V = (\<lambda>s. \<exists>r1 r2. s = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1)" unfolding Taut\<^sub>V_def F_valid_def by auto
lemma Taut\<^sub>V_init[simp]: "nba.initial Taut\<^sub>V = {q\<^sub>0}" unfolding Taut\<^sub>V_def by auto
lemma Taut\<^sub>V_initp[intro]:"p \<in> nba.initial Taut\<^sub>V \<longleftrightarrow> p = q\<^sub>0" by auto
lemma Taut\<^sub>V_trans[simp]:"nba.transition Taut\<^sub>V a b = \<Delta>_trans' a b" unfolding Taut\<^sub>V_def by auto

lemmas run_def = nba.run_alt_def_snth fst_nth_zip snd_nth_zip Taut\<^sub>V_trans Taut\<^sub>V_alpha nba.target_alt_def  nba.states_alt_def
(*The language of the trace automaton accepts all infinite sequences for which some suffix has a decreasing trace*)
(*necessary to include that the nodes are within the set of Nodes, otherwise we cannot transition in Delta *)
lemma Taut\<^sub>V_lang:"NBA.language Taut\<^sub>V = {nds. (\<exists>Ps. descentIpath nds Ps) \<and> alw (holdsS Node) nds}" 
proof(safe)
  fix x
  show "x \<in> NBA.language Taut\<^sub>V \<Longrightarrow> (\<exists>Ps. descentIpath x Ps)" 
  proof(erule nba.language_elim, unfold Taut\<^sub>V_accept singleton_iff)
    fix r p 
    assume init:"p \<in> nba.initial Taut\<^sub>V" and runs:"NBA.run Taut\<^sub>V (x ||| r) p" and "infs (\<lambda>s. \<exists>r1 r2. s = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1) (p##r)"
    hence p_eq:"p = q\<^sub>0" and run:"NBA.run Taut\<^sub>V (x ||| r) q\<^sub>0" and accept:"infs (\<lambda>s. \<exists>r1 r2. s = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1) r" by auto

    have run':"\<And>k. x !! k \<in> Node \<and> r !! k \<in> \<Delta>_trans' (x !! k) (last (q\<^sub>0 # map snd (stake k (x ||| r))))" using run unfolding run_def by auto


    have accept_from:"\<And>n. \<exists>k\<ge>n. \<exists>r1 r2. r !! k = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1 \<and> Some (r1, r2, Decr) \<in> \<Delta>_trans' (x !! k) (last (stake k r))"
      subgoal for n
      using accept unfolding infs_snth
      apply-apply(erule allE[of _ "Suc n"], safe)
      subgoal for k using runE_Suc'[OF run, of k, unfolded Taut\<^sub>V_trans] 
      apply-by(rule exI[of _ k], auto simp add: last_stake_i stl_Suc)+ . .

  (*If we reach a point k where Decr occurs, then no future state j with j\<ge>k can be q\<^sub>0*)
  have q\<^sub>0'_Decr:"\<And>r1 r2 k j. 0<k \<Longrightarrow> r !! k = Some (r1, r2, Decr) \<Longrightarrow> r1 \<in> Node \<Longrightarrow> r2 \<in> PosOf r1 \<Longrightarrow> k \<le> j \<Longrightarrow> r !! j \<noteq> q\<^sub>0"
    subgoal for r1 r2 k j proof(induct "j - k" arbitrary: j)
      case 0
      then show ?case by auto
    next
      case (Suc xa)
      hence Suc':"\<And> j. 0 < k \<Longrightarrow> xa = j - k \<Longrightarrow> k \<le> j \<Longrightarrow> r !! j \<noteq> q\<^sub>0" by auto
      obtain n where n:"j = Suc n" "xa = n - k" "k \<le> n" using Suc by(cases j,auto)
      show ?case 
        using Suc'[of n,OF Suc(3) n(2,3)] unfolding n
        using runE_Suc[OF run, of n]
        using q\<^sub>0'_notReachable[of "r !! n" "r !! Suc n"] by auto
    qed .


  obtain Ps where Ps:"Ps = smap (\<lambda>r. second (the r)) r" by auto

  have x_eq_r:"\<And>j. (\<exists>r1 r2 r3. r !! j = Some (r1, r2, r3)) \<Longrightarrow> x !! j = fst (the (r !! j))"
    subgoal for j apply(cases j)
      subgoal using runE_0[OF run] by (simp split: if_splits)
      apply safe
      subgoal for j' r1 r2 r3 
        using runE_Suc[OF run,of j', unfolded Taut\<^sub>V_trans]
        apply-by(erule \<Delta>_trans'_elim, auto) . .     

  have x_eq_r':"\<And>j. (\<exists>r1 r2 r3. stl r !! j = Some (r1, r2, r3)) \<Longrightarrow> stl x !! j = fst (the (stl r !! j))"
    subgoal for j using x_eq_r[of "Suc j"] by auto .

  show "\<exists>Ps. descentIpath x Ps"
  apply(rule exI[of _ Ps], unfold descentIpath_iff_snth2, intro conjI)
  subgoal using accept unfolding infs_snth apply-apply(erule allE[of _ "Suc 0"], safe)
    subgoal for k r1 r2 apply(rule exI[of _ k], intro allI impI)
      subgoal for j apply(drule Suc_le_lessD)
        apply(frule q\<^sub>0'_Decr[of k r1 r2 j], simp_all)
        apply(frule x_eq_r)
        using runE_Suc'[OF run zero_less_Suc, of j] 
              \<Delta>_trans'_ProgMRR[of "r !! j" "stl r !! j" "fst (the (stl r !! j))"] 
        unfolding Ps by auto . .
  apply(rule allI)
  subgoal for i using accept_from[of "Suc i"] apply-apply(elim exE conjE)
  subgoal for k r1 r2 apply(cases k, simp)
    subgoal for n
      apply(frule \<Delta>_trans'_Decr_not_q\<^sub>0,rule exI[of _ n])
      unfolding Ps using x_eq_r[of n] last_take_Suc'[of _ _ r] by auto . . .
  qed
next
  fix x
  show "x \<in> NBA.language Taut\<^sub>V \<Longrightarrow> alw (holdsS Node) x" 
  proof(erule nba.language_elim, unfold Taut\<^sub>V_init Taut\<^sub>V_accept singleton_iff)
    fix r p 
    assume "p = q\<^sub>0" and run:"NBA.run Taut\<^sub>V (x ||| r) p"
    thus "alw (holdsS Node) x" using streams_sset[OF nba.run_alphabet[OF run]] by (simp add: alw_holdsS_iff_snth subsetD)
  qed
next
  fix x Ps
  assume iDPath:"descentIpath x Ps" and x_node:"alw (holdsS Node) x"

  have ev:"ev (alw (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr))) (x ||| Ps)"and
      alw:"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) (x ||| Ps)"
      using iDPath[unfolded descentIpath_def2] by auto

    have hh:"\<And>x y z i. (stl x!!i, stl y!!i, stl z!!i) \<in>sset (x ||| y ||| z)" 
      by (metis snth_sset snth_szip stream.set_sel(2) szip.sel(2))
  
  define f where "f = (\<lambda>x' Ps' i. (if RR (x' !! i, Ps' !! i) (stl x' !! i, stl Ps' !! i) Decr then Decr else Main))"
  define Ss where "Ss = (\<lambda>x Ps. Main ## fToStream (f x Ps))"
  note Ss_defs = Ss_def f_def fToStream_def

  have Ss_i:"\<And>k m. m < Suc k \<Longrightarrow> (Ss (sdrop m x) (sdrop m Ps) !! (Suc k - m)) = f x Ps k" using Suc_diff_le unfolding Ss_defs by auto
    
  obtain m where m:"(\<And>n. n\<ge>m \<Longrightarrow> (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr)) (sdrop n (x ||| Ps)))"
    using ev unfolding ev_alw_iff_sdrop by auto


  have alw_dropm:"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) (sdrop m (x ||| Ps))"
    using alw unfolding alw_ev_sdrop by auto

  define r where "r = replicate m q\<^sub>0 @- smap Some ((sdrop m x) ||| (sdrop m Ps) ||| (Ss (sdrop m x) (sdrop m Ps)))"

  have x_node':"\<And>i. x !! i \<in> Node" using x_node unfolding alw_holdsS_iff_snth by auto

  have r_eq_q\<^sub>0':"\<And>n. Suc n \<le> m \<longleftrightarrow> r!!n = q\<^sub>0" 
    apply standard unfolding r_def
    subgoal using replicate_within_i by auto
    subgoal for n apply(rule ccontr, unfold not_le replicate_beyond_i) using x_node'[of "n"]  by auto .


  have r_neq_q\<^sub>0':"\<And>n. Suc n > m \<longleftrightarrow> r!!n = Some (x!!n, Ps !! n, Ss (sdrop m x) (sdrop m Ps) !! (n-m))" 
    apply standard
    subgoal unfolding r_def using replicate_beyond_i by auto 
    subgoal for n using r_eq_q\<^sub>0'[of n] by auto .

  have xn_gr:"\<And>n. Suc n > m \<Longrightarrow> x !! n = fst (the (r !! n))" using r_neq_q\<^sub>0' by auto
  have Psn_gr:"\<And>n. Suc n > m \<Longrightarrow> Ps !! n = second (the (r !! n))" using r_neq_q\<^sub>0' by auto

  have Ssn_gr:"\<And>n. Suc n > m \<Longrightarrow> third (the (r !! n)) = Ss (sdrop m x) (sdrop m Ps) !! (n-m)" using r_neq_q\<^sub>0' by auto

  have m_eq:"\<And>k m. Suc k \<le> m \<Longrightarrow> m < Suc (Suc k) \<Longrightarrow> m = Suc k" by auto

  show "x \<in> NBA.language Taut\<^sub>V"
  proof(rule nba.language[of q\<^sub>0 _ _ r], unfold Taut\<^sub>V_accept Taut\<^sub>V_initp, safe)
    (*can always drop from the stream and preserve these properties*)
    thm ev_alw_sdrop alw_ev_sdrop
    show "NBA.run Taut\<^sub>V (x ||| r) q\<^sub>0" 
    proof(unfold run_def, intro allI conjI) 
      fix k 
      show "x !! k \<in> Node" using x_node' by (metis)

      show "r !! k \<in> \<Delta>_trans' (x !! k) (last (q\<^sub>0 # map snd (stake k (x ||| r))))"
      proof(induct k)
        case 0
        then show ?case unfolding r_def apply(cases m)
          subgoal using m[of 0] RR_PosOf[of "shd x" "shd Ps" "shd (stl x)" "shd (stl Ps)"]
            unfolding Ss_def by (auto)
          using \<Delta>_trans_q\<^sub>0'I[of "x!!0", OF x_node'[of 0]] by auto
      next
        case (Suc k)
        then show ?case 
          unfolding last_stake_szip apply-apply(erule \<Delta>_trans'_elim exE)
          (*\<Delta>_trans\<^sub>1 within q\<^sub>0 -- q\<^sub>0 \<in> \<Delta>_trans' (x !! k) q\<^sub>0 \<Longrightarrow> r !! Suc k \<in> \<Delta>_trans' (x !! Suc k) q\<^sub>0*)
          subgoal apply(rule \<Delta>_trans'_intro[OF x_node'[of "Suc k"]])
            subgoal using le_less_linear[of "Suc (Suc k)" m] apply-apply(erule disjE)
              subgoal using r_eq_q\<^sub>0'[of "Suc k"] x_node'[of "Suc k"]  by auto 
              subgoal unfolding r_eq_q\<^sub>0'[symmetric, of k]  apply(frule m_eq[of k m], clarify)
                using r_neq_q\<^sub>0'[of "Suc k"] m[of "Suc k"] RR_PosOfD Ss_def by auto . 
            by auto
          (*\<Delta>_trans\<^sub>2 Initialise -- (x !! k,Ps,Main) \<in> \<Delta>_trans' (x !! k) q\<^sub>0 \<Longrightarrow> r !! Suc k \<in> \<Delta>_trans' (x !! Suc k) (x !! k,Ps,Main)*)
          subgoal apply(rule \<Delta>_trans'_intro[OF x_node'[of "Suc k"]], simp)
            using r_neq_q\<^sub>0'[of "Suc k"]  r_eq_q\<^sub>0'[of k] Ss_i[of m k]
                    m[of "k"] xn_gr[of k]  xn_gr[of "Suc k"]  Psn_gr[of k] Psn_gr[of "Suc k"]  Ssn_gr[of "Suc k"] 
                    unfolding f_def by auto 
          (*\<Delta>_trans\<^sub>3 within Main/Decr trace*)
          subgoal apply(rule \<Delta>_trans'_intro[OF x_node'[of "Suc k"]], simp)
            using r_neq_q\<^sub>0'[of "Suc k"]  r_eq_q\<^sub>0'[of k] Ss_i[of m k]
                    m[of "k"] xn_gr[of k]  xn_gr[of "Suc k"]  Psn_gr[of k] Psn_gr[of "Suc k"]  Ssn_gr[of "Suc k"] 
                    unfolding f_def by auto . 
      qed
    qed
    (*Found the appropriate invariant for this one...*)
    show "infs (\<lambda>s. \<exists>r1 r2. s = Some (r1, r2, Decr) \<and> r1 \<in> Node \<and> r2 \<in> PosOf r1) r"
      unfolding r_def alw_ev_shift alw_ev_holds_iff_snth
      apply(rule allI)
      subgoal for i using alw_dropm unfolding alw_ev_holds2_iff_snth case_prod_beta Ss_defs
        apply-apply(elim allE[of _ i] exE conjE)
        subgoal for j by(frule RR_PosOf,rule exI[of _ "Suc j"], auto)  . .           
  qed
qed

(*Trivial auxillary results required*)
lemma alpha_subseq_PTaut\<^sub>V: "nba.alphabet Paut\<^sub>V \<subseteq> nba.alphabet Taut\<^sub>V" by simp
(*PATH AUTO FINITE NODES*)

lemma Pnode_subseq_rule:"(\<And>r. \<forall>x\<in>Node. last (map snd r) \<noteq> Some x \<Longrightarrow>
         r \<noteq> [] \<Longrightarrow> NBA.path Paut\<^sub>V r None \<Longrightarrow> last (map snd r) = None) \<Longrightarrow>
(\<Union>p\<in>{p. p \<in> nba.initial Paut\<^sub>V}. {last (p # map snd r) |r. NBA.path Paut\<^sub>V r p})
    \<subseteq> {r. r = None \<or> (\<exists>x\<in>Node. r = Some x)}" by auto


lemma Paut\<^sub>V_node_subseq:"NBA.nodes Paut\<^sub>V \<subseteq> {r. r = None \<or> (\<exists>x\<in> Node. r = Some x)}" 
  unfolding nba.nodes_alt_def nba.reachable_alt_def nba.target_alt_def nba.states_alt_def 
  apply(rule Pnode_subseq_rule)
  subgoal premises p for r using p(3,1-2) apply(induct rule: nba.path.induct)
    subgoal by auto
    subgoal for a p by (cases p,  auto simp: RR_PosOfD' split: if_splits) . . 

lemma finite_Nodes_Paut\<^sub>V:"finite (NBA.nodes Paut\<^sub>V)" 
  apply(rule rev_finite_subset[OF _ Paut\<^sub>V_node_subseq]) using finite_Node_opt by auto 

(*TRACE AUTO FINITE NODES*)
lemma Tnode_subseq_rule:"(\<And>r. \<forall>a. a \<in> Node \<longrightarrow> (\<forall>aa. aa \<in> PosOf a \<longrightarrow> (\<forall>b. last (map snd r) \<noteq> Some (a, aa, b))) \<Longrightarrow>
         r \<noteq> [] \<Longrightarrow> NBA.path Taut\<^sub>V r None \<Longrightarrow> last (map snd r) = None)
  \<Longrightarrow> (\<Union>p\<in>{p. p \<in> nba.initial Taut\<^sub>V}. {last (p # map snd r) |r. NBA.path Taut\<^sub>V r p})
    \<subseteq> {r. r = None \<or> (\<exists>x\<in>{(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v}. r = Some x)}" by auto


lemma  Taut\<^sub>V_node_subseq:"NBA.nodes Taut\<^sub>V \<subseteq> {r. r = None \<or> (\<exists>x\<in>{(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v}. r = Some x)}" 
  unfolding nba.nodes_alt_def nba.reachable_alt_def nba.target_alt_def nba.states_alt_def
  apply(rule Tnode_subseq_rule)
  subgoal premises p for r using p(3,1-2) apply(induct rule: nba.path.induct)
    subgoal by auto
    subgoal for a p by (cases p,  auto simp: RR_PosOfD' split: if_splits) . . 


lemma set_slope_case:"{(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v} = {(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v \<and> s \<in>{Main, Decr}}" by auto

lemma finite_Node_Taut\<^sub>V_gr:"finite ({r. \<exists>x\<in>{(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v}. r = Some x}:: ('node \<times> 'pos \<times> slope) option set)"
proof(rule finite_imageI[unfolded image_def, of _ Some], unfold set_slope_case)
  define A where "A = {(v, p) | v p. v \<in> Node \<and> p \<in> PosOf v}"
  define f::"(('node \<times> 'pos) \<times> slope) \<Rightarrow> ('node \<times> 'pos \<times> slope)" where "f = (\<lambda>((n, p), s). (n, p, s))"

  have A_cart_eq:"A \<times> {Main, Decr} = {(n, p). n \<in> A \<and> p \<in> {Main, Decr}}" by auto
  have "A = \<Union> ((\<lambda>v. {v} \<times> PosOf v) ` Node)"
    unfolding A_def by auto

  hence "finite A" using Node_finite PosOf_finite by (simp add: finite_UN finite_cartesian_product)

  have finiteFull:"finite (A \<times> {Main, Decr})"
    using finite_cartesian_product[OF `finite A`, of "{Main, Decr}"] by simp

  have S_eq:"{(v, p, s) | v p s. v \<in> Node \<and> p \<in> PosOf v \<and> s \<in> {Main, Decr}} = f ` (A \<times> {Main, Decr})" unfolding A_def f_def case_prod_beta image_def by auto


  show "finite {(v, p, s) |v p s. v \<in> Node \<and> p \<in> PosOf v \<and> s \<in> {Main, Decr}}"unfolding S_eq using finite_imageI[OF finiteFull, of f] by auto
qed

lemma finite_Nodes_Taut\<^sub>V:"finite (NBA.nodes Taut\<^sub>V)" 
  apply(rule rev_finite_subset[OF _ Taut\<^sub>V_node_subseq]) using finite_Node_Taut\<^sub>V_gr by auto 

(*Theorem 4.1*)
theorem VLA_Criterion:"InfiniteDescent \<longleftrightarrow> NBA.language Paut\<^sub>V \<subseteq> NBA.language Taut\<^sub>V"
  unfolding Taut\<^sub>V_lang Paut\<^sub>V_lang InfiniteDescent_def ipath_def by auto


corollary VLA_Criterion':"InfiniteDescent \<longleftrightarrow> NBA.language Paut\<^sub>V \<inter> (NBA.language (complement Taut\<^sub>V)) = {}"
  unfolding VLA_Criterion by(rule complement_eq1, simp_all add: finite_Nodes_Taut\<^sub>V)
end

end