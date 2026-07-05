(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsubsection "Slope-language Criterion"
theory SLA_Criterion
  imports "../Sloped_Graphs"
          "../Buchi_Preliminaries"
begin

context Sloped_Graph 
begin

abbreviation q\<^sub>0 where "q\<^sub>0 \<equiv> None"
fun RR':: "'node \<times> 'node \<Rightarrow> 'pos \<times> 'pos \<times> slope \<Rightarrow> bool"  where "RR' (nd,nd') = (\<lambda>(ps, ps', s). RR (nd,ps) (nd',ps') s)"


fun ndOf where "ndOf ((nd,ps),(nd',ps'),s) = nd"
fun nd'Of where "nd'Of ((nd,ps),(nd',ps'),s) = nd'"

term "{Some nd'| nd. edge nd nd'}"
(*PATH AUTOMATON*)
fun \<Delta>\<^sub>s\<^sub>l :: "('pos \<times> 'pos \<times> slope \<Rightarrow> bool) \<Rightarrow> 'node option \<Rightarrow> 'node option set" where
  "\<Delta>\<^sub>s\<^sub>l t (Some nd) = {Some nd'| nd'. {nd, nd'} \<subseteq> Node \<and> edge nd nd' \<and> t = RR'(nd,nd') }"|
  "\<Delta>\<^sub>s\<^sub>l t q\<^sub>0 = {Some nd'| nd nd'. {nd, nd'} \<subseteq> Node \<and> edge nd nd' \<and> t = RR'(nd,nd')}"

lemma \<Delta>\<^sub>s\<^sub>l_intro_Some:
  assumes "edge s s'" 
    and "{s, s'} \<subseteq> Node"
    and "tr = RR'(s,s')"
  shows "Some s' \<in> \<Delta>\<^sub>s\<^sub>l tr (Some s)"
  using assms by auto

lemma \<Delta>\<^sub>s\<^sub>l_intro_q0:
  assumes  "edge s s'" 
    and "{s, s'} \<subseteq> Node"
    and "tr = RR'(s,s')"
  shows "Some s' \<in> \<Delta>\<^sub>s\<^sub>l tr q\<^sub>0"
  using assms by auto

lemma \<Delta>\<^sub>s\<^sub>l_elim:
  assumes "x \<in> \<Delta>\<^sub>s\<^sub>l t z"
  obtains nd nd' where
    "x = Some nd'" "nd \<in> Node" "nd' \<in> Node" "edge nd nd'" "t = RR' (nd, nd')"
    "z = q\<^sub>0 \<or> the z = nd"
  using assms by (cases z, auto)

lemma \<Delta>\<^sub>s\<^sub>l_q\<^sub>0_not_q\<^sub>0[simp]: "\<not> (q\<^sub>0 \<in> \<Delta>\<^sub>s\<^sub>l x q\<^sub>0)" by auto

lemma \<Delta>\<^sub>s\<^sub>l_some:"r' \<in> \<Delta>\<^sub>s\<^sub>l x r \<Longrightarrow> \<exists>y. r' = Some y" by(cases r, auto) 

(*Sanity check with the \<Delta>\<^sub>s\<^sub>l in the paper, 
  the sets of transitions as before*)
lemma "\<Delta>\<^sub>s\<^sub>l l s = 
       {Some v'| v v'. s = q\<^sub>0 \<and> (edge v v') \<and> {v, v'} \<subseteq> Node \<and> l = RR'(v,v')} \<union>
       {Some v'| v'. s \<noteq> q\<^sub>0 \<and> edge (the s) v' \<and> {(the s), v'} \<subseteq> Node \<and> l = RR'((the s),v')}"
  unfolding \<Delta>\<^sub>s\<^sub>l.simps by(cases s, auto)

definition Paut\<^sub>R :: "('pos \<times> 'pos \<times> slope \<Rightarrow> bool, 'node option) nba" where
  "Paut\<^sub>R = nba 
    {RR' (nd, nd')| nd nd'. edge nd nd'}
    {q\<^sub>0}
    \<Delta>\<^sub>s\<^sub>l
    (\<lambda>s. the s \<in> Node)"

lemmas Paut\<^sub>R_defs = Paut\<^sub>R_def \<Delta>\<^sub>s\<^sub>l.simps
lemma Paut\<^sub>R_alpha[simp]:"nba.alphabet Paut\<^sub>R = {RR' (nd, nd')| nd nd'. edge nd nd'}" unfolding Paut\<^sub>R_def by auto
lemma Paut\<^sub>R_accept[simp]:"nba.accepting Paut\<^sub>R = (\<lambda>s. the s \<in> Node)" unfolding Paut\<^sub>R_def by auto
lemma Paut\<^sub>R_init[simp]: "nba.initial Paut\<^sub>R = {q\<^sub>0}" unfolding Paut\<^sub>R_def by auto
lemma Paut\<^sub>R_initp[intro]:"p \<in> nba.initial Paut\<^sub>R \<longleftrightarrow> p = q\<^sub>0" by auto
lemma Paut\<^sub>R_trans[simp]:"nba.transition Paut\<^sub>R a b = \<Delta>\<^sub>s\<^sub>l a b" unfolding Paut\<^sub>R_def by auto

lemmas Paut\<^sub>R_trans' = Paut\<^sub>R_trans \<Delta>\<^sub>s\<^sub>l.simps
lemmas Paut\<^sub>R_run_def = nba.run_alt_def_snth Paut\<^sub>R_trans Paut\<^sub>R_alpha nba.target_alt_def  nba.states_alt_def


lemma Paut\<^sub>R_lang:"NBA.language Paut\<^sub>R = {Ri. \<exists>nds. ipath nds \<and> (\<forall>i. Ri !! i = RR' (nds !! i, nds !! Suc i))}" 
proof(safe)
  fix x 
  assume "x \<in> NBA.language Paut\<^sub>R"
  then obtain r where run:"NBA.run Paut\<^sub>R (x ||| r) None"  and accept:"infs (\<lambda>s. the s \<in> Node) r" apply-by(erule nba.language_elim, auto)


  (*We leave q\<^sub>0 immediately and never transition back during the run*)
  have q\<^sub>0'_notReachable:"\<And>k. r !! k \<noteq> q\<^sub>0"
      subgoal for k apply(induct k)
        subgoal using runE_0[OF run] apply-by(clarsimp)
        subgoal for k using runE_Suc[OF run, of k] by auto . .

  have x_prop:"\<And>k. k>0 \<Longrightarrow> \<exists>nd nd'. x !! k = RR' (nd, nd') \<and> edge nd nd' \<and> the(r!!k) = nd'  \<and> the(r!!(k-1)) = nd" 
    subgoal for k  
      using runE_Suc[OF run, of k, unfolded Paut\<^sub>R_trans]
      apply-apply(drule runE_Suc'[OF run, of k, unfolded Paut\<^sub>R_trans])
      apply(erule \<Delta>\<^sub>s\<^sub>l_elim)+
      using q\<^sub>0'_notReachable[of] by auto . 


  have q\<^sub>0'_notLast:"\<And>k. k>0 \<Longrightarrow> last (stake k r) \<noteq> q\<^sub>0" subgoal for k
     using q\<^sub>0'_notReachable[of "k-1"] last_conv_nth[of "stake k r"] by auto .
  
  hence i_eq_iff:"\<And>i. (if i = 0 then None else last (stake i r)) = None \<longleftrightarrow> i = 0" by simp

  obtain s where s_edge:"edge s (the (r !! 0))" and s_node:"s \<in>Node" and s_x:"x !! 0 = RR'(s, the (r !! 0))"
    using runE_0[OF run] by auto

  show "\<exists>nds. local.ipath nds \<and> (\<forall>i. x !! i = RR' (nds !! i, nds !! Suc i))"
  proof(rule exI[of _ "s ## smap the r"], unfold ipath_def Paut\<^sub>R_initp Paut\<^sub>R_accept, safe)
    fix i

    have "alw (holdsS Node) (smap the r)" unfolding alw_holdsS_iff_snth apply-apply(rule allI)
      subgoal for i apply(induct i)
        subgoal using runE_0[OF run] by auto 
        subgoal for i using runE_Suc[OF run, of i, unfolded Paut\<^sub>R_trans] apply-by(erule \<Delta>\<^sub>s\<^sub>l_elim, auto) . . 

    thus "alw (holdsS Node) (s ## smap the r)"
      using s_node unfolding alw_holdsS_iff_snth by (metis not0_implies_Suc snth.simps(1) snth_Stream stream.sel(1))

 

    have alwEdge:"alw (holds2 edge) (smap the r)" unfolding alw_holds2_iff_snth apply-apply(rule allI)
      subgoal for i using runE_Suc[OF run, of i, unfolded Paut\<^sub>R_trans] 
                          runE_Suc[OF run, of "Suc i", unfolded Paut\<^sub>R_trans]
          apply-apply(erule \<Delta>\<^sub>s\<^sub>l_elim)+
          using q\<^sub>0'_notReachable by auto .
          
    thus "alw (holds2 edge) (s ## smap the r)"
      using s_edge unfolding alw_holds2_iff_snth apply-apply(rule allI)
      subgoal for i apply(cases i, simp)
        subgoal for n by (erule allE[of _ n], auto) . . 

    show "x !! i = RR' ((s ## smap the r) !! i, (s ## smap the r) !! Suc i)" 
      using s_x x_prop[of i] by(cases i, auto)
  qed
next
  fix x nds
  assume ipath:"ipath nds" and
         Rel:"\<forall>i. x !! i = RR' (nds !! i, nds !! Suc i)"
  obtain nd1 nd2 where nds:"nds = nd1 ## nd2" by (cases nds)
  have Rel':"\<And>i. x !! i = RR' (nds !! i, nds !! Suc i) \<and> edge (nds !! i) (nds !! Suc i)" 
    using Rel RR'.simps ipath unfolding alw_holds2_iff_snth ipath_def by auto

  have nds_in_Node:"sset nds \<subseteq> Node" by (metis ipath sset_ipath)
  hence stl_nds_in_Node:"sset (stl nds) \<subseteq> Node" using nds by auto

  show "x \<in> NBA.language Paut\<^sub>R"
  proof(rule nba.language[of None Paut\<^sub>R x "smap Some (stl nds)"])

    show "q\<^sub>0 \<in> nba.initial Paut\<^sub>R" by auto

    show "NBA.run Paut\<^sub>R (x ||| smap Some (stl nds)) q\<^sub>0"
    proof(unfold Paut\<^sub>R_run_def fst_nth_zip snd_nth_zip, intro allI conjI, safe)
      fix k
      show " \<exists>nd nd'. x !! k = RR' (nd, nd') \<and> edge nd nd'" using Rel' by auto
      show "smap Some (stl nds) !! k \<in> \<Delta>\<^sub>s\<^sub>l (x !! k) (last (None # map snd (stake k (x ||| smap Some (stl nds)))))"
      proof(induct k)
        case 0
        have last:"(last (None # map snd (stake 0 (x ||| smap Some (stl nds))))) = None" by auto
        show ?case unfolding snth_smap last
          apply(rule \<Delta>\<^sub>s\<^sub>l_intro_q0[of "shd nds" ])
          subgoal using Rel'[of 0] by auto
          subgoal using nds_in_Node stl_nds_in_Node by auto
          subgoal using Rel'[of 0] by auto .
     next
        case (Suc k)
        then show ?case unfolding last_stake_szip snth_smap
          apply-apply(erule \<Delta>\<^sub>s\<^sub>l_elim,rule \<Delta>\<^sub>s\<^sub>l_intro_Some) 
          using Rel'[of "Suc k"]  ipath ipath_iff_snth ipath_stl nds_in_Node by auto
      qed
    qed


    have ruleInfs:"infs (nba.accepting Paut\<^sub>R) (smap Some (stl nds)) \<Longrightarrow>infs (nba.accepting Paut\<^sub>R) (q\<^sub>0 ## smap Some (stl nds))"
      using alw_ev_shift[of _ "[None]"] by auto

    show "infs (nba.accepting Paut\<^sub>R) (q\<^sub>0 ## smap Some (stl nds))"
      apply(rule ruleInfs,rule infs_all)
      using stl_nds_in_Node by auto
  qed
qed

lemma Paut\<^sub>R_lang_in:"x \<in> NBA.language Paut\<^sub>R \<longleftrightarrow> (\<exists>nds. ipath nds \<and> (\<forall>i. x !! i = RR' (nds !! i, nds !! Suc i)))"
  unfolding Paut\<^sub>R_lang by auto



(*What the states should be, per the paper:*)
definition Q'\<^sub>s\<^sub>l::"('pos \<times> slope) set" where 
"Q'\<^sub>s\<^sub>l \<equiv> {(p, s)| p s. p \<in> (\<Union>v\<in>Node. PosOf v)}"
abbreviation "\<Sigma> \<equiv> {RR' (nd, nd')| nd nd'. edge nd nd'}"
(*TRACE AUTO*)
fun \<Delta>\<^sub>s\<^sub>l' :: "('pos \<times> 'pos \<times> slope \<Rightarrow> bool) \<Rightarrow> ('pos \<times> slope) option \<Rightarrow> ('pos \<times> slope) option set" where
  "\<Delta>\<^sub>s\<^sub>l' R' (Some (p,s)) = {Some (p',s')| p' s'. (p,s) \<in> Q'\<^sub>s\<^sub>l \<and> R' \<in> \<Sigma> \<and> R' (p, p', s')}"|
  "\<Delta>\<^sub>s\<^sub>l' R' q\<^sub>0 = (if R' \<in> \<Sigma> then {q\<^sub>0} \<union> {Some (p',s')| p' s'. (p',s') \<in> Q'\<^sub>s\<^sub>l} else {})"

(*intros*)
lemma \<Delta>\<^sub>s\<^sub>l'_intro_Some:
  assumes "(p, s) \<in> Q'\<^sub>s\<^sub>l" "R' \<in> \<Sigma>" "R' (p, p', s')"
  shows "Some (p', s') \<in> \<Delta>\<^sub>s\<^sub>l' R' (Some (p, s))"
  using assms by auto

lemma \<Delta>\<^sub>s\<^sub>l'_intro_q0:
  assumes "R' \<in> \<Sigma>" "(p', s') \<in> Q'\<^sub>s\<^sub>l"
  shows "Some (p', s') \<in> \<Delta>\<^sub>s\<^sub>l' R' q\<^sub>0"
  using assms by auto

lemma \<Delta>\<^sub>s\<^sub>l'_q0_included:
  assumes "R' \<in> \<Sigma>"
  shows "q\<^sub>0 \<in> \<Delta>\<^sub>s\<^sub>l' R' q\<^sub>0"
  using assms by auto

lemma \<Delta>\<^sub>s\<^sub>l'_intro:
  assumes "ns \<in> \<Sigma>"
  assumes "rk \<noteq> q\<^sub>0 \<Longrightarrow> (\<exists> p' s'. rk' = Some (p', s') \<and> the rk \<in> Q'\<^sub>s\<^sub>l \<and> ns (fst(the rk), p', s'))"
  assumes "rk = q\<^sub>0 \<Longrightarrow> (rk' = q\<^sub>0 \<or> (\<exists>p' s'. rk' = Some (p', s') \<and> (p', s') \<in> Q'\<^sub>s\<^sub>l))"
  shows "rk' \<in> \<Delta>\<^sub>s\<^sub>l' ns rk"
  using assms apply (cases rk) by force+



(*elims*)
lemma \<Delta>\<^sub>s\<^sub>l'_elim:
  assumes "x \<in> \<Delta>\<^sub>s\<^sub>l' R' z"
  obtains (SomeCase) p s p' s' where 
    "z = Some (p, s)" "x = Some (p', s')" "(p, s) \<in> Q'\<^sub>s\<^sub>l" "R' \<in> \<Sigma>" "R' (p, p', s')"
  | (q0Case) p' s' where 
    "z = q\<^sub>0" "R' \<in> \<Sigma>" "(p', s') \<in> Q'\<^sub>s\<^sub>l" "x = Some (p', s')"
  | (q0Self) "z = q\<^sub>0" "R' \<in> \<Sigma>" "x = q\<^sub>0"
  using assms by (cases z,(auto split: if_splits)+)

(*If we transition from a state which is not q\<^sub>0, then we can never return*)
lemma q\<^sub>0_notReachable:"q \<noteq> q\<^sub>0 \<Longrightarrow> v' \<in> \<Delta>\<^sub>s\<^sub>l' v q \<Longrightarrow> v' \<noteq> q\<^sub>0" by(cases v', cases q, auto)





definition F\<^sub>s\<^sub>l::"('pos \<times> slope) option \<Rightarrow> bool" where 
"F\<^sub>s\<^sub>l \<equiv> \<lambda>ps. \<exists>p. ps = Some (p, Decr) \<and> (p, Decr) \<in> Q'\<^sub>s\<^sub>l"


definition Taut\<^sub>R :: "('pos \<times> 'pos \<times> slope \<Rightarrow> bool, ('pos \<times> slope) option) nba" where
  "Taut\<^sub>R = nba 
    {RR' (nd, nd')| nd nd'. edge nd nd'}
    {q\<^sub>0}
    \<Delta>\<^sub>s\<^sub>l'
    F\<^sub>s\<^sub>l"

lemma RR_reduce:"(\<forall>n\<ge>Suc 0. RR (r1 !! n, Ps !! n) (stl r1 !! n, stl Ps !! n) (stl Ss !! n)) \<longleftrightarrow>
       (\<forall>n. RR (stl r1 !! n, stl Ps !! n) (stl(stl r1) !! n, stl(stl Ps) !! n) (stl(stl Ss) !! n))"
  apply standard
subgoal by auto
  subgoal apply(rule allI)
    subgoal for n by(cases n, auto) . .


(*lemma kk:"\<And>k. k>0 \<Longrightarrow> r !! (k - Suc 0) = last (stake k r)" subgoal for k using last_conv_nth[of "stake k r"] by auto .
*)

lemma Taut\<^sub>R_alpha[simp]:"nba.alphabet Taut\<^sub>R = {RR' (nd, nd')| nd nd'. edge nd nd'}" unfolding Taut\<^sub>R_def by auto
lemma Taut\<^sub>R_accept[simp]:"nba.accepting Taut\<^sub>R = (\<lambda>ps. \<exists>p. ps = Some (p, Decr) \<and> (p, Decr) \<in> Q'\<^sub>s\<^sub>l)" unfolding Taut\<^sub>R_def F\<^sub>s\<^sub>l_def by auto
lemma Taut\<^sub>R_init[simp]: "nba.initial Taut\<^sub>R = {q\<^sub>0}" unfolding Taut\<^sub>R_def by auto
lemma Taut\<^sub>R_initp[intro]:"p \<in> nba.initial Taut\<^sub>R \<longleftrightarrow> p = q\<^sub>0" by auto
lemma Taut\<^sub>R_trans[simp]:"nba.transition Taut\<^sub>R a b = \<Delta>\<^sub>s\<^sub>l' a b" unfolding Taut\<^sub>R_def by auto

lemmas run_def' = nba.run_alt_def_snth fst_nth_zip snd_nth_zip Taut\<^sub>R_trans Taut\<^sub>R_alpha nba.target_alt_def  nba.states_alt_def


(**converting a stream of nodes to it's Ri sequence**)
fun Rst where "Rst nds = smap (\<lambda>i. RR' (nds !! i, nds !! Suc i)) nats"

lemma stl_shift:"(stl nds !! i,stl (stl nds) !! i) = (nds !! Suc i,(stl nds) !! Suc i)" by auto

lemma smap_shifted_eq:
        "smap (\<lambda>i. RR' (nds !! i,stl nds !! i)) (fromN (Suc 0)) = 
         smap (\<lambda>i. RR' (stl nds !! i,stl (stl nds) !! i)) nats"
  unfolding stl_shift
  apply(rule ssubst[of "smap (\<lambda>i. RR' (nds !! Suc i, stl nds !! Suc i)) nats" 
                       "smap (\<lambda>j (ps, ps', y). RR (stl nds !! (j - Suc 0), ps) (stl (stl nds) !! (j - Suc 0), ps') y) (fromN (Suc 0))"])
  subgoal using stream_smap_fromN[of "smap (\<lambda>i. RR' (stl nds !! i, stl (stl nds) !! i)) nats" "Suc 0"] by auto
  apply(rule stream.map_cong0)
  subgoal for z using stl_Suc[of z nds] stl_Suc[of "z" "stl nds"] by force .

lemma Rst_correct:"x = Rst nds \<longleftrightarrow> (\<forall>i. x !! i = RR' (nds !! i, nds !! Suc i))"
  apply(safe)
  subgoal for i by(cases i, auto)
  subgoal 
    apply (coinduction arbitrary: x nds, intro conjI)
    subgoal by (erule allE[of _ 0], auto)
    subgoal for x_hd x_tl nd_hd nd_tl x nds 
      apply(rule exI2[of _ x_tl "stl nds"], safe)
      subgoal using smap_shifted_eq by auto 
      subgoal for i by(erule allE[of _ "Suc i"], auto) . . . 


lemma Rst_r:"\<And>k. Rst nds !! k = RR' (nds !! k, nds !! Suc k)"using Rst_correct by auto

(***)
(*For any ipath nds, we have that for i\<in>N RR(nds!i, nds!Suc i) \<in> Lang Taut\<^sub>R iff nds is descending *)

lemma list_swap:"k>0 \<Longrightarrow> (p ## smap (\<lambda>r. fst (the r)) r) !! k = fst (the (r !! (k-1))) " by (cases k, auto)
lemma Taut\<^sub>R_lang_in:"ipath nds \<Longrightarrow> Rst nds \<in> NBA.language Taut\<^sub>R \<longleftrightarrow> (\<exists>Ps. descentIpath nds Ps)"
proof(safe)
  assume ipath:"ipath nds"

  have k_edge:"\<And>k. edge (nds !! k) (stl nds !! k)" using ipath unfolding ipath_def alw_holds2_iff_snth by auto

  show "Rst nds \<in> NBA.language Taut\<^sub>R \<Longrightarrow> \<exists>Ps. descentIpath nds Ps"

  proof -
    assume "Rst nds \<in> NBA.language Taut\<^sub>R"
    then obtain r where run:"NBA.run Taut\<^sub>R (Rst nds ||| r) None"  and accept:"infs (\<lambda>ps. \<exists>p. ps = Some (p, Decr) \<and> (p, Decr) \<in> Q'\<^sub>s\<^sub>l) r" apply-by(erule nba.language_elim, auto)

    hence run':"\<And>k. Rst nds !! k = RR' (nds !! k, nds !! Suc k) \<and> edge (nds !! k) (nds !! Suc k) \<and>
        r !! k \<in> \<Delta>\<^sub>s\<^sub>l' (Rst nds !! k) (if k = 0 then None else last (stake k r))"
      using k_edge unfolding Paut\<^sub>R_run_def by auto


  (*If we reach a point k where Decr occurs, then no future state j with j\<ge>k can be q\<^sub>0*)
  have q\<^sub>0'_Decr:"\<And>p k j. 0<k \<Longrightarrow> r !! k = Some (p, Decr) \<Longrightarrow> k \<le> j \<Longrightarrow> r !! j \<noteq> q\<^sub>0"
    subgoal for p k j proof(induct "j - k" arbitrary: j)
      case 0
      then show ?case by auto
    next
      case (Suc xa)
      hence Suc':"\<And> j. 0 < k \<Longrightarrow> xa = j - k \<Longrightarrow> k \<le> j \<Longrightarrow> r !! j \<noteq> q\<^sub>0" by auto
      obtain n where n:"j = Suc n" "xa = n - k" "k \<le> n" using Suc by(cases j,auto)
      show ?case 
        using Suc'[of n,OF Suc(3) n(2,3)] unfolding n
        using runE_Suc[OF run, of n] q\<^sub>0_notReachable[of "r !! n" "r !! Suc n"] by auto
    qed .

    have accept_from_notNone:"\<And>n. \<exists>k\<ge>n. \<exists>p. r !! k = Some (p, Decr) \<and> Some (p, Decr) \<in> \<Delta>\<^sub>s\<^sub>l' (Rst nds !! k) (last (stake k r)) \<and> (last (stake k r)) \<noteq> None"
      subgoal for n
      using accept unfolding infs_snth
      apply-apply(erule allE[of _ "Suc n"], safe)
      subgoal for k p       using accept unfolding infs_snth
        apply-apply(erule allE[of _ "Suc k"], safe)
        subgoal for k' p' apply(intro exI[of _ k'] conjI exI[of _ p'])
          subgoal by auto
          subgoal by auto
          subgoal using run'[of k'] by auto
          subgoal using q\<^sub>0'_Decr[of k p "k'-1"] last_stake_i[of k' r] by auto . . . .


  obtain Ps where Ps:"Ps = fst (the (shd r)) ## smap (\<lambda>r. fst (the r)) r" by auto

  have PsK:"\<And>k. k>0 \<Longrightarrow> Ps !! k = fst(the (r !!(k - Suc 0)))" subgoal for k unfolding Ps by(drule list_swap[of k "(fst (the (shd r)))" r], simp) .

  show "\<exists>Ps. descentIpath nds Ps"
  apply(rule exI[of _ Ps], unfold descentIpath_iff_snth2, intro conjI)
  subgoal using accept_from_notNone[of "Suc 0"] apply safe
  subgoal for k p' a b apply(rule exI[of _ k], intro allI impI)
  subgoal for j proof(induct "j - k" arbitrary: j)
    case 0
    then have k:"k>0"  by auto
    hence last:"(last (stake k r)) = (r !! (k - 1))" using last_stake_i by auto
    also have j:"j>0" using 0 by auto
    show ?case using 0 unfolding last apply-apply(erule \<Delta>\<^sub>s\<^sub>l'_elim)
      using PsK[OF j] PsK[of "Suc j"] by auto
  next
    case (Suc x)
    hence jk:"j \<noteq> 0" "k \<noteq> 0" "j > 0" "k > 0" "0 < Suc j" by auto
    then obtain n where j:"j = Suc n" by (cases j, auto)
    then have n_gr:"n > 0" "k \<le> n" using Suc by auto
    also have k_le:"k \<le> j - 1" using n_gr j by auto
    have nth_stake_szip:"r !! j \<in> \<Delta>\<^sub>s\<^sub>l' (Rst nds !! j) (r !! (j-1))" using run'[of "j", unfolded last_stake_i[OF jk(3)]] jk by auto
    obtain a' b' where r_j_min:"(r !! (j-1)) = Some(a',b')" using q\<^sub>0'_Decr[of k p' "j-1", OF jk(4) Suc(4) k_le]  by auto
    show ?case
      subgoal using nth_stake_szip apply-apply(erule \<Delta>\<^sub>s\<^sub>l'_elim)
        subgoal for p s p' s' unfolding Rst_r PsK[OF jk(3)] PsK[OF jk(5)] by (cases s', auto)
        subgoal using r_j_min by auto
        subgoal using r_j_min by auto . .  
  qed . .
  apply(rule allI)
  subgoal for i using accept_from_notNone[of "Suc(Suc i)"] apply clarify
    subgoal for k p apply(rule exI[of _ "k"], intro conjI)
      subgoal by auto
      using Suc_diff_1[of k] last_stake_i[of k r] PsK[of k] PsK[of "k-1"]
      unfolding Rst_r Ps apply-apply(erule \<Delta>\<^sub>s\<^sub>l'_elim)
      by (auto,metis fst_eqD option.sel)  . . 
  qed
(*Converse*)
  fix Ps  

  {assume iDPath:"descentIpath nds Ps"
   have ev:"ev (alw (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr))) (nds ||| Ps)"and
      alw:"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) (nds||| Ps)"
     using iDPath[unfolded descentIpath_def2] by auto

   also have wf:"wfLabS nds Ps" using descentIpath_wfLabS[OF iDPath] by auto

   have hh:"\<And>x y z i. (stl x!!i, stl y!!i, stl z!!i) \<in>sset (x ||| y ||| z)" 
      by (metis snth_sset snth_szip stream.set_sel(2) szip.sel(2))
   define F\<^sub>s\<^sub>l where "F\<^sub>s\<^sub>l = (\<lambda>x' Ps' i. (if RR (x' !! i, Ps' !! i) (stl x' !! i, stl Ps' !! i) Decr then Decr else Main))"
   define Ss where "Ss = (\<lambda>x Ps. Main ## fToStream (F\<^sub>s\<^sub>l x Ps))"
   note Ss_defs = Ss_def F\<^sub>s\<^sub>l_def fToStream_def

   have Ss_i:"\<And>k m. m < Suc k \<Longrightarrow> (Ss (sdrop (Suc m) nds) (sdrop (Suc m) Ps) !! (Suc k - m)) = F\<^sub>s\<^sub>l nds Ps (Suc k)" using Suc_diff_le unfolding Ss_defs by auto

   obtain m where m:"(\<And>n. n\<ge>m \<Longrightarrow> (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Main \<or> RR (nd, P) (nd', P') Decr)) (sdrop n (nds ||| Ps)))"
     using ev  unfolding ev_alw_iff_sdrop by auto

   have "\<And>n. n\<ge>m \<Longrightarrow> (Rst nds !! n) (Ps !! n, Ps !! Suc n, Main) \<or> (Rst nds !! n) (Ps !! n, Ps !! Suc n, Decr)"
     subgoal for n by(drule m[of n], simp) .

  obtain i where i:"\<forall>j\<ge>i. Ps !! j \<in> PosOf (nds !! j)" using wf unfolding wfLabS_iff_snth by auto

  define m' where "m' = i + m" 
  hence m':"(\<And>n. n\<ge>m' \<longrightarrow> Ps !! n \<in> PosOf (nds !! n) \<and> ((Rst nds !! n) (Ps !! n, Ps !! Suc n, Main) \<or> (Rst nds !! n) (Ps !! n, Ps !! Suc n, Decr)))"
    using i m by auto

  have alw_dropm:"alw (ev (holds2 (\<lambda>(nd, P) (nd', P'). RR (nd, P) (nd', P') Decr))) (sdrop (Suc m') (nds ||| Ps))"
    using alw unfolding alw_ev_sdrop by auto


  define r where "r = replicate m' q\<^sub>0 @- smap Some ((sdrop (Suc m') Ps) ||| (Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps)))"

  have x_node':"\<And>i. nds !! i \<in> Node" using ipath unfolding ipath_def alw_holdsS_iff_snth by auto

  have r_eq_q\<^sub>0':"\<And>n. Suc n \<le> m' \<longleftrightarrow> r!!n = q\<^sub>0" 
    apply standard unfolding r_def
    subgoal using replicate_within_i by auto
    subgoal for n apply(rule ccontr, unfold not_le replicate_beyond_i) using x_node'[of "n"]  by auto .


  have r_neq_q\<^sub>0':"\<And>n. Suc n > m' \<longleftrightarrow> r!!n = Some (Ps !! Suc n, Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps) !! (n-m'))" 
    apply standard
    subgoal unfolding r_def using replicate_beyond_i by auto 
    subgoal for n using r_eq_q\<^sub>0'[of n] by auto .


  have Rst_all:"\<And>k. (Rst nds !!k) \<in> \<Sigma>" using k_edge unfolding Rst_r by auto

  have Psk_node:"\<And>k. Ps !! k \<in> PosOf (nds !! k) \<Longrightarrow> \<exists>x\<in>Node. Ps !! k \<in> PosOf x"
    using x_node' by auto
  have m'_inQ'\<^sub>s\<^sub>l:"\<And>k x. k\<ge> m' \<Longrightarrow> (Ps !! k, x) \<in> Q'\<^sub>s\<^sub>l"
    unfolding Q'\<^sub>s\<^sub>l_def using Psk_node  m' by auto


  have m_eq:"\<And>k m. Suc k \<le> m \<Longrightarrow> m < Suc (Suc k) \<Longrightarrow> m = Suc k" by auto
  have Psn_gr:"\<And>n. Suc n > m' \<Longrightarrow> Ps !! (Suc n) = fst (the (r !! n))" using r_neq_q\<^sub>0' by auto
  have Ssn_gr:"\<And>n. Suc n > m' \<Longrightarrow> snd (the (r !! n)) = Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps) !! (n-m')" using r_neq_q\<^sub>0' by auto


  show"Rst nds \<in> NBA.language Taut\<^sub>R" 
  proof(rule nba.language[of q\<^sub>0 Taut\<^sub>R  _ r], unfold Taut\<^sub>R_accept Taut\<^sub>R_initp, safe)
    show "NBA.run Taut\<^sub>R (Rst nds ||| r) q\<^sub>0" 
    proof(unfold run_def', intro allI conjI) 
      fix k 
      show "Rst nds !! k \<in> \<Sigma>" using Rst_all by auto
  
      show "r !! k \<in> \<Delta>\<^sub>s\<^sub>l' (Rst nds !! k) (last (None # map snd (stake k (Rst nds ||| r))))"
      proof(induct k)
        case 0
        have l:"(last (None # map snd (stake 0 (Rst nds ||| r))))  = None" by auto
        show ?case unfolding l 
          apply(cases m')
          subgoal apply(rule ssubst[of "r !!0" "Some (Ps !! (Suc 0), Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps) !! 0)"])
            subgoal  using r_neq_q\<^sub>0'[of 0] by auto
            subgoal apply(rule \<Delta>\<^sub>s\<^sub>l'_intro_q0)
              subgoal using Rst_all[of 0] by auto
              subgoal using m'_inQ'\<^sub>s\<^sub>l[of "Suc 0"] by auto . . 
          subgoal apply(rule ssubst[of "r !!0" None]) 
            subgoal using r_eq_q\<^sub>0'[of 0] by auto
            apply(rule \<Delta>\<^sub>s\<^sub>l'_q0_included) using Rst_all[of 0] by auto .
      next
        case (Suc k)
        then show ?case unfolding last_stake_szip apply-apply(erule \<Delta>\<^sub>s\<^sub>l'_elim)
         (*\<Delta>\<^sub>s\<^sub>l' 3*)       
          subgoal for p s p' s'  apply(rule \<Delta>\<^sub>s\<^sub>l'_intro)
            subgoal using Rst_all[of "Suc k"] by auto
            subgoal apply(intro exI2[of _ "Ps !! Suc (Suc k)" "Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps) !! (Suc k - m')"] conjI)
              subgoal using r_eq_q\<^sub>0'[of k] r_neq_q\<^sub>0'[of "Suc k"] by auto
              subgoal using Psn_gr[of k] r_eq_q\<^sub>0'[of k] m'_inQ'\<^sub>s\<^sub>l[of "Suc k"] by auto
              subgoal using  m'[of "Suc k"] r_eq_q\<^sub>0'[of k] Ss_i Psn_gr unfolding F\<^sub>s\<^sub>l_def by auto .
            subgoal by auto .
          (*\<Delta>\<^sub>s\<^sub>l' 2*)   
          subgoal for p s apply(rule \<Delta>\<^sub>s\<^sub>l'_intro)
            subgoal using Rst_all[of "Suc k"] by auto
            subgoal apply(rule exI[of _ "Ps !! Suc (Suc k)"], intro exI[of _ "Ss (sdrop (Suc m') nds) (sdrop (Suc m') Ps) !! (Suc k - m')"] conjI)
              subgoal using r_eq_q\<^sub>0'[of k] r_neq_q\<^sub>0'[of "Suc k"] by auto
              subgoal by auto
              subgoal using  m'[of "Suc k"] r_eq_q\<^sub>0'[of k] Ss_i Psn_gr unfolding F\<^sub>s\<^sub>l_def by auto .
            subgoal by auto .
          (*\<Delta>\<^sub>s\<^sub>l' 1*)   
          subgoal apply(rule \<Delta>\<^sub>s\<^sub>l'_intro)
            subgoal using Rst_all[of "Suc k"] by auto
            subgoal by auto
            subgoal using le_less_linear[of "Suc (Suc k)" m'] apply-apply(erule disjE)
              subgoal using r_eq_q\<^sub>0'[of "Suc k"] by auto 
              subgoal using r_neq_q\<^sub>0'[of "Suc k"] m'_inQ'\<^sub>s\<^sub>l[of "Suc (Suc k)"] by auto . . .
      qed
    qed

    show "infs (\<lambda>ps. \<exists>p. ps = Some (p, Decr) \<and> (p, Decr) \<in> Q'\<^sub>s\<^sub>l) r"
      unfolding r_def alw_ev_shift infs_snth apply(clarify)
      subgoal for n using alw_dropm unfolding alw_ev_holds2_iff_snth
        apply-apply(erule allE[of _ "n + i"], clarify)
        subgoal for j x y xa ya apply(intro exI[of _ "Suc j"] conjI)
          subgoal by auto
          subgoal apply(intro exI[of _ ya] conjI)
            subgoal unfolding Ss_defs by auto
            subgoal using i RR_PosOfD' unfolding Q'\<^sub>s\<^sub>l_def by fastforce . . . .
  qed}
qed

(*Trivial auxillary results required*)
lemma alpha_subseq_PTaut\<^sub>R: "nba.alphabet Paut\<^sub>R \<subseteq> nba.alphabet Taut\<^sub>R" by simp
(*PATH AUTO FINITE NODES*)

lemma Paut\<^sub>R_subseq_rule:"(\<And>r. \<forall>x\<in>Node. last (map snd r) \<noteq> Some x \<Longrightarrow>
         r \<noteq> [] \<Longrightarrow> NBA.path Paut\<^sub>R r None \<Longrightarrow> last (map snd r) = None) \<Longrightarrow>
(\<Union>p\<in>{p. p \<in> nba.initial Paut\<^sub>R}. {last (p # map snd r) |r. NBA.path Paut\<^sub>R r p})
    \<subseteq> {r. r = None \<or> (\<exists>x\<in>Node. r = Some x)}" by auto


lemma Paut\<^sub>R_node_subseq:"NBA.nodes Paut\<^sub>R \<subseteq> {r. r = None \<or> (\<exists>x\<in> Node. r = Some x)}" 
  unfolding nba.nodes_alt_def nba.reachable_alt_def nba.target_alt_def nba.states_alt_def 
  apply(rule Paut\<^sub>R_subseq_rule)
  subgoal premises p for r using p(3,1-2) apply(induct rule: nba.path.induct)
    subgoal by auto
    subgoal for a p by (cases p,  auto simp: RR_PosOfD' split: if_splits) . . 


lemma finite_Nodes_Paut\<^sub>R:"finite (NBA.nodes Paut\<^sub>R)" 
  apply(rule rev_finite_subset[OF _ Paut\<^sub>R_node_subseq]) using finite_Node_opt by auto 

(*TRACE AUTO FINITE NODES*)

lemma Taut\<^sub>R_subseq_rule:"(\<And>r.  \<forall>a. (\<forall>x\<in>Node. a \<notin> PosOf x) \<or> (\<forall>b. last (map snd r) \<noteq> Some (a, b)) \<Longrightarrow>
         r \<noteq> [] \<Longrightarrow> NBA.path Taut\<^sub>R r None \<Longrightarrow> last (map snd r) = None)
  \<Longrightarrow> (\<Union>p\<in>{p. p \<in> nba.initial Taut\<^sub>R}. {last (p # map snd r) |r. NBA.path Taut\<^sub>R r p})
    \<subseteq> {r. r = None \<or> (\<exists>x\<in>{(p, s)| p s. p \<in> (\<Union>v\<in>Node. PosOf v)}. r = Some x)}" by auto


(*Theorem 5.4*)
theorem SLA_Criterion:"InfiniteDescent \<longleftrightarrow> NBA.language Paut\<^sub>R \<subseteq> NBA.language Taut\<^sub>R"
  apply standard
  subgoal unfolding subset_iff Paut\<^sub>R_lang_in InfiniteDescent_def apply clarify
    subgoal for Ri nds apply(erule allE[of _ nds], safe)
      by(drule Taut\<^sub>R_lang_in,unfold Rst_correct[of Ri nds,symmetric], auto) . 
  subgoal unfolding InfiniteDescent_def apply(clarify)
    subgoal for nds 
      apply(unfold subset_iff Paut\<^sub>R_lang_in)
      by(erule allE[of _ "Rst nds"], unfold Taut\<^sub>R_lang_in, auto) . .

end
end