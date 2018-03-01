section "A Theory of Blackboard Architectures"
text{*
  In the following, we formalize the specification of the blackboard pattern as described in~\cite{Marmsoler2018c}.
*}

theory Blackboard
imports Publisher_Subscriber
begin

subsection "Problems and Solutions"
text {*
  Blackboards work with problems and solutions for them.
*}
typedecl PROB
consts sb :: "(PROB \<times> PROB) set"
axiomatization where sbWF: "wf sb"
typedecl SOL
consts solve:: "PROB \<Rightarrow> SOL"

subsection "Blackboard Architectures"
text {*
  In the following, we describe the locale for the blackboard pattern.
*}
locale blackboard = publisher_subscriber bbactive bbcmp ksactive kscmp bbrp bbcs kscs ksrp
  for bbactive :: "'bid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and bbcmp :: "'bid \<Rightarrow> cnf \<Rightarrow> 'BB" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and ksactive :: "'kid \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and kscmp :: "'kid \<Rightarrow> cnf \<Rightarrow> 'KS" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and bbrp :: "'BB \<Rightarrow> ('kid, PROB set) subscription set"
    and bbcs :: "'BB \<Rightarrow> (PROB \<times> SOL) set"
    and kscs :: "'KS \<Rightarrow> (PROB \<times> SOL) set"
    and ksrp :: "'KS \<Rightarrow> ('kid, PROB set) subscription" +
  fixes bbns :: "'BB \<Rightarrow> (PROB \<times> SOL) set"
    and ksns :: "'KS \<Rightarrow> (PROB \<times> SOL) set"
    and bbop :: "'BB \<Rightarrow> PROB set"            
    and ksop :: "'KS \<Rightarrow> PROB set"
    and prob :: "'kid \<Rightarrow> PROB"
  assumes
    ks1: "\<forall>p. \<exists>ks. p=prob ks" --"Component Parameter"
    -- "Assertions about component behavior."
    and bhvbb1: "\<And>t t' bId p s. \<lbrakk>t \<in> arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (pb.glob (pb.ass (\<lambda>bb. (p,s)\<in>bbns bb)
      \<longrightarrow>\<^sup>p (pb.evt (pb.ass (\<lambda>bb. (p,s) \<in> bbcs bb)))))"
    and bhvbb2: "\<And>t t' bId kId P q. \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (pb.glob (pb.ass (\<lambda>bb. sub kId P \<in> bbrp bb \<and> q \<in> P) \<longrightarrow>\<^sup>p
      (pb.evt (pb.ass (\<lambda>bb. q \<in> bbop bb)))))"
    and bhvbb3: "\<And>t t' bId p . \<lbrakk>t\<in>arch\<rbrakk> \<Longrightarrow> pb.eval bId t t' 0
      (pb.glob (pb.ass (\<lambda>bb. p \<in> bbop(bb)) \<longrightarrow>\<^sup>p
      (pb.wuntil (pb.ass (\<lambda>bb. p\<in>bbop(bb))) (pb.ass (\<lambda>bb. (p,solve(p))\<in>bbcs(bb))))))"
    and bhvks1: "\<And>t t' kId p P. \<lbrakk>t\<in>arch; p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (sb.glob ((sb.ass (\<lambda>ks. sub kId P = ksrp ks)) \<and>\<^sup>s
      (sb.all (\<lambda>q. (sb.pred (q\<in>P)) \<longrightarrow>\<^sup>s (sb.evt (sb.ass (\<lambda>ks. (q,solve(q)) \<in> kscs ks)))))
      \<longrightarrow>\<^sup>s (sb.evt (sb.ass (\<lambda>ks. (p, solve p) \<in> ksns ks)))))"
    and bhvks2: "\<And>t t' kId p P q. \<lbrakk>t \<in> arch;p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (sb.glob (sb.ass (\<lambda>ks. sub kId P = ksrp ks \<and> q \<in> P \<longrightarrow> (q,p) \<in> sb)))"
    and bhvks3: "\<And>t t' kId p. \<lbrakk>t\<in>arch;p = prob kId\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (sb.glob ((sb.ass (\<lambda>ks. p\<in>ksop ks)) \<longrightarrow>\<^sup>s (sb.evt (sb.ass (\<lambda>ks. (\<exists>P. sub kId P = ksrp ks))))))"
    and bhvks4: "\<And>t t' kId p P. \<lbrakk>t\<in>arch; p\<in>P\<rbrakk> \<Longrightarrow> sb.eval kId t t' 0
      (sb.glob ((sb.ass (\<lambda>ks. sub kId P = ksrp ks)) \<longrightarrow>\<^sup>s
      (sb.wuntil (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p\<in>P') \<and>\<^sup>s (sb.ass (\<lambda>ks. unsub kId P' = ksrp ks)))))
      (sb.ass (\<lambda>ks. (p,solve p) \<in> kscs ks)))))"

    -- "Assertions about component activation."
    and actks:
      "\<And>t n kid p. \<lbrakk>t \<in> arch; ksactive kid (t n); p=prob kid; p\<in>ksop (kscmp kid (t n))\<rbrakk>
      \<Longrightarrow> (\<exists>n'\<ge>n. ksactive kid (t n') \<and> (p, solve p) \<in> ksns (kscmp kid (t n')) \<and>
      (\<forall>n''\<ge>n. n''<n' \<longrightarrow> ksactive kid (t n'')))
      \<or> (\<forall>n'\<ge>n. (ksactive kid (t n') \<and> (\<not>(p, solve p) \<in> ksns (kscmp kid (t n')))))"

    -- "Assertions about connections."
    and conn1: "\<And>k bid. bbactive bid k
      \<Longrightarrow> bbns (bbcmp bid k) = (\<Union>kid\<in>{kid. ksactive kid k}. ksns (kscmp kid k))"
    and conn2: "\<And>k kid. ksactive kid k
      \<Longrightarrow> ksop (kscmp kid k) = (\<Union>bid\<in>{bid. bbactive bid k}. bbop (bbcmp bid k))"
begin
  notation pb.lNAct ("\<langle>_ \<leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  notation pb.nxtAct ("\<langle>_ \<rightarrow> _\<rangle>\<^bsub>_\<^esub>")

  subsubsection "The Blackboard Component"
  text {*
    In the following we introduce an abbreviation for the unique blackboard component.
  *}
  abbreviation "the_bb \<equiv> pb.the_singleton"

  subsubsection "Knowledge Sources"
  text {*
    In the following we introduce an abbreviation for knowledge sources which are able to solve a specific problem.
  *}
  definition sKs:: "PROB \<Rightarrow> 'kid" where
    "sKs p \<equiv> (SOME kid. p = prob kid)"

  lemma sks_prob:
    "p = prob (sKs p)"
  using sKs_def someI_ex[of "\<lambda>kid. p = prob kid"] ks1 by auto

  subsubsection "Verifying Blackboards"
  text{*
    The following theorem verifies that a problem is eventually solved by the pattern even if no knowledge source exist which can solve the problem on its own.
    It assumes, however, that for every open sub problem, a corresponding knowledge source able to solve the problem will be eventually activated.
  *}
  theorem pSolved:
    fixes t and t'::"nat \<Rightarrow>'BB" and p and t''::"nat \<Rightarrow>'KS"
    assumes "t\<in>arch" and
      "\<forall>n. \<forall>p\<in>bbop(bbcmp the_bb (t n)).
        \<exists>n'\<ge>n. ksactive (sKs p) (t n')"
    shows
      "\<forall>n. p\<in>bbop(bbcmp the_bb (t n)) \<longrightarrow>
        (\<exists>m\<ge>n. (p,solve(p)) \<in> bbcs (bbcmp the_bb (t m)))" (*\eqref{eq:bb:g}*)
  -- "The proof is by well-founded induction over the subproblem relation @{term sb}"
  proof (rule wf_induct[where r=sb])
    -- "We first show that the subproblem relation is indeed well-founded ..."
    show "wf sb" by (simp add: sbWF)
  next
    -- "... then we show that a problem @{term p} is indeed solved"
    -- "if all its sub-problems @{term p'} are eventually solved"
    fix p assume indH: "\<forall>p'. (p', p) \<in> sb \<longrightarrow> (\<forall>n. (p' \<in> bbop (bbcmp the_bb (t n))
      \<longrightarrow> (\<exists>m\<ge>n. (p',solve(p')) \<in> bbcs (bbcmp the_bb (t m)))))"
    show "\<forall>n. p \<in> bbop (bbcmp the_bb (t n))
      \<longrightarrow> (\<exists>m\<ge>n. (p,solve(p)) \<in> bbcs (bbcmp the_bb (t m)))"
    proof
      fix n show "p \<in> bbop (bbcmp the_bb (t n)) \<longrightarrow>
      (\<exists>m\<ge>n. (p,solve(p)) \<in> bbcs (bbcmp the_bb (t m)))"
      proof
        assume "p \<in> bbop (bbcmp the_bb (t n))"
        
        -- "Problem p is provided at the output of the blackboard until it is solved"
        -- "or forever..."
        from pb.globE[OF bhvbb3] have
          "pb.eval the_bb t t' n (pb.ass (\<lambda> bb. p \<in> bbop(bb)) \<longrightarrow>\<^sup>p
          (pb.wuntil (pb.ass (\<lambda> bb. p\<in>bbop(bb)))
          (pb.ass (\<lambda>bb. (p,solve(p))\<in>bbcs(bb)))))"
          using `t\<in>arch` by auto
        moreover from `p \<in> bbop (bbcmp the_bb (t n))` have
          "pb.eval the_bb t t' n (pb.ass (\<lambda> bb. p\<in>bbop bb))"
          using `t\<in>arch` pb.assI by simp
        ultimately have "pb.eval the_bb t t' n
          (pb.wuntil (pb.ass (\<lambda> bb. p\<in>bbop(bb)))
          (pb.ass (\<lambda> bb. (p,solve(p))\<in>bbcs(bb))))"
          using pb.impE by blast
        hence "pb.eval the_bb t t' n ((pb.until (pb.ass (\<lambda> bb. p\<in>bbop bb))
          (pb.ass (\<lambda> bb. (p,solve(p))\<in>bbcs bb))) \<or>\<^sup>p (pb.glob (pb.ass (\<lambda> bb. p\<in>bbop bb))))"
          using pb.wuntil_def by simp
        hence "pb.eval the_bb t t' n
          (pb.until (pb.ass (\<lambda>bb. p\<in>bbop bb))
            (pb.ass (\<lambda>bb. (p,solve(p))\<in>bbcs bb))) \<or>
          (pb.eval the_bb t t' n (pb.glob (pb.ass (\<lambda> bb. p\<in>bbop bb))))"
          using pb.orE by simp
        thus "\<exists>m\<ge>n. (p,solve p) \<in> bbcs(bbcmp the_bb (t m))"
        -- "We need to consider both cases, the case in which the problem is eventually"
        -- "solved and the case in which the problem is always provided as an output"
        proof
          -- "First we consider the case in which the problem is eventually solved:"
          assume "pb.eval the_bb t t' n
            (pb.until (pb.ass (\<lambda>bb. p\<in>bbop bb))
            (pb.ass (\<lambda>bb. (p,solve(p))\<in>bbcs bb)))"
          hence "\<exists>i\<ge>n. (pb.eval the_bb t t' i
            (pb.ass (\<lambda>bb. (p,solve(p)) \<in> bbcs bb)) \<and>
            (\<forall>k\<ge>n. k<i \<longrightarrow> pb.eval the_bb t t' k (pb.ass (\<lambda> bb. p \<in> bbop bb))))"
            using `t\<in>arch` pb.untilE by simp
          then obtain i where "i\<ge>n" and
            "pb.eval the_bb t t' i (pb.ass (\<lambda>bb. (p,solve(p)) \<in> bbcs bb))" by auto
          hence "(p,solve(p))\<in>bbcs(bbcmp the_bb (t i))"
            using `t\<in>arch` pb.assEA by auto
          thus ?thesis using `i\<ge>n` by auto
        next
          -- "Now we consider the case in which p is always provided at the output"
          -- "of the blackboard:"
          assume "pb.eval the_bb t t' n
            (pb.glob (pb.ass (\<lambda>bb. p\<in>bbop bb)))"
          hence "\<forall>n'\<ge>n. (pb.eval the_bb t t' n' (pb.ass (\<lambda>bb. p \<in> bbop bb)))"
            using `t\<in>arch` pb.globE by auto
          hence outp: "\<forall>n'\<ge>n. (p \<in> bbop (bbcmp the_bb (t n')))"
            using `t\<in>arch` pb.assE by blast
  
          -- "thus, by assumption there exists a KS which is able to solve p and which"
          -- "is active at @{text n'}..."
          from assms(2) have "\<exists>n'\<ge>n. ksactive (sKs p) (t n')" using outp by auto
          then obtain n\<^sub>k where "n\<^sub>k\<ge>n" and "ksactive (sKs p) (t n\<^sub>k)" by auto
          -- "... and get the problem as its input."
          moreover from `n\<^sub>k\<ge>n` have "p \<in> bbop (bbcmp the_bb (t n\<^sub>k))"
            using outp by simp
          ultimately have "p\<in>ksop(kscmp (sKs p) (t n\<^sub>k))" using conn2[of "sKs p" "t n\<^sub>k"]
            by auto
  
          -- "thus the ks will either solve the problem or not solve it and"
          -- "be activated forever"
          hence "(\<exists>n'\<ge>n\<^sub>k. ksactive (sKs p) (t n') \<and>
            (p, solve p) \<in> ksns (kscmp (sKs p) (t n')) \<and>
            (\<forall>n''\<ge>n\<^sub>k. n''<n' \<longrightarrow> ksactive (sKs p) (t n''))) \<or>
            (\<forall>n'\<ge>n\<^sub>k. (ksactive (sKs p) (t n') \<and>
            (\<not>(p, solve p) \<in> ksns (kscmp (sKs p) (t n')))))"
            using `ksactive (sKs p) (t n\<^sub>k)` actks[of t "sKs p"] `t\<in>arch` sks_prob by simp
          thus ?thesis
          proof
            -- "if the ks solves it"
            assume "\<exists>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and> (p, solve p) \<in> ksns (\<sigma>\<^bsub>sKs p\<^esub>t n')
              \<and> (\<forall>n''\<ge>n\<^sub>k. n'' < n' \<longrightarrow> \<parallel>sKs p\<parallel>\<^bsub>t n''\<^esub>)"
            -- "it is forwarded to the blackboard"
            then obtain n\<^sub>s where "n\<^sub>s\<ge>n\<^sub>k" and "\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>"
              and "(p, solve p) \<in> ksns (\<sigma>\<^bsub>sKs p\<^esub>t n\<^sub>s)" by auto
            moreover have "sb.nxtAct (sKs p) t n\<^sub>s = n\<^sub>s"
              by (simp add: `\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>` sb.nxtAct_active)
            ultimately have
              "(p,solve(p)) \<in> bbns (bbcmp the_bb (t (sb.nxtAct (sKs p) t n\<^sub>s)))"
              using conn1[OF pb.the_active] `\<parallel>sKs p\<parallel>\<^bsub>t n\<^sub>s\<^esub>` by auto
   
            -- "finally, the blackboard will forward the solution which finishes the proof."
            with bhvbb1 have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>s)
              (pb.evt (pb.ass (\<lambda>bb. (p, solve p) \<in> bbcs bb)))"
              using `t\<in>arch` pb.globE pb.impE[of the_bb t t'] by blast
            then obtain n\<^sub>f where "n\<^sub>f\<ge>sb.nxtAct (sKs p) t n\<^sub>s" and
              "pb.eval the_bb t t' n\<^sub>f (pb.ass (\<lambda>bb. (p, solve p) \<in> bbcs bb))"
              using `t\<in>arch` pb.evtE[of t t' "sb.nxtAct (sKs p) t n\<^sub>s"] by auto
            hence "(p, solve p) \<in> bbcs (bbcmp the_bb (t n\<^sub>f))"
              using `t \<in> arch` pb.assEA by auto
            moreover have "n\<^sub>f\<ge>n"
            proof -
              from `ksactive (sKs p) (t n\<^sub>k)` have "sb.nxtAct (sKs p) t n\<^sub>k\<ge>n\<^sub>k"
                using sb.nxtActI by blast
              with `sb.nxtAct (sKs p) t n\<^sub>s = n\<^sub>s` show ?thesis
                using `n\<^sub>f\<ge>sb.nxtAct (sKs p) t n\<^sub>s` `n\<^sub>s\<ge>n\<^sub>k` `n\<^sub>k\<ge>n` by arith
            qed
            ultimately show ?thesis by auto
          next
            -- "otherwise, we derive a contradiction"
            assume case_ass: "\<forall>n'\<ge>n\<^sub>k. \<parallel>sKs p\<parallel>\<^bsub>t n'\<^esub> \<and> \<not>(p, solve p) \<in> ksns (\<sigma>\<^bsub>sKs p\<^esub>t n')"

            -- "first, the KS will eventually register for the subproblems P it requires to solve p..."
            from `ksactive (sKs p) (t n\<^sub>k)` have "\<exists>i\<ge>0. ksactive (sKs p) (t i)" by auto
            moreover have "sb.lNAct (sKs p) t 0 \<le> n\<^sub>k" by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>k
              ((sb.ass (\<lambda>ks. p\<in>ksop ks)) \<longrightarrow>\<^sup>s
              (sb.evt (sb.ass (\<lambda>ks. \<exists>P. sub (sKs p) P = ksrp ks))))"
              using sb.globEA[OF _ bhvks3[of t p "sKs p" t'']] `t\<in>arch` sks_prob by simp
            moreover have "sb.eval (sKs p) t t'' n\<^sub>k (sb.ass (\<lambda>ks. p \<in> ksop ks))"
            proof -
              from `ksactive (sKs p) (t n\<^sub>k)` have "\<exists>n'\<ge>n\<^sub>k. ksactive (sKs p) (t n')" by auto
              moreover have "p \<in> ksop (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>k)))"
              proof -
                from `ksactive (sKs p) (t n\<^sub>k)` have "sb.nxtAct (sKs p) t n\<^sub>k=n\<^sub>k"
                  using sb.nxtAct_active by blast
                with `p\<in>ksop(kscmp (sKs p) (t n\<^sub>k))` show ?thesis by simp
              qed
              ultimately show ?thesis using sb.assIA[of n\<^sub>k "sKs p" t] by blast
            qed
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>k (sb.evt (sb.ass (\<lambda>ks. \<exists>P. sub (sKs p) P = ksrp ks)))"
              using sb.impE by blast
            then obtain n\<^sub>r where "n\<^sub>r\<ge>sb.nxtAct (sKs p) t n\<^sub>k" and
              "\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i) \<and>
              (\<forall>n''\<ge>sb.lNAct (sKs p) t n\<^sub>r. n'' \<le> sb.nxtAct (sKs p) t n\<^sub>r
              \<longrightarrow> sb.eval (sKs p) t t'' n'' (sb.ass (\<lambda>ks. \<exists>P. sub (sKs p) P = ksrp ks))) \<or>
              \<not> (\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)) \<and>
              sb.eval (sKs p) t t'' n\<^sub>r (sb.ass (\<lambda>ks. \<exists>P. sub (sKs p) P = ksrp ks))"
              using `ksactive (sKs p) (t n\<^sub>k)` sb.evtEA[of n\<^sub>k "sKs p" t] by blast
            moreover from case_ass have "sb.nxtAct (sKs p) t n\<^sub>k\<ge>n\<^sub>k" using sb.nxtActI by blast
            with `n\<^sub>r\<ge>sb.nxtAct (sKs p) t n\<^sub>k` have "n\<^sub>r\<ge>n\<^sub>k" by arith
            hence "\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)" using case_ass by auto
            hence "n\<^sub>r \<le> sb.nxtAct (sKs p) t n\<^sub>r" using sb.nxtActLe by simp           
            moreover have "n\<^sub>r \<ge> sb.lNAct (sKs p) t n\<^sub>r" by simp
            ultimately have
              "sb.eval (sKs p) t t'' n\<^sub>r (sb.ass (\<lambda>ks. \<exists>P. sub (sKs p) P = ksrp ks))" by blast
            with `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` obtain P where
              "sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r)))"
              using sb.assEA by blast
            hence "sb.eval (sKs p) t t'' n\<^sub>r (sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks))"
              using `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` sb.assIA sks_prob by blast
            
            -- "the knowledgesource will eventually get a solution for each required subproblem:"
            moreover have "sb.eval (sKs p) t t'' n\<^sub>r (sb.all (\<lambda> p'. sb.pred (p'\<in>P) \<longrightarrow>\<^sup>s
              (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks)))))"
            proof -
              have "\<forall>p'. sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P) \<longrightarrow>\<^sup>s
                (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
              proof
                -- "by induction hypothesis, the blackboard will eventually provide solutions for subproblems"  
                fix p'
                have "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P)) \<longrightarrow>
                  (sb.eval (sKs p) t t'' n\<^sub>r
                  (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
                proof
                  assume "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P))"
                  hence "p' \<in> P" using sb.predE by blast
                  thus "(sb.eval (sKs p) t t'' n\<^sub>r (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
                  proof -
                    have "sb.lNAct (sKs p) t 0 \<le> n\<^sub>r" by simp
                    moreover from `ksactive (sKs p) (t n\<^sub>k)` have "\<exists>i\<ge>0. ksactive (sKs p) (t i)" by auto
                    ultimately have "sb.eval (sKs p) t t'' n\<^sub>r ((sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks))
                      \<longrightarrow>\<^sup>s (sb.wuntil (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s
                      (sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks)))))
                      (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
                      using sb.globEA[OF _ bhvks4[of t p' P "sKs p" t'']]
                      `t\<in>arch` `ksactive (sKs p) (t n\<^sub>k)` `p'\<in>P` by simp
                    with `sb.eval (sKs p) t t'' n\<^sub>r (sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks))` have
                      "sb.eval (sKs p) t t'' n\<^sub>r (sb.wuntil (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s
                      (sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))))) (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks)))"
                      using sb.impE[of "(sKs p)" t t'' n\<^sub>r "sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks)"] by blast
                    hence "sb.eval (sKs p) t t'' n\<^sub>r (sb.until (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s
                      (sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))))) (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))) \<or>
                      sb.eval (sKs p) t t'' n\<^sub>r (sb.glob (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s
                      sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks)))))" using sb.wuntil_def by auto
                    thus "(sb.eval (sKs p) t t'' n\<^sub>r (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
                    proof
                      let ?\<gamma>'="\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s (sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))))"
                      let ?\<gamma>="sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks)"
                      assume "sb.eval (sKs p) t t'' n\<^sub>r (sb.until ?\<gamma>' ?\<gamma>)"
                      with `\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>` obtain n' where "n'\<ge>sb.nxtAct (sKs p) t n\<^sub>r" and
                        lass: "(\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and> (\<forall>n''\<ge>sb.lNAct (sKs p) t n'. n'' \<le> sb.nxtAct (sKs p) t n'
                        \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>) \<and>
                        (\<forall>n''\<ge>sb.lNAct (sKs p) t n\<^sub>r. n'' < sb.lNAct (sKs p) t n'
                        \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>') \<or>
                        \<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>) \<and> sb.eval (sKs p) t t'' n' ?\<gamma> \<and>
                        (\<forall>n''\<ge>sb.lNAct (sKs p) t n\<^sub>r. n'' < n' \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>')"
                        using sb.untilEA[of n\<^sub>r "sKs p" t t''] `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` by blast
                      thus "?thesis"
                      proof cases
                        assume "\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>"
                        with lass have "\<forall>n''\<ge>sb.lNAct (sKs p) t n'. n'' \<le> sb.nxtAct (sKs p) t n'
                          \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>" by auto
                        moreover have "n'\<ge>sb.lNAct (sKs p) t n'" by simp
                        moreover have "n' \<le> sb.nxtAct (sKs p) t n'"
                          using \<open>\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>\<close> sb.nxtActLe by simp
                        ultimately have "sb.eval (sKs p) t t'' n' ?\<gamma>" by simp
                        moreover have "sb.lNAct (sKs p) t n\<^sub>r \<le> n'" using \<open>n\<^sub>r \<le> sb.nxtAct (sKs p) t n\<^sub>r\<close>
                        \<open>sb.lNAct (sKs p) t n\<^sub>r \<le> n\<^sub>r\<close> \<open>sb.nxtAct (sKs p) t n\<^sub>r \<le> n'\<close> by linarith
                        ultimately show ?thesis using `\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>` `\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>`
                          `n'\<ge>sb.lNAct (sKs p) t n'` `n' \<le> sb.nxtAct (sKs p) t n'`
                          sb.evtIA[of n\<^sub>r "sKs p" t n' t'' ?\<gamma>] by blast
                      next
                        assume "\<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>)"
                        with lass have "sb.eval (sKs p) t t'' n' ?\<gamma> \<and>
                          (\<forall>n''\<ge>sb.lNAct (sKs p) t n\<^sub>r. n'' < n' \<longrightarrow> sb.eval (sKs p) t t'' n'' ?\<gamma>')" by auto
                        moreover have "sb.lNAct (sKs p) t n\<^sub>r \<le> n'"
                          using \<open>n\<^sub>r \<le> sb.nxtAct (sKs p) t n\<^sub>r\<close> \<open>sb.lNAct (sKs p) t n\<^sub>r \<le> n\<^sub>r\<close>
                          \<open>sb.nxtAct (sKs p) t n\<^sub>r \<le> n'\<close> by linarith
                        ultimately show ?thesis using `\<exists>i\<ge>n\<^sub>r. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n'. \<parallel>sKs p\<parallel>\<^bsub>t i\<^esub>)`
                            sb.evtIA[of n\<^sub>r "sKs p" t n' t'' ?\<gamma>] by blast
                      qed                                     
                    next
                      assume cass: "sb.eval (sKs p) t t'' n\<^sub>r
                        (sb.glob (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P') \<and>\<^sup>s sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks)))))"

                      have "sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r))) \<and>
                        p' \<in> P \<longrightarrow> (p', p) \<in> sb"
                      proof -
                        have "\<exists>i\<ge>0. ksactive (sKs p) (t i)" using \<open>\<exists>i\<ge>0. ksactive (sKs p) (t i)\<close> by auto
                        moreover have "sb.lNAct (sKs p) t 0 \<le> (sb.nxtAct (sKs p) t n\<^sub>r)" by simp
                        ultimately have "sb.eval (sKs p) t t'' (sb.nxtAct (sKs p) t n\<^sub>r)
                          (sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks \<and> p' \<in> P \<longrightarrow> (p', p) \<in> sb))"
                          using sb.globEA[OF _ bhvks2[of t p "sKs p" t'' P]] `t \<in> arch` sks_prob by blast
                        moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` have
                          "ksactive (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r))" using sb.nxtActI by blast
                        ultimately show ?thesis
                          using sb.assEANow[of "sKs p" t t'' "sb.nxtAct (sKs p) t n\<^sub>r"] by simp
                      qed
                      with `p' \<in> P` have "(p', p) \<in> sb"
                        using `sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r)))`
                        sks_prob by simp
                      moreover have "\<exists>n\<^sub>p\<ge>(sb.nxtAct (sKs p) t n\<^sub>r).
                        pb.eval the_bb t t' n\<^sub>p (pb.ass (\<lambda>bb. p' \<in> bbop bb))"
                      proof -
                        from pb.globE[OF bhvbb2[of t "the_bb" t']]
                        have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>r)
                          (pb.ass (\<lambda>bb. sub (sKs p) P \<in> bbrp bb \<and> p' \<in> P) \<longrightarrow>\<^sup>p
                          (pb.evt (pb.ass (\<lambda>bb. p' \<in> bbop bb))))" using `t \<in> arch` by auto
                        moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` have
                          "ksactive (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r))" using sb.nxtActI by blast
                        with `sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r)))`
                          have "sub (sKs p) P \<in> bbrp (bbcmp the_bb (t (sb.nxtAct (sKs p) t n\<^sub>r)))"
                          using conn1A by auto
                        with `p' \<in> P` have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>r)
                          (pb.ass (\<lambda>bb. sub (sKs p) P \<in> bbrp bb \<and> p' \<in> P))" using `t \<in> arch`
                          pb.assIA[where \<phi>="\<lambda>bb. sub (sKs p) P \<in> bbrp bb \<and> p' \<in> P"] by blast
                        ultimately have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>r)
                          (pb.evt (pb.ass (\<lambda>bb. p' \<in> bbop bb)))" using pb.impE `p' \<in> P`
                          by blast
                        with `p' \<in> P` have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>r)
                          (pb.evt (pb.ass (\<lambda>bb. p' \<in> bbop bb)))" by simp
                        thus ?thesis using `t \<in> arch` pb.evtE[of t t' "sb.nxtAct (sKs p) t n\<^sub>r"]
                          by simp
                      qed                
                      then obtain "n\<^sub>p" where "n\<^sub>p \<ge> sb.nxtAct (sKs p) t n\<^sub>r" and
                        "pb.eval the_bb t t' n\<^sub>p (pb.ass (\<lambda>bb. p' \<in> bbop bb))" by auto
                      hence "p' \<in> bbop (bbcmp the_bb (t n\<^sub>p))" using `t \<in> arch` pb.assEA by auto
                      ultimately obtain m where "m\<ge>n\<^sub>p" and "(p', solve p') \<in> bbcs (bbcmp the_bb (t m))"
                        using indH by auto
            
                      -- "and due to the publisher subscriber property,"
                      -- "the knowledge source will receive them"
                      moreover have
                        "\<nexists>n P. sb.nxtAct (sKs p) t n\<^sub>r \<le> n \<and> n \<le> m \<and> ksactive (sKs p) (t n) \<and>
                        unsub (sKs p) P = ksrp (kscmp (sKs p) (t n)) \<and> p' \<in> P"
                      proof
                        assume "\<exists>n P'. sb.nxtAct (sKs p) t n\<^sub>r \<le> n \<and> n \<le> m \<and> ksactive (sKs p) (t n) \<and>
                          unsub (sKs p) P' = ksrp (kscmp (sKs p) (t n)) \<and> p' \<in> P'"
                        then obtain n P' where
                          "ksactive (sKs p) (t n)" and "sb.nxtAct (sKs p) t n\<^sub>r \<le> n" and "n \<le> m" and
                          "unsub (sKs p) P' = ksrp (kscmp (sKs p) (t n))" and "p' \<in> P'" by auto
                        hence "sb.eval (sKs p) t t'' n (\<exists>\<^sub>s P'. sb.pred (p'\<in>P') \<and>\<^sup>s
                          sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))" by blast
                        moreover have "sb.lNAct (sKs p) t n\<^sub>r \<le> n"
                          using \<open>n\<^sub>r \<le> sb.nxtAct (sKs p) t n\<^sub>r\<close> \<open>sb.lNAct (sKs p) t n\<^sub>r \<le> n\<^sub>r\<close>
                          \<open>sb.nxtAct (sKs p) t n\<^sub>r \<le> n\<close> by linarith
                        with cass have "sb.eval (sKs p) t t'' n (\<not>\<^sup>s (\<exists>\<^sub>s P'. (sb.pred (p'\<in>P')
                          \<and>\<^sup>s sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))))"
                          using sb.globEA[of n\<^sub>r "sKs p" t t''
                          "\<not>\<^sup>s (\<exists>\<^sub>sP'. sb.pred (p' \<in> P') \<and>\<^sup>s sb.ass (\<lambda>ks. unsub (sKs p) P' = ksrp ks))" n]
                          `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` by auto
                        ultimately show False using sb.notE by auto
                      qed
                      moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` have
                        "ksactive (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r))" using sb.nxtActI by blast
                      moreover have "sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r)))"
                        using `sub (sKs p) P = ksrp (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>r)))` .
                      moreover from `m\<ge>n\<^sub>p` `n\<^sub>p\<ge>sb.nxtAct (sKs p) t n\<^sub>r`
                        have "sb.nxtAct (sKs p) t n\<^sub>r \<le> m" by simp
                      moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` 
                        have "sb.nxtAct (sKs p) t n\<^sub>r\<ge>n\<^sub>r" using sb.nxtActI by blast
                      hence "m\<ge>n\<^sub>k" using `sb.nxtAct (sKs p) t n\<^sub>r \<le> m` \<open>sb.nxtAct (sKs p) t n\<^sub>k \<le> n\<^sub>r\<close>
                        `sb.nxtAct (sKs p) t n\<^sub>k \<ge> n\<^sub>k` by simp
                      with case_ass have "ksactive (sKs p) (t m)" by simp
                      ultimately have "(p', solve p') \<in> kscs (kscmp (sKs p) (t m))"
                        and "ksactive (sKs p) (t m)"
                        using `t \<in> arch` msgDelivery[of t "sKs p" "sb.nxtAct (sKs p) t n\<^sub>r" P m p' "solve p'"]
                        `p' \<in> P` by auto
                      hence "sb.eval (sKs p) t t'' m (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))"
                        using sb.assIANow by simp
                      moreover have "m \<ge> sb.lNAct (sKs p) t m" by simp
                      moreover from `ksactive (sKs p) (t m)` have "m \<le> sb.nxtAct (sKs p) t m"
                        using sb.nxtActLe by auto
                      moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` have
                        "sb.lNAct (sKs p) t n\<^sub>r \<le> sb.nxtAct (sKs p) t n\<^sub>r" by simp
                      with `sb.nxtAct (sKs p) t n\<^sub>r \<le> m` have "sb.lNAct (sKs p) t n\<^sub>r \<le> m" by arith
                      ultimately show "sb.eval (sKs p) t t'' n\<^sub>r
                        (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks)))"
                        using `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` sb.evtIA by blast
                    qed
                  qed
                qed
                thus "sb.eval (sKs p) t t'' n\<^sub>r (sb.pred (p'\<in>P) \<longrightarrow>\<^sup>s
                  (sb.evt (sb.ass (\<lambda>ks. (p',solve p') \<in> kscs ks))))"
                  using sb.impI by auto
              qed
              thus ?thesis using sb.allI by blast
            qed

            -- "Thus, the knowlege source will eventually solve the problem at hand..." 
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>r
              (sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks) \<and>\<^sup>s
              (\<forall>\<^sub>sq. (sb.pred (q \<in> P) \<longrightarrow>\<^sup>s sb.evt (sb.ass (\<lambda>ks. (q, solve q) \<in> kscs ks)))))"
              using sb.andI by simp
            moreover from `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` have "\<exists>i\<ge>0. ksactive (sKs p) (t i)" by blast
            hence "sb.eval (sKs p) t t'' n\<^sub>r
              ((sb.ass (\<lambda>ks. sub (sKs p) P = ksrp ks) \<and>\<^sup>s
              (\<forall>\<^sub>sq. (sb.pred (q \<in> P) \<longrightarrow>\<^sup>s
              sb.evt (sb.ass (\<lambda>ks. (q, solve q) \<in> kscs ks))))) \<longrightarrow>\<^sup>s
              (sb.evt (sb.ass (\<lambda>ks. (p, solve p) \<in> ksns ks))))" using `t \<in> arch`
              sb.globEA[OF _ bhvks1[of t p "sKs p" t'' P]] sks_prob by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>r
              (sb.evt (sb.ass (\<lambda>ks. (p,solve(p))\<in>ksns(ks))))"
              using sb.impE[of "sKs p" t t'' n\<^sub>r] by blast
    
            -- "and forward it to the blackboard"
            then obtain n\<^sub>s where "n\<^sub>s\<ge>sb.nxtAct (sKs p) t n\<^sub>r" and
              "(\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i) \<and>
              (\<forall>n''\<ge>sb.lNAct (sKs p) t n\<^sub>s. n'' \<le> sb.nxtAct (sKs p) t n\<^sub>s \<longrightarrow>
              sb.eval (sKs p) t t'' n'' (sb.ass (\<lambda>ks. (p,solve(p))\<in>ksns(ks))))) \<or>
              \<not> (\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i)) \<and>
              sb.eval (sKs p) t t'' n\<^sub>s (sb.ass (\<lambda>ks. (p,solve(p))\<in>ksns(ks)))"
              using sb.evtEA[of n\<^sub>r "sKs p" t] `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` by blast
            moreover from `sb.nxtAct (sKs p) t n\<^sub>r \<ge> n\<^sub>r` `n\<^sub>r\<ge>n\<^sub>k` `n\<^sub>s\<ge>sb.nxtAct (sKs p) t n\<^sub>r`
              have "n\<^sub>s\<ge>n\<^sub>k" by arith
            with case_ass have "\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i)" by auto
            moreover have "n\<^sub>s\<ge>sb.lNAct (sKs p) t n\<^sub>s" by simp
            moreover from `\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i)` have "n\<^sub>s \<le> sb.nxtAct (sKs p) t n\<^sub>s"
              using sb.nxtActLe by simp
            ultimately have "sb.eval (sKs p) t t'' n\<^sub>s (sb.ass (\<lambda>ks. (p,solve(p))\<in>ksns(ks)))"
              using sb.evtEA[of n\<^sub>r "sKs p" t] `\<exists>i\<ge>n\<^sub>r. ksactive (sKs p) (t i)` by blast
            with `\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i)` have
              "(p,solve(p)) \<in> ksns (kscmp (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>s)))"
              using sb.assEA[of n\<^sub>s "sKs p" t t'' "\<lambda>ks. (p, solve p) \<in> ksns ks"] by auto
            moreover from `\<exists>i\<ge>n\<^sub>s. ksactive (sKs p) (t i)`
              have "ksactive (sKs p) (t (sb.nxtAct (sKs p) t n\<^sub>s))" using sb.nxtActI by simp
            ultimately have "(p,solve(p)) \<in> bbns (bbcmp the_bb (t (sb.nxtAct (sKs p) t n\<^sub>s)))"
              using conn1[OF pb.the_active[of "t (sb.nxtAct (sKs p) t n\<^sub>s)"]] by auto
            hence "pb.eval the_bb t t'
              (sb.nxtAct (sKs p) t n\<^sub>s) (pb.ass (\<lambda>bb. (p,solve(p)) \<in> bbns bb))"
              using `t\<in>arch` pb.assI by simp
    
            -- "finally, the blackboard will forward the solution which finishes the proof."
            with bhvbb1 have "pb.eval the_bb t t' (sb.nxtAct (sKs p) t n\<^sub>s)
              (pb.evt (pb.ass (\<lambda>bb. (p, solve p) \<in> bbcs bb)))"
              using `t\<in>arch` pb.globE pb.impE[of the_bb t t'] by blast
            then obtain n\<^sub>f where "n\<^sub>f\<ge>sb.nxtAct (sKs p) t n\<^sub>s" and
              "pb.eval the_bb t t' n\<^sub>f (pb.ass (\<lambda>bb. (p, solve p) \<in> bbcs bb))"
              using `t\<in>arch` pb.evtE[of t t' "sb.nxtAct (sKs p) t n\<^sub>s"] by auto
            hence "(p, solve p) \<in> bbcs (bbcmp the_bb (t n\<^sub>f))"
              using `t \<in> arch` pb.assEA by auto
            moreover have "n\<^sub>f\<ge>n"
            proof -
              from `\<exists>n'''\<ge>n\<^sub>s. ksactive (sKs p) (t n''')` have "sb.nxtAct (sKs p) t n\<^sub>s\<ge>n\<^sub>s"
                using sb.nxtActLe by simp
              moreover from `n\<^sub>k\<ge>n` and `ksactive (sKs p) (t n\<^sub>k)` have "sb.nxtAct (sKs p) t n\<^sub>k\<ge>n\<^sub>k"
                using sb.nxtActI by blast
              ultimately show ?thesis
                using `n\<^sub>f\<ge>sb.nxtAct (sKs p) t n\<^sub>s` `n\<^sub>s\<ge>sb.nxtAct (sKs p) t n\<^sub>r`
                `sb.nxtAct (sKs p) t n\<^sub>r\<ge>n\<^sub>r` `n\<^sub>r\<ge>sb.nxtAct (sKs p) t n\<^sub>k` `n\<^sub>k\<ge>n` by arith
            qed
            ultimately show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
end

end