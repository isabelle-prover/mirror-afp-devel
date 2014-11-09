(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section {* Lamport's Inc example  *}

theory Inc
imports State   
begin

text{*
  This example illustrates use of the embedding by mechanising
  the running example of Lamports original TLA paper \cite{Lamport94}.
*}

datatype pcount = a | b | g

locale Firstprogram =
  fixes x :: "state \<Rightarrow> nat"
  and y :: "state \<Rightarrow> nat"
  and init :: "temporal"
  and m1  :: "temporal"
  and m2 :: "temporal"
  and phi :: "temporal"
  and Live :: "temporal"
  defines "init \<equiv> TEMP $x = # 0 \<and> $y = # 0"
  and "m1 \<equiv> TEMP x` = Suc<$x> \<and> y` = $y"
  and "m2 \<equiv> TEMP y` = Suc<$y> \<and> x` = $x"
  and "Live \<equiv> TEMP WF(m1)_(x,y) \<and> WF(m2)_(x,y)"
  and "phi \<equiv> TEMP (init \<and> \<box>[m1 \<or> m2]_(x,y) \<and> Live)"
  assumes bvar: "basevars (x,y)"

lemma (in Firstprogram) "STUTINV phi"
  by (auto simp: phi_def init_def m1_def m2_def Live_def stutinvs nstutinvs livestutinv)

lemma (in Firstprogram) enabled_m1: "\<turnstile> Enabled \<langle>m1\<rangle>_(x,y)"
proof (clarify)
  fix s
  show "s \<Turnstile> Enabled \<langle>m1\<rangle>_(x,y)"
    by (rule base_enabled[OF bvar]) (auto simp: m1_def tla_defs)
qed

lemma (in Firstprogram) enabled_m2: "\<turnstile> Enabled \<langle>m2\<rangle>_(x,y)"
proof (clarify)
  fix s
  show "s \<Turnstile> Enabled \<langle>m2\<rangle>_(x,y)"
    by (rule base_enabled[OF bvar]) (auto simp: m2_def tla_defs)
qed

locale Secondprogram = Firstprogram +
  fixes sem :: "state \<Rightarrow> nat" 
  and pc1 :: "state \<Rightarrow> pcount"
  and pc2 :: "state \<Rightarrow> pcount"
  and vars
  and initPsi :: "temporal"
  and alpha1 :: "temporal"
  and alpha2 :: "temporal"
  and beta1 :: "temporal"
  and beta2 :: "temporal"
  and gamma1 :: "temporal"
  and gamma2 :: "temporal"
  and n1 :: "temporal"
  and n2 :: "temporal"
  and Live2 :: "temporal"
  and psi :: "temporal"
  and I :: "temporal"
  defines "vars \<equiv> LIFT (x,y,sem,pc1,pc2)" 
  and "initPsi \<equiv> TEMP $pc1 = # a \<and> $pc2 = # a \<and> $x = # 0 \<and> $y = # 0 \<and> $sem = # 1"
  and "alpha1 \<equiv> TEMP $pc1 =#a \<and> # 0 < $sem \<and> pc1$ = #b \<and> sem$ = $sem - # 1 \<and> Unchanged (x,y,pc2)" 
  and "alpha2 \<equiv> TEMP $pc2 =#a \<and> # 0 < $sem \<and> pc2` = #b \<and> sem$ = $sem - # 1 \<and> Unchanged (x,y,pc1)" 
  and "beta1 \<equiv> TEMP $pc1 =#b \<and> pc1` = #g \<and> x` = Suc<$x> \<and> Unchanged (y,sem,pc2)" 
  and "beta2 \<equiv> TEMP $pc2 =#b \<and> pc2` = #g \<and> y` = Suc<$y> \<and> Unchanged (x,sem,pc1)" 
  and "gamma1 \<equiv> TEMP $pc1 =#g \<and> pc1` = #a \<and> sem` = Suc<$sem> \<and> Unchanged (x,y,pc2)"
  and "gamma2 \<equiv> TEMP $pc2 =#g \<and> pc2` = #a \<and> sem` = Suc<$sem> \<and> Unchanged (x,y,pc1)"
  and "n1 \<equiv> TEMP (alpha1 \<or> beta1 \<or> gamma1)"
  and "n2 \<equiv> TEMP (alpha2 \<or> beta2 \<or> gamma2)"
  and "Live2 \<equiv> TEMP SF(n1)_vars \<and> SF(n2)_vars"
  and "psi \<equiv> TEMP (initPsi \<and> \<box>[n1 \<or> n2]_vars \<and> Live2)"
  and "I \<equiv> TEMP ($sem = # 1 \<and> $pc1 = #a \<and> $pc2 = # a)
               \<or>   ($sem = # 0 \<and> (($pc1 = #a \<and> $pc2 \<in> {#b , #g}) 
                                \<or> ($pc2 = #a \<and> $pc1 \<in> {#b , #g})))"
  assumes bvar2: "basevars vars"

lemmas  (in Secondprogram) Sact2_defs = n1_def n2_def alpha1_def beta1_def gamma1_def alpha2_def beta2_def gamma2_def

text {*
  Proving invariants is the basis of every effort of system verification.
  We show that @{text I} is an inductive invariant of specification @{text psi}.
*}
lemma (in Secondprogram) psiI: "\<turnstile> psi \<longrightarrow> \<box>I"
proof -
  have init: "\<turnstile> initPsi \<longrightarrow> I" by (auto simp: initPsi_def I_def)
  have "|~ I \<and> Unchanged vars \<longrightarrow> \<circ>I" by (auto simp: I_def vars_def tla_defs)
  moreover
  have "|~ I \<and> n1 \<longrightarrow> \<circ>I" by (auto simp: I_def Sact2_defs tla_defs)
  moreover
  have "|~ I \<and> n2 \<longrightarrow> \<circ>I" by (auto simp: I_def Sact2_defs tla_defs)
  ultimately have step: "|~ I \<and> [n1 \<or> n2]_vars \<longrightarrow> \<circ>I" by (force simp: actrans_def)
  from init step have goal: "\<turnstile> initPsi \<and> \<box>[n1 \<or> n2]_vars \<longrightarrow> \<box>I" by (rule invmono)
  have "\<turnstile> initPsi \<and> \<box>[n1 \<or> n2]_vars \<and> Live2 ==> \<turnstile> initPsi \<and> \<box>[n1 \<or> n2]_vars"
   by auto
  with goal show ?thesis unfolding psi_def by auto
qed

text {*
  Using this invariant we now prove step simulation, i.e. the safety part of
  the refinement proof.
*}

theorem (in Secondprogram) step_simulation: "\<turnstile> psi \<longrightarrow> init \<and> \<box>[m1 \<or> m2]_(x,y)"
proof -
  have "\<turnstile> initPsi \<and> \<box>I \<and> \<box>[n1 \<or> n2]_vars \<longrightarrow> init \<and> \<box>[m1 \<or> m2]_(x,y)"
  proof (rule refinement1)
    show "\<turnstile> initPsi \<longrightarrow> init" by (auto simp: initPsi_def init_def)
  next
    show "|~ I \<and> \<circ>I \<and> [n1 \<or> n2]_vars \<longrightarrow> [m1 \<or> m2]_(x,y)"
      by (auto simp: I_def m1_def m2_def vars_def Sact2_defs tla_defs)
  qed
  with psiI show ?thesis unfolding psi_def by force
qed

text {*
  Liveness proofs require computing the enabledness conditions of actions.
  The first lemma below shows that all steps are visible, i.e. they change
  at least one variable.
*}
lemma  (in Secondprogram) n1_ch: "|~ \<langle>n1\<rangle>_vars = n1"
proof -
  have "|~ n1 \<longrightarrow> \<langle>n1\<rangle>_vars" by (auto simp: Sact2_defs tla_defs vars_def)
  thus ?thesis by (auto simp: angle_actrans_sem[int_rewrite])
qed

lemma (in Secondprogram) enab_alpha1: "\<turnstile> $pc1 = #a \<longrightarrow> # 0 < $sem \<longrightarrow> Enabled alpha1"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc1 (s 0) = a" and "0 < sem (s 0)"
  thus "s \<Turnstile> Enabled alpha1"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_beta1: "\<turnstile> $pc1 = #b \<longrightarrow> Enabled beta1"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc1 (s 0) = b"
  thus "s \<Turnstile> Enabled beta1"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_gamma1: "\<turnstile> $pc1 = #g \<longrightarrow> Enabled gamma1"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc1 (s 0) = g"
  thus "s \<Turnstile> Enabled gamma1"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_n1:
  "\<turnstile> Enabled \<langle>n1\<rangle>_vars = ($pc1 = #a \<longrightarrow> # 0 < $sem)"
unfolding n1_ch[int_rewrite] proof (rule int_iffI)
  show "\<turnstile> Enabled n1 \<longrightarrow> $pc1 = #a \<longrightarrow> # 0 < $sem"
    by (auto elim!: enabledE simp: Sact2_defs tla_defs)
next
  show "\<turnstile> ($pc1 = #a \<longrightarrow> # 0 < $sem) \<longrightarrow> Enabled n1"
  proof (clarsimp simp: tla_defs)
    fix s :: "state seq"
    assume "pc1 (s 0) = a \<longrightarrow> 0 < sem (s 0)"
    thus "s \<Turnstile> Enabled n1"
      using enab_alpha1[unlift_rule]
            enab_beta1[unlift_rule]
            enab_gamma1[unlift_rule]
      by (cases "pc1 (s 0)") (force simp: n1_def Enabled_disj[int_rewrite] tla_defs)+
  qed
qed

text {*
  The analogous properties for the second process are obtained by copy and paste.
*}
lemma  (in Secondprogram) n2_ch: "|~ \<langle>n2\<rangle>_vars = n2"
proof -
  have "|~ n2 \<longrightarrow> \<langle>n2\<rangle>_vars" by (auto simp: Sact2_defs tla_defs vars_def)
  thus ?thesis by (auto simp: angle_actrans_sem[int_rewrite])
qed

lemma (in Secondprogram) enab_alpha2: "\<turnstile> $pc2 = #a \<longrightarrow> # 0 < $sem \<longrightarrow> Enabled alpha2"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc2 (s 0) = a" and "0 < sem (s 0)"
  thus "s \<Turnstile> Enabled alpha2"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_beta2: "\<turnstile> $pc2 = #b \<longrightarrow> Enabled beta2"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc2 (s 0) = b"
  thus "s \<Turnstile> Enabled beta2"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_gamma2: "\<turnstile> $pc2 = #g \<longrightarrow> Enabled gamma2"
proof (clarsimp simp: tla_defs)
  fix s :: "state seq"
  assume "pc2 (s 0) = g"
  thus "s \<Turnstile> Enabled gamma2"
    by (intro base_enabled[OF bvar2]) (auto simp: Sact2_defs tla_defs vars_def)
qed

lemma (in Secondprogram) enab_n2:
  "\<turnstile> Enabled \<langle>n2\<rangle>_vars = ($pc2 = #a \<longrightarrow> # 0 < $sem)"
unfolding n2_ch[int_rewrite] proof (rule int_iffI)
  show "\<turnstile> Enabled n2 \<longrightarrow> $pc2 = #a \<longrightarrow> # 0 < $sem"
    by (auto elim!: enabledE simp: Sact2_defs tla_defs)
next
  show "\<turnstile> ($pc2 = #a \<longrightarrow> # 0 < $sem) \<longrightarrow> Enabled n2"
  proof (clarsimp simp: tla_defs)
    fix s :: "state seq"
    assume "pc2 (s 0) = a \<longrightarrow> 0 < sem (s 0)"
    thus "s \<Turnstile> Enabled n2"
      using enab_alpha2[unlift_rule]
            enab_beta2[unlift_rule]
            enab_gamma2[unlift_rule]
      by (cases "pc2 (s 0)") (force simp: n2_def Enabled_disj[int_rewrite] tla_defs)+
  qed
qed

text {*
  We use rule @{text SF2} to prove that @{text psi} implements strong fairness
  for the abstract action @{text m1}. Since strong fairness implies weak fairness,
  it follows that @{text psi} refines the liveness condition of @{text phi}.
*}

lemma (in Secondprogram) psi_fair_m1: "\<turnstile> psi \<longrightarrow> SF(m1)_(x,y)"
proof -
  have "\<turnstile> \<box>[n1 \<or> n2]_vars \<and> SF(n1)_vars \<and> \<box>(I \<and> SF(n2)_vars) \<longrightarrow> SF(m1)_(x,y)"
  proof (rule SF2)
    txt {*
      Rule @{text SF2} requires us to choose a helpful action (whose effect implies
      @{text "\<langle>m1\<rangle>_(x,y)"}) and a persistent condition, which will eventually remain
      true if the helpful action is never executed. In our case, the helpful action
      is @{text beta1} and the persistent condition is @{text "pc1 = b"}.
    *}
    show "|~ \<langle>(n1 \<or> n2) \<and> beta1\<rangle>_vars \<longrightarrow> \<langle>m1\<rangle>_(x,y)"
      by (auto simp: beta1_def m1_def vars_def tla_defs)
  next
    show "|~ $pc1 = #b \<and> \<circ>($pc1 = #b) \<and> \<langle>(n1 \<or> n2) \<and> n1\<rangle>_vars \<longrightarrow> beta1"
      by (auto simp: n1_def alpha1_def beta1_def gamma1_def tla_defs)
  next
    show "\<turnstile> $pc1 = #b \<and> Enabled \<langle>m1\<rangle>_(x, y) \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
      unfolding enab_n1[int_rewrite] by auto
  next
    txt {*
      The difficult part of the proof is showing that the persistent condition
      will eventually always be true if the helpful action is never executed.
      We show that (1) whenever the condition becomes true it remains so and
      (2) eventually the condition must be true.
    *}
    show "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars
            \<and> SF(n1)_vars \<and> \<box>(I \<and> SF(n2)_vars) \<and> \<box>\<diamond>Enabled \<langle>m1\<rangle>_(x, y)
            \<longrightarrow> \<diamond>\<box>($pc1 = #b)"
    proof -
      have "\<turnstile> \<box>\<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> \<box>($pc1 = #b \<longrightarrow> \<box>($pc1 = #b))"
      proof (rule STL4)
        have "|~ $pc1 = #b \<and> [(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> \<circ>($pc1 = #b)"
          by (auto simp: Sact2_defs vars_def tla_defs)
        from this[THEN INV1]
        show "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> $pc1 = #b \<longrightarrow> \<box>($pc1 = #b)" by auto
      qed
      hence 1: "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> \<diamond>($pc1 = #b) \<longrightarrow> \<diamond>\<box>($pc1 = #b)"
        by (force intro: E31[unlift_rule])
      have "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<and> SF(n1)_vars \<and> \<box>(I \<and> SF(n2)_vars)
              \<longrightarrow> \<diamond>($pc1 = #b)"
      proof -
        txt {*
          The plan of the proof is to show that from any state where @{text "pc1 = g"}
          one eventually reaches @{text "pc1 = a"}, from where one eventually reaches
          @{text "pc1 = b"}. The result follows by combining leadsto properties.
        *}
        let ?F = "LIFT (\<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<and> SF(n1)_vars \<and> \<box>(I \<and> SF(n2)_vars))"
        txt {*
          Showing that @{text "pc1 = g"} leads to @{text "pc1 = a"} is a simple
          application of rule @{text SF1} because the first process completely
          controls this transition.
        *}
        have ga: "\<turnstile> ?F \<longrightarrow> ($pc1 = #g \<leadsto> $pc1 = #a)"
        proof (rule SF1)
          show "|~ $pc1 = #g \<and> [(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> \<circ>($pc1 = #g) \<or> \<circ>($pc1 = #a)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc1 = #g \<and> \<langle>((n1 \<or> n2) \<and> \<not> beta1) \<and> n1\<rangle>_vars \<longrightarrow> \<circ>($pc1 = #a)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc1 = #g \<and> Unchanged vars \<longrightarrow> \<circ>($pc1 = #g)"
            by (auto simp: vars_def tla_defs)
        next
          have "\<turnstile> $pc1 = #g \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
            unfolding enab_n1[int_rewrite] by (auto simp: tla_defs)
          hence "\<turnstile> \<box>($pc1 = #g) \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
            by (rule lift_imp_trans[OF ax1])
          hence "\<turnstile> \<box>($pc1 = #g) \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
            by (rule lift_imp_trans[OF _ E3])
          thus "\<turnstile> \<box>($pc1 = #g) \<and> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<and> \<box>(I \<and> SF(n2)_vars)
                  \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
            by auto
        qed
        txt {*
          The proof that @{text "pc1 = a"} leads to @{text "pc1 = b"} follows
          the same basic schema. However, showing that @{text n1} is eventually
          enabled requires reasoning about the second process, which must liberate
          the critical section.
        *}
        have ab: "\<turnstile> ?F \<longrightarrow> ($pc1 = #a \<leadsto> $pc1 = #b)"
        proof (rule SF1)
          show "|~ $pc1 = #a \<and> [(n1 \<or> n2) \<and> \<not> beta1]_vars \<longrightarrow> \<circ>($pc1 = #a) \<or> \<circ>($pc1 = #b)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc1 = #a \<and> \<langle>((n1 \<or> n2) \<and> \<not> beta1) \<and> n1\<rangle>_vars \<longrightarrow> \<circ>($pc1 = #b)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc1 = #a \<and> Unchanged vars \<longrightarrow> \<circ>($pc1 = #a)"
            by (auto simp: vars_def tla_defs)
        next
          txt {* We establish a suitable leadsto-chain. *}
          let ?G = "LIFT \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<and> SF(n2)_vars \<and> \<box>($pc1 = #a \<and> I)"
          have "\<turnstile> ?G \<longrightarrow> \<diamond>($pc2 = #a \<and> $pc1 = #a \<and> I)"
          proof -
            txt {* Rule @{text SF1} takes us from @{text "pc2 = b"} to @{text "pc2 = g"}. *}
            have bg2: "\<turnstile> ?G \<longrightarrow> ($pc2 = #b \<leadsto> $pc2 = #g)"
            proof (rule SF1)
              show "|~ $pc2 = #b \<and> [(n1 \<or> n2) \<and> \<not>beta1]_vars \<longrightarrow> \<circ>($pc2 = #b) \<or> \<circ>($pc2 = #g)"
                by (auto simp: Sact2_defs vars_def tla_defs)
            next
              show "|~ $pc2 = #b \<and> \<langle>((n1 \<or> n2) \<and> \<not>beta1) \<and> n2\<rangle>_vars \<longrightarrow> \<circ>($pc2 = #g)"
                by (auto simp: Sact2_defs vars_def tla_defs)
            next
              show "|~ $pc2 = #b \<and> Unchanged vars \<longrightarrow> \<circ>($pc2 = #b)"
                by (auto simp: vars_def tla_defs)
            next
              have "\<turnstile> $pc2 = #b \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
                unfolding enab_n2[int_rewrite] by (auto simp: tla_defs)
              hence "\<turnstile> \<box>($pc2 = #b) \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
                by (rule lift_imp_trans[OF ax1])
              hence "\<turnstile> \<box>($pc2 = #b) \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
                by (rule lift_imp_trans[OF _ E3])
              thus "\<turnstile> \<box>($pc2 = #b) \<and> \<box>[(n1 \<or> n2) \<and> \<not>beta1]_vars \<and> \<box>($pc1 = #a \<and> I)
                      \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
                by auto
            qed
            txt {* Similarly, @{text "pc2 = b"} leads to @{text "pc2 = g"}. *}
            have ga2: "\<turnstile> ?G \<longrightarrow> ($pc2 = #g \<leadsto> $pc2 = #a)"
            proof (rule SF1)
              show "|~ $pc2 = #g \<and> [(n1 \<or> n2) \<and> \<not>beta1]_vars \<longrightarrow> \<circ>($pc2 = #g) \<or> \<circ>($pc2 = #a)"
                by (auto simp: Sact2_defs vars_def tla_defs)
            next
              show "|~ $pc2 = #g \<and> \<langle>((n1 \<or> n2) \<and> \<not>beta1) \<and> n2\<rangle>_vars \<longrightarrow> \<circ>($pc2 = #a)"
                by (auto simp: n2_def alpha2_def beta2_def gamma2_def vars_def tla_defs)
            next
              show "|~ $pc2 = #g \<and> Unchanged vars \<longrightarrow> \<circ>($pc2 = #g)"
                by (auto simp: vars_def tla_defs)
            next
              have "\<turnstile> $pc2 = #g \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
                unfolding enab_n2[int_rewrite] by (auto simp: tla_defs)
              hence "\<turnstile> \<box>($pc2 = #g) \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
                by (rule lift_imp_trans[OF ax1])
              hence "\<turnstile> \<box>($pc2 = #g) \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
                by (rule lift_imp_trans[OF _ E3])
              thus "\<turnstile> \<box>($pc2 = #g) \<and> \<box>[(n1 \<or> n2) \<and> \<not>beta1]_vars \<and> \<box>($pc1 = #a \<and> I)
                      \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
                by auto
            qed
            with bg2 have "\<turnstile> ?G \<longrightarrow> ($pc2 = #b \<leadsto> $pc2 = #a)"
              by (force elim: LT13[unlift_rule])
            with ga2 have "\<turnstile> ?G \<longrightarrow> ($pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g) \<leadsto> ($pc2 = #a)"
              unfolding LT17[int_rewrite] LT1[int_rewrite] by force
            moreover
            have "\<turnstile> $pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g"
            proof (clarsimp simp: tla_defs)
              fix s :: "state seq"
              assume "pc2 (s 0) \<noteq> a" and "pc2 (s 0) \<noteq> g"
              thus "pc2 (s 0) = b" by (cases "pc2 (s 0)") auto
            qed
            hence "\<turnstile> (($pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g) \<leadsto> $pc2 = #a) \<longrightarrow> \<diamond>($pc2 = #a)"
              by (rule fmp[OF _ LT4])
            ultimately
            have "\<turnstile> ?G \<longrightarrow> \<diamond>($pc2 = #a)" by force
            thus ?thesis by (auto intro!: SE3[unlift_rule])
          qed
          moreover
          have "\<turnstile> \<diamond>($pc2 = #a \<and> $pc1 = #a \<and> I) \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
            unfolding enab_n1[int_rewrite] by (rule STL4_eve) (auto simp: I_def tla_defs)
          ultimately
          show "\<turnstile> \<box>($pc1 = #a) \<and> \<box>[(n1 \<or> n2) \<and> \<not> beta1]_vars \<and> \<box>(I \<and> SF(n2)_vars)
                  \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
            by (force simp: STL5[int_rewrite])
        qed
        from ga ab have "\<turnstile> ?F \<longrightarrow> ($pc1 = #g \<leadsto> $pc1 = #b)"
          by (force elim: LT13[unlift_rule])
        with ab have "\<turnstile> ?F \<longrightarrow> (($pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g) \<leadsto> $pc1 = #b)"
          unfolding LT17[int_rewrite] LT1[int_rewrite] by force
        moreover
        have "\<turnstile> $pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g"
        proof (clarsimp simp: tla_defs)
          fix s :: "state seq"
          assume "pc1 (s 0) \<noteq> a" and "pc1 (s 0) \<noteq> g"
          thus "pc1 (s 0) = b" by (cases "pc1 (s 0)", auto)
        qed
        hence "\<turnstile> (($pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g) \<leadsto> $pc1 = #b) \<longrightarrow> \<diamond>($pc1 = #b)"
          by (rule fmp[OF _ LT4])
        ultimately show ?thesis by (rule lift_imp_trans)
      qed
      with 1 show ?thesis by force
    qed
  qed
  with psiI show ?thesis unfolding psi_def Live2_def STL5[int_rewrite] by force
qed

text {*
  In the same way we prove that @{text psi} implements strong fairness
  for the abstract action @{text m1}. The proof is obtained by copy and paste
  from the previous one.
*}

lemma (in Secondprogram) psi_fair_m2: "\<turnstile> psi \<longrightarrow> SF(m2)_(x,y)"
proof -
  have "\<turnstile> \<box>[n1 \<or> n2]_vars \<and> SF(n2)_vars \<and> \<box>(I \<and> SF(n1)_vars) \<longrightarrow> SF(m2)_(x,y)"
  proof (rule SF2)
    txt {*
      Rule @{text SF2} requires us to choose a helpful action (whose effect implies
      @{text "\<langle>m2\<rangle>_(x,y)"}) and a persistent condition, which will eventually remain
      true if the helpful action is never executed. In our case, the helpful action
      is @{text beta2} and the persistent condition is @{text "pc2 = b"}.
    *}
    show "|~ \<langle>(n1 \<or> n2) \<and> beta2\<rangle>_vars \<longrightarrow> \<langle>m2\<rangle>_(x,y)"
      by (auto simp: beta2_def m2_def vars_def tla_defs)
  next
    show "|~ $pc2 = #b \<and> \<circ>($pc2 = #b) \<and> \<langle>(n1 \<or> n2) \<and> n2\<rangle>_vars \<longrightarrow> beta2"
      by (auto simp: n2_def alpha2_def beta2_def gamma2_def tla_defs)
  next
    show "\<turnstile> $pc2 = #b \<and> Enabled \<langle>m2\<rangle>_(x, y) \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
      unfolding enab_n2[int_rewrite] by auto
  next
    txt {*
      The difficult part of the proof is showing that the persistent condition
      will eventually always be true if the helpful action is never executed.
      We show that (1) whenever the condition becomes true it remains so and
      (2) eventually the condition must be true.
    *}
    show "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars
            \<and> SF(n2)_vars \<and> \<box>(I \<and> SF(n1)_vars) \<and> \<box>\<diamond>Enabled \<langle>m2\<rangle>_(x, y)
            \<longrightarrow> \<diamond>\<box>($pc2 = #b)"
    proof -
      have "\<turnstile> \<box>\<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> \<box>($pc2 = #b \<longrightarrow> \<box>($pc2 = #b))"
      proof (rule STL4)
        have "|~ $pc2 = #b \<and> [(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> \<circ>($pc2 = #b)"
          by (auto simp: Sact2_defs vars_def tla_defs)
        from this[THEN INV1]
        show "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> $pc2 = #b \<longrightarrow> \<box>($pc2 = #b)" by auto
      qed
      hence 1: "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> \<diamond>($pc2 = #b) \<longrightarrow> \<diamond>\<box>($pc2 = #b)"
        by (force intro: E31[unlift_rule])
      have "\<turnstile> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<and> SF(n2)_vars \<and> \<box>(I \<and> SF(n1)_vars)
              \<longrightarrow> \<diamond>($pc2 = #b)"
      proof -
        txt {*
          The plan of the proof is to show that from any state where @{text "pc2 = g"}
          one eventually reaches @{text "pc2 = a"}, from where one eventually reaches
          @{text "pc2 = b"}. The result follows by combining leadsto properties.
        *}
        let ?F = "LIFT (\<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<and> SF(n2)_vars \<and> \<box>(I \<and> SF(n1)_vars))"
        txt {*
          Showing that @{text "pc2 = g"} leads to @{text "pc2 = a"} is a simple
          application of rule @{text SF1} because the second process completely
          controls this transition.
        *}
        have ga: "\<turnstile> ?F \<longrightarrow> ($pc2 = #g \<leadsto> $pc2 = #a)"
        proof (rule SF1)
          show "|~ $pc2 = #g \<and> [(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> \<circ>($pc2 = #g) \<or> \<circ>($pc2 = #a)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc2 = #g \<and> \<langle>((n1 \<or> n2) \<and> \<not> beta2) \<and> n2\<rangle>_vars \<longrightarrow> \<circ>($pc2 = #a)"
            by (auto simp: n2_def alpha2_def beta2_def gamma2_def vars_def tla_defs)
        next
          show "|~ $pc2 = #g \<and> Unchanged vars \<longrightarrow> \<circ>($pc2 = #g)"
            by (auto simp: vars_def tla_defs)
        next
          have "\<turnstile> $pc2 = #g \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
            unfolding enab_n2[int_rewrite] by (auto simp: tla_defs)
          hence "\<turnstile> \<box>($pc2 = #g) \<longrightarrow> Enabled \<langle>n2\<rangle>_vars"
            by (rule lift_imp_trans[OF ax1])
          hence "\<turnstile> \<box>($pc2 = #g) \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
            by (rule lift_imp_trans[OF _ E3])
          thus "\<turnstile> \<box>($pc2 = #g) \<and> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<and> \<box>(I \<and> SF(n1)_vars)
                  \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
            by auto
        qed
        txt {*
          The proof that @{text "pc2 = a"} leads to @{text "pc2 = b"} follows
          the same basic schema. However, showing that @{text n2} is eventually
          enabled requires reasoning about the second process, which must liberate
          the critical section.
        *}
        have ab: "\<turnstile> ?F \<longrightarrow> ($pc2 = #a \<leadsto> $pc2 = #b)"
        proof (rule SF1)
          show "|~ $pc2 = #a \<and> [(n1 \<or> n2) \<and> \<not> beta2]_vars \<longrightarrow> \<circ>($pc2 = #a) \<or> \<circ>($pc2 = #b)"
            by (auto simp: Sact2_defs vars_def tla_defs)
        next
          show "|~ $pc2 = #a \<and> \<langle>((n1 \<or> n2) \<and> \<not> beta2) \<and> n2\<rangle>_vars \<longrightarrow> \<circ>($pc2 = #b)"
            by (auto simp: n2_def alpha2_def beta2_def gamma2_def vars_def tla_defs)
        next
          show "|~ $pc2 = #a \<and> Unchanged vars \<longrightarrow> \<circ>($pc2 = #a)"
            by (auto simp: vars_def tla_defs)
        next
          txt {* We establish a suitable leadsto-chain. *}
          let ?G = "LIFT \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<and> SF(n1)_vars \<and> \<box>($pc2 = #a \<and> I)"
          have "\<turnstile> ?G \<longrightarrow> \<diamond>($pc1 = #a \<and> $pc2 = #a \<and> I)"
          proof -
            txt {* Rule @{text SF1} takes us from @{text "pc1 = b"} to @{text "pc1 = g"}. *}
            have bg1: "\<turnstile> ?G \<longrightarrow> ($pc1 = #b \<leadsto> $pc1 = #g)"
            proof (rule SF1)
              show "|~ $pc1 = #b \<and> [(n1 \<or> n2) \<and> \<not>beta2]_vars \<longrightarrow> \<circ>($pc1 = #b) \<or> \<circ>($pc1 = #g)"
                by (auto simp: Sact2_defs vars_def tla_defs)
            next
              show "|~ $pc1 = #b \<and> \<langle>((n1 \<or> n2) \<and> \<not>beta2) \<and> n1\<rangle>_vars \<longrightarrow> \<circ>($pc1 = #g)"
                by (auto simp: n1_def alpha1_def beta1_def gamma1_def vars_def tla_defs)
            next
              show "|~ $pc1 = #b \<and> Unchanged vars \<longrightarrow> \<circ>($pc1 = #b)"
                by (auto simp: vars_def tla_defs)
            next
              have "\<turnstile> $pc1 = #b \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
                unfolding enab_n1[int_rewrite] by (auto simp: tla_defs)
              hence "\<turnstile> \<box>($pc1 = #b) \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
                by (rule lift_imp_trans[OF ax1])
              hence "\<turnstile> \<box>($pc1 = #b) \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
                by (rule lift_imp_trans[OF _ E3])
              thus "\<turnstile> \<box>($pc1 = #b) \<and> \<box>[(n1 \<or> n2) \<and> \<not>beta2]_vars \<and> \<box>($pc2 = #a \<and> I)
                      \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
                by auto
            qed
            txt {* Similarly, @{text "pc1 = b"} leads to @{text "pc1 = g"}. *}
            have ga1: "\<turnstile> ?G \<longrightarrow> ($pc1 = #g \<leadsto> $pc1 = #a)"
            proof (rule SF1)
              show "|~ $pc1 = #g \<and> [(n1 \<or> n2) \<and> \<not>beta2]_vars \<longrightarrow> \<circ>($pc1 = #g) \<or> \<circ>($pc1 = #a)"
                by (auto simp: Sact2_defs vars_def tla_defs)
            next
              show "|~ $pc1 = #g \<and> \<langle>((n1 \<or> n2) \<and> \<not>beta2) \<and> n1\<rangle>_vars \<longrightarrow> \<circ>($pc1 = #a)"
                by (auto simp: n1_def alpha1_def beta1_def gamma1_def vars_def tla_defs)
            next
              show "|~ $pc1 = #g \<and> Unchanged vars \<longrightarrow> \<circ>($pc1 = #g)"
                by (auto simp: vars_def tla_defs)
            next
              have "\<turnstile> $pc1 = #g \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
                unfolding enab_n1[int_rewrite] by (auto simp: tla_defs)
              hence "\<turnstile> \<box>($pc1 = #g) \<longrightarrow> Enabled \<langle>n1\<rangle>_vars"
                by (rule lift_imp_trans[OF ax1])
              hence "\<turnstile> \<box>($pc1 = #g) \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
                by (rule lift_imp_trans[OF _ E3])
              thus "\<turnstile> \<box>($pc1 = #g) \<and> \<box>[(n1 \<or> n2) \<and> \<not>beta2]_vars \<and> \<box>($pc2 = #a \<and> I)
                      \<longrightarrow> \<diamond>Enabled \<langle>n1\<rangle>_vars"
                by auto
            qed
            with bg1 have "\<turnstile> ?G \<longrightarrow> ($pc1 = #b \<leadsto> $pc1 = #a)"
              by (force elim: LT13[unlift_rule])
            with ga1 have "\<turnstile> ?G \<longrightarrow> ($pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g) \<leadsto> ($pc1 = #a)"
              unfolding LT17[int_rewrite] LT1[int_rewrite] by force
            moreover
            have "\<turnstile> $pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g"
            proof (clarsimp simp: tla_defs)
              fix s :: "state seq"
              assume "pc1 (s 0) \<noteq> a" and "pc1 (s 0) \<noteq> g"
              thus "pc1 (s 0) = b" by (cases "pc1 (s 0)") auto
            qed
            hence "\<turnstile> (($pc1 = #a \<or> $pc1 = #b \<or> $pc1 = #g) \<leadsto> $pc1 = #a) \<longrightarrow> \<diamond>($pc1 = #a)"
              by (rule fmp[OF _ LT4])
            ultimately
            have "\<turnstile> ?G \<longrightarrow> \<diamond>($pc1 = #a)" by force
            thus ?thesis by (auto intro!: SE3[unlift_rule])
          qed
          moreover
          have "\<turnstile> \<diamond>($pc1 = #a \<and> $pc2 = #a \<and> I) \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
            unfolding enab_n2[int_rewrite] by (rule STL4_eve) (auto simp: I_def tla_defs)
          ultimately
          show "\<turnstile> \<box>($pc2 = #a) \<and> \<box>[(n1 \<or> n2) \<and> \<not> beta2]_vars \<and> \<box>(I \<and> SF(n1)_vars)
                  \<longrightarrow> \<diamond>Enabled \<langle>n2\<rangle>_vars"
            by (force simp: STL5[int_rewrite])
        qed
        from ga ab have "\<turnstile> ?F \<longrightarrow> ($pc2 = #g \<leadsto> $pc2 = #b)"
          by (force elim: LT13[unlift_rule])
        with ab have "\<turnstile> ?F \<longrightarrow> (($pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g) \<leadsto> $pc2 = #b)"
          unfolding LT17[int_rewrite] LT1[int_rewrite] by force
        moreover
        have "\<turnstile> $pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g"
        proof (clarsimp simp: tla_defs)
          fix s :: "state seq"
          assume "pc2 (s 0) \<noteq> a" and "pc2 (s 0) \<noteq> g"
          thus "pc2 (s 0) = b" by (cases "pc2 (s 0)") auto
        qed
        hence "\<turnstile> (($pc2 = #a \<or> $pc2 = #b \<or> $pc2 = #g) \<leadsto> $pc2 = #b) \<longrightarrow> \<diamond>($pc2 = #b)"
          by (rule fmp[OF _ LT4])
        ultimately show ?thesis by (rule lift_imp_trans)
      qed
      with 1 show ?thesis by force
    qed
  qed
  with psiI show ?thesis unfolding psi_def Live2_def STL5[int_rewrite] by force
qed

text {* 
  We can now prove the main theorem, which states that @{text psi}
  implements @{text phi}.
*}

theorem (in Secondprogram) impl: "\<turnstile> psi \<longrightarrow> phi"
  unfolding phi_def Live_def
  by (auto dest: step_simulation[unlift_rule]
                 lift_imp_trans[OF psi_fair_m1 SF_imp_WF, unlift_rule]
                 lift_imp_trans[OF psi_fair_m2 SF_imp_WF, unlift_rule])

end
