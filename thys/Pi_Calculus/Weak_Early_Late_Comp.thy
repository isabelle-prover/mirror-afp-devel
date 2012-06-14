(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Late_Comp
  imports Weak_Early_Cong Weak_Late_Cong Strong_Early_Late_Comp
begin

(*************** Transitions *********************)

abbreviation earlyTauChain_judge ("_ \<Longrightarrow>\<^isub>\<tau>\<^isub>e _" [80, 80] 80) where "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e Q \<equiv> Early_Tau_Chain.tauChain P Q"
abbreviation lateTauChain_judge ("_ \<Longrightarrow>\<^isub>\<tau>\<^isub>l _" [80, 80] 80) where "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l Q \<equiv> Late_Tau_Chain.tauChain_judge P Q"

(************** Tau Chains *******************)

lemma lateEarlyTauChain:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l Q"

  shows "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e Q"
using assms
proof(induct rule: Late_Tau_Chain.tauChainInduct)
  case id
  show ?case by simp
next
  case(ih P' P'')
  have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'" by fact
  moreover have "P' \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e P''"
  proof -
    have "P' \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l P''" by fact
    thus ?thesis by(rule lateEarlyTau)
  qed
  ultimately show ?case by blast
qed

lemma earlyLateTauChain:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e Q"

  shows "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l Q"
using assms
proof(induct rule: Early_Tau_Chain.tauChainInduct)
  case id
  show ?case by simp
next
  case(ih P' P'')
  have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'" by fact
  moreover have "P' \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l P''"
  proof -
    have "P' \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e P''" by fact
    thus ?thesis by(rule earlyLateTau)
  qed
  ultimately show ?case by blast
qed

lemma tauChainEq:
  fixes P :: pi
  and   Q :: pi

  shows "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l Q = P \<Longrightarrow>\<^isub>\<tau>\<^isub>e Q"
by(blast intro: lateEarlyTauChain earlyLateTauChain)

(***************** Step semantics ****************)
  
lemma lateEarlyStepOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l(a[b] \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e(a[b] \<prec>\<^isub>e P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^isub>la[b] \<prec>\<^isub>l P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^isub>ea[b] \<prec>\<^isub>e P''" by(rule lateEarlyOutput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'" by(rule lateEarlyTauChain)
  ultimately show ?thesis by(rule Weak_Early_Step_Semantics.transitionI)
qed
  
lemma earlyLateStepOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e(a[b] \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l(a[b] \<prec>\<^isub>l P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^isub>ea[b] \<prec>\<^isub>e P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^isub>la[b] \<prec>\<^isub>l P''" by(rule earlyLateOutput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'" by(rule earlyLateTauChain)
  ultimately show ?thesis by(rule Weak_Late_Step_Semantics.transitionI)
qed
  
lemma stepOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^isub>e(a[b] \<prec>\<^isub>e P') = P \<Longrightarrow>\<^isub>l(a[b] \<prec>\<^isub>l P')"
by(auto intro: lateEarlyStepOutput earlyLateStepOutput)

lemma lateEarlyStepBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P'); x \<sharp> P\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')"
  proof -
    fix P a x P'
    assume "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')" and "x \<sharp> P"
    then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^isub>la<\<nu>x> \<prec>\<^isub>l P''"
                           and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'"
      by(blast dest: Weak_Late_Step_Semantics.transitionE)

    from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''" by(rule lateEarlyTauChain)
    moreover from P'''Trans have "P''' \<longmapsto>\<^isub>ea<\<nu>x> \<prec>\<^isub>e P''" by(rule lateEarlyBoundOutput)
    moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'" by(rule lateEarlyTauChain)
    ultimately show "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')" by(rule Weak_Early_Step_Semantics.transitionI)
  qed
  have "\<exists>c::name. c \<sharp> (P, P')" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<Longrightarrow>\<^isub>la<\<nu>c> \<prec>\<^isub>l ([(x, c)] \<bullet> P')" by(simp add: alphaBoundResidual)
  hence "P \<Longrightarrow>\<^isub>ea<\<nu>c> \<prec>\<^isub>e ([(x, c)] \<bullet> P')" using cFreshP by(rule Goal)
  with cFreshP' show ?thesis by(simp add: alphaBoundOutput)
qed
  
lemma earlyLateStepBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P'); x \<sharp> P\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')"
  proof -
    fix P a x P'
    assume "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')" and "x \<sharp> P"
    then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^isub>ea<\<nu>x> \<prec>\<^isub>e P''"
                           and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'"
      by(blast dest: Weak_Early_Step_Semantics.transitionE)

    from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''" by(rule earlyLateTauChain)
    moreover from P'''Trans have "P''' \<longmapsto>\<^isub>la<\<nu>x> \<prec>\<^isub>l P''" by(rule earlyLateBoundOutput)
    moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'" by(rule earlyLateTauChain)
    ultimately show "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')" by(rule Weak_Late_Step_Semantics.transitionI)
  qed
  have "\<exists>c::name. c \<sharp> (P, P')" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<Longrightarrow>\<^isub>ea<\<nu>c> \<prec>\<^isub>e ([(x, c)] \<bullet> P')" by(simp add: alphaBoundOutput)
  hence "P \<Longrightarrow>\<^isub>la<\<nu>c> \<prec>\<^isub>l ([(x, c)] \<bullet> P')" using cFreshP by(rule Goal)
  with cFreshP' show ?thesis by(simp add: alphaBoundResidual)
qed
  
lemma stepBoundOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P') = P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')"
by(auto intro: lateEarlyStepBoundOutput earlyLateStepBoundOutput)

lemma earlyLateStepInput:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes "P \<Longrightarrow>\<^isub>e(a<u> \<prec>\<^isub>e P')"

  shows "\<exists>P'' x. P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow>a<x> \<prec> P' \<and> x \<sharp> C"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''"
                              and P'''Trans: "P''' \<longmapsto>\<^isub>ea<u> \<prec>\<^isub>e P''"
                              and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans obtain P'''' x where P'''Trans: "P''' \<longmapsto>\<^isub>la<x> \<prec>\<^isub>l P''''" 
                                           and P''eqP'''': "P'' = P''''[x::=u]"
                                           and xFreshC: "x \<sharp> C"
    by(blast dest: earlyLateInput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'" by(rule earlyLateTauChain)
  ultimately show "\<exists>P'' x. P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow> a<x> \<prec> P' \<and> x \<sharp> C"
    by(blast intro: Weak_Late_Step_Semantics.transitionI)
qed
  
lemma lateEarlyStepInput:
  fixes P   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi

  assumes "P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow> a<x> \<prec> P'"

  shows "P \<Longrightarrow>\<^isub>e(a<u> \<prec>\<^isub>e P')"
proof -
  from assms obtain P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^isub>la<x> \<prec>\<^isub>l P''"
                           and P''Chain: "P''[x::=u] \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^isub>ea<u> \<prec>\<^isub>e P''[x::=u]" by(rule lateEarlyInput)
  moreover from P''Chain have "P''[x::=u] \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'" by(rule lateEarlyTauChain)
  ultimately show "P \<Longrightarrow>\<^isub>e(a<u> \<prec>\<^isub>e P')" by(rule Weak_Early_Step_Semantics.transitionI)
qed

lemma lateEarlyStepTau:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l(\<tau> \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e(\<tau> \<prec>\<^isub>e P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e P''" by(rule lateEarlyTau)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'" by(rule lateEarlyTauChain)
  ultimately show ?thesis by(rule Weak_Early_Step_Semantics.transitionI)
qed

lemma earlyLateStepTau:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e(\<tau> \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l(\<tau> \<prec>\<^isub>l P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l P''" by(rule earlyLateTau)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^isub>\<tau>\<^isub>l P'" by(rule earlyLateTauChain)
  ultimately show ?thesis by(rule Weak_Late_Step_Semantics.transitionI)
qed

lemma stepTauEq:
  fixes P  :: pi
  and   P' :: pi
  
  shows "P \<Longrightarrow>\<^isub>e\<tau> \<prec>\<^isub>e P' = P \<Longrightarrow>\<^isub>l\<tau> \<prec>\<^isub>l P'"
by(blast intro: earlyLateStepTau lateEarlyStepTau)

(****************** Weak Semantics *************)

lemma lateEarlyOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l\<^isup>^(a[b] \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(a[b] \<prec>\<^isub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^isub>l(a[b] \<prec>\<^isub>l P')"
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^isub>e(a[b] \<prec>\<^isub>e P')" by(rule lateEarlyStepOutput)
  thus ?thesis
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed
  
lemma earlyLateOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e\<^isup>^(a[b] \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l\<^isup>^(a[b] \<prec>\<^isub>l P')"
proof -
  from assms have "P \<Longrightarrow>\<^isub>e(a[b] \<prec>\<^isub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^isub>l(a[b] \<prec>\<^isub>l P')" by(rule earlyLateStepOutput)
  thus ?thesis
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
qed

lemma outputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(a[b] \<prec>\<^isub>e P') = P \<Longrightarrow>\<^isub>l\<^isup>^(a[b] \<prec>\<^isub>l P')"
by(auto intro: lateEarlyOutput earlyLateOutput)

lemma lateEarlyBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l\<^isup>^(a<\<nu>x> \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(a<\<nu>x> \<prec>\<^isub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')"
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')" by(rule lateEarlyStepBoundOutput)
  thus ?thesis
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed
  
lemma earlyLateBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e\<^isup>^(a<\<nu>x> \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l\<^isup>^(a<\<nu>x> \<prec>\<^isub>l P')"
proof -
  from assms have "P \<Longrightarrow>\<^isub>e(a<\<nu>x> \<prec>\<^isub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^isub>l(a<\<nu>x> \<prec>\<^isub>l P')" by(rule earlyLateStepBoundOutput)
  thus ?thesis
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
qed

lemma boundOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(a<\<nu>x> \<prec>\<^isub>e P') = P \<Longrightarrow>\<^isub>l\<^isup>^(a<\<nu>x> \<prec>\<^isub>l P')"
by(auto intro: lateEarlyBoundOutput earlyLateBoundOutput)

lemma earlyLateInput:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes "P \<Longrightarrow>\<^isub>e\<^isup>^(a<u> \<prec>\<^isub>e P')"

  shows "\<exists>P'' x. P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow>a<x> \<prec> P' \<and> x \<sharp> C"
proof -
  from assms have "P \<Longrightarrow>\<^isub>e(a<u> \<prec>\<^isub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  thus ?thesis by(rule earlyLateStepInput)
qed
  
lemma lateEarlyInput:
  fixes P   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi

  assumes "P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow> a<x> \<prec> P'"

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(a<u> \<prec>\<^isub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^isub>e(a<u> \<prec>\<^isub>e P')" by(rule lateEarlyStepInput)
  thus ?thesis by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed

lemma lateEarlyTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>l\<^isup>^(\<tau> \<prec>\<^isub>l P')"

  shows "P \<Longrightarrow>\<^isub>e\<^isup>^(\<tau> \<prec>\<^isub>e P')"
proof -
  from assms show ?thesis
  proof(induct rule: Weak_Late_Semantics.transitionCases)
    case Stay
    thus ?case
      by(auto simp add: Late_Semantics.residual.inject Weak_Early_Semantics.weakTransition_def)
  next
    case Step
    have "P \<Longrightarrow>\<^isub>l\<tau> \<prec>\<^isub>l P'" by fact
    hence "P \<Longrightarrow>\<^isub>e\<tau> \<prec>\<^isub>e P'" by(rule lateEarlyStepTau)
    thus ?case by(simp add: Weak_Early_Semantics.weakTransition_def)
  qed
qed

lemma earlyLateTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^isub>e\<^isup>^(\<tau> \<prec>\<^isub>e P')"

  shows "P \<Longrightarrow>\<^isub>l\<^isup>^(\<tau> \<prec>\<^isub>l P')"
proof -
  from assms show ?thesis
  proof(induct rule: Weak_Early_Semantics.transitionCases)
    case Stay
    thus ?case
      by(auto simp add: Early_Semantics.residual.inject Weak_Late_Semantics.weakTransition_def)
  next
    case Step
    have "P \<Longrightarrow>\<^isub>e\<tau> \<prec>\<^isub>e P'" by fact
    hence "P \<Longrightarrow>\<^isub>l\<tau> \<prec>\<^isub>l P'" by(rule earlyLateStepTau)
    thus ?case by(simp add: Weak_Late_Semantics.weakTransition_def)
  qed
qed

lemma tauEq:
  fixes P  :: pi
  and   P' :: pi
  
  shows "P \<Longrightarrow>\<^isub>e\<^isup>^\<tau> \<prec>\<^isub>e P' = P \<Longrightarrow>\<^isub>l\<^isup>^\<tau> \<prec>\<^isub>l P'"
by(blast intro: earlyLateTau lateEarlyTau)

(****************** Weak Simulation ******************)

abbreviation weakSimStepLate_judge ("_ \<leadsto>\<^isub>l<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^isub>l<Rel> Q \<equiv> Weak_Late_Step_Sim.weakStepSim P Rel Q"
abbreviation weakSimStepEarly_judge ("_ \<leadsto>\<^isub>e<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^isub>e<Rel> Q \<equiv> Weak_Early_Step_Sim.weakStepSimulation P Rel Q"
abbreviation weakSimLate_judge ("_ \<leadsto>\<^isub>l\<^isup>^<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^isub>l\<^isup>^<Rel> Q \<equiv> Weak_Late_Sim.weakSimulation P Rel Q"
abbreviation weakSimEarly_judge ("_ \<leadsto>\<^isub>e\<^isup>^<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^isub>e\<^isup>^<Rel> Q \<equiv> Weak_Early_Sim.weakSimulation P Rel Q"

lemma lateEarlyStepSim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^isub>l<Rel> Q"

  shows "P \<leadsto>\<^isub>e<Rel> Q"
proof(induct rule: Weak_Early_Step_Sim.simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>\<^isub>ea<\<nu>x> \<prec>\<^isub>e Q'" by fact
  hence "Q \<longmapsto>\<^isub>la<\<nu>x> \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately obtain P' where PTrans: "P \<Longrightarrow>\<^isub>la<\<nu>x> \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Step_Sim.simE)
  from PTrans have "P \<Longrightarrow>\<^isub>ea<\<nu>x> \<prec>\<^isub>e P'" by(rule lateEarlyStepBoundOutput)
  with P'RelQ' show ?case by blast
next
  case(Free Q' \<alpha>)
  have "Q \<longmapsto>\<^isub>e Early_Semantics.residual.FreeR \<alpha> Q'" by fact
  thus ?case
  proof(cases \<alpha>, auto)
    fix a u
    assume "Q \<longmapsto>\<^isub>ea<u> \<prec>\<^isub>e Q'"
    then obtain Q'' x where QTrans: "Q \<longmapsto>\<^isub>la<x> \<prec>\<^isub>l Q''" and Q'eqQ'': "Q' = Q''[x::=u]"
                        and xFreshP: "x \<sharp> P"
      by(blast dest: Strong_Early_Late_Comp.earlyLateInput[of _ _ _ _ P])
    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow> a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q''[x::=u]) \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>ea<u> \<prec>\<^isub>e P'" by(rule lateEarlyStepInput)
    with P'RelQ' Q'eqQ'' show "\<exists>P'. P \<Longrightarrow>\<^isub>ea<u> \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel" by blast
  next
    fix a b
    assume "Q \<longmapsto>\<^isub>ea[b] \<prec>\<^isub>e Q'"
    hence "Q \<longmapsto>\<^isub>la[b] \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateOutput)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^isub>la[b] \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>ea[b] \<prec>\<^isub>e P'" by(rule lateEarlyStepOutput)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^isub>ea[b] \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel"  by blast
  next
    assume "Q \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e Q'"
    hence "Q \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateTau)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^isub>l\<tau> \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>e\<tau> \<prec>\<^isub>e P'" by(rule lateEarlyStepTau)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^isub>e\<tau> \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel"  by blast
  qed
qed

lemma lateEarlySim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^isub>l\<^isup>^<Rel> Q"

  shows "P \<leadsto>\<^isub>e\<^isup>^<Rel> Q"
proof(induct rule: Weak_Early_Sim.simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>\<^isub>ea<\<nu>x> \<prec>\<^isub>e Q'" by fact
  hence "Q \<longmapsto>\<^isub>la<\<nu>x> \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately obtain P' where PTrans: "P \<Longrightarrow>\<^isub>l\<^isup>^a<\<nu>x> \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Sim.simE)
  from PTrans have "P \<Longrightarrow>\<^isub>e\<^isup>^a<\<nu>x> \<prec>\<^isub>e P'" by(rule lateEarlyBoundOutput)
  with P'RelQ' show ?case by blast
next
  case(Free Q' \<alpha>)
  have "Q \<longmapsto>\<^isub>e Early_Semantics.residual.FreeR \<alpha> Q'" by fact
  thus ?case
  proof(cases \<alpha>, auto)
    fix a u
    assume "Q \<longmapsto>\<^isub>ea<u> \<prec>\<^isub>e Q'"
    then obtain Q'' x where QTrans: "Q \<longmapsto>\<^isub>la<x> \<prec>\<^isub>l Q''" and Q'eqQ'': "Q' = Q''[x::=u]"
                        and xFreshP: "x \<sharp> P"
      by(blast dest: Strong_Early_Late_Comp.earlyLateInput[of _ _ _ _ P])
    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^isub>lu in P'' \<rightarrow> a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q''[x::=u]) \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>e\<^isup>^a<u> \<prec>\<^isub>e P'" by(rule lateEarlyInput)
    with P'RelQ' Q'eqQ'' show "\<exists>P'. P \<Longrightarrow>\<^isub>e\<^isup>^a<u> \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel" by blast
  next
    fix a b
    assume "Q \<longmapsto>\<^isub>ea[b] \<prec>\<^isub>e Q'"
    hence "Q \<longmapsto>\<^isub>la[b] \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateOutput)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^isub>l\<^isup>^a[b] \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>e\<^isup>^a[b] \<prec>\<^isub>e P'" by(rule lateEarlyOutput)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^isub>e\<^isup>^a[b] \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel"  by blast
  next
    assume "Q \<longmapsto>\<^isub>e\<tau> \<prec>\<^isub>e Q'"
    hence "Q \<longmapsto>\<^isub>l\<tau> \<prec>\<^isub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateTau)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^isub>l\<^isup>^\<tau> \<prec>\<^isub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^isub>e\<^isup>^\<tau> \<prec>\<^isub>e P'" by(rule lateEarlyTau)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^isub>e\<^isup>^\<tau> \<prec>\<^isub>e P' \<and> (P', Q') \<in> Rel"  by blast
  qed
qed

(*************** Bisimulation ***************)

abbreviation weakBisimLate_judge (infixl "\<approx>\<^isub>l" 80) where "P \<approx>\<^isub>l Q \<equiv> (P, Q) \<in> Weak_Late_Bisim.weakBisim"
abbreviation weakBisimEarly_judge (infixl "\<approx>\<^isub>e" 80) where "P \<approx>\<^isub>e Q \<equiv> (P, Q) \<in> Weak_Early_Bisim.weakBisim"
abbreviation weakCongLate_judge (infixl "\<simeq>\<^isub>l" 80) where "P \<simeq>\<^isub>l Q \<equiv> (P, Q) \<in> Weak_Late_Cong.congruence"
abbreviation weakCongEarly_judge (infixl "\<simeq>\<^isub>e" 80) where "P \<simeq>\<^isub>e Q \<equiv> (P, Q) \<in> Weak_Early_Cong.congruence"

lemma lateEarlyBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx>\<^isub>l Q"

  shows "P \<approx>\<^isub>e Q"
proof -
  from assms show ?thesis
  by(coinduct rule: Weak_Early_Bisim.weak_coinduct,
     auto dest: Weak_Late_Bisim.unfoldE intro: lateEarlySim)
qed

lemma lateEarlyCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^isub>l Q"

  shows "P \<simeq>\<^isub>e Q"
proof -
  from lateEarlyBisim have "\<And>P Q. P \<leadsto>\<^isub>l<(Weak_Late_Bisim.weakBisim)> Q \<Longrightarrow> P \<leadsto>\<^isub>l<(Weak_Early_Bisim.weakBisim)> Q"
    by(auto intro: Weak_Late_Step_Sim.monotonic)
  with assms show ?thesis
    by(auto simp add: Weak_Late_Cong.congruence_def Weak_Early_Cong.congruence_def intro: lateEarlyStepSim)
qed

abbreviation weakLateBisimSubst_judge (infixl "\<approx>\<^sup>s\<^isub>l" 80) where "P \<approx>\<^sup>s\<^isub>l Q \<equiv> (P, Q) \<in> (substClosed Weak_Late_Bisim.weakBisim)"
abbreviation weakEarlyBisimSubst_judge (infixl "\<approx>\<^sup>s\<^isub>e" 80) where "P \<approx>\<^sup>s\<^isub>e Q \<equiv> (P, Q) \<in> (substClosed Weak_Early_Bisim.weakBisim)"

abbreviation weakLateCongSubst_judge (infixl "\<simeq>\<^sup>s\<^isub>l" 80) where "P \<simeq>\<^sup>s\<^isub>l Q \<equiv> (P, Q) \<in> (substClosed Weak_Late_Cong.congruence)"
abbreviation weakEarlyTongSubst_judge (infixl "\<simeq>\<^sup>s\<^isub>e" 80) where "P \<simeq>\<^sup>s\<^isub>e Q \<equiv> (P, Q) \<in> (substClosed Weak_Early_Cong.congruence)"

lemma lateEarlyBisimSubst:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx>\<^sup>s\<^isub>l Q"

  shows "P \<approx>\<^sup>s\<^isub>e Q"
using assms
by(auto simp add: substClosed_def intro: lateEarlyBisim)

lemma lateEarlyBisimSubst:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^sup>s\<^isub>l Q"

  shows "P \<simeq>\<^sup>s\<^isub>e Q"
using assms
by(auto simp add: substClosed_def intro: lateEarlyCong)

end