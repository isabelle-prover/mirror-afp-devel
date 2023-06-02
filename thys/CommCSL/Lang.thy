section \<open>Imperative Concurrent Language\<close>

text \<open>This file defines the syntax and semantics of a concurrent programming language,
based on Viktor Vafeiadis' Isabelle soundness proof of CSL~\cite{cslsound},
and adapted to Isabelle 2016-1 by Qin Yu and James Brotherston
(see https://people.mpi-sws.org/~viktor/cslsound/).\<close>

theory Lang
imports Main StateModel
begin

subsection \<open>Language Syntax and Semantics\<close>

type_synonym  state = "store \<times> normal_heap"        (*r States *)

datatype exp =                  (*r Arithmetic expressions *)
    Evar var                    (*r Variable *)
  | Enum nat                    (*r Constant *)
  | Eplus exp exp               (*r Addition *)

datatype bexp =                 (*r Boolean expressions *)
    Beq exp exp                 (*r Equality of expressions *)
  | Band bexp bexp              (*r Conjunction *)
  | Bnot bexp                   (*r Negation *)
  | Btrue

datatype cmd =                  (*r Commands *)
    Cskip                       (*r Empty command *)
  | Cassign var exp             (*r Assignment *)
  | Cread   var exp             (*r Memory load *)
  | Cwrite  exp exp             (*r Memory store *)
  | Calloc  var exp             (*r Memory allocation *)
  | Cdispose exp                (*r Memory de-allocation *)
  | Cseq   cmd cmd              (*r Sequential composition *)
  | Cpar   cmd cmd              (*r Parallel composition *)
  | Cif    bexp cmd cmd         (*r If-then-else *)
  | Cwhile bexp cmd             (*r While loops *)
  | Catomic   cmd         (*r Atomic block *)


text \<open>Arithmetic expressions (@{text exp}) consist of variables, constants, and
arithmetic operations. Boolean expressions (@{text bexp}) consist of comparisons
between arithmetic expressions.  Commands (@{text cmd}) include the empty command,
variable assignments, memory reads, writes, allocations and deallocations,
sequential and parallel composition, conditionals, while loops, local variable
declarations, and atomic statements.\<close>



subsubsection \<open>Semantics of expressions\<close>

text \<open>Denotational semantics for arithmetic and boolean expressions.\<close>

primrec
  edenot :: "exp \<Rightarrow> store \<Rightarrow> nat"
where
    "edenot (Evar v) s      = s v"
  | "edenot (Enum n) s      = n"
  | "edenot (Eplus e1 e2) s = edenot e1 s + edenot e2 s"

primrec
  bdenot :: "bexp \<Rightarrow> store \<Rightarrow> bool" 
where
    "bdenot (Beq e1 e2) s   = (edenot e1 s = edenot e2 s)"
  | "bdenot (Band b1 b2) s  = (bdenot b1 s \<and> bdenot b2 s)"
  | "bdenot (Bnot b) s      = (\<not> bdenot b s)"
  | "bdenot Btrue _      = True"

subsubsection \<open>Semantics of commands\<close>

text \<open>We give a standard small-step operational semantics to commands with configurations being command-state pairs.\<close>

inductive
  red :: "cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool"
and red_rtrans :: "cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool"
where
  red_Seq1[intro]: "red (Cseq Cskip C) \<sigma> C \<sigma>"
| red_Seq2[elim]: "red C1 \<sigma> C1' \<sigma>' \<Longrightarrow> red (Cseq C1 C2) \<sigma> (Cseq C1' C2) \<sigma>'" 
| red_If1[intro]: "bdenot B (fst \<sigma>) \<Longrightarrow> red (Cif B C1 C2) \<sigma> C1 \<sigma>"
| red_If2[intro]: "\<not> bdenot B (fst \<sigma>) \<Longrightarrow> red (Cif B C1 C2) \<sigma> C2 \<sigma>"
| red_Atomic[intro]:  "red_rtrans C \<sigma> Cskip \<sigma>' \<Longrightarrow> red (Catomic C) \<sigma> Cskip \<sigma>'"
| red_Par1[elim]: "red C1 \<sigma> C1' \<sigma>' \<Longrightarrow> red (Cpar C1 C2) \<sigma> (Cpar C1' C2) \<sigma>'" 
| red_Par2[elim]: "red C2 \<sigma> C2' \<sigma>' \<Longrightarrow> red (Cpar C1 C2) \<sigma> (Cpar C1 C2') \<sigma>'"
| red_Par3[intro]: "red (Cpar Cskip Cskip) \<sigma> (Cskip) \<sigma>"
| red_Loop[intro]: "red (Cwhile B C) \<sigma> (Cif B (Cseq C (Cwhile B C)) Cskip) \<sigma>"
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x := edenot E s), h) \<rbrakk> \<Longrightarrow> red (Cassign x E) \<sigma> Cskip \<sigma>'"
| red_Read[intro]:  "\<lbrakk> \<sigma> = (s,h); h(edenot E s) = Some v; \<sigma>' = (s(x := v), h) \<rbrakk> \<Longrightarrow> red (Cread x E) \<sigma> Cskip \<sigma>'"
| red_Write[intro]: "\<lbrakk> \<sigma> = (s,h);  \<sigma>' = (s, h(edenot E s \<mapsto> edenot E' s)) \<rbrakk>  \<Longrightarrow> red (Cwrite E E') \<sigma> Cskip \<sigma>'"
| red_Alloc[intro]: "\<lbrakk> \<sigma> = (s,h); v \<notin> dom h; \<sigma>' = (s(x := v), h(v \<mapsto> edenot E s)) \<rbrakk>  \<Longrightarrow> red (Calloc x E) \<sigma> Cskip \<sigma>'"
| red_Free[intro]:  "\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s, h(edenot E s := None)) \<rbrakk> \<Longrightarrow> red (Cdispose E) \<sigma> Cskip \<sigma>'"

| NoStep: "red_rtrans C \<sigma> C \<sigma>"
| OneMoreStep: "\<lbrakk> red C \<sigma> C' \<sigma>' ; red_rtrans C' \<sigma>' C'' \<sigma>'' \<rbrakk> \<Longrightarrow> red_rtrans C \<sigma> C'' \<sigma>''"


inductive_cases red_par_cases: "red (Cpar C1 C2) \<sigma> C' \<sigma>'"
inductive_cases red_atomic_cases: "red (Catomic C) \<sigma> C' \<sigma>'"

subsubsection \<open>Abort semantics\<close>

inductive
  aborts :: "cmd \<Rightarrow> state \<Rightarrow> bool"
where
  aborts_Seq[intro]:   "aborts C1 \<sigma> \<Longrightarrow> aborts (Cseq C1 C2) \<sigma>"
| aborts_Atomic[intro]: "\<lbrakk> red_rtrans C \<sigma> C' \<sigma>' ; aborts C' \<sigma>' \<rbrakk> \<Longrightarrow> aborts (Catomic C) \<sigma>"
| aborts_Par1[intro]:  "aborts C1 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>" 
| aborts_Par2[intro]:  "aborts C2 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"
| aborts_Read[intro]:  "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cread x E) \<sigma>"
| aborts_Write[intro]: "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cwrite E E') \<sigma>"
| aborts_Free[intro]:  "edenot E (fst \<sigma>) \<notin> dom (snd \<sigma>) \<Longrightarrow> aborts (Cdispose E) \<sigma>"

inductive_cases abort_atomic_cases: "aborts (Catomic C) \<sigma>"

subsection \<open>Useful Definitions and Results\<close>

text \<open>The free variables of expressions, boolean expressions, and
commands are defined as expected:\<close>

primrec
  fvE :: "exp \<Rightarrow> var set"
where
  "fvE (Evar v) = {v}"
| "fvE (Enum n) = {}"
| "fvE (Eplus e1 e2) = (fvE e1 \<union> fvE e2)"

primrec
  fvB :: "bexp \<Rightarrow> var set"
where
  "fvB (Beq e1 e2)  = (fvE e1 \<union> fvE e2)"
| "fvB (Band b1 b2) = (fvB b1 \<union> fvB b2)"
| "fvB (Bnot b)     = (fvB b)"
| "fvB Btrue        = {}"

primrec
  fvC :: "cmd \<Rightarrow> var set"
where
  "fvC (Cskip)         = {}"
| "fvC (Cassign v E)   = ({v} \<union> fvE E)"
| "fvC (Cread v E)     = ({v} \<union> fvE E)"
| "fvC (Cwrite E1 E2)  = (fvE E1 \<union> fvE E2)"
| "fvC (Calloc v E)    = ({v} \<union> fvE E)"
| "fvC (Cdispose E)    = (fvE E)"
| "fvC (Cseq C1 C2)    = (fvC C1 \<union> fvC C2)"
| "fvC (Cpar C1 C2)    = (fvC C1 \<union> fvC C2)"
| "fvC (Cif B C1 C2)   = (fvB B \<union> fvC C1 \<union> fvC C2)"
| "fvC (Cwhile B C)    = (fvB B \<union> fvC C)"
| "fvC (Catomic C)     = (fvC C)"

primrec
  wrC :: "cmd \<Rightarrow> var set"
where
  "wrC (Cskip)         = {}"
| "wrC (Cassign v E)   = {v}"
| "wrC (Cread v E)     = {v}"
| "wrC (Cwrite E1 E2)  = {}"
| "wrC (Calloc v E)    = {v}"
| "wrC (Cdispose E)    = {}"
| "wrC (Cseq C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cpar C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cif B C1 C2)   = (wrC C1 \<union> wrC C2)"
| "wrC (Cwhile B C)    = (wrC C)"
| "wrC (Catomic C)     = (wrC C)"


primrec
  subE :: "var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp"
where
  "subE x E (Evar y)      = (if x = y then E else Evar y)"
| "subE x E (Enum n)      = Enum n"
| "subE x E (Eplus e1 e2) = Eplus (subE x E e1) (subE x E e2)"

primrec
  subB :: "var \<Rightarrow> exp \<Rightarrow> bexp \<Rightarrow> bexp"
where
  "subB x E (Beq e1 e2)  = Beq (subE x E e1) (subE x E e2)"
| "subB x E (Band b1 b2) = Band (subB x E b1) (subB x E b2)"
| "subB x E (Bnot b)     = Bnot (subB x E b)"
| "subB x E Btrue = Btrue"

text \<open>Basic properties of substitutions:\<close>

lemma subE_assign:
 "edenot (subE x E e) s = edenot e (s(x := edenot E s))"
  by (induct e, simp_all)

lemma subB_assign:
 "bdenot (subB x E b) s = bdenot b (s(x := edenot E s))"
proof (induct b)
  case (Beq x1 x2)
  then show ?case
    using bdenot.simps(1) subB.simps(1) subE_assign by presburger
qed (simp_all)

inductive_cases red_skip_cases: "red Cskip \<sigma> C' \<sigma>'"
inductive_cases aborts_skip_cases: "aborts Cskip \<sigma>"


lemma skip_simps[simp]: 
  "\<not> red Cskip \<sigma> C' \<sigma>'"
  "\<not> aborts Cskip \<sigma>"
  using red_skip_cases apply blast
  using aborts_skip_cases by blast


definition 
  agrees :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
where
  "agrees X s s' \<equiv> \<forall>x \<in> X. s x = s' x"

lemma agrees_union:
  "agrees (A \<union> B) s s' \<longleftrightarrow> agrees A s s' \<and> agrees B s s'"
  by (meson Un_iff agrees_def)

text \<open>Proposition 4.1: Properties of basic properties of @{term red}.\<close>

lemma agreesI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> s x = s' x"
  shows "agrees X s s'"
  using agrees_def assms by blast

lemma red_properties: 
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> fvC C' \<subseteq> fvC C \<and> wrC C' \<subseteq> wrC C \<and> agrees (- wrC C) (fst \<sigma>') (fst \<sigma>)"
  "red_rtrans C \<sigma> C' \<sigma>' \<Longrightarrow> fvC C' \<subseteq> fvC C \<and> wrC C' \<subseteq> wrC C \<and> agrees (- wrC C) (fst \<sigma>') (fst \<sigma>)"
proof (induct rule: red_red_rtrans.inducts)
  case (OneMoreStep C \<sigma> C' \<sigma>' C'' \<sigma>'')
  then have "fvC C'' \<subseteq> fvC C"
    by blast
  moreover have "wrC C'' \<subseteq> wrC C"
    using OneMoreStep.hyps(2) OneMoreStep.hyps(4) by blast
  moreover have "agrees (- wrC C) (fst \<sigma>'') (fst \<sigma>)"
  proof (rule agreesI)
    fix x assume "x \<in> - wrC C"
    then have "x \<in> -wrC C' \<and> x \<in> -wrC C''"
      using OneMoreStep.hyps(2) OneMoreStep.hyps(4) by blast
    then show "fst \<sigma>'' x = fst \<sigma> x"
      by (metis OneMoreStep.hyps(2) OneMoreStep.hyps(4) \<open>x \<in> - wrC C\<close> agrees_def)
  qed
  ultimately show ?case by simp
qed (auto simp add: agrees_def)

text \<open>Proposition 4.2: Semantics does not depend on variables not free in the term\<close>

lemma exp_agrees: "agrees (fvE E) s s' \<Longrightarrow> edenot E s = edenot E s'"
by (simp add: agrees_def, induct E, auto)

lemma bexp_agrees:
  "agrees (fvB B) s s' \<Longrightarrow> bdenot B s = bdenot B s'"
proof (induct B)
  case (Beq x1 x2)
  then have "agrees (fvE x1) s s' \<and> agrees (fvE x2) s s'"
    by (simp add: agrees_def)
  then show ?case using exp_agrees
    by force
next
  case (Band B1 B2)
  then show ?case
    by (simp add: agrees_def)
qed (simp_all)

lemma red_not_in_fv_not_touched:
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> x \<notin> fvC C \<Longrightarrow> fst \<sigma> x = fst \<sigma>' x"
  "red_rtrans C \<sigma> C' \<sigma>' \<Longrightarrow> x \<notin> fvC C \<Longrightarrow> fst \<sigma> x = fst \<sigma>' x"
proof (induct arbitrary: rule: red_red_rtrans.inducts)
  case (OneMoreStep C \<sigma> C' \<sigma>' C'' \<sigma>'')
  then show "fst \<sigma> x = fst \<sigma>'' x"
    by (metis red_properties(1) subsetD)
qed (auto)

lemma agrees_update1:
  assumes "agrees X s s'"
  shows "agrees X (s(x := v)) (s'(x := v))"
proof (rule agreesI)
  fix y show "y \<in> X \<Longrightarrow> (s(x := v)) y = (s'(x := v)) y"
    apply (cases "y = x")
    apply simp
    using agrees_def assms by fastforce
qed

lemma agrees_update2:
  assumes "agrees X s s'"
      and "x \<notin> X"
  shows "agrees X (s(x := v)) (s'(x := v'))"
proof (rule agreesI)
  fix y show "y \<in> X \<Longrightarrow> (s(x := v)) y = (s'(x := v')) y"
    apply (cases "y = x")
    using assms(2) apply blast
    using agrees_def assms(1) by fastforce
qed

lemma red_agrees_aux:
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> (\<forall>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC C \<subseteq> X \<longrightarrow>
   (\<exists>s' h'. red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'))"
   "red_rtrans C \<sigma> C' \<sigma>' \<Longrightarrow> (\<forall>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC C \<subseteq> X \<longrightarrow>
   (\<exists>s' h'. red_rtrans C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'))"
proof (induct rule: red_red_rtrans.inducts)
  case (red_If1 B \<sigma> C1 C2)
  then show ?case
  proof (clarify)
    fix X s h
    assume asm0: "bdenot B (fst \<sigma>)" "agrees X (fst \<sigma>) s" "fvC (Cif B C1 C2) \<subseteq> X"
    then have "bdenot B s"
      using Un_iff agrees_def[of X "fst \<sigma>" s] bexp_agrees fvC.simps(9) in_mono agrees_def[of "fvB B"]
      by fastforce
    then show "\<exists>s' h'. red (Cif B C1 C2) (s, snd \<sigma>) C1 (s', h') \<and> agrees X (fst \<sigma>) s' \<and> snd \<sigma> = h'"
      by (metis asm0(2) fst_eqD red_red_rtrans.red_If1)
  qed
next
  case (red_If2 B \<sigma> C1 C2)
  then show ?case
  proof (clarify)
    fix X s h
    assume asm0: "\<not> bdenot B (fst \<sigma>)" "agrees X (fst \<sigma>) s" "fvC (Cif B C1 C2) \<subseteq> X"
    then have "\<not> bdenot B s"
      using Un_subset_iff agrees_def[of X] agrees_def[of "fvB B"] bexp_agrees fvC.simps(9) in_mono
      by metis
    then show "\<exists>s' h'. red (Cif B C1 C2) (s, snd \<sigma>) C2 (s', h') \<and> agrees X (fst \<sigma>) s' \<and> snd \<sigma> = h'"
      by (metis asm0(2) fst_eqD red_red_rtrans.red_If2)
  qed
next
  case (red_Assign \<sigma> ss hh \<sigma>' x E)
  then show ?case
  proof (clarify)
    fix X s h
    assume asm0: "\<sigma>' = (ss(x := edenot E ss), hh)" "\<sigma> = (ss, hh)" "agrees X (fst (ss, hh)) s" "fvC (Cassign x E) \<subseteq> X"
    then have "edenot E s = edenot E ss"
      using exp_agrees fst_conv fvC.simps(2)
      by (metis (mono_tags, lifting) Un_subset_iff agrees_def in_mono)
    then have "red (Cassign x E) (ss, snd (s, h)) Cskip (ss(x := edenot E s), h)"
      by force
    moreover have "agrees X (fst (s(x := edenot E s), h)) (ss(x := edenot E s))"
    proof (rule agreesI)
      fix y assume "y \<in> X"
      show "fst (s(x := edenot E s), h) y = (ss(x := edenot E s)) y"
        apply (cases "x = y")
        apply simp
        by (metis \<open>y \<in> X\<close> agrees_def asm0(3) fstI fun_upd_other)
    qed
    ultimately show "\<exists>s' h'. red (Cassign x E) (s, snd (ss, hh)) Cskip (s', h') \<and> agrees X (fst (ss(x := edenot E ss), hh)) s' \<and> snd (ss(x := edenot E ss), hh) = h'"
      using \<open>edenot E s = edenot E ss\<close> 
      by (metis agrees_update1 asm0(3) fst_conv red_red_rtrans.red_Assign snd_conv)
  qed
next
  case (red_Read \<sigma> ss hh E v \<sigma>' x)
  have "\<And>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cread x E) \<subseteq> X \<Longrightarrow> (\<exists>s' h'. red (Cread x E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  proof -
    fix s h assume asm0: "agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cread x E) \<subseteq> X"
    then have "hh (edenot E s) = Some v"
      using red_Read(1) red_Read(2) exp_agrees fstI fvC.simps(3) Un_subset_iff agrees_def[of "fvE E"] in_mono
        agrees_def[of X] by metis
    then have "agrees X (fst \<sigma>') (s(x := v))"
      by (metis asm0(1) agrees_update1 fstI red_Read.hyps(1) red_Read.hyps(3) red_Read.prems)
    then show "\<exists>s' h'. red (Cread x E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      using \<open>hh (edenot E s) = Some v\<close> red_Read.hyps(1) red_Read.hyps(3) red_Read.prems
      by (metis asm0 red_red_rtrans.red_Read snd_conv)
  qed
  then show ?case by blast
next
  case (red_Write \<sigma> ss hh \<sigma>' E E')
  have "\<And>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cwrite E E') \<subseteq> X \<Longrightarrow> (\<exists>s' h'. red (Cwrite E E') (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  proof -
    fix s h assume asm0: "agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cwrite E E') \<subseteq> X"
    then have "edenot E ss = edenot E s \<and> edenot E' ss = edenot E' s"
      using red_Write(1) exp_agrees fstI fvC.simps(4)
      by (metis (mono_tags, lifting) Un_subset_iff agrees_def in_mono)
    then show "\<exists>s' h'. red (Cwrite E E') (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      by (metis fst_conv asm0 red_Write.hyps(1) red_Write.hyps(2) red_Write.prems red_red_rtrans.red_Write snd_conv)
  qed
  then show ?case by blast
next
  case (red_Alloc \<sigma> ss hh v \<sigma>' x E)
  have "\<And>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Calloc x E) \<subseteq> X \<Longrightarrow> (\<exists>s' h'. red (Calloc x E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  proof -
    fix s h assume asm0: "agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Calloc x E) \<subseteq> X"
    then have "edenot E ss = edenot E s"
      using red_Alloc(1) exp_agrees fst_conv fvC.simps(5)
      by (metis (mono_tags, lifting) Un_iff agrees_def in_mono)
    then have "agrees X (fst \<sigma>') (s(x := v))"
      by (metis agrees_update1 asm0 fstI red_Alloc.hyps(1) red_Alloc.hyps(3) red_Alloc.prems)
    then show "\<exists>s' h'. red (Calloc x E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      by (metis \<open>edenot E ss = edenot E s\<close> red_Alloc.hyps(1) red_Alloc.hyps(2) red_Alloc.hyps(3) red_Alloc.prems red_red_rtrans.red_Alloc snd_eqD asm0)
  qed
  then show ?case by blast
next
  case (red_Free \<sigma> ss hh \<sigma>' E)
  have "\<And>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cdispose E) \<subseteq> X \<Longrightarrow> (\<exists>s' h'. red (Cdispose E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  proof -
    fix s h assume asm0: "agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC (Cdispose E) \<subseteq> X"
    then have "edenot E ss = edenot E s"
      using red_Free(1) exp_agrees fst_eqD fvC.simps(6)
      by (metis agrees_def in_mono)
    then show "\<exists>s' h'. red (Cdispose E) (s, h) Cskip (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      using red_Free.hyps(1) red_Free.hyps(2) red_Free.prems asm0 by fastforce
  qed
  then show ?case by blast
next
  case (NoStep C \<sigma>)
  then show ?case
    using red_red_rtrans.NoStep by blast
next
  case (OneMoreStep C \<sigma> C' \<sigma>' C'' \<sigma>'')
  have "\<And>s h. agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC C \<subseteq> X \<Longrightarrow> (\<exists>s' h'. red_rtrans C (s, h) C'' (s', h') \<and> agrees X (fst \<sigma>'') s' \<and> snd \<sigma>'' = h')"
  proof -
    fix s h assume asm0: "agrees X (fst \<sigma>) s \<and> snd \<sigma> = h \<and> fvC C \<subseteq> X"
    then obtain h' s' where "red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      using OneMoreStep(2) by auto
    then obtain h'' s'' where "red_rtrans C' (s', h') C'' (s'', h'') \<and> agrees X (fst \<sigma>'') s'' \<and> snd \<sigma>'' = h''"
      using OneMoreStep.hyps(4) asm0 red_properties(1) by fastforce
    then show "\<exists>s' h'. red_rtrans C (s, h) C'' (s', h') \<and> agrees X (fst \<sigma>'') s' \<and> snd \<sigma>'' = h'"
      using \<open>red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'\<close> red_red_rtrans.OneMoreStep by blast
  qed
  then show ?case by blast
qed (fastforce+)

lemma red_agrees[rule_format]:
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> \<forall>X s. agrees X (fst \<sigma>) s \<longrightarrow> snd \<sigma> = h \<longrightarrow> fvC C \<subseteq> X \<longrightarrow> 
   (\<exists>s' h'. red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h')"
  using red_agrees_aux(1) by blast

lemma aborts_agrees:
  assumes "aborts C \<sigma>"
      and "agrees (fvC C) (fst \<sigma>) s"
      and "snd \<sigma> = h"
    shows "aborts C (s, h)"
  using assms
proof (induct arbitrary: s h rule: aborts.induct)
  case (aborts_Atomic C \<sigma> C' \<sigma>')
  then obtain s' where "red_rtrans C (s, h) C' (s', snd \<sigma>') \<and> agrees (fvC C) (fst \<sigma>') s'"
    by (metis dual_order.refl fvC.simps(11) red_agrees_aux(2))
  moreover have "agrees (fvC C') (fst \<sigma>') s'"
    using calculation red_properties(2)
    by (meson agrees_def in_mono)
  ultimately show ?case
    using aborts_Atomic.hyps(3) by blast
next
  case (aborts_Read E \<sigma> x)
  then show ?case
    using aborts.aborts_Read[of E \<sigma> x] exp_agrees[of E "fst \<sigma>" s] fst_conv fvC.simps(3) snd_conv
    by (simp add: aborts.aborts_Read agrees_def)
next
  case (aborts_Write E \<sigma> E')
  then show ?case
    using aborts.aborts_Write[of E \<sigma> E'] exp_agrees[of _ "fst \<sigma>" s] fst_conv fvC.simps(4)[of E E'] snd_conv
    by (simp add: aborts.aborts_Write agrees_def)
next
  case (aborts_Free E \<sigma>)
  then show ?case
    using exp_agrees by auto
next
  case (aborts_Par1 C1 \<sigma> C2)
  then have "agrees (fvC C1) (fst \<sigma>) s"
    by (simp add: agrees_def)
  then show ?case using aborts.aborts_Par1
    by (simp add: aborts_Par1.hyps(2) aborts_Par1.prems(2))
next
  case (aborts_Par2 C2 \<sigma> C1)
  then have "agrees (fvC C2) (fst \<sigma>) s"
    by (simp add: agrees_def)
  then show ?case using aborts.aborts_Par2
    by (simp add: aborts_Par2.hyps(2) aborts_Par2.prems(2))
next
  case (aborts_Seq C1 \<sigma> C2)
  then have "agrees (fvC C1) (fst \<sigma>) s"
    by (simp add: agrees_def)
  then show ?case
    by (simp add: aborts.aborts_Seq aborts_Seq.hyps(2) aborts_Seq.prems(2))
qed

corollary exp_agrees2[simp]:
  "x \<notin> fvE E \<Longrightarrow> edenot E (s(x := v)) = edenot E s"
by (rule exp_agrees, simp add: agrees_def)

lemma agrees_update:
  assumes "a \<notin> S"
  shows "agrees S s (s(a := v))"
  by (simp add: agrees_def assms)


lemma agrees_comm:
  "agrees S s s' \<longleftrightarrow> agrees S s' s"
  by (metis agrees_def)

lemma not_in_dom:
  assumes "x \<notin> dom s"
  shows "s x = None"
  using assms by auto

lemma agrees_minusD:
  "agrees (-X) x y \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> agrees Y x y"
  by (metis Int_Un_eq(2) agrees_union compl_le_swap1 inf.order_iff inf_shunt)

end