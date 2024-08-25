section "Basic Semantics"

theory Step_Basic
imports Language_Syntax
begin


text \<open>This theory introduces a standard semantics for the commands defined\<close>

subsection "Well-formed programs"
text \<open>A well-formed program is a nonempty list of commands where the head of the list is the "Start" command\<close>

type_synonym prog = "com list"

locale Prog = 
fixes prog :: prog
assumes (* well-formed programs begin with a "Start" command: *) 
wf_prog: "prog \<noteq> [] \<and> hd prog = Start"
begin

text "This is the program counter signifying the end of the program:"
definition "endPC \<equiv> length prog"

text "And some sanity checks for a well formed program..."

lemma lenth_prog_gt_0: "length prog > 0"
using wf_prog by auto

lemma lenth_prog_not_0: "length prog \<noteq> 0"
using wf_prog by auto

lemma endPC_gt_0: "endPC > 0"
unfolding endPC_def using lenth_prog_gt_0 by blast

lemma endPC_not_0: "endPC \<noteq> 0"
unfolding endPC_def using lenth_prog_not_0 by blast


lemma hd_prog_Start: "hd prog = Start" 
using wf_prog by auto

lemma prog_0: "prog ! 0 = Start"
by (metis hd_conv_nth wf_prog)

subsection "Basic Semantics of Commands"
text \<open>The basic small step semantics of the language, parameterised by a fixed program. 
The semantics operate on input streams and memories which are consumed and updated while the program counter moves through the list of commands.
This emulates standard (and expected) execution of the commands defined. Since no speculation is captured in this basic semantics, the Fence command the same as SKIP\<close>

inductive
stepB :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B" 55)
where
Seq_Start_Skip_Fence: 
"pc < endPC \<Longrightarrow> prog!pc \<in> {Start, Skip, Fence} \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>B (Config (Suc pc) s, ibT, ibUT)"
|
Assign:  
"pc < endPC \<Longrightarrow> prog!pc = (x ::= a) \<Longrightarrow> 
 s = State (Vstore vs) avst h p \<Longrightarrow> 
 (Config pc s, ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State (Vstore (vs(x := aval a s))) avst h p), ibT, ibUT)" 
|
ArrAssign:  
"pc < endPC \<Longrightarrow> prog!pc = (arr[index] ::= a) \<Longrightarrow>  
 v = aval index s \<Longrightarrow> w = aval a s \<Longrightarrow> 
 0 \<le> v \<Longrightarrow> v < int (array_bound arr avst) \<Longrightarrow>
 l = array_loc arr (nat v) avst \<Longrightarrow>
 s = State vst avst (Heap h) p
 \<Longrightarrow> 
 (Config pc s, ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State vst avst (Heap (h(l := w))) p), ibT, ibUT)"
|
getTrustedInput: 
"pc < endPC \<Longrightarrow> prog!pc = Input T x \<Longrightarrow>
 (Config pc (State (Vstore vs) avst h p), LCons i ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State (Vstore (vs(x := i))) avst h p), ibT, ibUT)"
|
getUntrustedInput: 
"pc < endPC \<Longrightarrow> prog!pc = Input U x \<Longrightarrow>
 (Config pc (State (Vstore vs) avst h p), ibT, LCons i ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State (Vstore (vs(x := i))) avst h p), ibT, ibUT)"
|
Output: 
"pc < endPC \<Longrightarrow> prog!pc = Output t aexp \<Longrightarrow>
 (Config pc s, ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) s, ibT, ibUT)"
|
Jump: 
"pc < endPC \<Longrightarrow> prog!pc = Jump pc1 \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>B (Config pc1 s, ibT, ibUT)" 
|
IfTrue: 
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 bval b s \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>B (Config pc1 s, ibT, ibUT)" 
|
IfFalse: 
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 \<not> bval b s \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>B (Config pc2 s, ibT, ibUT)" 
|
MaskTrue:  
"pc < endPC \<Longrightarrow> prog!pc = (M x I b T a1 E a2 ) \<Longrightarrow> 
 bval b s \<Longrightarrow>
 s = State (Vstore vs) avst h p \<Longrightarrow>
 (Config pc s, ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State (Vstore (vs(x := aval a1 s))) avst h p), ibT, ibUT)" 
|
MaskFalse:  
"pc < endPC \<Longrightarrow> prog!pc = (M x I b T a1 E a2 ) \<Longrightarrow>
 \<not>bval b s \<Longrightarrow>
 s = State (Vstore vs) avst h p \<Longrightarrow>
 (Config pc s, ibT, ibUT) 
 \<rightarrow>B 
 (Config (Suc pc) (State (Vstore (vs(x := aval a2 s))) avst h p), ibT, ibUT)" 

lemmas stepB_induct = stepB.induct[split_format(complete)]
(* thm stepB_induct *)

abbreviation
  stepsB :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B*" 55)
  where "x \<rightarrow>B* y == star stepB x y"

declare stepB.intros[simp,intro]
(*

*)

(* *)
subsection "State Transitions"
text \<open>Useful lemmas regarding valid transitions of the semantics along with conditions for termination (finalB)\<close>

definition "finalB = final stepB"
lemmas finalB_defs  = final_def finalB_def


lemma finalB_iff_aux:  
"pc < endPC \<and> 
 (\<forall>x i a. prog!pc = (x[i] ::= a) \<longrightarrow> aval i s \<ge> 0 \<and> 
          aval i s < int (array_bound x (getAvstore s))) \<and> 
 (\<forall>y. prog!pc = Input T y \<longrightarrow> ibT \<noteq> LNil) \<and>
 (\<forall>y. prog!pc = Input U y \<longrightarrow> ibUT \<noteq> LNil)
 \<longleftrightarrow> 
 (\<exists>cfg'. (Config pc s, ibT, ibUT) \<rightarrow>B cfg')"
apply (cases s) subgoal for vst avst h p 
apply(cases vst) apply(cases h) subgoal for vs hh apply clarsimp 
(* apply safe subgoal *)
apply (cases "prog!pc")
  subgoal by (auto elim: stepB.cases, blast)
  subgoal by (auto elim: stepB.cases, blast)
  subgoal for t apply(cases t)
     subgoal by(cases ibT, auto elim: stepB.cases, blast) 
     subgoal by(cases ibUT, auto elim: stepB.cases, blast) .
   subgoal for t apply(cases t) 
     subgoal by (auto elim: stepB.cases, blast)
     subgoal by (auto elim: stepB.cases, blast) .
  subgoal by (auto elim: stepB.cases, blast)
  subgoal by (auto elim: stepB.cases, blast)   
  subgoal by (auto elim: stepB.cases, blast)
  subgoal by (auto elim: stepB.cases, blast)
  subgoal by (auto elim: stepB.cases, blast)
  subgoal by (auto elim: stepB.cases,meson IfFalse IfTrue) . . .

lemma finalB_iff: 
"finalB (Config pc s, ibT, ibUT) 
 \<longleftrightarrow>
 (pc \<ge> endPC \<or>
  (\<exists>x i a. prog!pc = (x[i] ::= a) \<and> 
       (\<not> aval i s \<ge> 0 \<or> \<not> aval i s < int (array_bound x (getAvstore s))))) \<or> 
  (\<exists>y. prog!pc = Input T y \<and> ibT = LNil) \<or> 
  (\<exists>y. prog!pc = Input U y \<and> ibUT = LNil)"
using finalB_iff_aux[of pc s ibT ibUT] unfolding finalB_def final_def 
using verit_comp_simplify1(3) by blast


(* *)

lemma stepB_determ:
"cfg_ib \<rightarrow>B cfg_ib' \<Longrightarrow> cfg_ib \<rightarrow>B cfg_ib'' \<Longrightarrow> cfg_ib'' = cfg_ib'"
apply(induction arbitrary: cfg_ib'' rule: stepB.induct)
by (auto elim: stepB.cases)
 
definition nextB :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist" where 
"nextB cfg_ib \<equiv> SOME cfg'_ib'. cfg_ib \<rightarrow>B cfg'_ib'"
 
lemma nextB_stepB: "\<not> finalB cfg_ib \<Longrightarrow> cfg_ib \<rightarrow>B (nextB cfg_ib)"
unfolding nextB_def apply(rule someI_ex) 
unfolding finalB_def final_def by auto

lemma stepB_nextB: "cfg_ib \<rightarrow>B cfg'_ib' \<Longrightarrow> cfg'_ib' = nextB cfg_ib"
unfolding nextB_def apply(rule sym) apply(rule some_equality)
using stepB_determ by auto

lemma nextB_iff_stepB: "\<not> finalB cfg_ib \<Longrightarrow> nextB cfg_ib  = cfg'_ib' \<longleftrightarrow> cfg_ib \<rightarrow>B cfg'_ib'"
using nextB_stepB stepB_nextB by blast

lemma stepB_iff_nextB: "cfg_ib \<rightarrow>B cfg'_ib' \<longleftrightarrow> \<not> finalB cfg_ib \<and> nextB cfg_ib  = cfg'_ib'"
by (metis finalB_def final_def stepB_nextB)

(* *)
subsubsection "Simplification Rules"
text \<open>Sufficient conditions for a given command to "execute" transit to the next state\<close>

lemma nextB_Start_Skip_Fence[simp]:  
"pc < endPC \<Longrightarrow> prog!pc \<in> {Start, Skip, Fence} \<Longrightarrow>
 nextB (Config pc s, ibT, ibUT) = (Config (Suc pc) s, ibT, ibUT)"
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_Assign[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = (x ::= a) \<Longrightarrow>
 s = State (Vstore vs) avst h p \<Longrightarrow> 
 nextB (Config pc s, ibT, ibUT) 
 = 
 (Config (Suc pc) (State (Vstore (vs(x := aval a s))) avst h p), 
    ibT, ibUT)" 
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_ArrAssign[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = (arr[index] ::= a) \<Longrightarrow>
 ls' = readLocs a vst avst (Heap h) \<Longrightarrow> 
 v = aval index s \<Longrightarrow> w = aval a s \<Longrightarrow> 
 0 \<le> v \<Longrightarrow> v < int (array_bound arr avst)  \<Longrightarrow>
 l = array_loc arr (nat v) avst \<Longrightarrow>
 s = State vst avst (Heap h) p 
 \<Longrightarrow> 
 nextB (Config pc s, ibT, ibUT) 
 =
 (Config (Suc pc) (State vst avst (Heap (h(l := w))) p), ibT, ibUT)"
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_getTrustedInput[simp]: 
"pc < endPC \<Longrightarrow> prog!pc = (Input T x) \<Longrightarrow>
 nextB (Config pc (State (Vstore vs) avst h p), LCons i ibT, ibUT) 
 = 
 (Config (Suc pc) (State (Vstore (vs(x := i))) avst h p), ibT, ibUT)"  
  by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_getUntrustedInput[simp]: 
"pc < endPC \<Longrightarrow> prog!pc = (Input U x) \<Longrightarrow>
 nextB (Config pc (State (Vstore vs) avst h p), ibT, LCons i ibUT) 
 = 
 (Config (Suc pc) (State (Vstore (vs(x := i))) avst h p), ibT, ibUT)"  
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_getTrustedInput'[simp]: 
"pc < endPC \<Longrightarrow> prog!pc = Input T x \<Longrightarrow>
 ibT \<noteq> LNil \<Longrightarrow> 
 nextB (Config pc (State (Vstore vs) avst h p), ibT, ibUT) 
 = 
 (Config (Suc pc) (State (Vstore (vs(x := lhd ibT))) avst h p), ltl ibT, ibUT)"  
  by(cases ibT, auto)

lemma nextB_getUntrustedInput'[simp]: 
"pc < endPC \<Longrightarrow> prog!pc = Input U x \<Longrightarrow>
 ibUT \<noteq> LNil \<Longrightarrow> 
 nextB (Config pc (State (Vstore vs) avst h p), ibT, ibUT) 
 = 
 (Config (Suc pc) (State (Vstore (vs(x := lhd ibUT))) avst h p), ibT, ltl ibUT)"  
by(cases ibUT, auto)

lemma nextB_Output[simp]: 
"pc < endPC \<Longrightarrow> prog!pc = Output t aexp \<Longrightarrow>
 nextB (Config pc s, ibT, ibUT) 
 = 
 (Config (Suc pc) s, ibT, ibUT)"
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_Jump[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = Jump pc1 \<Longrightarrow> 
 nextB (Config pc s, ibT, ibUT) = (Config pc1 s, ibT, ibUT)" 
  by(intro stepB_nextB[THEN sym] stepB.intros, simp_all+)

lemma nextB_IfTrue[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 bval b s \<Longrightarrow> 
 nextB (Config pc s, ibT, ibUT) = (Config pc1 s, ibT, ibUT)" 
by(intro stepB_nextB[THEN sym] stepB.intros)

lemma nextB_IfFalse[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 \<not> bval b s \<Longrightarrow> 
 nextB (Config pc s, ibT, ibUT) = (Config pc2 s, ibT, ibUT)" 
by(intro stepB_nextB[THEN sym] stepB.intros)


lemma nextB_MaskTrue[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = (M x I b T a1 E a2) \<Longrightarrow> 
 bval b (State (Vstore vs) avst h p) \<Longrightarrow> 
 nextB (Config pc (State (Vstore vs) avst h p), ibT, ibUT) = 
       (Config (Suc pc) (State (Vstore (vs(x := aval a1 (State (Vstore vs) avst h p)))) avst h p), ibT, ibUT)" 
apply(intro stepB_nextB[THEN sym])
  using MaskTrue by simp

lemma nextB_MaskFalse[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = (M x I b T a1 E a2) \<Longrightarrow> 
 \<not>bval b (State (Vstore vs) avst h p) \<Longrightarrow> 
 nextB (Config pc (State (Vstore vs) avst h p), ibT, ibUT) = 
       (Config (Suc pc) (State (Vstore (vs(x := aval a2 (State (Vstore vs) avst h p)))) avst h p), ibT, ibUT)" 
apply(intro stepB_nextB[THEN sym])
  using MaskFalse by simp
(* *)


lemma finalB_endPC: "pcOf cfg = endPC \<Longrightarrow> finalB (cfg,ibT, ibUT)"
  by (metis finalB_iff config.collapse le_eq_less_or_eq)

lemma stepB_endPC: "pcOf cfg = endPC \<Longrightarrow> \<not> (cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')"
  by (simp add: stepB_iff_nextB finalB_endPC)

lemma stepB_imp_le_endPC: assumes "(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')"
  shows "pcOf cfg < endPC"
  using assms by(cases rule: stepB.cases, simp_all)

(* *)

lemma stebB_0: "(Config 0 s, ibT, ibUT) \<rightarrow>B (Config 1 s, ibT, ibUT)"
using prog_0 by (simp add: endPC_gt_0)

subsubsection "Elimination Rules"
text "In the unwinding proofs of relative security it is often the case that two traces will progress in lockstep, when doing so we wish to preserve/update invariants of the current state. T
he following are some useful elimination rules to help simplify reasoning"
(*elims*)
lemma stepB_Seq_Start_Skip_FenceE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc \<in> {Start, Skip, Fence}\<close>
    shows \<open>vs' = vs \<and> ibT = ibT' \<and> ibUT = ibUT' \<and> 
           pc' = Suc pc \<and> avst' = avst \<and> h' = h \<and>
           p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_AssignE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = (x ::= a)\<close>
    shows \<open>vs' = (vs(x := aval a (stateOf cfg))) \<and>
           ibT = ibT' \<and> ibUT = ibUT' \<and> pc' = Suc pc \<and>
           avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_getTrustedInputE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = Input T x\<close>
    shows \<open>vs' = (vs(x := lhd ibT)) \<and>
           ibT' = ltl ibT \<and> ibUT = ibUT' \<and> pc' = Suc pc \<and>
           avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_getUntrustedInputE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = Input U x\<close>
    shows \<open>vs' = (vs(x := lhd ibUT)) \<and>
           ibT' = ibT \<and> ibUT' = ltl ibUT \<and> pc' = Suc pc \<and>
           avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_OutputE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = Output t aexp\<close>
    shows \<open>vs' = vs \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> 
           pc' = Suc pc \<and> avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_JumpE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = Jump pc1\<close>
    shows \<open>vs' = vs \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> 
           pc' = pc1 \<and> avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto

lemma stepB_IfTrueE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = IfJump b pc1 pc2\<close> and \<open>bval b (stateOf cfg)\<close>
    shows \<open>vs' = vs \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> 
           pc' = pc1 \<and> avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto 

lemma stepB_IfFalseE:
  assumes \<open>(cfg, ibT, ibUT) \<rightarrow>B (cfg', ibT',ibUT')\<close>
      and \<open>cfg = (Config pc (State (Vstore vs) avst h p))\<close> 
      and \<open>cfg' = (Config pc' (State (Vstore vs') avst' h' p'))\<close>
      and \<open>prog!pc = IfJump b pc1 pc2\<close> and \<open>\<not>bval b (stateOf cfg)\<close>
    shows \<open>vs' = vs \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> 
           pc' = pc2 \<and> avst' = avst \<and> h' = h \<and> p' = p\<close>
  using assms apply (cases "(cfg, ibT, ibUT)" "(cfg', ibT',ibUT')" rule: stepB.cases)
  by auto 

end (* context Prog *)

subsection "Read locations"

text \<open>For modeling Spectre-like vulnerabilities, we record memory reads (as in \cite{Cheang}),
i.e., accessed for reading during the execution. 
We let readLocs(pc,u) be the (possibly empty) set of locations 
that are read when executing the current command c - computed from all sub-expressions of the form a[e]. i.e. array reads.
For example, if c is the assignment "x = a [b[3]]", then readLocs returns two locations: counting from 0, the 3rd location of b and the b[3]'th location of a.\<close>
(* the locations read by an arithmetic expression: *)
fun readLocsA :: "aexp \<Rightarrow> state \<Rightarrow> loc set" and 
readLocsB :: "bexp \<Rightarrow> state \<Rightarrow> loc set" where
"readLocsA (N n) s = {}" 
|
"readLocsA (V x) s = {}" 
|
"readLocsA (VA arr index) s = 
 insert (array_loc arr (nat (aval index s)) (getAvstore s)) 
        (readLocsA index s)"
|
"readLocsA (Plus a1 a2) s = readLocsA a1 s \<union> readLocsA a2 s"
|
"readLocsA (Times a1 a2) s = readLocsA a1 s \<union> readLocsA a2 s"
|
"readLocsA (Ite b a1 a2) s = readLocsB b s \<union> readLocsA a1 s \<union> readLocsA a2 s"
|
"readLocsA (Fun a b) s = {}"
|
"readLocsB (Bc c) s= {}" 
|
"readLocsB (Not b) s = readLocsB b s" 
|
"readLocsB (And b1 b2) s = readLocsB b1 s \<union> readLocsB b2 s" 
|
"readLocsB (Less a1 a2) s = readLocsA a1 s \<union> readLocsA a2 s" 

(* the locations read by a command: *)
fun readLocsC :: "com \<Rightarrow> state \<Rightarrow> loc set" where
"readLocsC (x ::= a) s = readLocsA a s"
|
"readLocsC (arr[index] ::= a) s = readLocsA a s"
|
"readLocsC (Output t a) s = readLocsA a s"
|
"readLocsC (IfJump b n1 n2) s = readLocsB b s"
|
"readLocsC (M x I b T a1 E a2) s = readLocsB b s \<union> (if (bval b s) then readLocsA a1 s 
                                    else readLocsA a2 s) "
|
"readLocsC _ _ = {}"

context Prog
begin

(* the locations read by a configuration: *)
definition "readLocs cfg \<equiv> readLocsC (prog!(pcOf cfg)) (stateOf cfg)"

end (* context Prog *)


end