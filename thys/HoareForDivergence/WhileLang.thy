section "The definition of the While language"

theory WhileLang imports MiscLemmas Coinductive.Coinductive_List begin

(* -- AST and other types -- *)

type_synonym name = "char list"
type_synonym val = nat
type_synonym store = "name \<Rightarrow> val"
type_synonym exp = "store \<Rightarrow> val"

datatype prog =
  Skip
  | Assign name exp
  | Print exp
  | Seq prog prog
  | If exp prog prog
  | While exp prog

(* -- small-step semantics -- *)

type_synonym out = "val list"
type_synonym state = "store \<times> out"

definition output_of :: "state \<Rightarrow> out" where
  "output_of \<equiv> \<lambda>(_, out). out"

definition subst :: "name \<Rightarrow> exp \<Rightarrow> state \<Rightarrow> state" where
  "subst n e \<equiv> \<lambda>(s, out). (s(n:= e s), out)"

definition print :: "exp \<Rightarrow> state \<Rightarrow> state" where
  "print e \<equiv> \<lambda>(s, out). (s,  out @ [e s])"

definition guard :: "exp \<Rightarrow> state \<Rightarrow> bool" where
  "guard x \<equiv> \<lambda>(s, _). x s \<noteq> 0"

inductive step :: "prog \<times> state \<Rightarrow> prog \<times> state \<Rightarrow> bool" where
  step_skip: "step (Skip,s) (Skip,s)"
| step_assign: "step (Assign n x,s) (Skip, subst n x s)"
| step_print: "step (Print x,s) (Skip, print x s)"
| step_seq1: "step (Seq Skip q,s) (q,s)"
| step_seq2: "step (p0,s0) (p1,s1) \<Longrightarrow> p0 \<noteq> Skip \<Longrightarrow> step (Seq p0 q,s0) (Seq p1 q,s1)"
| step_if: "step (If x p q, s) ((if guard x s then p else q), s)"
| step_while: "step (While x p, s) (If x (Seq p (While x p)) Skip, s)"

declare step.intros[simp,intro]

inductive_cases skipE[elim!]: "step (Skip, s) ct"
inductive_cases assignE[elim!]: "step (Assign n x, s) ct"
inductive_cases printE[elim!]: "step (Print x, s) ct"
inductive_cases seqE[elim]: "step (Seq c1 c2, s) ct"
inductive_cases ifE[elim!]: "step (If x c1 c2, s) ct"
inductive_cases whileE[elim]: "step (While x p, s) ct"

lemmas step_induct = step.induct[split_format(complete)]

inductive terminates where
  "star step (p, s) (Skip, t) \<Longrightarrow> terminates s p t"

inductive diverges where
  "\<forall>t. \<not> terminates s p t
       \<and> out = lSup { llist_of out | out. \<exists>q t. star step (p, s) (q, t, out) }
   \<Longrightarrow> 
   diverges s p out"

(* -- sanity theorems -- *)

lemma step_exists':
  "\<exists>t. step (prog, (s, out)) t"
proof (induct prog)
  case Skip
  then show ?case by fastforce
next
  case (Assign x1 x2)
  then show ?case
    apply clarsimp
    apply (rule_tac x=Skip in exI)
    apply (rule_tac x="fst (subst x1 x2 (s, out))" in exI)
    apply (rule_tac x="snd (subst x1 x2 (s, out))" in exI)
    by fastforce
next
  case (Print x)
  then show ?case
    apply clarsimp
    apply (rule_tac x=Skip in exI)
    apply (rule_tac x="fst (print x (s, out))" in exI)
    apply (rule_tac x="snd (print x (s, out))" in exI)
    by fastforce
next
  case (Seq prog1 prog2)
  then show ?case
    apply (case_tac "prog1 = Skip")
    by fastforce+
next
  case (If x1 prog1 prog2)
  then show ?case by fastforce
next
  case (While x1 prog)
  then show ?case by fastforce
qed

theorem step_exists: (* one can always take a step *)
  "\<forall>s. \<exists>t. step s t"
  using step_exists' by simp

theorem terminates_or_diverges: (* every program either terminates or diverges *)
  "(\<exists>t. terminates s p t) \<or> (\<exists>output. diverges s p output)"
  by (clarsimp simp: diverges.simps)

lemma step_deterministic':
  "step (prog, st, out) t1 \<Longrightarrow> step (prog, st, out) t2 \<Longrightarrow> t1 = t2"
proof (induct prog arbitrary: t1 t2)
  case Skip
  then show ?case by clarsimp
next
  case (Assign x1 x2)
  then show ?case by clarsimp
next
  case (Print x)
  then show ?case by clarsimp
next
  case (Seq prog1 prog2)
  then show ?case by (elim seqE; clarsimp)
next
  case (If x1 prog1 prog2)
  then show ?case by clarsimp
next
  case (While x1 prog)
  then show ?case by (elim whileE; clarsimp)
qed

theorem step_deterministic:
  "step s t1 \<Longrightarrow> step s t2 \<Longrightarrow> t1 = t2"
  apply (cases s)
  using step_deterministic' by clarsimp

lemma star_step_refl:
  "star step (Skip, t1) (Skip, t2) \<Longrightarrow> t1 = t2"
  by (induct "(Skip, t1)" "(Skip, t2)" arbitrary: t1 t2 rule: star.induct; clarsimp)

theorem terminates_deterministic:
  "terminates s p t1 \<Longrightarrow> terminates s p t2 \<Longrightarrow> t1 = t2"
proof (simp add: terminates.simps, induct "(p, s)" "(Skip, t1)" arbitrary: p s t1 rule: star.induct)
  case refl
  then show ?case
    by (clarsimp intro!: star_step_refl)
next
  case (step y)
  then show ?case
    apply (rotate_tac 3)
    apply (erule star.cases)
     apply clarsimp
    apply simp
    apply (drule (1) step_deterministic)
    apply simp
    apply (drule_tac x="fst ya" and y="snd ya" in meta_spec2)
    by simp
qed

theorem diverges_deterministic:
  "diverges s p t1 \<Longrightarrow> diverges s p t2 \<Longrightarrow> t1 = t2"
  by (simp add: diverges.simps)

end