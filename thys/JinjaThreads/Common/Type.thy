(*  Title:      JinjaThreads/Common/Type.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

header {*
  \chapter{Concepts for all JinjaThreads Languages}\label{cha:j}
  \isaheader{JinjaThreads types}
*}

theory Type
imports
  "../Basic/Aux"
begin

type_synonym cname = String.literal -- "class names"
type_synonym mname = String.literal -- "method name"
type_synonym vname = String.literal -- "names for local/field variables"

definition Object :: cname
where "Object \<equiv> STR ''java/lang/Object''"

definition Thread :: cname
where "Thread \<equiv> STR ''java/lang/Thread''"

definition Throwable :: cname
where "Throwable \<equiv> STR ''java/lang/Throwable''"

definition this :: vname
where "this \<equiv> STR ''this''"

definition run :: mname
where "run \<equiv> STR ''run()V''"

definition start :: mname
where "start \<equiv> STR ''start()V''"

definition wait :: mname
where "wait \<equiv> STR ''wait()V''"

definition notify :: mname
where "notify \<equiv> STR ''notify()V''"

definition notifyAll :: mname
where "notifyAll \<equiv> STR ''notifyAll()V''"

definition join :: mname
where "join \<equiv> STR ''join()V''"

definition interrupt :: mname
where "interrupt \<equiv> STR ''interrupt()V''"

definition isInterrupted :: mname
where "isInterrupted \<equiv> STR ''isInterrupted()Z''"

(* Method names for Class Object *)

definition hashcode :: mname
where "hashcode = STR ''hashCode()I''"

definition clone :: mname
where "clone = STR ''clone()Ljava/lang/Object;''"

definition print :: mname
where "print = STR ''~print(I)V''"

definition currentThread :: mname
where "currentThread = STR ''~Thread.currentThread()Ljava/lang/Thread;''"

definition interrupted :: mname
where "interrupted = STR ''~Thread.interrupted()Z''"

definition yield :: mname
where "yield = STR ''~Thread.yield()V''"

lemmas identifier_name_defs [code_unfold] =
  this_def run_def start_def wait_def notify_def notifyAll_def join_def interrupt_def isInterrupted_def
  hashcode_def clone_def print_def currentThread_def interrupted_def yield_def

lemma Object_Thread_Throwable_neq [simp]:
  "Thread \<noteq> Object" "Object \<noteq> Thread"
  "Object \<noteq> Throwable" "Throwable \<noteq> Object"
  "Thread \<noteq> Throwable" "Throwable \<noteq> Thread"
by(auto simp add: Thread_def Object_def Throwable_def)

lemma synth_method_names_neq_aux:
  "start \<noteq> wait" "start \<noteq> notify" "start \<noteq> notifyAll" "start \<noteq> join" "start \<noteq> interrupt" "start \<noteq> isInterrupted"
  "start \<noteq> hashcode" "start \<noteq> clone" "start \<noteq> print" "start \<noteq> currentThread"
  "start \<noteq> interrupted" "start \<noteq> yield" "start \<noteq> run"
  "wait \<noteq> notify" "wait \<noteq> notifyAll" "wait \<noteq> join"  "wait \<noteq> interrupt" "wait \<noteq> isInterrupted"
  "wait \<noteq> hashcode" "wait \<noteq> clone" "wait \<noteq> print" "wait \<noteq> currentThread" 
  "wait \<noteq> interrupted" "wait \<noteq> yield"  "wait \<noteq> run"
  "notify \<noteq> notifyAll" "notify \<noteq> join" "notify \<noteq> interrupt" "notify \<noteq> isInterrupted"
  "notify \<noteq> hashcode" "notify \<noteq> clone" "notify \<noteq> print" "notify \<noteq> currentThread"
  "notify \<noteq> interrupted" "notify \<noteq> yield" "notify \<noteq> run"
  "notifyAll \<noteq> join" "notifyAll \<noteq> interrupt" "notifyAll \<noteq> isInterrupted"
  "notifyAll \<noteq> hashcode" "notifyAll \<noteq> clone" "notifyAll \<noteq> print" "notifyAll \<noteq> currentThread"
  "notifyAll \<noteq> interrupted" "notifyAll \<noteq> yield" "notifyAll \<noteq> run"
  "join \<noteq> interrupt" "join \<noteq> isInterrupted"
  "join \<noteq> hashcode" "join \<noteq> clone" "join \<noteq> print" "join \<noteq> currentThread" 
  "join \<noteq> interrupted" "join \<noteq> yield" "join \<noteq> run"
  "interrupt \<noteq> isInterrupted"
  "interrupt \<noteq> hashcode" "interrupt \<noteq> clone" "interrupt \<noteq> print" "interrupt \<noteq> currentThread" 
  "interrupt \<noteq> interrupted" "interrupt \<noteq> yield" "interrupt \<noteq> run"
  "isInterrupted \<noteq> hashcode" "isInterrupted \<noteq> clone" "isInterrupted \<noteq> print" "isInterrupted \<noteq> currentThread" 
  "isInterrupted \<noteq> interrupted" "isInterrupted \<noteq> yield" "isInterrupted \<noteq> run"
  "hashcode \<noteq> clone" "hashcode \<noteq> print" "hashcode \<noteq> currentThread" 
  "hashcode \<noteq> interrupted" "hashcode \<noteq> yield" "hashcode \<noteq> run"
  "clone \<noteq> print" "clone \<noteq> currentThread" 
  "clone \<noteq> interrupted" "clone \<noteq> yield" "clone \<noteq> run"
  "print \<noteq> currentThread" 
  "print \<noteq> interrupted" "print \<noteq> yield" "print \<noteq> run"
  "currentThread \<noteq> interrupted" "currentThread \<noteq> yield" "currentThread \<noteq> run"
  "interrupted \<noteq> yield" "interrupted \<noteq> run"
  "yield \<noteq> run"
by(simp_all add: identifier_name_defs)

lemmas synth_method_names_neq [simp] = synth_method_names_neq_aux synth_method_names_neq_aux[symmetric]

-- "types"
datatype ty
  = Void          -- "type of statements"
  | Boolean
  | Integer
  | NT            -- "null type"
  | Class cname   -- "class type"
  | Array ty      ("_\<lfloor>\<rceil>" 95) -- "array type"

inductive is_refT :: "ty \<Rightarrow> bool" where
  "is_refT NT"
| "is_refT (Class C)"
| "is_refT (A\<lfloor>\<rceil>)"

declare is_refT.intros[iff]

lemmas refTE [consumes 1, case_names NT Class Array] = is_refT.cases

lemma not_refTE [consumes 1, case_names Void Boolean Integer]:
  "\<lbrakk> \<not>is_refT T; T = Void \<Longrightarrow> P; T = Boolean \<Longrightarrow> P; T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (cases T, auto)

fun ground_type :: "ty \<Rightarrow> ty" where
  "ground_type (Array T) = ground_type T"
| "ground_type T = T"

abbreviation is_NT_Array :: "ty \<Rightarrow> bool" where
  "is_NT_Array T \<equiv> ground_type T = NT"

primrec the_Class :: "ty \<Rightarrow> cname"
where
  "the_Class (Class C) = C"

primrec the_Array :: "ty \<Rightarrow> ty"
where
  "the_Array (T\<lfloor>\<rceil>) = T"

fun class_type_of :: "ty \<Rightarrow> cname option"
where 
  "class_type_of (Class C) = \<lfloor>C\<rfloor>"
| "class_type_of (Array T) = \<lfloor>Object\<rfloor>"
| "class_type_of _ = None"

inductive is_class_type_of :: "ty \<Rightarrow> cname \<Rightarrow> bool"
where 
  is_class_type_of_Class: "is_class_type_of (Class C) C"
| is_class_type_of_Array: "is_class_type_of (Array T) Object"

inductive_simps is_class_type_of_simps [simp]:
  "is_class_type_of (Class C) X"
  "is_class_type_of (Array T) X"
  "is_class_type_of Integer X"
  "is_class_type_of Boolean X"
  "is_class_type_of Void X"
  "is_class_type_of NT X"

lemma class_type_of_eq:
  "class_type_of T = 
  (case T of Class C \<Rightarrow> \<lfloor>C\<rfloor> | Array T \<Rightarrow> \<lfloor>Object\<rfloor> | _ \<Rightarrow> None)"
by(cases T rule: class_type_of.cases) simp_all

lemma is_class_type_of_conv_class_type_of_Some:
  "is_class_type_of T C \<longleftrightarrow> class_type_of T = \<lfloor>C\<rfloor>"
by(cases T rule: class_type_of.cases) auto

fun is_Array :: "ty \<Rightarrow> bool"
where
  "is_Array (Array T) = True"
| "is_Array _ = False"

lemma is_Array_conv [simp]: "is_Array T \<longleftrightarrow> (\<exists>U. T = Array U)"
by(cases T) simp_all

fun is_Class :: "ty \<Rightarrow> bool"
where
  "is_Class (Class C) = True"
| "is_Class _ = False"

lemma is_Class_conv [simp]: "is_Class T \<longleftrightarrow> (\<exists>C. T = Class C)"
by(cases T) simp_all

subsection {* Code generator setup *}

code_pred is_refT .

code_pred
  (modes: i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> bool)
  [detect_switches, skip_proof]
  is_class_type_of
.

declare is_class_type_of_conv_class_type_of_Some [code]

end
