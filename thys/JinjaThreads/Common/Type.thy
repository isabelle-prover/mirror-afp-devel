(*  Title:      JinjaThreads/Common/Type.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

header {*
  \chapter{Concepts for all JinjaThreads Languages}\label{cha:j}
  \isaheader{JinjaThreads types}
*}

theory Type imports
  Aux
begin

types
  cname = String.literal -- "class names"
  mname = String.literal -- "method name"
  vname = String.literal -- "names for local/field variables"

definition Object :: cname
where "Object \<equiv> STR ''java/lang/Object''"

definition Thread :: cname
where "Thread \<equiv> STR ''java/lang/Thread''"

definition Throwable :: cname
where "Throwable \<equiv> STR ''java/lang/Throwable''"

definition String :: cname
where "String \<equiv> STR ''java/lang/String''"

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

definition interrupted_flag :: vname
where "interrupted_flag \<equiv> STR ''interrupted_flag''"

(* Method names for Class Object *)

definition hashcode :: mname
where "hashcode = STR ''hashCode()I''"

definition clone :: mname
where "clone = STR ''clone()Ljava/lang/Object;''"

definition equals :: mname
where "equals = STR ''equals(Ljava/lang/Object;)Z''"

definition toString :: mname
where "toString = STR ''toString()Ljava/lang/String;''"

lemmas identifier_name_defs [code_inline] =
  this_def run_def start_def wait_def notify_def notifyAll_def join_def interrupt_def 
  hashcode_def clone_def equals_def toString_def

lemma Object_Thread_Throwable_neq [simp]:
  "Thread \<noteq> Object" "Object \<noteq> Thread"
  "Object \<noteq> Throwable" "Throwable \<noteq> Object"
  "Thread \<noteq> Throwable" "Throwable \<noteq> Thread"
  "Object \<noteq> String" "String \<noteq> Object"
  "Thread \<noteq> String" "String \<noteq> Thread"
  "Throwable \<noteq> String" "String \<noteq> Throwable"
by(auto simp add: Thread_def Object_def Throwable_def String_def)

lemma synth_method_names_neq_aux:
  "start \<noteq> wait" "start \<noteq> notify" "start \<noteq> notifyAll" "start \<noteq> join" "start \<noteq> interrupt"
  "start \<noteq> hashcode" "start \<noteq> clone" "start \<noteq> equals" "start \<noteq> toString"
  "wait \<noteq> notify" "wait \<noteq> notifyAll" "wait \<noteq> join"  "wait \<noteq> interrupt"
  "wait \<noteq> hashcode" "wait \<noteq> clone" "wait \<noteq> equals" "wait \<noteq> toString"
  "notify \<noteq> notifyAll" "notify \<noteq> join" "notify \<noteq> interrupt"
  "notify \<noteq> hashcode" "notify \<noteq> clone" "notify \<noteq> equals" "notify \<noteq> toString"
  "notifyAll \<noteq> join" "notifyAll \<noteq> interrupt"
  "notifyAll \<noteq> hashcode" "notifyAll \<noteq> clone" "notifyAll \<noteq> equals" "notifyAll \<noteq> toString"
  "join \<noteq> interrupt"
  "join \<noteq> hashcode" "join \<noteq> clone" "join \<noteq> equals" "join \<noteq> toString"
  "interrupt \<noteq> hashcode" "interrupt \<noteq> clone" "interrupt \<noteq> equals" "interrupt \<noteq> toString"
  "hashcode \<noteq> clone" "hashcode \<noteq> equals" "hashcode \<noteq> toString"
  "clone \<noteq> equals" "clone \<noteq> toString"
  "equals \<noteq> toString"
by(auto simp add: identifier_name_defs)

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

code_pred is_refT .

declare is_refT.intros[iff]

lemmas refTE [consumes 1, case_names NT Class Array] = is_refT.cases

lemma not_refTE [consumes 1, case_names Void Boolean Integer]:
  "\<lbrakk> \<not>is_refT T; T = Void \<Longrightarrow> P; T = Boolean \<Longrightarrow> P; T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (cases T, auto)

fun ground_type :: "ty \<Rightarrow> ty" where
  "ground_type (T\<lfloor>\<rceil>) = ground_type T"
| "ground_type T = T"

abbreviation is_NT_Array :: "ty \<Rightarrow> bool" where
  "is_NT_Array T \<equiv> ground_type T = NT"

primrec the_Class :: "ty \<Rightarrow> cname" where
  "the_Class (Class C) = C"

primrec the_Array :: "ty \<Rightarrow> ty" where
  "the_Array (T\<lfloor>\<rceil>) = T"

end
