(*  Title:      JinjaThreads/Common/Type.thy
    Author:     David von Oheimb, Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

header {* \isaheader{Jinja types} *}

theory Type imports Aux begin

types
  cname = string -- "class names"
  mname = string -- "method name"
  vname = string -- "names for local/field variables"

constdefs
  Object :: cname
  "Object \<equiv> ''Object''"
  Thread :: cname
  "Thread \<equiv> ''Thread''"
  this :: vname
  "this \<equiv> ''this''"
  run :: mname
  "run \<equiv> ''run''"
  start :: mname
  "start \<equiv> ''start''"
  wait :: mname
  "wait \<equiv> ''wait''"
  notify :: mname
  "notify \<equiv> ''notify''"
  notifyAll :: mname
  "notifyAll \<equiv> ''notifyAll''"
  join :: mname
  "join \<equiv> ''join''"

lemma thread_neq_object [simp]: "Thread \<noteq> Object"
by(simp add: Thread_def Object_def)

lemmas object_neq_thread [simp] = thread_neq_object[symmetric]

lemma synth_method_names_neq_aux:
  "start \<noteq> wait" "start \<noteq> notify" "start \<noteq> notifyAll" "start \<noteq> join"
  "wait \<noteq> notify" "wait \<noteq> notifyAll" "wait \<noteq> join" "notify \<noteq> notifyAll"
  "notify \<noteq> join" "notifyAll \<noteq> join"
by(auto simp add: start_def wait_def notify_def notifyAll_def join_def)

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


inductive is_refT_class :: "ty \<Rightarrow> bool" where
  "is_refT_class NT"
| "is_refT_class (Class C)"

declare is_refT_class.intros[iff]

lemmas refT_classE [consumes 1, case_names NT Class] = is_refT_class.cases

lemma not_refT_classE [consumes 1, case_names Void Boolean Integer Array]:
  "\<lbrakk> \<not>is_refT_class T; T = Void \<Longrightarrow> P; T = Boolean \<Longrightarrow> P; T = Integer \<Longrightarrow> P; \<And>A. T = Array A \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (cases T, auto)

fun ground_type :: "ty \<Rightarrow> ty" where
  "ground_type (T\<lfloor>\<rceil>) = ground_type T"
| "ground_type T = T"

abbreviation is_NT_Array :: "ty \<Rightarrow> bool" where
  "is_NT_Array T \<equiv> ground_type T = NT"

consts
  the_Class :: "ty \<Rightarrow> cname"
primrec
  "the_Class (Class C) = C"

consts
  the_Array :: "ty \<Rightarrow> ty"
primrec
  "the_Array (T\<lfloor>\<rceil>) = T"

end
