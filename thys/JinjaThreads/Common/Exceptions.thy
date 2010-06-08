(*  Title:      JinjaThreads/Common/Exceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Andreas Lochbihler

    Based on the Jinja theory Common/Exceptions.thy by Gerwin Klein and Martin Strecker
*)

header {* \isaheader{Exceptions} *}

theory Exceptions imports Value begin

definition NullPointer :: cname
where [code_inline]: "NullPointer = STR ''java/lang/NullPointerException''"

definition ClassCast :: cname
where [code_inline]: "ClassCast = STR ''java/lang/ClassCastException''"

definition OutOfMemory :: cname
where [code_inline]: "OutOfMemory = STR ''java/lang/OutOfMemoryError''"

definition ArrayIndexOutOfBounds :: cname
where [code_inline]: "ArrayIndexOutOfBounds = STR ''java/lang/ArrayIndexOutOfBoundsException''"

definition ArrayStore :: cname
where [code_inline]: "ArrayStore = STR ''java/lang/ArrayStoreException''"

definition NegativeArraySize :: cname
where [code_inline]: "NegativeArraySize = STR ''java/lang/NegativeArraySizeException''"

definition IllegalMonitorState :: cname
where [code_inline]: "IllegalMonitorState = STR ''java/lang/IllegalMonitorStateException''"

definition IllegalThreadState :: cname
where [code_inline]: "IllegalThreadState = STR ''java/lang/IllegalThreadStateException''"

definition CloneNotSupported :: cname
where [code_inline]: "CloneNotSupported = STR ''java/lang/CloneNotSupportedException''"

definition InterruptedException :: cname
where [code_inline]: "InterruptedException = STR ''java/lang/InterruptedException''"

definition sys_xcpts :: "cname set"
where "sys_xcpts = {NullPointer, ClassCast, OutOfMemory, ArrayIndexOutOfBounds,
                    ArrayStore, NegativeArraySize, IllegalMonitorState, IllegalThreadState,
                    CloneNotSupported, InterruptedException}"

lemma sys_xcpts_code [code_inline]:
  "sys_xcpts = set [NullPointer, ClassCast, OutOfMemory, ArrayIndexOutOfBounds, ArrayStore,
                    NegativeArraySize, IllegalMonitorState, IllegalThreadState, CloneNotSupported, InterruptedException]"
by(simp add: sys_xcpts_def)

section "System exceptions"

lemma [simp]:
  "NullPointer \<in> sys_xcpts \<and> 
   OutOfMemory \<in> sys_xcpts \<and> 
   ClassCast \<in> sys_xcpts \<and> 
   ArrayIndexOutOfBounds \<in> sys_xcpts \<and> 
   ArrayStore \<in> sys_xcpts \<and> 
   NegativeArraySize \<in> sys_xcpts \<and> 
   IllegalMonitorState \<in> sys_xcpts \<and>
   IllegalThreadState \<in> sys_xcpts \<and>
   CloneNotSupported \<in> sys_xcpts \<and>
   InterruptedException \<in> sys_xcpts"
by(simp add: sys_xcpts_def)

lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast; 
     P ArrayIndexOutOfBounds; P ArrayStore; P NegativeArraySize;
     P IllegalMonitorState; P IllegalThreadState; P CloneNotSupported; P InterruptedException \<rbrakk> \<Longrightarrow> P C"
by (auto simp add: sys_xcpts_def)

lemma OutOfMemory_not_Object[simp]: "OutOfMemory \<noteq> Object"
by(simp add: OutOfMemory_def Object_def)

lemma ClassCast_not_Object[simp]: "ClassCast \<noteq> Object"
by(simp add: ClassCast_def Object_def)

lemma NullPointer_not_Object[simp]: "NullPointer \<noteq> Object"
by(simp add: NullPointer_def Object_def)

lemma ArrayIndexOutOfBounds_not_Object[simp]: "ArrayIndexOutOfBounds \<noteq> Object"
by(simp add: ArrayIndexOutOfBounds_def Object_def)

lemma ArrayStore_not_Object[simp]: "ArrayStore \<noteq> Object"
by(simp add: ArrayStore_def Object_def)

lemma NegativeArraySize_not_Object[simp]: "NegativeArraySize \<noteq> Object"
by(simp add: NegativeArraySize_def Object_def)

lemma IllegalMonitorState_not_Object[simp]: "IllegalMonitorState \<noteq> Object"
by(simp add: IllegalMonitorState_def Object_def)

lemma IllegalThreadState_not_Object[simp]: "IllegalThreadState \<noteq> Object"
by(simp add: IllegalThreadState_def Object_def)

lemma CloneNotSupported_not_Object[simp]: "CloneNotSupported \<noteq> Object"
by(simp add: CloneNotSupported_def Object_def)

lemma InterruptedException_not_Object[simp]: "InterruptedException \<noteq> Object"
by(simp add: InterruptedException_def Object_def)

lemma sys_xcpts_neqs_aux:
  "NullPointer \<noteq> ClassCast" "NullPointer \<noteq> OutOfMemory" "NullPointer \<noteq> ArrayIndexOutOfBounds"
  "NullPointer \<noteq> ArrayStore" "NullPointer \<noteq> NegativeArraySize" "NullPointer \<noteq> IllegalMonitorState"
  "NullPointer \<noteq> IllegalThreadState" "NullPointer \<noteq> CloneNotSupported" "NullPointer \<noteq> InterruptedException"
  "ClassCast \<noteq> OutOfMemory" "ClassCast \<noteq> ArrayIndexOutOfBounds"
  "ClassCast \<noteq> ArrayStore" "ClassCast \<noteq> NegativeArraySize" "ClassCast \<noteq> IllegalMonitorState"
  "ClassCast \<noteq> IllegalThreadState" "ClassCast \<noteq> CloneNotSupported" "ClassCast \<noteq> InterruptedException"
  "OutOfMemory \<noteq> ArrayIndexOutOfBounds"
  "OutOfMemory \<noteq> ArrayStore" "OutOfMemory \<noteq> NegativeArraySize" "OutOfMemory \<noteq> IllegalMonitorState"
  "OutOfMemory \<noteq> IllegalThreadState" "OutOfMemory \<noteq> CloneNotSupported" "OutOfMemory \<noteq> InterruptedException"
  "ArrayIndexOutOfBounds \<noteq> ArrayStore" "ArrayIndexOutOfBounds \<noteq> NegativeArraySize" "ArrayIndexOutOfBounds \<noteq> IllegalMonitorState"
  "ArrayIndexOutOfBounds \<noteq> IllegalThreadState" "ArrayIndexOutOfBounds \<noteq> CloneNotSupported" "ArrayIndexOutOfBounds \<noteq> InterruptedException"
  "ArrayStore \<noteq> NegativeArraySize" "ArrayStore \<noteq> IllegalMonitorState"
  "ArrayStore \<noteq> IllegalThreadState" "ArrayStore \<noteq> CloneNotSupported" "ArrayStore \<noteq> InterruptedException"
  "NegativeArraySize \<noteq> IllegalMonitorState"
  "NegativeArraySize \<noteq> IllegalThreadState" "NegativeArraySize \<noteq> CloneNotSupported" "NegativeArraySize \<noteq> InterruptedException"
  "IllegalMonitorState \<noteq> IllegalThreadState" "IllegalMonitorState \<noteq> CloneNotSupported" "IllegalMonitorState \<noteq> InterruptedException"
  "IllegalThreadState \<noteq> CloneNotSupported" "IllegalThreadState \<noteq> InterruptedException"
  "CloneNotSupported \<noteq> InterruptedException"
by(simp_all add: NullPointer_def ClassCast_def OutOfMemory_def ArrayIndexOutOfBounds_def ArrayStore_def NegativeArraySize_def IllegalMonitorState_def IllegalThreadState_def CloneNotSupported_def InterruptedException_def)

lemmas sys_xcpts_neqs = sys_xcpts_neqs_aux sys_xcpts_neqs_aux[symmetric]

end
