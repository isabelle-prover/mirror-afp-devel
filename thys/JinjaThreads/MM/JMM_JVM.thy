theory JMM_JVM
imports
  JMM_Framework
  "../JVM/JVMThreaded"
begin

sublocale JVM_heap_base < execd_mthr!: 
  heap_multithreaded_base 
    addr2thread_id thread_id2addr
    empty_heap allocate typeof_addr heap_read heap_write
    JVM_final "mexecd P" convert_RA
  for P
.

-- "Move to JVMExec"
abbreviation JVM_local_start ::
  "cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'addr jvm_method \<Rightarrow> 'addr val list
  \<Rightarrow> 'addr jvm_thread_state"
where
  "JVM_local_start \<equiv> 
   \<lambda>C M Ts T (mxs, mxl0, b) vs. 
   (None, [([], Null # vs @ replicate mxl0 undefined_value, C, M, 0)])"

context JVM_heap_base begin

abbreviation JVMd_\<E> ::
  "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> status
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) llist set"
where "JVMd_\<E> P \<equiv> execd_mthr.\<E>_start P JVM_local_start P"

end

end
