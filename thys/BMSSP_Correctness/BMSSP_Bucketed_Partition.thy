theory BMSSP_Bucketed_Partition
  imports BMSSP_Bucketed_Partition_Internal
begin

section \<open>Bucketed Partition\<close>

text \<open>
  This theory is the public import point for the bucketed partition
  implementation.  The definitions and proof-engineering lemmas live in
  \<open>BMSSP_Bucketed_Partition_Internal\<close>; importing this wrapper exports
  the same constants and facts to the rest of the BMSSP development while
  keeping the documented surface short.
\<close>

end
