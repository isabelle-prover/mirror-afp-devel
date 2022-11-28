theory CHERI_C_Global_Environment
  imports CHERI_C_Concrete_Memory_Model
begin

text \<open>Here, we define the global environment. The Global Environment does the following:
  \begin{enumerate}
    \item Creates a mapping from variables to locations (or rather, the capabilities) 
    \item Sets global variables by invoking alloc. These variables cannot be freed by design
  \end{enumerate}\<close>

type_synonym genv = "(String.literal, cap) mapping"

definition alloc_glob_var :: "heap \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> (heap \<times> cap) result"
  where
  "alloc_glob_var h c s \<equiv> 
     let h' = alloc h c s in
     Success (fst (res h'), snd (res h') \<lparr> perm_global := True \<rparr>)"

definition set_glob_var :: "heap \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> String.literal \<Rightarrow> genv \<Rightarrow> (heap \<times> cap \<times> genv) result"
  where
  "set_glob_var h c s v g \<equiv>
     let (h', cap) = res (alloc_glob_var h c s) in
     let g' = Mapping.update v cap g in
     Success (h', cap, g')"

lemma set_glob_var_glob_bit:
  assumes "alloc_glob_var h c s = Success (h', cap)"
  shows "perm_global cap"
  using assms
  unfolding alloc_glob_var_def alloc_def
  by fastforce

lemma set_glob_var_glob_bit_lift:
  assumes "set_glob_var h c s v g = Success (h', cap, g')"
  shows "perm_global cap"
  using assms
  unfolding alloc_glob_var_def set_glob_var_def alloc_def
  by fastforce

(* It is worth noting that other operations such as load and store still work. *)
(* However, free should only work on values returned by m?alloc. *)
lemma free_fails_on_glob_var:
  assumes "alloc_glob_var h c s = Success (h', cap)"
  shows "free h' cap = Error (LogicErr (Unhandled 0))"
  by (metis alloc_updated_heap_and_cap assms capability.select_convs(1) free_global_cap 
      mem_capability.select_convs(10) mem_capability.simps(21) null_capability_def result.sel(1) 
      alloc_glob_var_def snd_conv zero_mem_capability_ext_def)

lemma free_fails_on_glob_lift:
  assumes "set_glob_var h c s v g = Success (h', cap, g')"
  shows "free h' cap = Error (LogicErr (Unhandled 0))"
proof -
  have res: "alloc_glob_var h c s = Success (h', cap)"
    using assms 
    unfolding set_glob_var_def alloc_glob_var_def alloc_def
    by fastforce
  show ?thesis using free_fails_on_glob_var[OF res]
    by blast
qed

section \<open>Code Generation\<close>
text \<open>Here we generate an OCaml instance of the memory model that will be used for Gillian.\<close>
export_code 
            null_capability init_heap next_block get_memory_leak_size get_unfreed_blocks (* Utility Functions *)
            alloc free load store (* Memory Actions *)
            memcpy 
            set_glob_var (* Global Environment Actions *)
            word8_of_integer   word16_of_integer  word32_of_integer  word64_of_integer (* Value Conversions *)    
            integer_of_word8   integer_of_word16  integer_of_word32  integer_of_word64
            sword8_of_integer  sword16_of_integer sword32_of_integer sword64_of_integer
            integer_of_sword8  integer_of_sword16 integer_of_sword32 integer_of_sword64
            integer_of_nat cast_val
            C2Err LogicErr (* Error Types *)
            TagViolation PermitLoadViolation PermitStoreViolation PermitStoreCapViolation
            PermitStoreLocalCapViolation LengthViolation BadAddressViolation
            UseAfterFree BufferOverrun MissingResource WrongMemVal MemoryNotFreed Unhandled
            in OCaml 
            file_prefix CHERI_C_Memory_Model

end