theory CHERI_C_Concrete_Memory_Model
  imports "Preliminary_Library"
          "Separation_Algebra.Separation_Algebra"
          "Containers.Containers"
          "HOL-Library.Mapping"
          "HOL-Library.Code_Target_Numeral"
begin

section \<open>CHERI-C Error System\<close>
text \<open>In this section, we formalise the error system used by the memory model.\<close>
text \<open>Below are coprocessor 2 excessptions thrown by the hardware. 
      BadAddressViolation is not a coprocessor 2 exception but remains one given by the hardware. 
      This corresponds to CapErr in the paper~\cite{park_2022}.\<close>
datatype c2errtype = 
  TagViolation
  | PermitLoadViolation
  | PermitStoreViolation
  | PermitStoreCapViolation
  | PermitStoreLocalCapViolation
  | LengthViolation
  | BadAddressViolation

text \<open>These are logical errors produced by the language. In practice, Some of these errors would never
      be caught due to the inherent spatial safety guarantees given by capabilities. 
      This corresponds to LogicErr in the paper~\cite{park_2022}. \\
      NOTE: Unhandled corresponds to a custom error not mentioned in \emph{logicerrtype}. One can provide
      the custom error as a string, but here, for custom errors, we leave it empty to simplify the
      proof. Ultimately, the important point is that the memory model can still catch custom errors.\<close>
datatype logicerrtype =
  UseAfterFree
  | BufferOverrun
  | MissingResource
  | WrongMemVal
  | MemoryNotFreed
  | Unhandled "String.literal"

text \<open>We make the distinction between the error types. This corresponds to Err in the paper~\cite{park_2022}.\<close>
datatype errtype = 
  C2Err c2errtype
  | LogicErr logicerrtype

text \<open>Finally, we have the `return' type $\mathcal{R}\ \rho$ in the paper~\cite{park_2022}.\<close>
datatype 'a result =
  Success (res: 'a)
  | Error (err: errtype)

text \<open>In this theory, we concretise the notion of blocks\<close>
\<comment> \<open>While we can use int as blocks, integer makes it more efficient for code execution\<close>
type_synonym block = integer
type_synonym memcap = "block mem_capability"
type_synonym cap = "block capability"

text \<open>Because \texttt{sizeof} depends on the architecture, it shall be given via the memory model. We also
      use uncompressed capabilities.\<close>
definition sizeof :: "cctype \<Rightarrow> nat" ("|_|\<^sub>\<tau>")
  where
  "sizeof \<tau> \<equiv> case \<tau> of
     Uint8  \<Rightarrow> 1
   | Sint8  \<Rightarrow> 1
   | Uint16 \<Rightarrow> 2
   | Sint16 \<Rightarrow> 2
   | Uint32 \<Rightarrow> 4
   | Sint32 \<Rightarrow> 4
   | Uint64 \<Rightarrow> 8
   | Sint64 \<Rightarrow> 8
   | Cap \<Rightarrow> 32"

text \<open>We provide some helper lemmas\<close>
lemma size_type_align:
  assumes "|t|\<^sub>\<tau> = x"
  shows "\<exists> n. 2 ^ n = x"
proof (cases t)
  case Uint8
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by fastforce
next
  case Sint8
  then show ?thesis
    using assms 
    unfolding sizeof_def 
    by fastforce
next
  case Uint16
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=1 in exI) fastforce
next
  case Sint16
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=1 in exI) fastforce
next
  case Uint32
  then show ?thesis
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=2 in exI) fastforce
next
  case Sint32
  then show ?thesis
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=2 in exI) fastforce
next
  case Uint64
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=3 in exI) fastforce
next
  case Sint64
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=3 in exI) fastforce
next
  case Cap
  then show ?thesis 
    using assms 
    unfolding sizeof_def 
    by (rule_tac x=5 in exI) fastforce
qed

lemma memval_size_u8:
  "|memval_type (Uint8_v v)|\<^sub>\<tau> = 1"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_s8:
  "|memval_type (Sint8_v v)|\<^sub>\<tau> = 1"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_u16:
  "|memval_type (Uint16_v v)|\<^sub>\<tau> = 2"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_s16:
  "|memval_type (Sint16_v v)|\<^sub>\<tau> = 2"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_u32:
  "|memval_type (Uint32_v v)|\<^sub>\<tau> = 4"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_s32:
  "|memval_type (Sint32_v v)|\<^sub>\<tau> = 4"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_u64:
  "|memval_type (Uint64_v v)|\<^sub>\<tau> = 8"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_s64:
  "|memval_type (Sint64_v v)|\<^sub>\<tau> = 8"
  unfolding sizeof_def 
  by fastforce

lemma memval_size_cap:
  "|memval_type (Cap_v v)|\<^sub>\<tau> = 32"
  unfolding sizeof_def 
  by fastforce

lemmas memval_size_types = memval_size_u8 memval_size_s8 memval_size_u16 memval_size_s16 memval_size_u32 memval_size_s32 memval_size_u64 memval_size_s64 memval_size_cap

corollary memval_size_u16_eq_word_split_len:
  assumes "val = Uint16_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (u16_split v)"
  using assms memval_size_u16 flatten_u16_length 
  by force

corollary memval_size_s16_eq_word_split_len:
  assumes "val = Sint16_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (s16_split v)"
  using assms memval_size_s16 flatten_s16_length 
  by force

corollary memval_size_u32_eq_word_split_len:
  assumes "val = Uint32_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (flatten_u32 v)"
  using assms memval_size_u32 flatten_u32_length
  by force

corollary memval_size_s32_eq_word_split_len:
  assumes "val = Sint32_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (flatten_s32 v)"
  using assms memval_size_s32 flatten_s32_length 
  by force

corollary memval_size_u64_eq_word_split_len:
  assumes "val = Uint64_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (flatten_u64 v)"
  using assms memval_size_u64 flatten_u64_length
  by force

corollary memval_size_s64_eq_word_split_len:
  assumes "val = Sint64_v v"
  shows "|memval_type val|\<^sub>\<tau> = length (flatten_s64 v)"
  using assms memval_size_s64 flatten_s64_length 
  by force

lemma sizeof_nonzero:
  "|t|\<^sub>\<tau> > 0"
  by (simp add: sizeof_def split: cctype.split)

text \<open>We prove that integer is a countable type.\<close>
instance int :: comp_countable ..

lemma integer_encode_eq: "(int_encode \<circ> int_of_integer) x = (int_encode \<circ> int_of_integer) y \<longleftrightarrow> x = y"
  using int_encode_eq integer_eq_iff 
  by auto

instance integer :: countable
  by (rule countable_classI[of "int_encode \<circ> int_of_integer"]) (simp only: integer_encode_eq)

instance integer :: comp_countable ..

section \<open>Memory\<close>
text \<open>In this section, we formalise the heap and prove some initial properties.\<close>
subsection \<open>Definitions\<close>

text \<open>First, we provide $\mathcal{V}_\mathcal{M}$---refer to ~\cite{park_2022} for the definition. 
      We note that this representation allows us to make the distinction between what is a 
      capability and what is a primitive value stored in memory. We can define a 
      tag-preserving \texttt{memcpy} by checking ahead whether there are valid capabilities stored 
      in memory or whether there are simply bytes. The downside to this approach is that overwriting
      primitive values to where capabilities were stored---and vice versa---will lead to an undefined 
      load operation. However, this tends not to be a big problem, as (1) overwritten capabilities 
      are tag-invalidated anyway, so the capabilities cannot be dereferenced even if the user 
      obtained the capability somehow, and (2) for legacy C programs that do not have access to 
      CHERI library functions, there is no way to access the metadata of the invalidated 
      capabilities. For compatibility purposes, this imposes hardly any problems.\<close>
datatype memval =
  Byte (of_byte: "8 word")
  | ACap (of_cap: "memcap") (of_nth: "nat")

text \<open>In general, the bound is irrelevant, as capability bound ensures spatial safety. We add bounds
      in the heap so that we can incorporate \textit{hybrid} CHERI C programs in the future, where 
      pointers and capabilities co-exist, but strictly speaking, this is not required in 
      \textit{purecap} CHERI C programs, which is what this memory model is based on. Ultimately, 
      this is the pair of mapping defined in the paper~\cite{park_2022}.\<close>
record object =
  bounds :: "nat \<times> nat"
  content :: "(nat, memval) mapping"
  tags :: "(nat, bool) mapping"

text \<open>t is the datatype that allows us to make the distinction between blocks that are freed and 
      blocks that are valid.\<close>
datatype t = 
  Freed
  | Map (the_map: "object")

text \<open>heap\_map in heap is essentially $\mathcal{H}$ defined in the paper~\cite{park_2022}. We 
      extend the structure and keep track of the next block for the allocator for efficiency---much
      like how CompCert's C memory model does this~\cite{leroy_2012}.\<close>
record heap =
  next_block :: "block"
  heap_map :: "(block, t) mapping"

definition memval_is_byte :: "memval \<Rightarrow> bool"
  where
  "memval_is_byte m \<equiv> case m of Byte _ \<Rightarrow> True | ACap _ _ \<Rightarrow> False"

abbreviation memval_is_cap :: "memval \<Rightarrow> bool"
  where
  "memval_is_cap m \<equiv> \<not> memval_is_byte m"

lemma memval_byte:
  "memval_is_byte m \<Longrightarrow> \<exists> b. m = Byte b"
  by (simp add: memval_is_byte_def split: memval.split_asm)

lemma memval_byte_not_memcap:
  "memval_is_byte m \<Longrightarrow> m \<noteq> ACap c n"
  by (simp add: memval_is_byte_def split: memval.split_asm)

lemma memval_memcap:
  "memval_is_cap m \<Longrightarrow> \<exists> c n. m = ACap c n"
  by (simp add: memval_is_byte_def split: memval.split_asm)

lemma memval_memcap_not_byte:
  "memval_is_cap m \<Longrightarrow> m \<noteq> Byte b"
  by (simp add: memval_is_byte_def split: memval.split_asm)

subsection \<open>Properties\<close>
text \<open>We prove that the heap is an instance of separation algebra.\<close>
instantiation unit :: cancellative_sep_algebra
begin
definition "0 \<equiv> ()"
definition "u1 + u2 = ()"
definition "(u1::unit) ## u2 \<equiv> True"
instance 
  by (standard; (blast | simp add: sep_disj_unit_def))
end

instantiation nat :: cancellative_sep_algebra
begin
definition "(n1::nat) ## n2 \<equiv> True"
instance 
  by (standard; (blast | simp add: sep_disj_nat_def))
end

text \<open>This proof ultimately shows that heap\_map forms a separation algebra.\<close>
instantiation mapping :: (type, type) cancellative_sep_algebra
begin

definition zero_map_def: "0 \<equiv> Mapping.empty"
definition plus_map_def: "m1 + m2 \<equiv> Mapping ((Mapping.lookup m1) ++ (Mapping.lookup m2))"
definition sep_disj_map_def: "m1 ## m2 \<equiv> Mapping.keys m1 \<inter> Mapping.keys m2 = {}"

instance
proof
  show "\<And>x :: ('a, 'b) mapping. x ## 0"
    by (simp add: sep_disj_map_def zero_map_def)
next
  show "\<And>x :: ('a, 'b) mapping. x + 0 = x"
    by (simp add: sep_disj_map_def Mapping.keys_def zero_map_def plus_map_def Mapping.empty.abs_eq Mapping.lookup.abs_eq mapping_eqI)
next
  show "\<And>x y :: ('a, 'b) mapping. x ## y \<Longrightarrow> y ## x"
    using sep_disj_map_def 
    by auto
next 
  show "\<And>x y :: ('a, 'b) mapping. x ## y \<Longrightarrow> x + y = y + x"
    using map_add_comm
    by (fastforce simp add: sep_disj_map_def Mapping.keys_def zero_map_def plus_map_def Mapping.lookup_def)
next
  show "\<And>x y z :: ('a, 'b) mapping. \<lbrakk>x ## y; y ## z; x ## z\<rbrakk> \<Longrightarrow> x + y + z = x + (y + z)"
    by (simp add: sep_disj_map_def Mapping.keys_def zero_map_def plus_map_def Mapping.lookup_def Mapping_inverse)
next 
  show "\<And>x y z :: ('a, 'b) mapping. \<lbrakk>x ## y + z; y ## z\<rbrakk> \<Longrightarrow> x ## y"
    by (simp add: sep_disj_map_def Mapping.keys_def zero_map_def plus_map_def Mapping.lookup_def map_add_comm) 
      (metis (no_types, opaque_lifting) Mapping.keys.abs_eq Mapping.keys.rep_eq disjoint_iff domIff map_add_dom_app_simps(3))
next
  show "\<And>x y z :: ('a, 'b) mapping. \<lbrakk>x ## y + z; y ## z\<rbrakk> \<Longrightarrow> x + y ## z"
    by (simp add: sep_disj_map_def Mapping.keys_def zero_map_def plus_map_def Mapping.lookup_def map_add_comm Mapping_inverse inf_commute inf_sup_distrib1)
next 
  show "\<And>x z y :: ('a, 'b) mapping. \<lbrakk>x + z = y + z; x ## z; y ## z\<rbrakk> \<Longrightarrow> x = y"
    by (simp add: plus_map_def sep_disj_map_def)
      (metis (mono_tags, opaque_lifting) Mapping.keys.abs_eq Mapping.lookup.abs_eq disjoint_iff domIff map_add_dom_app_simps(3) mapping_eqI)
qed
end

instantiation heap_ext :: (cancellative_sep_algebra) cancellative_sep_algebra 
begin
definition "0 :: 'a heap_scheme \<equiv> \<lparr> next_block = 0, heap_map = Mapping.empty, \<dots> = 0 \<rparr>"
definition "(m1 :: 'a heap_scheme) + (m2 :: 'a heap_scheme) \<equiv> 
              \<lparr> next_block = next_block m1 + next_block m2,
                heap_map = Mapping ((Mapping.lookup (heap_map m1)) ++ (Mapping.lookup (heap_map m2))), 
                \<dots> = heap.more m1 + heap.more m2 \<rparr>" 
definition "(m1 :: 'a heap_scheme) ## (m2 :: 'a heap_scheme) \<equiv> 
              Mapping.keys (heap_map m1) \<inter> Mapping.keys (heap_map m2) = {}
              \<and> heap.more m1 ## heap.more m2" 
instance 
proof
  show "\<And>x :: 'a heap_scheme. x ## 0"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def)
next
  show "\<And>x y :: 'a heap_scheme. x ## y \<Longrightarrow> y ## x"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def inf_commute sep_disj_commute)
next
  show "\<And>x :: 'a heap_scheme. x + 0 = x"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def inf_commute sep_disj_commute Mapping.empty_def Mapping.lookup.abs_eq)
      (simp add: Mapping.lookup.rep_eq rep_inverse)
next
  show "\<And>x y :: 'a heap_scheme. x ## y \<Longrightarrow> x + y = y + x"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def)
      (metis keys_dom_lookup map_add_comm sep_add_commute)
next 
  show "\<And>x y z :: 'a heap_scheme. \<lbrakk>x ## y; y ## z; x ## z\<rbrakk> \<Longrightarrow> x + y + z = x + (y + z)"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def Mapping.lookup.abs_eq sep_add_assoc)
next 
  show "\<And>x y z :: 'a heap_scheme. \<lbrakk>x ## y + z; y ## z\<rbrakk> \<Longrightarrow> x ## y"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def)
      (metis plus_map_def sep_disj_addD sep_disj_map_def)
next
  show "\<And>x y z :: 'a heap_scheme. \<lbrakk>x ## y + z; y ## z\<rbrakk> \<Longrightarrow> x + y ## z"
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def Mapping.lookup.abs_eq disjoint_iff keys_dom_lookup sep_disj_addI1)
next 
  show "\<And>x z y :: 'a heap_scheme. \<lbrakk>x + z = y + z; x ## z; y ## z\<rbrakk> \<Longrightarrow> x = y "
    by (simp add: plus_heap_ext_def sep_disj_heap_ext_def zero_heap_ext_def)
      (metis  heap.equality plus_map_def sep_add_cancel sep_disj_map_def)
qed
end

instantiation mem_capability_ext :: (comp_countable, zero) zero
begin
definition "0 :: ('a, 'b) mem_capability_scheme \<equiv> 
          \<lparr> block_id = 0, 
            offset = 0,
            base = 0, 
            len = 0, 
            perm_load = False, 
            perm_cap_load = False, 
            perm_store = False,
            perm_cap_store = False,
            perm_cap_store_local = False,
            perm_global = False,
            \<dots> =  0\<rparr>"
instance ..
end

subclass (in comp_countable) zero .

instantiation capability_ext :: (zero) zero
begin
definition "0 \<equiv> \<lparr> tag = False, \<dots> = 0\<rparr>"
instance ..
end

text \<open>Section 4.5 of CHERI C/C++ Programming Guide defines what a \texttt{NULL} capability is~\cite{watson_cc_2019}.\<close>
definition null_capability :: "cap" ("NULL")
  where
  "NULL \<equiv> 0"

context 
  notes null_capability_def[simp]
begin

lemma null_capability_block_id[simp]: 
  "block_id NULL = 0"
  by (simp add: zero_mem_capability_ext_def) 

lemma null_capability_offset[simp]:
  "offset NULL = 0"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_base[simp]:
  "base NULL = 0"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_len[simp]:
  "len NULL = 0"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_perm_load[simp]:
  "perm_load NULL = False"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_perm_cap_load[simp]:
  "perm_cap_load NULL = False"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_perm_store[simp]:
  "perm_store NULL = False"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_perm_cap_store[simp]:
  "perm_cap_store NULL = False"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_perm_cap_store_local[simp]:
  "perm_cap_store_local NULL = False"
  by (simp add: zero_mem_capability_ext_def)

lemma null_capability_tag[simp]:
  "tag NULL = False"
  by (simp add: zero_capability_ext_def zero_mem_capability_ext_def)

end

text \<open>Here, we define the initial heap.\<close>
definition init_heap :: "heap"
  where
  "init_heap \<equiv> 0 \<lparr> next_block := 1 \<rparr>"

abbreviation cap_offset :: "nat \<Rightarrow> nat"
  where
  "cap_offset p \<equiv> if p mod |Cap|\<^sub>\<tau> = 0 then p else p - p mod |Cap|\<^sub>\<tau>"

text \<open>We state the well-formedness property $\mathcal{W}^\mathcal{C}_f$ stated in the paper~\cite{park_2022}.\<close>
definition wellformed :: "(block, t) mapping \<Rightarrow> bool" ("\<W>\<^sub>\<ff>/(_/)")
  where
  "\<W>\<^sub>\<ff>(h) \<equiv> 
     \<forall> b obj. Mapping.lookup h b = Some (Map obj) 
     \<longrightarrow> Set.filter (\<lambda>x. x mod |Cap|\<^sub>\<tau> \<noteq> 0) (Mapping.keys (tags obj)) = {}"

lemma init_heap_empty:
  "Mapping.keys (heap_map init_heap) = {}"
  unfolding init_heap_def zero_heap_ext_def
  by simp

text \<open>Below shows $\mathcal{W}^\mathcal{C}_f(\mu_0)$\<close>
lemma init_wellformed:
  "\<W>\<^sub>\<ff>(heap_map init_heap)"
  unfolding init_heap_def wellformed_def zero_heap_ext_def
  by simp

lemma mapping_lookup_disj1:
  "m1 ## m2 \<Longrightarrow> Mapping.lookup m1 n = Some x \<Longrightarrow> Mapping.lookup (m1 + m2) n = Some x"
  by (metis Mapping.keys.rep_eq Mapping.lookup.abs_eq Mapping.lookup.rep_eq disjoint_iff is_none_simps(2) keys_is_none_rep map_add_dom_app_simps(3) plus_map_def sep_disj_map_def)

lemma mapping_lookup_disj2:
  "m1 ## m2 \<Longrightarrow> Mapping.lookup m2 n = Some x \<Longrightarrow> Mapping.lookup (m1 + m2) n = Some x"
  by (metis Mapping.keys.rep_eq Mapping.lookup.abs_eq Mapping.lookup.rep_eq disjoint_iff is_none_simps(2) keys_is_none_rep map_add_dom_app_simps(2) plus_map_def sep_disj_map_def)

text \<open>Below shows that well-formedness is composition-compatible\<close>
lemma "heap_map h1 ## heap_map h2 \<Longrightarrow> \<W>\<^sub>\<ff>(heap_map h1 + heap_map h2) 
   \<Longrightarrow> \<W>\<^sub>\<ff>(heap_map h1) \<and> \<W>\<^sub>\<ff>(heap_map h2)"
  unfolding wellformed_def
  by (safe, erule_tac x=b in allE, erule_tac x=obj in allE)
    (fastforce intro: mapping_lookup_disj1 mapping_lookup_disj2)+

section \<open>Helper functions and lemmas\<close>
primrec is_memval_defined :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_memval_defined _ _ 0 = True"
| "is_memval_defined m off (Suc siz) = ((off \<in> Mapping.keys m) \<and> is_memval_defined m (Suc off) siz)"

primrec is_contiguous_bytes :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_contiguous_bytes _ _ 0 = True"
| "is_contiguous_bytes m off (Suc siz) = ((off \<in> Mapping.keys m) 
                                         \<and> memval_is_byte (the (Mapping.lookup m off))
                                         \<and> is_contiguous_bytes m (Suc off) siz)"

definition get_cap :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> memcap"
  where
  "get_cap m off = of_cap (the (Mapping.lookup m off))"

fun is_cap :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_cap m off = (off \<in> Mapping.keys m \<and> memval_is_cap (the (Mapping.lookup m off)))"

primrec is_contiguous_cap :: "(nat, memval) mapping \<Rightarrow> memcap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_contiguous_cap _ _ _ 0 = True"
| "is_contiguous_cap m c off (Suc siz) = ((off \<in> Mapping.keys m)
                                         \<and> memval_is_cap (the (Mapping.lookup m off))
                                         \<and> of_cap (the (Mapping.lookup m off)) = c
                                         \<and> of_nth (the (Mapping.lookup m off)) = siz
                                         \<and> is_contiguous_cap m c (Suc off) siz)"

primrec is_contiguous_zeros_prim :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_contiguous_zeros_prim _ _ 0 = True"
| "is_contiguous_zeros_prim m off (Suc siz) = (Mapping.lookup m off = Some (Byte 0)
                                              \<and> is_contiguous_zeros_prim m (Suc off) siz)"

definition is_contiguous_zeros :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_contiguous_zeros m off siz \<equiv> \<forall> ofs \<ge> off. ofs < off + siz \<longrightarrow> Mapping.lookup m ofs = Some (Byte 0)"

lemma is_contiguous_zeros_code[code]:
  "is_contiguous_zeros m off siz = is_contiguous_zeros_prim m off siz"
proof safe
  show "is_contiguous_zeros m off siz \<Longrightarrow> is_contiguous_zeros_prim m off siz"
    unfolding is_contiguous_zeros_def
  proof (induct siz arbitrary: off)
    case 0
    thus ?case by simp
  next
    case (Suc siz)
    thus ?case
      by fastforce
  qed
next
  show "is_contiguous_zeros_prim m off siz \<Longrightarrow> is_contiguous_zeros m off siz"
    unfolding is_contiguous_zeros_def
  proof (induct siz arbitrary: off)
    case 0
    thus ?case
      by auto
  next
    case (Suc siz)
    have alt: "is_contiguous_zeros_prim m (Suc off) siz"
      using Suc(2) is_contiguous_zeros_prim.simps(2)[where ?m=m and ?off=off and ?siz=siz]
      by blast
    have add_simp: "Suc off + siz = off + Suc siz" 
      by simp
    show ?case 
      using Suc(1)[where ?off="Suc off", OF alt, simplified add_simp le_eq_less_or_eq Suc_le_eq] 
        Suc(2) Suc_le_eq le_eq_less_or_eq 
      by auto
  qed
qed

  

primrec retrieve_bytes :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word list"
  where
  "retrieve_bytes m _ 0 = []"
| "retrieve_bytes m off (Suc siz) = of_byte (the (Mapping.lookup m off)) # retrieve_bytes m (Suc off) siz"

primrec is_same_cap :: "(nat, memval) mapping \<Rightarrow> memcap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
  "is_same_cap _ _ _ 0 = True"
| "is_same_cap m c off (Suc siz) = (of_cap (the (Mapping.lookup m off)) = c \<and> is_same_cap m c (Suc off) siz)"

(* tag retrieval must be based on offset now *)
definition retrieve_tval :: "object \<Rightarrow> nat \<Rightarrow> cctype \<Rightarrow> bool \<Rightarrow> block ccval"
  where
  "retrieve_tval obj off typ pcl \<equiv> 
     if is_contiguous_bytes (content obj) off |typ|\<^sub>\<tau> then
       (case typ of 
          Uint8  \<Rightarrow> Uint8_v  (decode_u8_list (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Sint8  \<Rightarrow> Sint8_v  (decode_s8_list (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Uint16 \<Rightarrow> Uint16_v (cat_u16 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Sint16 \<Rightarrow> Sint16_v (cat_s16 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Uint32 \<Rightarrow> Uint32_v (cat_u32 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Sint32 \<Rightarrow> Sint32_v (cat_s32 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Uint64 \<Rightarrow> Uint64_v (cat_u64 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Sint64 \<Rightarrow> Sint64_v (cat_s64 (retrieve_bytes (content obj) off |typ|\<^sub>\<tau>))
        | Cap    \<Rightarrow> if is_contiguous_zeros (content obj) off |typ|\<^sub>\<tau> then Cap_v NULL else Undef)
     else if is_cap (content obj) off then
       let cap = get_cap (content obj) off in
       let tv = the (Mapping.lookup (tags obj) (cap_offset off)) in
       let t = (case pcl of False \<Rightarrow> False | True \<Rightarrow> tv) in
       let cv = mem_capability.extend cap \<lparr> tag = t \<rparr> in
       let nth_frag = of_nth (the (Mapping.lookup (content obj) off)) in 
       (case typ of 
          Uint8 \<Rightarrow> Cap_v_frag (mem_capability.extend cap \<lparr> tag = False \<rparr>) nth_frag
        | Sint8 \<Rightarrow> Cap_v_frag (mem_capability.extend cap \<lparr> tag = False \<rparr>) nth_frag
        | Cap   \<Rightarrow> if is_contiguous_cap (content obj) cap off |typ|\<^sub>\<tau> then Cap_v cv else Undef
        | _     \<Rightarrow> Undef)
     else Undef"

primrec store_bytes :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> (nat, memval) mapping"
  where
  "store_bytes obj _ [] = obj"
| "store_bytes obj off (v # vs) = store_bytes (Mapping.update off (Byte v) obj) (Suc off) vs"

primrec store_cap :: "(nat, memval) mapping \<Rightarrow> nat \<Rightarrow> cap \<Rightarrow> nat \<Rightarrow> (nat, memval) mapping"
  where
  "store_cap obj _ _ 0 = obj"
| "store_cap obj off cap (Suc n) = store_cap (Mapping.update off (ACap (mem_capability.truncate cap) n) obj) (Suc off) cap n"

abbreviation store_tag :: "(nat, bool) mapping \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat, bool) mapping"
  where
  "store_tag obj off tg \<equiv> Mapping.update off tg obj"
                                                             
definition store_tval :: "object \<Rightarrow> nat \<Rightarrow> block ccval \<Rightarrow> object"
  where
  "store_tval obj off val \<equiv> 
     case val of Uint8_v  v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (encode_u8_list v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Sint8_v  v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (encode_s8_list v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Uint16_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (u16_split v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Sint16_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (s16_split v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Uint32_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (flatten_u32 v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Sint32_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (flatten_s32 v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Uint64_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (flatten_u64 v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Sint64_v v     \<Rightarrow> obj \<lparr> content := store_bytes (content obj) off (flatten_s64 v), 
                                         tags := store_tag (tags obj) (cap_offset off) False \<rparr>
               | Cap_v    c     \<Rightarrow> obj \<lparr> content := store_cap (content obj) off c |Cap|\<^sub>\<tau>, 
                                         tags := store_tag (tags obj) (cap_offset off) (tag c) \<rparr>
               | Cap_v_frag c n \<Rightarrow> obj \<lparr> content := Mapping.update off (ACap (mem_capability.truncate c) n) (content obj),
                                         tags := store_tag (tags obj) (cap_offset off) False\<rparr>"

lemma stored_bytes_prev:
  assumes "x < off"
  shows "Mapping.lookup (store_bytes obj off vs) x = Mapping.lookup obj x"
  using assms 
  by (induct vs arbitrary: obj off) fastforce+

lemma stored_tags_prev:
  assumes "x < off"
  shows "Mapping.lookup (store_tag obj off vs) x = Mapping.lookup obj x"
  using assms 
  by force

lemma stored_cap_prev:
  assumes "x < off"
  shows "Mapping.lookup (store_cap obj off cap siz) x = Mapping.lookup obj x"
  using assms 
  by (induct siz arbitrary: obj off) fastforce+

lemma stored_bytes_instant_correctness:
  "Mapping.lookup (store_bytes obj off (v # vs)) off = Some (Byte v)"
proof (induct vs arbitrary: obj off)
  case Nil
  thus ?case by force
next 
  case (Cons a vs)
  thus ?case using stored_bytes_prev Suc_eq_plus1 lessI store_bytes.simps(2)
    by metis
qed

lemma stored_cap_instant_correctness:
  "Mapping.lookup (store_cap obj off cap (Suc siz)) off = Some (ACap (mem_capability.truncate cap) siz)"
proof (induct siz arbitrary: obj off)
  case 0
  thus ?case by force
next 
  case (Suc siz)
  thus ?case using stored_cap_prev Suc_eq_plus1 lessI store_cap.simps(2) lookup_update
    by metis
qed

lemma numeral_4_eq_4: "4 = Suc (Suc (Suc (Suc 0)))"
  by (simp add: eval_nat_numeral)

lemma numeral_5_eq_5: "5 = Suc (Suc (Suc (Suc (Suc 0))))"
  by (simp add: eval_nat_numeral)

lemma numeral_6_eq_6: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by (simp add: eval_nat_numeral)

lemma numeral_7_eq_7: "7 = Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  by (simp add: eval_nat_numeral)

lemma numeral_8_eq_8: "8 = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  by (simp add: eval_nat_numeral)

lemma list_length_2_realise:
  "length ls = 2 \<Longrightarrow> \<exists> n0 n1. ls = [n0, n1]"
  by (metis One_nat_def Suc_length_conv add_diff_cancel_right' len_gt_0 len_of_finite_2_def 
      list.size(4) list_exhaust_size_eq0 list_exhaust_size_gt0 one_add_one)

lemma list_length_4_realise: 
  "length ls = 4 \<Longrightarrow> \<exists> n0 n1 n2 n3. ls = [n0, n1, n2, n3]"
  by (metis list_exhaust_size_eq0 list_exhaust_size_gt0 numeral_4_eq_4 size_Cons_lem_eq zero_less_Suc)

lemma list_length_8_realise:
  "length ls = 8 \<Longrightarrow> \<exists> n0 n1 n2 n3 n4 n5 n6 n7. ls = [n0, n1, n2, n3, n4, n5, n6, n7]"
  using list_exhaust_size_eq0 list_exhaust_size_gt0 numeral_8_eq_8 size_Cons_lem_eq zero_less_Suc
  by smt

lemma u16_split_realise:
  "\<exists> b0 b1. u16_split v = [b0, b1]" 
  using list_length_2_realise[where ?ls="u16_split v", OF flatten_u16_length[where ?vs=v]]
  by assumption

lemma s16_split_realise:
  "\<exists> b0 b1. s16_split v = [b0, b1]"
  using list_length_2_realise[where ?ls="s16_split v", OF flatten_s16_length[where ?vs=v]]
  by assumption

lemma u32_split_realise:
  "\<exists> b0 b1 b2 b3. flatten_u32 v = [b0, b1, b2, b3]"
  using list_length_4_realise[where ?ls="flatten_u32 v", OF flatten_u32_length[where ?vs=v]]
  by assumption

lemma s32_split_realise:
  "\<exists> b0 b1 b2 b3. flatten_s32 v = [b0, b1, b2, b3]"
  using list_length_4_realise[where ?ls="flatten_s32 v", OF flatten_s32_length[where ?vs=v]]
  by assumption

lemma u64_split_realise:
  "\<exists> b0 b1 b2 b3 b4 b5 b6 b7. flatten_u64 v = [b0, b1, b2, b3, b4, b5, b6, b7]"
  using list_length_8_realise[where ?ls="flatten_u64 v", OF flatten_u64_length[where ?vs=v]]
  by assumption

lemma s64_split_realise:
  "\<exists> b0 b1 b2 b3 b4 b5 b6 b7. flatten_s64 v = [b0, b1, b2, b3, b4, b5, b6, b7]"
  using list_length_8_realise[where ?ls="flatten_s64 v", OF flatten_s64_length[where ?vs=v]]
  by assumption

lemma store_bytes_u16:
  shows "off \<in> Mapping.keys (store_bytes m off (u16_split v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (u16_split v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (u16_split v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (u16_split v)) (Suc off) = Some (Byte b1)" 
proof -
  show "off \<in> Mapping.keys (store_bytes m off (u16_split v))"
    by (metis (no_types, opaque_lifting) domIff u16_split_realise handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (u16_split v))"
    by (metis (mono_tags, opaque_lifting) domIff u16_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (u16_split v)) off = Some (Byte b0)"
    by (metis u16_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (u16_split v)) (Suc off) = Some (Byte b1)"
    by (metis u16_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

lemma store_bytes_s16:
  shows "off \<in> Mapping.keys (store_bytes m off (s16_split v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (s16_split v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (s16_split v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (s16_split v)) (Suc off) = Some (Byte b1)" 
proof -
  show "off \<in> Mapping.keys (store_bytes m off (s16_split v))"
    by (metis (no_types, opaque_lifting) domIff s16_split_realise handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (s16_split v))"
    by (metis (mono_tags, opaque_lifting) domIff s16_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (s16_split v)) off = Some (Byte b0)"
    by (metis s16_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (s16_split v)) (Suc off) = Some (Byte b1)"
    by (metis s16_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

lemma store_bytes_u32:
  shows "off \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    and "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    and "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u32 v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc off) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc (Suc off)) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
proof -
  show "off \<in> Mapping.keys (store_bytes m off (flatten_u32 v))" 
    by (metis (no_types, opaque_lifting) domIff handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness u32_split_realise)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (flatten_u32 v))" 
    by (metis (mono_tags, opaque_lifting) domIff u32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    by (metis (mono_tags, opaque_lifting) domIff u32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_u32 v))"
    by (metis (mono_tags, opaque_lifting) domIff u32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u32 v)) off = Some (Byte b0)"
    by (metis u32_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc off) = Some (Byte b1)"
    by (metis u32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc (Suc off)) = Some (Byte b2)"
    by (metis u32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u32 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
    by (metis u32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

lemma store_bytes_s32:
  shows "off \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    and "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    and "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s32 v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc off) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc (Suc off)) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
proof -
  show "off \<in> Mapping.keys (store_bytes m off (flatten_s32 v))" 
    by (metis (no_types, opaque_lifting) domIff handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness s32_split_realise)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (flatten_s32 v))" 
    by (metis (mono_tags, opaque_lifting) domIff s32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    by (metis (mono_tags, opaque_lifting) domIff s32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_s32 v))"
    by (metis (mono_tags, opaque_lifting) domIff s32_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s32 v)) off = Some (Byte b0)"
    by (metis s32_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc off) = Some (Byte b1)"
    by (metis s32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc (Suc off)) = Some (Byte b2)"
    by (metis s32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s32 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
    by (metis s32_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

lemma store_bytes_u64:
  shows "off \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc (Suc (Suc off))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc (Suc (Suc (Suc off)))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc (Suc (Suc (Suc (Suc off))))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "Suc (Suc (Suc (Suc (Suc (Suc (Suc off)))))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u64 v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc off) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc off)) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc off))) = Some (Byte b3)"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc off)))) = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc off))))) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))) = Some (Byte b3)"
proof -
  show "off \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (no_types, opaque_lifting) domIff handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness u64_split_realise)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (flatten_u64 v))" 
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc off))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc off)))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc (Suc off))))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc (Suc (Suc off)))))) \<in> Mapping.keys (store_bytes m off (flatten_u64 v))"
    by (metis (mono_tags, opaque_lifting) domIff u64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u64 v)) off = Some (Byte b0)"
    by (metis u64_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc off) = Some (Byte b1)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc off)) = Some (Byte b2)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc off)))) = Some (Byte b0)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next 
  show"\<exists> b1. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc off))))) = Some (Byte b1)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))) = Some (Byte b2)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next 
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_u64 v)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))) = Some (Byte b3)"
    by (metis u64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

lemma store_bytes_s64:
  shows "off \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc off \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc (Suc (Suc off))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc (Suc (Suc (Suc off)))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc (Suc (Suc (Suc (Suc off))))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "Suc (Suc (Suc (Suc (Suc (Suc (Suc off)))))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s64 v)) off = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc off) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc off)) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc off))) = Some (Byte b3)"
    and "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc off)))) = Some (Byte b0)"
    and "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc off))))) = Some (Byte b1)"
    and "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))) = Some (Byte b2)"
    and "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))) = Some (Byte b3)"
proof -
  show "off \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (no_types, opaque_lifting) domIff handy_if_lemma keys_dom_lookup 
        stored_bytes_instant_correctness s64_split_realise)
next
  show "Suc off \<in> Mapping.keys (store_bytes m off (flatten_s64 v))" 
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc off) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc off)) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc off))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc off)))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc (Suc off))))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "Suc (Suc (Suc (Suc (Suc (Suc (Suc off)))))) \<in> Mapping.keys (store_bytes m off (flatten_s64 v))"
    by (metis (mono_tags, opaque_lifting) domIff s64_split_realise handy_if_lemma keys_dom_lookup 
        store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s64 v)) off = Some (Byte b0)"
    by (metis s64_split_realise stored_bytes_instant_correctness)
next
  show "\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc off) = Some (Byte b1)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc off)) = Some (Byte b2)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc off))) = Some (Byte b3)" 
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b0. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc off)))) = Some (Byte b0)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next 
  show"\<exists> b1. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc off))))) = Some (Byte b1)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next
  show "\<exists> b2. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))) = Some (Byte b2)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
next 
  show "\<exists> b3. Mapping.lookup (store_bytes m off (flatten_s64 v)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))) = Some (Byte b3)"
    by (metis s64_split_realise store_bytes.simps(2) stored_bytes_instant_correctness)
qed

corollary u16_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (u16_split v)) off 2"
  by (metis One_nat_def Suc_1 is_contiguous_bytes.simps(1) is_contiguous_bytes.simps(2) memval_memcap_not_byte option.sel store_bytes_u16)

corollary s16_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (s16_split v)) off 2"
  by (metis One_nat_def Suc_1 is_contiguous_bytes.simps(1) is_contiguous_bytes.simps(2) memval_memcap_not_byte option.sel store_bytes_s16)

corollary u32_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (flatten_u32 v)) off 4" 
  by(simp add: numeral_4_eq_4, safe) 
    (simp add: store_bytes_u32, metis memval_memcap_not_byte option.sel store_bytes_u32)+ 

corollary s32_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (flatten_s32 v)) off 4" 
  by(simp add: numeral_4_eq_4, safe) 
    (simp add: store_bytes_s32, metis memval_memcap_not_byte option.sel store_bytes_s32)+

corollary u64_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (flatten_u64 v)) off 8" 
  by(simp add: numeral_8_eq_8, safe) 
    (simp add: store_bytes_u64, metis memval_memcap_not_byte option.sel store_bytes_u64)+ 

corollary s64_store_bytes_imp_is_contiguous_bytes:
  "is_contiguous_bytes (store_bytes m off (flatten_s64 v)) off 8" 
  by(simp add: numeral_8_eq_8, safe) 
    (simp add: store_bytes_s64, metis memval_memcap_not_byte option.sel store_bytes_s64)+ 

lemma stored_tval_contiguous_bytes:
  assumes "val \<noteq> Undef"
    and "\<forall> v. val \<noteq> Cap_v v"
    and "\<forall> v n. val \<noteq> Cap_v_frag v n"
  shows "is_contiguous_bytes (content (store_tval obj off val)) off |memval_type val|\<^sub>\<tau>"
  unfolding sizeof_def
  by (simp add: assms store_tval_def memval_is_byte_def split: ccval.split) (presburger add: s16_store_bytes_imp_is_contiguous_bytes s32_store_bytes_imp_is_contiguous_bytes s64_store_bytes_imp_is_contiguous_bytes u16_store_bytes_imp_is_contiguous_bytes u32_store_bytes_imp_is_contiguous_bytes u64_store_bytes_imp_is_contiguous_bytes)

lemma suc_of_32: 
  "32 = Suc 31"
  by simp

lemma store_cap_correct_dom:
  shows "off      \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 1  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 2  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 3  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 4  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 5  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 6  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 7  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 8  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 9  \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 10 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 11 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 12 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 13 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 14 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 15 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 16 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 17 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 18 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 19 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 20 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 21 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 22 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 23 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 24 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 25 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 26 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 27 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 28 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 29 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 30 \<in> Mapping.keys (store_cap m off cap 32)"
    and "off + 31 \<in> Mapping.keys (store_cap m off cap 32)" 
proof - qed (simp add: suc_of_32 domIff eval_nat_numeral(3) numeral_Bit0)+

lemma store_cap_correct_val:
  shows "Mapping.lookup (store_cap m off cap 32) off = 
         Some (ACap (mem_capability.truncate cap) 31)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 1) = 
         Some (ACap (mem_capability.truncate cap) 30)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 2) = 
         Some (ACap (mem_capability.truncate cap) 29)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 3) = 
         Some (ACap (mem_capability.truncate cap) 28)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 4) = 
         Some (ACap (mem_capability.truncate cap) 27)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 5) = 
         Some (ACap (mem_capability.truncate cap) 26)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 6) = 
         Some (ACap (mem_capability.truncate cap) 25)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 7) = 
         Some (ACap (mem_capability.truncate cap) 24)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 8) = 
         Some (ACap (mem_capability.truncate cap) 23)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 9) = 
         Some (ACap (mem_capability.truncate cap) 22)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 10) = 
         Some (ACap (mem_capability.truncate cap) 21)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 11) = 
         Some (ACap (mem_capability.truncate cap) 20)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 12) = 
         Some (ACap (mem_capability.truncate cap) 19)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 13) = 
         Some (ACap (mem_capability.truncate cap) 18)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 14) = 
         Some (ACap (mem_capability.truncate cap) 17)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 15) = 
         Some (ACap (mem_capability.truncate cap) 16)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 16) = 
         Some (ACap (mem_capability.truncate cap) 15)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 17) = 
         Some (ACap (mem_capability.truncate cap) 14)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 18) = 
         Some (ACap (mem_capability.truncate cap) 13)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 19) = 
         Some (ACap (mem_capability.truncate cap) 12)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 20) = 
         Some (ACap (mem_capability.truncate cap) 11)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 21) = 
         Some (ACap (mem_capability.truncate cap) 10)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 22) = 
         Some (ACap (mem_capability.truncate cap) 9)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 23) = 
         Some (ACap (mem_capability.truncate cap) 8)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 24) = 
         Some (ACap (mem_capability.truncate cap) 7)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 25) = 
         Some (ACap (mem_capability.truncate cap) 6)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 26) = 
         Some (ACap (mem_capability.truncate cap) 5)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 27) = 
         Some (ACap (mem_capability.truncate cap) 4)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 28) = 
         Some (ACap (mem_capability.truncate cap) 3)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 29) = 
         Some (ACap (mem_capability.truncate cap) 2)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 30) = 
         Some (ACap (mem_capability.truncate cap) 1)"
    and "Mapping.lookup (store_cap m off cap 32) (off + 31) = 
         Some (ACap (mem_capability.truncate cap) 0)"
proof - qed (simp add: stored_cap_instant_correctness suc_of_32 eval_nat_numeral(3) numeral_Bit0)+

corollary store_cap_imp_is_contiguous_cap:
  "is_contiguous_cap (store_cap m off cap 32) (mem_capability.truncate cap) off 32"
  using memval_byte_not_memcap 
  by (simp add: eval_nat_numeral(3) numeral_Bit0, blast)

lemma stored_tval_is_cap:
  assumes "val = Cap_v v"
  shows "is_cap (content (store_tval obj off val)) off" 
  using memval_byte_not_memcap sizeof_def store_cap_correct_val(1) 
  by (auto simp add: assms store_tval_def conjI sizeof_def store_cap_correct_dom(1) split: ccval.split)

lemma stored_tval_contiguous_cap:
  assumes "val = Cap_v cap"
  shows "is_contiguous_cap (content (store_tval obj off val)) (mem_capability.truncate cap) off |memval_type val|\<^sub>\<tau>"
  using assms store_tval_def
  by (simp add: sizeof_def store_cap_imp_is_contiguous_cap)

lemma decode_encoded_u16_in_mem:
  "cat_u16 (retrieve_bytes (content (store_tval obj off (Uint16_v x))) off |Uint16|\<^sub>\<tau>) = x"
proof -
  have "of_byte (the (Mapping.lookup (store_bytes (content obj) off (u16_split x)) off)) = u16_split x ! 0"
    by (smt (verit, best) Some_to_the length_nth_simps(3) memval.sel(1) stored_bytes_instant_correctness u16_split_realise)
  also have "of_byte (the (Mapping.lookup (store_bytes (content obj) off (u16_split x)) (Suc off))) = (u16_split x) ! 1"
    by (metis One_nat_def length_nth_simps(3) memval.sel(1) nth_Cons_Suc option.sel store_bytes.simps(2) stored_bytes_instant_correctness u16_split_realise)
  ultimately show ?thesis 
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0)
      (metis cat_flatten_u16_eq length_nth_simps(3) nth_Cons_Suc u16_split_realise)
qed

lemma decode_encoded_s16_in_mem: 
  "cat_s16 (retrieve_bytes (content (store_tval obj off (Sint16_v x))) off |Sint16|\<^sub>\<tau>) = x"
proof -
  have "of_byte (the (Mapping.lookup (store_bytes (content obj) off (s16_split x)) off)) = s16_split x ! 0"
    by (smt (verit, best) Some_to_the length_nth_simps(3) memval.sel(1) stored_bytes_instant_correctness s16_split_realise)
  also have "of_byte (the (Mapping.lookup (store_bytes (content obj) off (s16_split x)) (Suc off))) = (s16_split x) ! 1"
    by (metis One_nat_def length_nth_simps(3) memval.sel(1) nth_Cons_Suc option.sel store_bytes.simps(2) stored_bytes_instant_correctness s16_split_realise)
  ultimately show ?thesis 
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0)
      (metis cat_flatten_s16_eq length_nth_simps(3) nth_Cons_Suc s16_split_realise)
qed

lemma decode_encoded_u32_in_mem:
  "cat_u32 (retrieve_bytes (content (store_tval obj off (Uint32_v x))) off |Uint32|\<^sub>\<tau>) = x"
proof -
  have fst: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u32 x)) off)) = flatten_u32 x ! 0"
    by (metis length_nth_simps(3) memval.sel(1) option.sel stored_bytes_instant_correctness u32_split_realise)
  have snd: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u32 x)) (Suc off))) = flatten_u32 x ! 1" 
    by (metis One_nat_def length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel store_bytes.simps(2) stored_bytes_instant_correctness u32_split_realise)
  have trd: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u32 x)) (Suc (Suc off)))) = flatten_u32 x ! 2" 
    by (metis One_nat_def Suc_1 length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel store_bytes.simps(2) stored_bytes_instant_correctness u32_split_realise)
  have fth: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u32 x)) (Suc (Suc (Suc off))))) = flatten_u32 x ! 3"
    by (metis Some_to_the length_nth_simps(3) length_nth_simps(4) memval.sel(1) numeral_3_eq_3 store_bytes.simps(2) stored_bytes_instant_correctness u32_split_realise)
  show ?thesis 
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0)
      (smt (verit, del_insts) fst snd trd fth One_nat_def Suc_1 eval_nat_numeral(3) length_nth_simps(3) length_nth_simps(4) u32_split_realise word_rcat_rsplit)
qed

lemma decode_encoded_s32_in_mem:
  "cat_s32 (retrieve_bytes (content (store_tval obj off (Sint32_v x))) off |Sint32|\<^sub>\<tau>) = x"
proof -
  have fst: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s32 x)) off)) = flatten_s32 x ! 0"
    by (metis length_nth_simps(3) memval.sel(1) option.sel stored_bytes_instant_correctness s32_split_realise)
  have snd: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s32 x)) (Suc off))) = flatten_s32 x ! 1" 
    by (metis One_nat_def length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel store_bytes.simps(2) stored_bytes_instant_correctness s32_split_realise)
  have trd: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s32 x)) (Suc (Suc off)))) = flatten_s32 x ! 2" 
    by (metis One_nat_def Suc_1 length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel store_bytes.simps(2) stored_bytes_instant_correctness s32_split_realise)
  have fth: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s32 x)) (Suc (Suc (Suc off))))) = flatten_s32 x ! 3"
    by (metis Some_to_the length_nth_simps(3) length_nth_simps(4) memval.sel(1) numeral_3_eq_3 store_bytes.simps(2) stored_bytes_instant_correctness s32_split_realise)
  show ?thesis 
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0) 
      (smt (verit, del_insts) fst snd trd fth One_nat_def Suc_1 eval_nat_numeral(3) length_nth_simps(3) length_nth_simps(4) s32_split_realise word_rcat_rsplit)
qed

lemma cat_flatten_u64_contents_eq:
  "cat_u64 [flatten_u64 vs ! 0, flatten_u64 vs ! 1, flatten_u64 vs ! 2, flatten_u64 vs ! 3, flatten_u64 vs ! 4, flatten_u64 vs ! 5, flatten_u64 vs ! 6, flatten_u64 vs ! 7] = vs"
  using u64_split_realise[where ?v=vs] 
  by clarsimp (metis cat_flatten_u64_eq)

lemma cat_flatten_s64_contents_eq:
  "cat_s64 [flatten_s64 vs ! 0, flatten_s64 vs ! 1, flatten_s64 vs ! 2, flatten_s64 vs ! 3, flatten_s64 vs ! 4, flatten_s64 vs ! 5, flatten_s64 vs ! 6, flatten_s64 vs ! 7] = vs"
  using s64_split_realise[where ?v=vs] 
  by clarsimp (metis word_rcat_rsplit)

lemma decode_encoded_u64_in_mem:
  "cat_u64 (retrieve_bytes (content (store_tval obj off (Uint64_v x))) off |Uint64|\<^sub>\<tau>) = x"
proof -
  have all_bytes: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) off)) = flatten_u64 x ! 0 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc off))) = flatten_u64 x ! 1 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc off)))) = flatten_u64 x ! 2 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc (Suc off))))) = flatten_u64 x ! 3 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc (Suc (Suc off)))))) = flatten_u64 x ! 4 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc (Suc (Suc (Suc off))))))) = flatten_u64 x ! 5 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))))) = flatten_u64 x ! 6 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_u64 x)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))))) = flatten_u64 x ! 7"
    by (smt (verit, best) length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel One_nat_def numeral_2_eq_2 numeral_3_eq_3 numeral_4_eq_4 numeral_5_eq_5 numeral_6_eq_6 numeral_7_eq_7 store_bytes.simps(2) stored_bytes_instant_correctness u64_split_realise)
  show ?thesis
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0)
      (presburger add: all_bytes cat_flatten_u64_contents_eq)
qed

lemma decode_encoded_s64_in_mem:
  "cat_s64 (retrieve_bytes (content (store_tval obj off (Sint64_v x))) off |Sint64|\<^sub>\<tau>) = x"
proof -
  have all_bytes: "of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) off)) = flatten_s64 x ! 0 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc off))) = flatten_s64 x ! 1 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc off)))) = flatten_s64 x ! 2 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc (Suc off))))) = flatten_s64 x ! 3 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc (Suc (Suc off)))))) = flatten_s64 x ! 4 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc (Suc (Suc (Suc off))))))) = flatten_s64 x ! 5 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc (Suc (Suc (Suc (Suc off)))))))) = flatten_s64 x ! 6 \<and>
    of_byte (the (Mapping.lookup (store_bytes (content obj) off (flatten_s64 x)) (Suc (Suc (Suc (Suc (Suc (Suc (Suc off))))))))) = flatten_s64 x ! 7"
    by (smt (verit, best) length_nth_simps(3) length_nth_simps(4) memval.sel(1) option.sel One_nat_def numeral_2_eq_2 numeral_3_eq_3 numeral_4_eq_4 numeral_5_eq_5 numeral_6_eq_6 numeral_7_eq_7 store_bytes.simps(2) stored_bytes_instant_correctness s64_split_realise)
  show ?thesis
    by (clarsimp simp add: sizeof_def store_tval_def eval_nat_numeral(3), simp add: numeral_Bit0)
      (presburger add: all_bytes cat_flatten_s64_contents_eq)
qed                                                                                                                                                                                                                                                

lemma retrieve_stored_tval_cap:
  assumes "val = Cap_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) True = val"
  apply (clarsimp simp add: assms)
  unfolding retrieve_tval_def
  apply (clarsimp simp add: stored_tval_contiguous_cap; safe)
                     apply (metis is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero)
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp 
     apply (subst suc_of_32) 
     apply (simp only: stored_cap_instant_correctness)
     apply simp
     apply (simp add: mem_capability.extend_def mem_capability.truncate_def)
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    apply (metis is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero)
    done
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp 
     apply (subst suc_of_32) 
     apply (simp only: stored_cap_instant_correctness)
     apply simp
     apply (simp add: mem_capability.extend_def mem_capability.truncate_def)
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    apply (metis cctype.simps(81) is_contiguous_bytes.simps(2) sizeof_def suc_of_32)
    done
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp
    apply (metis is_contiguous_zeros_def le_eq_less_or_eq less_add_same_cancel1 memval_memcap_not_byte option.sel suc_of_32 zero_less_Suc) 
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    apply (metis gr_implies_not_zero is_contiguous_bytes.simps(2) old.nat.exhaust sizeof_nonzero)
    done
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp 
     apply (subst suc_of_32) 
     apply (simp only: stored_cap_instant_correctness)
     apply simp
     apply (simp add: mem_capability.extend_def mem_capability.truncate_def)
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  done

lemma retrieve_stored_tval_cap_no_perm_cap_load:
  assumes "val = Cap_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) False = (Cap_v (v \<lparr> tag := False \<rparr>))"
  apply (clarsimp simp add: assms)
  unfolding retrieve_tval_def
  apply (clarsimp simp add: stored_tval_contiguous_cap; safe)
  subgoal
    apply (metis is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero)
    done
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp
    apply (metis is_contiguous_zeros_def le_eq_less_or_eq less_add_same_cancel1 memval_memcap_not_byte option.sel suc_of_32 zero_less_Suc) 
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    apply (metis is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero)
    done
  subgoal
    apply (subgoal_tac "is_contiguous_cap (content (store_tval obj off (Cap_v v))) (get_cap (content (store_tval obj off (Cap_v v))) off) off |Cap|\<^sub>\<tau>")
     apply clarsimp 
     apply (simp only: store_tval_def get_cap_def sizeof_def)
     apply clarsimp 
     apply (subst suc_of_32) 
     apply (simp only: stored_cap_instant_correctness)
     apply simp
     apply (simp add: mem_capability.extend_def mem_capability.truncate_def)
    apply (metis cctype.simps(81) get_cap_def is_contiguous_cap.simps(2) memval_size_cap sizeof_def stored_tval_contiguous_cap suc_of_32)
    done
  subgoal
    using stored_tval_is_cap by auto
  subgoal
    using stored_tval_is_cap by auto
  done

lemma retrieve_stored_tval_u8:
  assumes "val = Uint8_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint8_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint8_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>\<rbrakk>
     \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>) = v"
    by (simp add: sizeof_def) 
next 
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint8_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint8_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>"
    by (metis One_nat_def ccval.distinct(15) ccval.distinct(17) ccval.distinct(19) is_contiguous_bytes.simps(2) memval_size_u8 stored_tval_contiguous_bytes)
next
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Uint8_v v))); is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>) = v"
    by (simp add: sizeof_def)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Uint8_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>"
    by (metis cctype.simps(73) ccval.distinct(15) ccval.distinct(17) ccval.distinct(19) memval_size_u8 sizeof_def stored_tval_contiguous_bytes)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint8_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau>) = v"
    by (clarsimp simp add: sizeof_def store_tval_def)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint8_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint8_v v))) off |Uint8|\<^sub>\<tau> "
    by (metis cctype.simps(73) ccval.distinct(15) ccval.distinct(17) ccval.distinct(19) memval_size_u8 sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_s8:
  assumes "val = Sint8_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint8_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint8_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>) = SCAST(8 signed \<rightarrow> 8) v"
    by (simp add: sizeof_def)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint8_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint8_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>"
    by (metis One_nat_def ccval.distinct(33) ccval.distinct(35) ccval.distinct(37) is_contiguous_bytes.simps(2) memval_size_s8 stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Sint8_v v))); is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>) = SCAST(8 signed \<rightarrow> 8) v"
    by (simp add: sizeof_def)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Sint8_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>"
    by (metis cctype.simps(74) ccval.distinct(33) ccval.distinct(35) ccval.distinct(37) memval_size_s8 sizeof_def stored_tval_contiguous_bytes)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint8_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> decode_u8_list (retrieve_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>) = SCAST(8 signed \<rightarrow> 8) v"
    by (clarsimp simp add: sizeof_def store_tval_def)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint8_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint8_v v))) off |Sint8|\<^sub>\<tau>"
    by (metis cctype.simps(74) ccval.distinct(33) ccval.distinct(35) ccval.distinct(37) memval_size_s8 sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_u16:
  assumes "val = Uint16_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint16_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint16_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u16 (retrieve_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u16_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint16_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint16_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>"
    by (metis ccval.distinct(49) ccval.distinct(51) ccval.distinct(53) is_contiguous_bytes.simps(2) memval_size_u16 numeral_2_eq_2 stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Uint16_v v))); is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u16 (retrieve_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u16_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Uint16_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>"
    by (metis Suc_1 ccval.distinct(49) ccval.distinct(51) ccval.distinct(53) is_contiguous_bytes.simps(2) memval_size_u16 stored_tval_contiguous_bytes)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint16_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u16 (retrieve_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u16_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint16_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint16_v v))) off |Uint16|\<^sub>\<tau>"
    by (metis cctype.simps(75) ccval.distinct(49) ccval.distinct(51) ccval.distinct(53) memval_size_u16 sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_s16:
  assumes "val = Sint16_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint16_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint16_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s16 (retrieve_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s16_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint16_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint16_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>"
    by (metis ccval.distinct(63) ccval.distinct(65) ccval.distinct(67) is_contiguous_bytes.simps(2) memval_size_s16 numeral_2_eq_2 stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Sint16_v v))); is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s16 (retrieve_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s16_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Sint16_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>"
    by (metis Suc_1 ccval.distinct(63) ccval.distinct(65) ccval.distinct(67) is_contiguous_bytes.simps(2) memval_size_s16 stored_tval_contiguous_bytes)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint16_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s16 (retrieve_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s16_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint16_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint16_v v))) off |Sint16|\<^sub>\<tau>"
    by (metis cctype.simps(76) ccval.distinct(63) ccval.distinct(65) ccval.distinct(67) memval_size_s16 sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_u32:
  assumes "val = Uint32_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint32_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint32_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u32 (retrieve_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u32_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint32_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint32_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>"
    by (metis ccval.distinct(75) ccval.distinct(77) ccval.distinct(79) is_contiguous_bytes.simps(2) memval_size_u32 numeral_4_eq_4 stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Uint32_v v))); is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u32 (retrieve_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u32_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Uint32_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>"
    by (metis ccval.distinct(77) ccval.distinct(79) is_cap.elims(2) is_contiguous_bytes.simps(2) memval_size_u32 numeral_4_eq_4 stored_tval_contiguous_bytes stored_tval_is_cap)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint32_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u32 (retrieve_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u32_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint32_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint32_v v))) off |Uint32|\<^sub>\<tau>"
    by (metis cctype.simps(77) ccval.distinct(75) ccval.distinct(77) ccval.distinct(79) memval_size_u32 sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_s32:
  assumes "val = Sint32_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint32_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint32_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s32 (retrieve_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s32_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint32_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint32_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>"
    by (metis cctype.simps(78) ccval.distinct(85) ccval.distinct(87) ccval.distinct(89) flatten_s32_length memval_size_s32_eq_word_split_len sizeof_def stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Sint32_v v))); is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s32 (retrieve_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s32_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Sint32_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>"
    by (metis ccval.distinct(85) ccval.distinct(87) ccval.distinct(89) is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero stored_tval_contiguous_bytes)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint32_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s32 (retrieve_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s32_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint32_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint32_v v))) off |Sint32|\<^sub>\<tau>"
    by (metis cctype.simps(78) ccval.distinct(85) ccval.distinct(87) ccval.simps(100) flatten_s32_length memval_size_s32_eq_word_split_len sizeof_def stored_tval_contiguous_bytes)
qed

lemma retrieve_stored_tval_u64:
  assumes "val = Uint64_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint64_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint64_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u64 (retrieve_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u64_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Uint64_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Uint64_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>"
    by (metis cctype.simps(79) ccval.distinct(93) ccval.distinct(95) ccval.distinct(97) memval_size_u64 sizeof_def stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Uint64_v v))); is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u64 (retrieve_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u64_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Uint64_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>"
    by (metis cctype.simps(79) ccval.distinct(95) ccval.distinct(97) is_cap.elims(1) memval_size_u64 sizeof_def stored_tval_contiguous_bytes stored_tval_is_cap)
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint64_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_u64 (retrieve_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_u64_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Uint64_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Uint64_v v))) off |Uint64|\<^sub>\<tau>"
    by (metis cctype.simps(79) ccval.distinct(93) ccval.distinct(95) ccval.distinct(97) memval_size_u64 sizeof_def stored_tval_contiguous_bytes) 
qed

lemma retrieve_stored_tval_s64:
  assumes "val = Sint64_v v"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  unfolding retrieve_tval_def
proof (clarsimp simp add: assms stored_tval_contiguous_bytes; safe)
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint64_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint64_v v))) off));
     is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s64 (retrieve_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s64_in_mem)
next
  show "\<lbrakk>off \<in> Mapping.keys (content (store_tval obj off (Sint64_v v))); memval_is_cap (the (Mapping.lookup (content (store_tval obj off (Sint64_v v))) off))\<rbrakk>
    \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>"
    by (metis cctype.simps(80) ccval.distinct(101) ccval.distinct(103) ccval.distinct(99) memval_size_s64 sizeof_def stored_tval_contiguous_bytes)
next 
  show "\<lbrakk>off \<notin> Mapping.keys (content (store_tval obj off (Sint64_v v))); is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s64 (retrieve_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s64_in_mem)
next
  show "off \<notin> Mapping.keys (content (store_tval obj off (Sint64_v v))) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>"
    by (metis bot_nat_0.not_eq_extremum ccval.distinct(101) ccval.distinct(103) ccval.distinct(99) is_contiguous_bytes.simps(2) list_decode.cases sizeof_nonzero stored_tval_contiguous_bytes) 
next
  show "\<lbrakk>memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint64_v v))) off)); is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>\<rbrakk>
    \<Longrightarrow> cat_s64 (retrieve_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>) = v"
    by (presburger add: decode_encoded_s64_in_mem)
next
  show "memval_is_byte (the (Mapping.lookup (content (store_tval obj off (Sint64_v v))) off)) \<Longrightarrow> is_contiguous_bytes (content (store_tval obj off (Sint64_v v))) off |Sint64|\<^sub>\<tau>"
    by (metis cctype.simps(80) ccval.distinct(101) ccval.distinct(103) ccval.distinct(99) memval_size_s64 sizeof_def stored_tval_contiguous_bytes)
qed

lemma memcap_truncate_extend_equiv:
  "mem_capability.extend (mem_capability.truncate c) \<lparr> tag = tag c \<rparr> = c"
  by (simp add: mem_capability.extend_def mem_capability.truncate_def)

corollary Acap_truncate_extend_equiv:
  "mem_capability.extend (of_cap (ACap (mem_capability.truncate c) n)) \<lparr> tag = tag c \<rparr> = c"
  by clarsimp (blast intro: memcap_truncate_extend_equiv)

lemma memcap_truncate_extend_gen:
  "mem_capability.extend (mem_capability.truncate c) \<lparr> tag = b \<rparr> = c \<lparr> tag := b \<rparr>"
  by (simp add: mem_capability.extend_def mem_capability.truncate_def)

corollary Acap_truncate_extend_gen:
  "mem_capability.extend (of_cap (ACap (mem_capability.truncate c) n)) \<lparr> tag = b \<rparr> = c \<lparr> tag := b \<rparr>"
  by clarsimp (blast intro: memcap_truncate_extend_gen)

lemma retrieve_stored_tval_cap_frag:
  assumes "val = Cap_v_frag c n"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = 
         Cap_v_frag (c \<lparr> tag := False \<rparr>) n"
  by (clarsimp simp add: assms retrieve_tval_def store_tval_def sizeof_def get_cap_def memcap_truncate_extend_gen memval_is_byte_def split: bool.split) 

lemmas retrieve_stored_tval_prim = retrieve_stored_tval_u8 retrieve_stored_tval_s8
retrieve_stored_tval_u16 retrieve_stored_tval_s16
retrieve_stored_tval_u32 retrieve_stored_tval_s32
retrieve_stored_tval_u64 retrieve_stored_tval_s64

lemma retrieve_stored_tval_any_perm:
  assumes "val \<noteq> Undef"
    and "\<forall> v. val \<noteq> Cap_v v"
    and "\<forall> v n. val \<noteq> Cap_v_frag v n"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) b = val"
  using retrieve_stored_tval_prim[where ?obj=obj and ?off=off and ?val=val and ?b=b]
  by (clarsimp simp add: assms split: ccval.split)

lemma retrieve_stored_tval_with_perm_cap_load:
  assumes "val \<noteq> Undef"
    and "\<forall> v n. val \<noteq> Cap_v_frag v n"
  shows "retrieve_tval (store_tval obj off val) off (memval_type val) True = val"
  using retrieve_stored_tval_prim[where ?obj=obj and ?off=off and ?val=val and ?b=True]
    retrieve_stored_tval_cap[where ?obj=obj and ?off=off and ?val=val]
  by (clarsimp simp add: assms split: ccval.split) 

lemma store_bytes_domain_1:
  assumes "x + length vs \<le> n"
  shows "Mapping.lookup (store_bytes m n vs) x = Mapping.lookup m x"
  using assms 
  by (induct vs arbitrary: x m n) simp_all

lemma store_bytes_domain_2:
  assumes "n + length vs \<le> x"
  shows "Mapping.lookup (store_bytes m n vs) x = Mapping.lookup m x"
  using assms 
  by (induct vs arbitrary: x m n) simp_all

lemma store_bytes_keys_1:
  "Set.filter (\<lambda> x. x + length vs \<le> n) (Mapping.keys m) = 
   Set.filter (\<lambda> x. x + length vs \<le> n) (Mapping.keys (store_bytes m n vs))"
  by (induct vs arbitrary: m n)
    (simp, smt (verit, best) Collect_cong Set.filter_def keys_is_none_rep store_bytes_domain_1)

lemma store_bytes_keys_2:
  "Set.filter (\<lambda> x. n + length vs \<le> x) (Mapping.keys m) = 
   Set.filter (\<lambda> x. n + length vs \<le> x) (Mapping.keys (store_bytes m n vs))"
  by (induct vs arbitrary: m n)
    (simp, smt (verit, best) Collect_cong Set.filter_def keys_is_none_rep store_bytes_domain_2)

lemma store_cap_domain_1:
  assumes "x + n \<le> p"
  shows "Mapping.lookup (store_cap m p c n) x = Mapping.lookup m x"
  using assms 
  by (induct n arbitrary: x m p) simp_all

lemma store_cap_domain_2:
  assumes "p + n \<le> x"
  shows "Mapping.lookup (store_cap m p c n) x = Mapping.lookup m x"
  using assms 
  by (induct n arbitrary: x m p) simp_all

lemma store_cap_keys_1:
  "Set.filter (\<lambda> x. x + n \<le> p) (Mapping.keys m) = 
   Set.filter (\<lambda> x. x + n \<le> p) (Mapping.keys (store_cap m p c n))"
  by (induct n arbitrary: m p) 
    (force, smt (verit, best) Collect_cong Set.filter_def keys_is_none_rep store_cap_domain_1)

lemma store_cap_keys_2:
  "Set.filter (\<lambda> x. p + n \<le> x) (Mapping.keys m) = 
   Set.filter (\<lambda> x. p + n \<le> x) (Mapping.keys (store_cap m p c n))"
  by (induct n arbitrary: m p)
    (force, smt (verit, best) Collect_cong Set.filter_def keys_is_none_rep store_cap_domain_2)

lemma store_tags_domain_1:
  assumes "x < n"
  shows "Mapping.lookup (store_tag m n b) x = Mapping.lookup m x"
  using assms by auto

lemma store_tags_domain_2:
  assumes "n < x"
  shows "Mapping.lookup (store_tag m n b) x = Mapping.lookup m x"
  using assms by auto

lemma store_tags_keys_1:
  "Set.filter (\<lambda> x. x < n) (Mapping.keys m) = 
   Set.filter (\<lambda> x. x < n) (Mapping.keys (store_tag m n b))"
  by fastforce

lemma store_tags_keys_2:
  "Set.filter (\<lambda> x. n < x) (Mapping.keys m) = 
   Set.filter (\<lambda> x. n < x) (Mapping.keys (store_tag m n b))"
  by fastforce

lemma cap_offset_aligned: 
  "(cap_offset n) mod |Cap|\<^sub>\<tau> = 0"
  unfolding sizeof_def
  by force
  
lemma store_tags_offset: 
  assumes "Set.filter (\<lambda> x. x mod |Cap|\<^sub>\<tau> \<noteq> 0) (Mapping.keys m) = {}"
  shows "Set.filter (\<lambda> x. x mod |Cap|\<^sub>\<tau> \<noteq> 0) (Mapping.keys (store_tag m (cap_offset n) b)) = {}"
  using assms 
  unfolding sizeof_def 
  by force

lemma store_tval_disjoint_bounds:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
  shows "bounds obj = bounds obj'"
  using assms
  unfolding store_tval_def 
  by (clarsimp split: ccval.split_asm)

lemma store_tval_disjoint_1_content:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' < off"
  shows "Mapping.lookup (content obj) off' = Mapping.lookup (content obj') off'"
  using assms
  by (clarsimp simp add: store_tval_def split: ccval.split_asm)
    (presburger add: stored_bytes_prev stored_cap_prev)+

lemma store_tval_disjoint_1_content_bytes:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' + n \<le> off"
  shows "retrieve_bytes (content obj) off' n  = retrieve_bytes (content obj') off' n"
  using assms

proof (induct n arbitrary: obj obj' off val off')
  case 0
  then show ?case 
    by force
next
  case (Suc n)
  then show ?case 
    by (metis (no_types, lifting) Suc_eq_plus1 add.assoc le_eq_less_or_eq less_add_same_cancel1 order_le_less_trans plus_1_eq_Suc retrieve_bytes.simps(2) store_tval_disjoint_1_content zero_less_Suc)
qed

lemma store_tval_disjoint_1_content_contiguous_bytes:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' + n \<le> off"
  shows "is_contiguous_bytes (content obj) off' n  = is_contiguous_bytes (content obj') off' n"
  using assms
proof (induct n arbitrary: obj obj' off val off')
  case 0
  then show ?case
    by force
next
  case (Suc n)
  then show ?case
    by (smt (verit, best) add.assoc add.commute domIff is_contiguous_bytes.simps(2) keys_dom_lookup le_eq_less_or_eq less_add_same_cancel1 order_le_less_trans plus_1_eq_Suc store_tval_disjoint_1_content zero_less_Suc)
qed

lemma store_tval_disjoint_1_content_contiguous_caps:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' + n \<le> off"
  shows "is_contiguous_cap (content obj) cap off' n  = is_contiguous_cap (content obj') cap off' n"
  using assms
proof (induct n arbitrary: obj obj' off val off')
  case 0
  then show ?case 
    by force
next
  case (Suc n)
  then show ?case 
    by (smt (verit, best) add.assoc add.commute domIff is_contiguous_cap.simps(2) keys_dom_lookup le_eq_less_or_eq less_add_same_cancel1 order_le_less_trans plus_1_eq_Suc store_tval_disjoint_1_content zero_less_Suc)
qed

lemma store_tval_disjoint_1_tags:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' + |Cap|\<^sub>\<tau> \<le> off"
  shows "Mapping.lookup (tags obj) off' = Mapping.lookup (tags obj') off'"
  using assms
  by (clarsimp simp add: store_tval_def split: ccval.split_asm)
    (metis Mapping.lookup_update_neq add.commute add_cancel_right_right bot_nat_0.extremum_strict diff_diff_cancel le_add1 le_add_diff_inverse less_diff_conv2 mod_less_divisor mod_less_eq_dividend sizeof_nonzero)+



lemma store_tval_disjoint_2_content:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
  shows "Mapping.lookup (content obj) off' = Mapping.lookup (content obj') off'" 
  using assms
proof (clarsimp simp add: store_tval_def split: ccval.split_asm) 
  show "\<And>x. \<lbrakk>off + |Cap|\<^sub>\<tau> \<le> off'; val = Cap_v x; obj' = obj\<lparr>content := store_cap (content obj) off x |Cap|\<^sub>\<tau>, tags := store_tag (tags obj) (cap_offset off) (tag x)\<rparr>\<rbrakk>
          \<Longrightarrow> Mapping.lookup (content obj) off' = Mapping.lookup (store_cap (content obj) off x |Cap|\<^sub>\<tau>) off'"
    by (presburger add: store_cap_domain_2)
qed (force simp add: sizeof_def | metis assms(3) store_bytes_domain_2 flatten_types_length memval_size_types)+

lemma store_tval_disjoint_2_content_bytes:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
  shows "retrieve_bytes (content obj) off' n = retrieve_bytes (content obj') off' n"
  using assms
proof (induct n arbitrary: obj obj' off off' val)
  case 0
  then show ?case 
    by force
next
  case (Suc n)
  then show ?case 
    by (metis less_Suc_eq_le less_or_eq_imp_le retrieve_bytes.simps(2) store_tval_disjoint_2_content)
qed

lemma store_tval_disjoint_2_content_contiguous_bytes:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
  shows "is_contiguous_bytes (content obj) off' n  = is_contiguous_bytes (content obj') off' n"
  using assms
proof (induct n arbitrary: obj obj' off val off')
  case 0
  then show ?case 
    by force
next
  case (Suc n)
  then show ?case 
    by (smt (verit, best) domIff is_contiguous_bytes.simps(2) keys_dom_lookup le_eq_less_or_eq lessI order_le_less_trans store_tval_disjoint_2_content)
qed

lemma store_tval_disjoint_2_content_contiguous_caps:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
  shows "is_contiguous_cap (content obj) cap off' n  = is_contiguous_cap (content obj') cap off' n"
  using assms
proof (induct n arbitrary: obj obj' off val off')
  case 0
  then show ?case 
    by force
next
  case (Suc n)
  then show ?case 
    by (smt (verit, best) domIff is_contiguous_cap.simps(2) keys_dom_lookup le_eq_less_or_eq lessI order_le_less_trans store_tval_disjoint_2_content)
qed

lemma store_tval_disjoint_2_tags:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
  shows "Mapping.lookup (tags obj) off' = Mapping.lookup (tags obj') off'"
  using assms
  by (clarsimp simp add: store_tval_def split: ccval.split_asm) 
    (force simp add: assms(3) sizeof_def)+

lemma zero_imp_bytes:
  "is_contiguous_zeros obj off n  \<Longrightarrow> \<not> is_contiguous_bytes obj off n \<Longrightarrow> False"
proof (simp add: is_contiguous_zeros_code, induct n arbitrary: obj off)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case
    using keys_dom_lookup memval_memcap_not_byte 
    by fastforce
qed

lemma retrieve_stored_tval_disjoint_1:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off' + |t|\<^sub>\<tau> \<le> off"
  shows "retrieve_tval obj off' t b = retrieve_tval obj' off' t b"
  using assms 
  apply (clarsimp simp add: retrieve_tval_def)
  apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
  subgoal
    by (simp split: cctype.split, safe; (force simp add: numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8 sizeof_def)+)
  subgoal
    apply (simp split: cctype.split, safe, (force simp add: sizeof_def numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8)+)
    apply (metis is_contiguous_bytes.simps(2) less_imp_Suc_add sizeof_nonzero)
    done
  subgoal
    apply (intro strip conjI)
     apply (simp split: cctype.split, safe; (force simp add: numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8 sizeof_def)+)
    apply (simp split: cctype.split, metis is_contiguous_bytes.simps(1) is_contiguous_bytes.simps(2) old.nat.exhaust)
    done
  subgoal
    using zero_imp_bytes  by presburger
  subgoal 
    by (smt (z3) store_tval_disjoint_1_content_bytes zero_imp_bytes)
  subgoal 
    by (simp add: is_contiguous_zeros_def, metis (no_types, lifting) order_less_le_trans store_tval_disjoint_1_content)
  subgoal 
    unfolding is_contiguous_zeros_def 
    by (smt (verit) cctype.exhaust cctype.simps(73) cctype.simps(74) cctype.simps(75) cctype.simps(76) cctype.simps(77) cctype.simps(78) cctype.simps(79) cctype.simps(80) get_cap_def keys_is_none_rep less_add_same_cancel1 order_less_le_trans sizeof_nonzero store_tval_disjoint_1_content store_tval_disjoint_1_content_bytes store_tval_disjoint_1_content_contiguous_bytes store_tval_disjoint_1_content_contiguous_caps store_tval_disjoint_1_tags)
  apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
     apply (smt (z3) store_tval_disjoint_1_content_bytes zero_imp_bytes)
    apply (smt (verit, best) store_tval_disjoint_1_content_bytes zero_imp_bytes)
   apply (simp add: is_contiguous_zeros_def, smt (z3) le_add_diff_inverse2 store_tval_disjoint_1_content trans_less_add2)
  apply (rule impI, rule conjI, rule impI)
   apply (simp add: is_contiguous_zeros_def)
   apply (smt (z3) le_add_diff_inverse2 store_tval_disjoint_1_content trans_less_add2)
    subgoal 
      apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
          apply (metis is_contiguous_bytes.simps(2) less_nat_zero_code old.nat.exhaust sizeof_nonzero)
      using store_tval_disjoint_1_content_contiguous_bytes 
         apply blast
        apply (metis is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero)
       apply (rule impI, rule conjI, rule impI, rule conjI, rule impI)
      using store_tval_disjoint_1_content_contiguous_bytes 
         apply blast
        apply (simp add: Let_def split: cctype.split; clarsimp, smt (verit, best) add.commute add_diff_cancel_right' add_le_cancel_left bot_nat_0.not_eq_extremum get_cap_def le_add_diff_inverse2 le_eq_less_or_eq order_less_le_trans sizeof_nonzero store_tval_disjoint_1_content store_tval_disjoint_1_content_contiguous_caps store_tval_disjoint_1_tags zero_less_diff)
       apply (metis add.right_neutral add_less_cancel_left domIff keys_dom_lookup le_add_diff_inverse2 sizeof_nonzero store_tval_disjoint_1_content trans_less_add2)
      apply (smt (z3) keys_is_none_rep less_add_same_cancel1 order_less_le_trans sizeof_nonzero store_tval_disjoint_1_content store_tval_disjoint_1_content_bytes store_tval_disjoint_1_content_contiguous_bytes)
      done
  done

lemma retrieve_stored_tval_disjoint_2:
  assumes "store_tval obj off val = obj'"
    and "val \<noteq> Undef"
    and "off + |memval_type val|\<^sub>\<tau> \<le> off'"
    and "t = Cap \<Longrightarrow> off' mod |Cap|\<^sub>\<tau> = 0"
  shows "retrieve_tval obj off' t b = retrieve_tval obj' off' t b"
  using assms(1) assms(2) assms(3)
  apply (clarsimp simp add: retrieve_tval_def)
  apply (rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
  subgoal
    by (simp split: cctype.split, safe; (force simp add: numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8 sizeof_def)+)
  subgoal
    apply (simp split: cctype.split, safe, (force simp add: sizeof_def numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8)+)
    apply (metis is_contiguous_bytes.simps(2) less_imp_Suc_add sizeof_nonzero)
    done
  subgoal
    apply (rule impI, rule conjI, rule impI)
     apply (simp split: cctype.split, safe; (force simp add: numeral_2_eq_2 numeral_4_eq_4 numeral_8_eq_8 sizeof_def)+)
    apply (simp split: cctype.split, metis is_contiguous_bytes.simps(1) is_contiguous_bytes.simps(2) old.nat.exhaust)
    done
  subgoal
    using zero_imp_bytes by presburger
  subgoal 
    by (smt (z3) memval_type.elims store_tval_disjoint_2_content_bytes zero_imp_bytes)
  subgoal
    by (smt (z3) is_contiguous_zeros_def le_trans memval_type.elims store_tval_disjoint_2_content)
  subgoal 
    unfolding is_contiguous_zeros_def
    by (smt (verit) get_cap_def keys_is_none_rep le_trans memval_type.elims store_tval_disjoint_2_content store_tval_disjoint_2_content_bytes store_tval_disjoint_2_content_contiguous_bytes store_tval_disjoint_2_content_contiguous_caps store_tval_disjoint_2_tags)
  subgoal
    apply (rule impI, rule conjI, rule impI, rule conjI, rule impI, rule conjI, rule impI)
       apply (metis (no_types, opaque_lifting) is_contiguous_bytes.simps(2) less_numeral_extra(3) not0_implies_Suc sizeof_nonzero zero_imp_bytes)
      apply (smt (z3) assms(3) store_tval_disjoint_2_content_bytes zero_imp_bytes)
     apply (simp add: is_contiguous_zeros_def, metis assms(3) order_trans store_tval_disjoint_2_content)
    unfolding is_contiguous_zeros_def 
    by (smt (verit) assms(3) assms(4) cctype.exhaust cctype.simps(73) cctype.simps(74) cctype.simps(75) cctype.simps(76) cctype.simps(77) cctype.simps(78) cctype.simps(79) cctype.simps(80) get_cap_def keys_is_none_rep mod_0_imp_dvd mod_greater_zero_iff_not_dvd store_tval_disjoint_2_content store_tval_disjoint_2_content_bytes store_tval_disjoint_2_content_contiguous_bytes)
  done


lemma type_uniq: 
  assumes "\<exists> x n. ret = Cap_v_frag x n"
  shows "ret \<noteq> Uint8_v v1" "ret \<noteq> Sint8_v v2" "ret \<noteq> Uint16_v v3" "ret \<noteq> Sint16_v v4"
    "ret \<noteq> Uint32_v v5" "ret \<noteq> Sint32_v v6" "ret \<noteq> Uint64_v v7" "ret \<noteq> Sint64_v v8" 
    "ret \<noteq> Cap_v v9" 
  using assms 
  by blast+

section \<open>Memory Actions / Operations\<close>

definition alloc :: "heap \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> (heap \<times> cap) result"
  where
  "alloc h c s \<equiv> 
     let cap = \<lparr> block_id = (next_block h),
                 offset = 0,
                 base = 0,
                 len = s,
                 perm_load = True,
                 perm_cap_load = c,
                 perm_store = True,
                 perm_cap_store = c,
                 perm_cap_store_local = c,
                 perm_global = False,
                 tag = True
               \<rparr> in
     let h' = h \<lparr> next_block := (next_block h) + 1,
                  heap_map := Mapping.update 
                                (next_block h) 
                                (Map \<lparr> bounds = (0, s), 
                                       content = Mapping.empty, 
                                       tags = Mapping.empty 
                                     \<rparr>
                                 ) (heap_map h)
                \<rparr> in
     Success (h', cap)"

definition free :: "heap \<Rightarrow> cap \<Rightarrow> (heap \<times> cap) result"
  where
  "free h c \<equiv>
     if c = NULL then Success (h, c) else
     if tag c = False then Error (C2Err (TagViolation)) else
     if perm_global c = True then Error (LogicErr (Unhandled 0)) else
     let obj = Mapping.lookup (heap_map h) (block_id c) in
     (case obj of None      \<Rightarrow> Error (LogicErr (MissingResource))
               | Some cobj \<Rightarrow>
       (case cobj of Freed \<Rightarrow> Error (LogicErr (UseAfterFree))
                  | Map m \<Rightarrow>
         if offset c \<noteq> 0 then Error (LogicErr (Unhandled 0)) 
         else if offset c > base c + len c then Error (LogicErr (Unhandled 0)) else
       let cap_bound = (base c, base c + len c) in
       if cap_bound \<noteq> bounds m then Error (LogicErr (Unhandled 0)) else
       let h' = h \<lparr> heap_map := Mapping.update (block_id c) Freed (heap_map h) \<rparr> in 
       let cap = c \<lparr> tag := False \<rparr> in
       Success (h', cap)))"

text \<open>How load works:
      The hardware would perform a CL[C] operation on the given capability first.
      An invalid capability for load would be caught by the hardware.
      Once all the hardware checks are performed, we then proceed to the logical checks.\<close>
definition load :: "heap \<Rightarrow> cap \<Rightarrow> cctype \<Rightarrow> block ccval result"
  where
  "load h c t \<equiv> 
     if tag c = False then
       Error (C2Err TagViolation)
     else if perm_load c = False then 
       Error (C2Err PermitLoadViolation)
     else if offset c + |t|\<^sub>\<tau> > base c + len c then
       Error (C2Err LengthViolation)
     else if offset c < base c then
       Error (C2Err LengthViolation)
     else if offset c mod |t|\<^sub>\<tau> \<noteq> 0 then
       Error (C2Err BadAddressViolation)
     else
       let obj = Mapping.lookup (heap_map h) (block_id c) in
      (case obj of None      \<Rightarrow> Error (LogicErr (MissingResource))
                 | Some cobj \<Rightarrow>
        (case cobj of Freed \<Rightarrow> Error (LogicErr (UseAfterFree))
                    | Map m \<Rightarrow> if offset c < fst (bounds m) \<or> offset c + |t|\<^sub>\<tau> > snd (bounds m) then 
                               Error (LogicErr BufferOverrun) else
                               Success (retrieve_tval m (nat (offset c)) t (perm_cap_load c))))"

definition store :: "heap \<Rightarrow> cap \<Rightarrow> block ccval \<Rightarrow> heap result"
  where
  "store h c v \<equiv> 
     if tag c = False then 
       Error (C2Err TagViolation)
     else if perm_store c = False then 
       Error (C2Err PermitStoreViolation)
     else if (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store c \<and> tag cv | _ \<Rightarrow> False) then 
       Error (C2Err PermitStoreCapViolation)
     else if (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store_local c \<and> tag cv \<and> \<not> perm_global cv | _ \<Rightarrow> False) then
       Error (C2Err PermitStoreLocalCapViolation)
     else if offset c + |memval_type v|\<^sub>\<tau> > base c + len c then 
       Error (C2Err LengthViolation)
     else if offset c < base c then 
       Error (C2Err LengthViolation)
     else if offset c mod |memval_type v|\<^sub>\<tau> \<noteq> 0 then 
       Error (C2Err BadAddressViolation)
     else if v = Undef then
       Error (LogicErr (Unhandled 0))
     else
       let obj = Mapping.lookup (heap_map h) (block_id c) in
      (case obj of None      \<Rightarrow> Error (LogicErr (MissingResource))
                 | Some cobj \<Rightarrow>
        (case cobj of Freed \<Rightarrow> Error (LogicErr (UseAfterFree))
                    | Map m \<Rightarrow> if offset c < fst (bounds m) \<or> offset c + |memval_type v|\<^sub>\<tau> > snd (bounds m) then 
                               Error (LogicErr BufferOverrun) else
                               Success (h \<lparr> heap_map := Mapping.update 
                                                         (block_id c) 
                                                         (Map (store_tval m (nat (offset c)) v)) 
                                                         (heap_map h) \<rparr>)))"

subsection \<open>Properties of the operations\<close>
text \<open>Here we provide all the properties the operations satisfy. In general, you may find the following
      forms of proofs:
       \begin{itemize}
           \item If we have valid input, the operation will succeed
           \item If we have invalid inputs, the operations will return the appropriate error
           \item If the operation succeeds, we have a valid input
       \end{itemize}
       good variable laws are also proven at the next subsubsection.\<close>

subsubsection \<open>Correctness Properties\<close>

lemma alloc_always_success:
  "\<exists>! res. alloc h c s = Success res"
  by (simp add: alloc_def)

schematic_goal alloc_updated_heap_and_cap:
  "alloc h c s = Success (?h', ?cap)"
  by (fastforce simp add: alloc_def)

lemma alloc_never_fails:
  "alloc h c s = Error e \<Longrightarrow> False"
  by (simp add: alloc_def)

text \<open>In practice, malloc may actually return NULL when allocation fails. However, this still complies
    with The C Standard.\<close>
lemma alloc_no_null_ret:
  assumes "alloc h c s = Success (h', cap)"
  shows "cap \<noteq> NULL"
proof -
  have "perm_load cap"
    using assms alloc_def
    by force
  moreover have "\<not> perm_load NULL"
    unfolding null_capability_def zero_capability_ext_def zero_mem_capability_ext_def
    by force
  ultimately show ?thesis 
    by blast
qed

lemma alloc_correct:
  assumes "alloc h c s = Success (h', cap)"
  shows "next_block h' = next_block h + 1"
    and "Mapping.lookup (heap_map h') (next_block h) 
         = Some (Map \<lparr> bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>)"
  using assms alloc_def
  by auto

text \<open>Section 7.20.3.2 of The C Standard states free(NULL) results in no action occurring~\cite{cstandard_2003}.\<close>
lemma free_null:
  "free h NULL = Success (h, NULL)"
  by (simp add: free_def)

lemma free_false_tag:
  assumes "c \<noteq> NULL"
    and "tag c = False"
  shows "free h c = Error (C2Err (TagViolation))"
  by (presburger add: assms free_def)

lemma free_global_cap:
  assumes "c \<noteq> NULL"
    and "tag c = True"
    and "perm_global c = True"
  shows "free h c = Error (LogicErr (Unhandled 0))"
  by (presburger add: assms free_def)

lemma free_nonexistant_obj:
  assumes "c \<noteq> NULL"
    and "tag c = True"
    and "perm_global c = False"
    and "Mapping.lookup (heap_map h) (block_id c) = None"
  shows "free h c = Error (LogicErr (MissingResource))"
  using assms free_def
  by auto

text \<open>This case may arise if there are copies of the same capability, where only one was freed.
      It is worth noting that due to this, temporal safety is not guaranteed by the CHERI hardware.\<close>
lemma free_double_free:
  assumes "c \<noteq> NULL"
    and "tag c = True"
    and "perm_global c = False"
    and "Mapping.lookup (heap_map h) (block_id c) = Some Freed"
  shows "free h c = Error (LogicErr (UseAfterFree))"
  using free_def assms
  by force

text \<open>An incorrect offset implies the actual ptr value is not that returned by alloc.
    Section 7.20.3.2 of The C Standard states this leads to undefined behaviour~\cite{cstandard_2003}.
    Clang, in practice, however, terminates the C program with an invalid pointer error. \<close>
lemma free_incorrect_cap_offset:
  assumes "c \<noteq> NULL"
    and "tag c = True"
    and "perm_global c = False"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<noteq> 0"
  shows "free h c = Error (LogicErr (Unhandled 0))"
  using free_def assms
  by force

lemma free_incorrect_bounds:
  assumes "c \<noteq> NULL"
    and "tag c = True"
    and "perm_global c = False"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c = 0"
    and "bounds m \<noteq> (base c, base c + len c)"
  shows "free h c = Error (LogicErr (Unhandled 0))"
  unfolding free_def
  using assms 
  by force

lemma free_non_null_correct:
  assumes "c \<noteq> NULL"
    and valid_tag: "tag c = True"
    and "perm_global c = False"
    and map_has_contents: "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and offset_correct: "offset c = 0"
    and bounds_correct: "bounds m = (base c, base c + len c)"
  shows "free h c = Success (h \<lparr> heap_map := Mapping.update (block_id c) Freed (heap_map h) \<rparr>, 
                             c \<lparr> tag := False \<rparr>)"
  unfolding free_def 
  using assms
  by simp

lemma free_cond:
  assumes "free h c = Success (h', cap)"
  shows "c \<noteq> NULL \<Longrightarrow> tag c = True"
    and "c \<noteq> NULL \<Longrightarrow> perm_global c = False"
    and "c \<noteq> NULL \<Longrightarrow> offset c = 0"
    and "c \<noteq> NULL \<Longrightarrow> \<exists> m. Mapping.lookup (heap_map h) (block_id c) = Some (Map m) \<and> 
              bounds m = (base c, base c + len c)"
    and "c \<noteq> NULL \<Longrightarrow> Mapping.lookup (heap_map h') (block_id c) = Some Freed"
    and "c \<noteq> NULL \<Longrightarrow> cap = c \<lparr> tag := False \<rparr>"
    and "c = NULL \<Longrightarrow> (h, c) = (h', cap)"
proof -
  assume "c \<noteq> NULL"
  thus "tag c = True"
    using assms unfolding free_def
    by (meson result.simps(4))
next
  assume "c \<noteq> NULL"
  thus "perm_global c = False"
    using assms unfolding free_def
    by (meson result.simps(4))
next
  assume "c \<noteq> NULL"
  thus "offset c = 0"
    using assms unfolding free_def
    by (smt (verit, ccfv_SIG) not_None_eq option.simps(4) option.simps(5) result.distinct(1) t.exhaust t.simps(4) t.simps(5))
next
  assume "c \<noteq> NULL"
  thus "\<exists> m. Mapping.lookup (heap_map h) (block_id c) = Some (Map m) \<and> 
             bounds m = (base c, base c + len c)"
    using assms unfolding free_def
    by (metis assms free_double_free free_incorrect_bounds free_incorrect_cap_offset free_nonexistant_obj not_Some_eq result.distinct(1) t.exhaust)
next 
  assume "c \<noteq> NULL"
  hence "h' = h \<lparr> heap_map := Mapping.update (block_id c) Freed (heap_map h) \<rparr>"
    using assms unfolding free_def
    by (smt (verit, ccfv_SIG) free_nonexistant_obj not_Some_eq option.simps(4) option.simps(5) prod.inject result.distinct(1) result.exhaust result.inject(1) t.exhaust t.simps(4) t.simps(5))
  thus "Mapping.lookup (heap_map h') (block_id c) = Some Freed"
    by fastforce
next
  assume "c \<noteq> NULL"
  thus "cap = c \<lparr> tag := False \<rparr>"
    using assms unfolding free_def
    by (smt (verit, ccfv_SIG) not_Some_eq option.simps(4) option.simps(5) prod.inject result.distinct(1) result.inject(1) t.exhaust t.simps(4) t.simps(5))
next
  assume "c = NULL"
  thus "(h, c) = (h', cap)"
    using free_null assms 
    by force
qed

lemmas free_cond_non_null = free_cond(1) free_cond(2) free_cond(3) free_cond(4) free_cond(5) free_cond(6)

lemma double_free:
  assumes "free h c = Success (h', cap)"
    and "cap \<noteq> NULL"
  shows "free h' cap = Error (C2Err TagViolation)"
proof -
  have "cap = c \<lparr> tag := False \<rparr> \<Longrightarrow> tag cap = False"
    by fastforce
  thus ?thesis
    using assms free_cond(6)[where ?h=h and ?c=c and ?h'=h' and ?cap=cap] free_false_tag[where ?c=cap and ?h=h'] free_cond(7)[where ?h=h and ?c=c and ?h'=h' and ?cap=cap]
    by blast
qed

lemma free_next_block:
  assumes "free h cap = Success (h', cap')"
  shows "next_block h = next_block h'"
  proof -
  consider (null) "cap = NULL" | (non_null) "cap \<noteq> NULL" by blast
  then show ?thesis
  proof (cases)
    case null
    then show ?thesis 
      using free_null assms null
      by simp
  next
    case non_null
    then show ?thesis 
      using assms free_cond_non_null[OF assms non_null]
      unfolding free_def
      by (auto split: option.split_asm t.split_asm)
  qed
qed

lemma load_null_error:
  "load h NULL t = Error (C2Err TagViolation)" 
  unfolding load_def
  by simp

lemma load_false_tag:
  assumes "tag c = False"
  shows "load h c t = Error (C2Err TagViolation)"
  unfolding load_def
  using assms
  by presburger

lemma load_false_perm_load:
  assumes "tag c = True"
    and "perm_load c = False"
  shows "load h c t = Error (C2Err PermitLoadViolation)"
  unfolding load_def
  using assms 
  by presburger

lemma load_bound_over:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> > base c + len c"
  shows "load h c t = Error (C2Err LengthViolation)"
  unfolding load_def
  using assms 
  by presburger

lemma load_bound_under:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c < base c"
  shows "load h c t = Error (C2Err LengthViolation)"
  unfolding load_def
  using assms 
  by presburger

lemma load_misaligned:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> \<noteq> 0"
  shows "load h c t = Error (C2Err BadAddressViolation)"
  unfolding load_def
  using assms 
  by force

lemma load_nonexistant_obj:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = None"
  shows "load h c t = Error (LogicErr MissingResource)"
  unfolding load_def
  using assms
  by auto

lemma load_load_after_free:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some Freed"
  shows "load h c t = Error (LogicErr UseAfterFree)"
  unfolding load_def
  using assms
  by fastforce

lemma load_cap_on_heap_bounds_fail_1:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Cap"
    and "\<not> is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "offset c < fst (bounds m)"
  shows "load h c t = Error (LogicErr BufferOverrun)"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_cap_on_heap_bounds_fail_2:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Cap"
    and "\<not> is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "offset c + |t|\<^sub>\<tau> > snd (bounds m)"
  shows "load h c t = Error (LogicErr BufferOverrun)"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_cap_on_membytes_fail:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Cap"
    and "\<not> is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
  shows "load h c t = Success Undef"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_null_cap_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Cap"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau>"
  shows "load h c t = Success (Cap_v NULL)"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_u8_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Uint8"
  shows "load h c t = Success (Uint8_v (decode_u8_list (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_s8_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Sint8"
  shows "load h c t = Success (Sint8_v (decode_s8_list (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_u16_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Uint16"
  shows "load h c t = Success (Uint16_v (cat_u16 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_s16_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Sint16"
  shows "load h c t = Success (Sint16_v (cat_s16 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_u32_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Uint32"
  shows "load h c t = Success (Uint32_v (cat_u32 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_s32_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Sint32"
  shows "load h c t = Success (Sint32_v (cat_s32 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_u64_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Uint64"
  shows "load h c t = Success (Uint64_v (cat_u64 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_s64_on_membytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Sint64"
  shows "load h c t = Success (Sint64_v (cat_s64 (retrieve_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>)))"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_not_cap_in_mem:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "\<not> is_cap (content m) (nat (offset c))"
  shows "load h c t = Success Undef"
  unfolding load_def retrieve_tval_def 
  using assms
  by fastforce

lemma load_not_contiguous_cap_in_mem:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "is_cap (content m) (nat (offset c))"
    and "mc = get_cap (content m) (nat (offset c))"
    and "\<not> is_contiguous_cap (content m) mc (nat (offset c)) |t|\<^sub>\<tau>"
    and "t \<noteq> Uint8"
    and "t \<noteq> Sint8"
  shows "load h c t = Success Undef"
  unfolding load_def retrieve_tval_def Let_def
  using assms
  by (clarsimp split: cctype.split)

lemma load_cap_frag_u8:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "is_cap (content m) (nat (offset c))"
    and "mc = get_cap (content m) (nat (offset c))"
    and "t = Uint8"
    and "tagval = the (Mapping.lookup (tags m) (cap_offset (nat (offset c))))"
    and "tg = (case perm_cap_load c of False \<Rightarrow> False | True \<Rightarrow> tagval)"
    and "nth_frag = of_nth (the (Mapping.lookup (content m) (nat (offset c))))"
  shows "load h c t = Success (Cap_v_frag (mem_capability.extend mc \<lparr> tag = False \<rparr>) nth_frag)"
  unfolding load_def retrieve_tval_def Let_def
  using assms
  by (clarsimp simp add: sizeof_def split: cctype.split)


lemma load_cap_frag_s8:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "is_cap (content m) (nat (offset c))"
    and "mc = get_cap (content m) (nat (offset c))"
    and "\<not> is_contiguous_cap (content m) mc (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Sint8"
    and "tagval = the (Mapping.lookup (tags m) (cap_offset (nat (offset c))))"
    and "tg = (case perm_cap_load c of False \<Rightarrow> False | True \<Rightarrow> tagval)"
    and "nth_frag = of_nth (the (Mapping.lookup (content m) (nat (offset c))))"
  shows "load h c t = Success (Cap_v_frag (mem_capability.extend mc \<lparr> tag = False \<rparr>) nth_frag)"
  unfolding load_def retrieve_tval_def Let_def
  using assms
  by (clarsimp simp add: sizeof_def split: cctype.split)

lemma load_bytes_on_capbytes_fail:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "is_cap (content m) (nat (offset c))"
    and "mc = get_cap (content m) (nat (offset c))"
    and "is_contiguous_cap (content m) mc (nat (offset c)) |t|\<^sub>\<tau>"
    and "t \<noteq> Cap"
    and "t \<noteq> Uint8"
    and "t \<noteq> Sint8"
  shows "load h c t = Success Undef"
  unfolding load_def retrieve_tval_def Let_def
  using assms 
  by (clarsimp split: cctype.split)

lemma load_cap_on_capbytes:
  assumes "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)"
    and "\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
    and "is_cap (content m) (nat (offset c))"
    and "mc = get_cap (content m) (nat (offset c))"
    and "is_contiguous_cap (content m) mc (nat (offset c)) |t|\<^sub>\<tau>"
    and "t = Cap"
    and "tagval = the (Mapping.lookup (tags m) (nat (offset c)))"
    and "tg = (case perm_cap_load c of False \<Rightarrow> False | True \<Rightarrow> tagval)"
  shows "load h c t = Success (Cap_v (mem_capability.extend mc \<lparr> tag = tg \<rparr>))"
  unfolding load_def retrieve_tval_def 
  using assms 
  by (clarsimp split: cctype.split) 
    (smt (verit) assms(5) nat_int nat_less_le nat_mod_distrib of_nat_0_le_iff semiring_1_class.of_nat_0)

lemma load_cond_hard_cap:
  assumes "load h c t = Success ret"
  shows "tag c = True"
    and "perm_load c = True"
    and "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |t|\<^sub>\<tau> = 0"
proof -
  show "tag c = True"
    using assms result.distinct(1) 
    unfolding load_def
    by metis
next
  show "perm_load c = True"
    using assms result.distinct(1) 
    unfolding load_def
    by metis
next
  show "offset c + |t|\<^sub>\<tau> \<le> base c + len c"
    using assms result.distinct(1) linorder_not_le
    unfolding load_def 
    by metis
next 
  show "offset c \<ge> base c"
    using assms result.distinct(1) linorder_not_le
    unfolding load_def 
    by metis
next
  show "offset c mod |t|\<^sub>\<tau> = 0"
    using assms result.distinct(1)
    unfolding load_def 
    by metis
qed

lemma load_cond_bytes:
  assumes "load h c t = Success ret"
    and "ret \<noteq> Undef"
    and "\<forall> x. ret \<noteq> Cap_v x"
    and "\<forall> x n . ret \<noteq> Cap_v_frag x n"
  shows "\<exists> m. Mapping.lookup (heap_map h) (block_id c) = Some (Map m)
            \<and> offset c \<ge> fst (bounds m) 
            \<and> offset c + |t|\<^sub>\<tau> \<le> snd (bounds m)
            \<and> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>"
proof (cases ret)
  case (Cap_v x9)
  thus ?thesis 
    using assms(3)
    by blast
next
  case (Cap_v_frag x101 x102)
  thus ?thesis
    using assms(4)
    by blast
next
  case Undef
  thus ?thesis
    using assms(2)
    by simp
qed (insert assms(1) load_cond_hard_cap[where ?h=h and ?c=c and ?t=t and ?ret=ret], clarsimp, unfold load_def retrieve_tval_def, clarsimp split: option.split_asm t.split_asm, smt (z3) assms(2) assms(3) assms(4) cctype.exhaust cctype.simps(73) cctype.simps(74) cctype.simps(75) cctype.simps(76) cctype.simps(77) cctype.simps(78) cctype.simps(79) cctype.simps(80) cctype.simps(81) result.distinct(1) result.inject(1))+
(* WARNING: the above takes quite some time to prove the remaining cases *)

lemma load_cond_cap:
  assumes "load h c t = Success ret"
    and "\<exists> x. ret = Cap_v x"
  shows "\<exists> m mc tagval tg. 
              Mapping.lookup (heap_map h) (block_id c) = Some (Map m) \<and>
              offset c \<ge> fst (bounds m) \<and>
              offset c + |t|\<^sub>\<tau> \<le> snd (bounds m) \<and>
              (is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau> \<longrightarrow> 
               is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau> \<and>
               ret = Cap_v NULL) \<and>
              (\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>  \<longrightarrow>
               is_cap (content m) (nat (offset c)) \<and>
               mc = get_cap (content m) (nat (offset c)) \<and>
               is_contiguous_cap (content m) mc (nat (offset c)) |t|\<^sub>\<tau> \<and>
               t = Cap \<and>
               tagval = the (Mapping.lookup (tags m) (nat (offset c))) \<and> 
               tg = (case perm_cap_load c of False \<Rightarrow> False | True \<Rightarrow> tagval))"
  using assms(2)
proof (cases ret)
  case (Cap_v ca)
  show ?thesis
    using assms load_cond_hard_cap[where ?h=h and ?c=c and ?t=t and ?ret=ret]
    by (clarsimp, simp only: load_def retrieve_tval_def Let_def, clarsimp split: option.split_asm, clarsimp split: t.split_asm, rename_tac x nth map, subgoal_tac "int (fst (bounds map)) \<le> int |t|\<^sub>\<tau> * nth \<and> int |t|\<^sub>\<tau> * nth + int |t|\<^sub>\<tau> \<le> int (snd (bounds map))", clarsimp split: cctype.split_asm, safe; force?)
      (metis ccval.distinct(105) ccval.distinct(107) ccval.inject(9) is_cap.elims(2) linorder_not_le result.distinct(1))+
qed blast+

lemma load_cond_cap_frag:
  assumes "load h c t = Success ret"
    and "\<exists> x n. ret = Cap_v_frag x n"
  shows "\<exists> m mc tagval tg nth_frag. 
              Mapping.lookup (heap_map h) (block_id c) = Some (Map m) \<and>
              offset c \<ge> fst (bounds m) \<and>
              offset c + |t|\<^sub>\<tau> \<le> snd (bounds m) \<and>
              (is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau> \<longrightarrow> 
               is_contiguous_zeros (content m) (nat (offset c)) |t|\<^sub>\<tau> \<and>
               ret = Cap_v NULL) \<and>
              (\<not> is_contiguous_bytes (content m) (nat (offset c)) |t|\<^sub>\<tau>  \<longrightarrow>
               is_cap (content m) (nat (offset c)) \<and>
               mc = get_cap (content m) (nat (offset c)) \<and>
               (t = Uint8 \<or> t = Sint8) \<and>
               tagval = the (Mapping.lookup (tags m) (nat (offset c))) \<and> 
               tg = (case perm_cap_load c of False \<Rightarrow> False | True \<Rightarrow> tagval) \<and>
               nth_frag = of_nth (the (Mapping.lookup (content m) (nat (offset c)))))"
  using assms(2)
proof (cases ret)
  case (Cap_v_frag x101 x102)
  show ?thesis 
    using assms load_cond_hard_cap[where ?h=h and ?c=c and ?t=t and ?ret=ret]
    by (clarsimp, simp only: load_def retrieve_tval_def Let_def, clarsimp split: option.split_asm, clarsimp split: t.split_asm if_split_asm cctype.split_asm)
qed (simp add: type_uniq assms(2))+ 


lemma store_null_error:
  "store h NULL v = Error (C2Err TagViolation)" 
  unfolding store_def
  by simp

lemma store_false_tag:
  assumes "tag c = False"
  shows "store h c v = Error (C2Err TagViolation)"
  unfolding store_def
  using assms
  by presburger

lemma store_false_perm_store:
  assumes "tag c = True"
    and "perm_store c = False"
  shows "store h c v = Error (C2Err PermitStoreViolation)"
  unfolding store_def
  using assms 
  by presburger

lemma store_cap_false_perm_cap_store:
  assumes "tag c = True"
    and "perm_store c = True"
    and "perm_cap_store c = False"
    and "\<exists> cv. v = Cap_v cv \<and> tag cv = True"
  shows "store h c v = Error (C2Err PermitStoreCapViolation)"
  unfolding store_def  
  using assms
  by force

lemma store_cap_false_perm_cap_store_local:
    assumes "tag c = True"
    and "perm_store c = True"
    and "perm_cap_store c = True"
    and "perm_cap_store_local c = False"
    and "\<exists> cv. v = Cap_v cv \<and> tag cv = True \<and> perm_global cv = False"
  shows "store h c v = Error (C2Err PermitStoreLocalCapViolation)"
  unfolding store_def
  using assms
  by force
  
lemma store_bound_over:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> > base c + len c"
  shows "store h c v = Error (C2Err LengthViolation)"
  unfolding store_def
  using assms 
  by (clarsimp split: ccval.split) 

lemma store_bound_under:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c < base c"
  shows "store h c v = Error (C2Err LengthViolation)"
  unfolding store_def
  using assms 
  by (clarsimp split: ccval.split)

lemma store_misaligned:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> \<noteq> 0"
  shows "store h c v = Error (C2Err BadAddressViolation)"
  unfolding store_def
  using assms
  by (clarsimp split: ccval.split)

lemma store_undef_val:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v = Undef"
  shows "store h c v = Error (LogicErr (Unhandled 0))"
  unfolding store_def 
  using assms
  by auto

lemma store_nonexistant_obj:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v \<noteq> Undef"
    and "Mapping.lookup (heap_map h) (block_id c) = None"
  shows "store h c v = Error (LogicErr MissingResource)"
  unfolding store_def
  using assms 
  by (clarsimp split: ccval.split)

lemma store_store_after_free:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v \<noteq> Undef"
    and "Mapping.lookup (heap_map h) (block_id c) = Some Freed"
  shows "store h c v = Error (LogicErr UseAfterFree)"
  unfolding store_def
  using assms
  by (clarsimp split: ccval.split)

lemma store_bound_violated_1:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v \<noteq> Undef"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c < fst (bounds m)"
  shows "store h c v = Error (LogicErr BufferOverrun)"
  unfolding store_def using assms
  by (clarsimp split: ccval.split)

lemma store_bound_violated_2:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v \<noteq> Undef"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c + |memval_type v|\<^sub>\<tau> > snd (bounds m)"
  shows "store h c v = Error (LogicErr BufferOverrun)"
  unfolding store_def using assms
  by (clarsimp split: ccval.split)

lemma store_success:
  assumes "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    and "v \<noteq> Undef"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "offset c \<ge> fst (bounds m)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> snd (bounds m)"
  shows "\<exists> ret. store h c v = Success ret \<and>
                next_block ret = next_block h \<and>
                heap_map ret = Mapping.update (block_id c) (Map (store_tval m (nat (offset c)) v)) (heap_map h)"
  unfolding store_def
  using assms 
  by (clarsimp split: ccval.split)
  
lemma store_cond_hard_cap:
  assumes "store h c v = Success ret"
  shows "tag c = True"
    and "perm_store c = True"
    and "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    and "offset c \<ge> base c"
    and "offset c mod |memval_type v|\<^sub>\<tau> = 0"
proof -
  show "tag c = True"
    using assms unfolding store_def
    by (meson result.simps(4))
next
  show "perm_store c = True"
    using assms unfolding store_def
    by (meson result.simps(4))
next
  show "\<And> cv. \<lbrakk> v = Cap_v cv; tag cv \<rbrakk> \<Longrightarrow> perm_cap_store c \<and> (perm_cap_store_local c \<or> perm_global cv)"
    using assms unfolding store_def
    by (metis (no_types, lifting) assms result.simps(4) store_cap_false_perm_cap_store store_cap_false_perm_cap_store_local)
next
  show "offset c + |memval_type v|\<^sub>\<tau> \<le> base c + len c"
    using assms unfolding store_def
    by (meson linorder_not_le result.simps(4))
next 
  show "offset c \<ge> base c"
    using assms unfolding store_def
    by (meson linorder_not_le result.simps(4))
next 
  show "offset c mod |memval_type v|\<^sub>\<tau> = 0"
    using assms unfolding store_def
    by (meson linorder_not_le result.simps(4))
qed

lemma store_cond_bytes_bounds:
  assumes "store h c val = Success h'"
    and "\<forall> x. val \<noteq> Cap_v x"
shows "\<exists> m. Mapping.lookup (heap_map h) (block_id c) = Some (Map m)
          \<and> offset c \<ge> fst (bounds m) 
          \<and> offset c + |memval_type val|\<^sub>\<tau> \<le> snd (bounds m)"
using store_cond_hard_cap[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)] assms
  unfolding store_def
  by (simp split: ccval.split_asm; simp split: option.split_asm t.split_asm)
    (metis nle_le order.strict_iff_not result.distinct(1))+

lemma store_cond_bytes:
  assumes "store h c val = Success h'"
    and "\<forall> x. val \<noteq> Cap_v x"
  shows "\<exists> m. Mapping.lookup (heap_map h') (block_id c) = Some (Map m)
          \<and> offset c \<ge> fst (bounds m) 
          \<and> offset c + |memval_type val|\<^sub>\<tau> \<le> snd (bounds m)"
  using store_cond_hard_cap[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)] assms
  unfolding store_def
  by (simp split: ccval.split_asm; simp split: option.split_asm t.split_asm)
    (auto split: if_split_asm simp add: store_tval_def)

lemma store_cond_cap_bounds:
  assumes "store h c val = Success h'"
    and "val = Cap_v x"
shows "\<exists> m. Mapping.lookup (heap_map h) (block_id c) = Some (Map m)
          \<and> offset c \<ge> fst (bounds m) 
          \<and> offset c + |memval_type val|\<^sub>\<tau> \<le> snd (bounds m)"
proof -
  have cap_perms: "\<not>(\<not> perm_cap_store c \<and> tag x) \<and> \<not>(\<not> perm_cap_store_local c \<and> tag x \<and> \<not> perm_global x)" 
    using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(3)[where ?h=h and ?c=c and ?v=val and ?ret=h' and ?cv=x, OF assms(1)]
    store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    assms
    unfolding store_def
    by blast
  thus ?thesis 
    using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(3)[where ?h=h and ?c=c and ?v=val and ?ret=h' and ?cv=x, OF assms(1)]
    store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    assms
    by (simp split: ccval.split option.split_asm t.split_asm add: store_def cap_perms)
      (metis linorder_not_le result.distinct(1))
qed

lemma store_cond_cap:
  assumes "store h c val = Success h'"
    and "val = Cap_v v"
  shows "\<exists> m. Mapping.lookup (heap_map h') (block_id c) = Some (Map m)
          \<and> offset c \<ge> fst (bounds m) 
          \<and> offset c + |memval_type val|\<^sub>\<tau> \<le> snd (bounds m)"
proof -
  have cap_perms: "\<not>(\<not> perm_cap_store c \<and> tag v) \<and> \<not>(\<not> perm_cap_store_local c \<and> tag v \<and> \<not> perm_global v)"
    using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(3)[where ?h=h and ?c=c and ?v=val and ?ret=h' and ?cv=v, OF assms(1)]
      store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      assms
    by blast
  show ?thesis
    using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(3)[where ?h=h and ?c=c and ?v=val and ?ret=h' and ?cv=v, OF assms(1)]
      store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
      assms
    by (clarsimp split: ccval.split option.split_asm t.split_asm simp add: store_def cap_perms)
      (smt (verit) Mapping.lookup_update assms(1) result.distinct(1) result.sel(1) store_bound_violated_2 store_cond_hard_cap(3) store_def store_success store_tval_disjoint_bounds)
qed

lemma store_cond:
  assumes "store h c val = Success h'"
  shows "\<exists> m. Mapping.lookup (heap_map h') (block_id c) = Some (Map m)
          \<and> offset c \<ge> fst (bounds m) 
          \<and> offset c + |memval_type val|\<^sub>\<tau> \<le> snd (bounds m)"
  using store_cond_bytes[OF assms(1)] store_cond_cap[OF assms(1)]
  by blast

lemma store_bounds_preserved:
  assumes "store h c v = Success h'"
    and "Mapping.lookup (heap_map h) (block_id c) = Some (Map m)"
    and "Mapping.lookup (heap_map h') (block_id c) = Some (Map m')"
  shows "bounds m = bounds m'"
  using assms store_cond_hard_cap[OF assms(1)] 
proof (cases v)
  case (Uint8_v x1)
  thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Sint8_v x2)
  thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Uint16_v x3)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Sint16_v x4)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Uint32_v x5)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Sint32_v x6)
  thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)]
    unfolding store_def
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Uint64_v x7)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Sint64_v x8)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case (Cap_v x9)
  moreover hence "\<not>(\<not> perm_cap_store c \<and> tag x9) \<and>  \<not>(\<not> perm_cap_store_local c \<and> tag x9 \<and> \<not> perm_global x9)"
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def
    by blast
  ultimately show ?thesis 
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def
    by (simp split: if_split_asm add: store_tval_def; auto)
next
  case (Cap_v_frag x101 x102)
    thus ?thesis
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def 
    by (clarsimp split: if_split_asm) (blast intro: store_tval_disjoint_bounds) 
next
  case Undef
  thus ?thesis 
    using assms store_cond_hard_cap[OF assms(1)] 
    unfolding store_def
    by force
qed

lemma store_cond_cap_frag:
  assumes "store h c val = Success h'"
    and "val = Cap_v_frag v n"
  shows "\<exists> m. Mapping.lookup (heap_map h') (block_id c) = Some (Map m)"
  using store_cond_hard_cap[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)] assms
  unfolding store_def
  by (simp split: ccval.split_asm; simp split: option.split_asm t.split_asm) 
    (metis Mapping.lookup_update heap.select_convs(2) heap.surjective heap.update_convs(2) result.distinct(1) result.sel(1))

lemma store_undef_false:
  assumes "store h c Undef = Success ret"
  shows "False"
  using store_cond_hard_cap[where ?h=h and ?c=c and ?v="Undef" and ?ret=ret, OF assms] assms
  unfolding store_def
  by simp

lemma load_after_alloc_size_fail:
  assumes "alloc h c s = Success (h', cap)"
    and "|t|\<^sub>\<tau> > s"
  shows "load h' cap t = Error (C2Err LengthViolation)"
proof -
  have "tag cap = True"
    using assms alloc_def
    by auto
  moreover have "perm_load cap = True"
    using assms alloc_def
    by force
  moreover have "base cap = 0"
    using assms alloc_def
    by fastforce
  moreover have "len cap = s"
    using assms alloc_def 
    by auto
  ultimately show ?thesis 
    using assms load_def by auto
qed


subsubsection \<open>Good Variable Laws\<close>
text \<open>The properties defined above are intermediate results. Properties that govern the
      correctness while executing are the \textit{good variable} laws. The most important ones are:
      \begin{itemize}
          \item load after alloc
          \item load after free
          \item load after store
      \end{itemize}
      The \textit{load after store} case requires particular attention. For disjoint cases within
      the same block (refer to load\_after\_store\_disjoint\_2 and \\ load\_after\_store\_disjoint\_3),
      extra attention must be paid to the tagged memory, where the updated tag may occur at a location
      specified \textit{before} whatever was given by the capability offset. This is why
      the lemma retrieve\_stored\_tval\_disjoint\_2 requires an additional constraint where
      capability values are aligned. Of course, this is not a problem for 
      load\_after\_store\_disjoint\_3 since the capability conditions state that offsets must be aligned.
      
      For the compatible case, as stated in the paper~\cite{park_2022}, extra care has to be put in the cases where
      we load capabilities and capability fragments. For this, we have three cases:
      \begin{itemize}
          \item load\_after\_store\_prim
          \item load\_after\_store\_cap
          \item load\_after\_store\_cap\_frag
      \end{itemize}
      The load\_after\_store\_prim case returns the exact value that was stored. 
      The load\_after\_store\_cap case returns the stored capability with the tag bit dependent on
      the permissions of the capability provided to load. Finally, the load\_after\_store\_cap\_frag
      case returns the capability fragment with the tag bit falsifed.
      
      Finally, we note that there are slight differences to the CompCert version of the Good Variable
      Law due to the differences in the type and value system. Thus, there are cases in the
      CompCert version that are trivial in our case.\<close>

theorem load_after_alloc_1:
  assumes "alloc h c s = Success (h', cap)"
    and "|t|\<^sub>\<tau> \<le> s"
  shows "load h' cap t = Success Undef"
proof -
  let ?m = "\<lparr>bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>"
  have "tag cap = True"
    using assms(1) alloc_def 
    by fastforce
  moreover have "perm_load cap = True"
    using assms(1) alloc_def
    by fastforce
  moreover have "offset cap + |t|\<^sub>\<tau> \<le> base cap + len cap"
    using assms alloc_def 
    by fastforce
  moreover have "offset cap \<ge> base cap"
    using assms alloc_def
    by fastforce
  moreover have "offset cap mod |t|\<^sub>\<tau> = 0"
    using assms alloc_def
    by fastforce
  moreover have "Mapping.lookup (heap_map h') (block_id cap) = Some (Map ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset cap \<ge> fst (bounds ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset cap + |t|\<^sub>\<tau> \<le> snd (bounds ?m)"
    using assms alloc_def
    by fastforce
  moreover have "\<not> is_contiguous_bytes (content ?m) (nat (offset cap)) |t|\<^sub>\<tau>"
  proof -
    have "\<exists> n. |t|\<^sub>\<tau> = Suc n"
      using not0_implies_Suc sizeof_nonzero 
      by force
    thus ?thesis 
      using assms alloc_def
      by fastforce
  qed
  moreover have "\<not> is_cap (content ?m) (nat (offset cap))"
    by simp
  ultimately show ?thesis
    using load_not_cap_in_mem
    by presburger
qed

theorem load_after_alloc_2:
  assumes "alloc h c s = Success (h', cap)"
    and "|t|\<^sub>\<tau> \<le> s"
    and "block_id cap \<noteq> block_id cap'"
  shows "load h' cap' t = load h cap' t"
  using assms unfolding alloc_def load_def 
  by force

theorem load_after_free_1:
  assumes "free h c = Success (h', cap)"
  shows "load h cap t = Error (C2Err TagViolation)"
proof -
  consider (null) "c = NULL" | (non_null) "c \<noteq> NULL" by blast
  then show ?thesis
  proof (cases)
    case null
    moreover hence "c = cap"
      using assms free_null
      by force
    ultimately show ?thesis
      using load_null_error assms
      by blast
  next
    case non_null
    hence "cap = c \<lparr> tag := False \<rparr>"
      using assms free_cond(6)[where ?h=h and ?c=c and ?h'=h' and ?cap=cap] 
      by presburger
    moreover hence "tag cap = False"
      using assms
      by force
    ultimately show ?thesis using load_false_tag
      by blast
  qed
qed

theorem load_after_free_2:
  assumes "free h c = Success (h', cap)"
    and "block_id cap \<noteq> block_id cap'"
  shows "load h cap' t = load h' cap' t"
  using assms free_cond[OF assms(1)] 
  unfolding free_def load_def
  by fastforce

theorem load_after_store_disjoint_1:
  assumes "store h c val = Success h'"
    and "block_id c \<noteq> block_id c'"
  shows "load h c' t = load h' c' t"
  using assms store_cond_hard_cap[OF assms(1)] 
  unfolding store_def load_def
  by (clarsimp split: ccval.split_asm option.split_asm t.split_asm if_split_asm)

theorem load_after_store_disjoint_2:
  assumes "store h c v = Success h'"
    and "offset c' + |t|\<^sub>\<tau> \<le> offset c"
  shows "load h' c' t = load h c' t"
  using assms store_cond[OF assms(1)] store_cond_hard_cap[OF assms(1)]
  apply (clarsimp simp add: store_def load_def split: if_split_asm option.split t.split option.split_asm t.split_asm)
  apply (intro conjI impI)
   apply (smt (z3) lookup_update' option.discI)
  apply (rule allI, rule conjI, rule impI)
   apply (simp add: lookup_update')
  apply (rule allI, rule conjI, rule impI)
   apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.distinct(1) option.inject store_tval_disjoint_bounds t.distinct(1) t.inject)
  apply (rule conjI, rule impI)
   apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.distinct(1) option.sel store_tval_disjoint_bounds t.distinct(1) t.sel)
  apply (intro impI conjI allI)
      apply (metis (no_types, lifting) Mapping.lookup_update_neq option.distinct(1))
     apply (metis (no_types, lifting) lookup_update' option.inject t.discI)
    apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.inject store_tval_disjoint_bounds t.inject)
   apply (metis (no_types, lifting) lookup_update' option.sel store_tval_disjoint_bounds t.sel)
  using retrieve_stored_tval_disjoint_1 
  apply (smt (z3) int_nat_eq lookup_update' of_nat_0_le_iff of_nat_add of_nat_le_iff option.sel t.sel)
  done

theorem load_after_store_disjoint_3:
  assumes "store h c v = Success h'"
    and "offset c + |memval_type v|\<^sub>\<tau> \<le> offset c'"
  shows "load h' c' t = load h c' t"
  using assms store_cond[OF assms(1)] store_cond_hard_cap[OF assms(1)]
  apply (clarsimp simp add: store_def load_def split: if_split_asm option.split t.split option.split_asm t.split_asm)
  apply (rule conjI)
   apply (smt (z3) lookup_update' option.discI)
  apply (rule allI, rule conjI)
   apply (simp add: lookup_update')
  apply (rule allI, rule conjI)
   apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.distinct(1) option.inject store_tval_disjoint_bounds t.distinct(1) t.inject)
  apply (rule conjI)
   apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.distinct(1) option.sel store_tval_disjoint_bounds t.distinct(1) t.sel)
  apply (intro impI conjI allI)
      apply (metis (no_types, lifting) Mapping.lookup_update_neq option.distinct(1))
     apply (metis (no_types, lifting) lookup_update' option.inject t.discI)
    apply (smt (z3) Mapping.lookup_update Mapping.lookup_update_neq option.inject store_tval_disjoint_bounds t.inject)
   apply (metis (no_types, lifting) lookup_update' option.sel store_tval_disjoint_bounds t.sel)
  using retrieve_stored_tval_disjoint_2
  apply (smt (z3) int_nat_eq lookup_update' memval_type.simps nat_int nat_mod_distrib of_nat_add of_nat_le_0_iff of_nat_le_iff option.sel t.sel)
  done

theorem load_after_store_prim:
  assumes "store h c val = Success h'"
    and "\<forall> v. val \<noteq> Cap_v v"
    and "\<forall> v n. val \<noteq> Cap_v_frag v n"
    and "perm_load c = True"
  shows "load h' c (memval_type val) = Success val"
  using assms(1) store_cond_hard_cap[where ?h=h and ?c=c and ?v=val and ?ret=h', OF assms(1)]
    store_cond_bytes[OF assms(1) assms(2)] retrieve_stored_tval_any_perm[OF _ _ assms(3)]
  by (clarsimp simp add: store_def load_def split: if_split_asm option.split_asm t.split_asm ccval.split)
    (safe; clarsimp simp add: assms)

theorem load_after_store_cap:
  assumes "store h c (Cap_v v) = Success h'"
    and "perm_load c = True"
  shows "load h' c (memval_type (Cap_v v)) = Success (Cap_v (v \<lparr> tag := case perm_cap_load c of False => False | True => tag v \<rparr>))"
 using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h', OF assms(1)]
    store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h', OF assms(1)] 
    store_cond_hard_cap(3)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h' and ?cv=v, OF assms(1) refl]
    store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h', OF assms(1)]
    store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h', OF assms(1)]
    store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v="Cap_v v" and ?ret=h', OF assms(1)]
    assms
    retrieve_stored_tval_cap[where ?val="Cap_v v" and ?v=v, OF refl]
    retrieve_stored_tval_cap_no_perm_cap_load[where ?val="Cap_v v" and ?v=v, OF refl]
  apply (clarsimp, simp split: ccval.split; safe; clarsimp)
  apply (simp only: load_def; clarsimp split: option.split)
  apply (simp add: sizeof_def split: t.split, safe)
  subgoal
    by (blast dest: store_cond_cap)
  subgoal
    by (metis option.sel store_cond_cap t.distinct(1))
  subgoal
    apply (simp add: sizeof_def store_def)
    apply (subgoal_tac "\<not>(\<not> perm_cap_store c \<and> tag v) \<and> \<not>(\<not> perm_cap_store_local c \<and> tag v \<and> \<not> perm_global v)"; presburger?)
    apply (clarsimp split: if_split_asm)
    apply (simp split: option.split_asm t.split_asm if_split_asm)
    apply clarsimp 
    apply (smt (verit, best) \<open>offset c + int |memval_type (Cap_v v)|\<^sub>\<tau> \<le> int (base c + len c)\<close> \<open>offset c mod int |memval_type (Cap_v v)|\<^sub>\<tau> = 0\<close> assms(1) ccval.distinct(107) lookup_update' option.sel result.inject(1) result.simps(4) store_bound_violated_2 store_cond_cap store_cond_hard_cap(3) store_success t.sel)
    done
  subgoal
    apply (simp add: sizeof_def store_def)
    apply (subgoal_tac "\<not>(\<not> perm_cap_store c \<and> tag v) \<and> \<not>(\<not> perm_cap_store_local c \<and> tag v \<and> \<not> perm_global v)"; presburger?)
    apply (clarsimp split: if_split_asm)
    apply (simp split: option.split_asm t.split_asm if_split_asm)
    apply (clarsimp simp add: sizeof_def) 
    apply (smt (verit, ccfv_SIG) Mapping.lookup_update assms(1) heap.select_convs(2) heap.surjective heap.update_convs(2) store_bounds_preserved)
    done
  subgoal
    apply (simp add: store_def)
    apply (subgoal_tac "\<not>(\<not> perm_cap_store c \<and> tag v) \<and> \<not>(\<not> perm_cap_store_local c \<and> tag v \<and> \<not> perm_global v)"; presburger?)
    apply (clarsimp split: if_split_asm option.split_asm t.split_asm) 
    apply (cases "perm_cap_load c"; clarsimp)
    done
  done

theorem load_after_store_cap_frag:
  assumes "store h c (Cap_v_frag c' n) = Success h'"
    and "perm_load c"
  shows "load h' c (memval_type (Cap_v_frag c' n)) = Success (Cap_v_frag (c' \<lparr> tag := False \<rparr>) n)"
  using assms(1) store_cond_hard_cap[where ?h=h and ?c=c and ?v="Cap_v_frag c' n" and ?ret=h', OF assms(1)] 
        retrieve_stored_tval_cap_frag[where ?val="Cap_v_frag c' n" and ?c=c' and ?n=n and ?off="nat (offset c)" and ?b="(perm_cap_load c)", OF refl, simplified] 
  unfolding store_def
  apply (simp split: option.split_asm t.split_asm option.split t.split add: load_def assms(2), safe; simp split: if_split_asm)
  using assms(1) store_cond_cap_frag apply blast
     apply (metis assms(1) option.sel store_cond_cap_frag t.distinct(1))
    apply (metis assms(1) store_bounds_preserved)
   apply (metis assms(1) store_bounds_preserved)
  apply (metis Mapping.lookup_update heap.select_convs(2) heap.surjective heap.update_convs(2) option.sel t.sel)
  done

subsubsection \<open>Miscellaneous Laws\<close>

lemma free_after_alloc:
  assumes "alloc h c s = Success (h', cap)"
  shows "\<exists>! ret. free h' cap = Success ret"
  using alloc_def assms free_non_null_correct alloc_no_null_ret
  by force 

lemma store_after_alloc:
  assumes "alloc h True s = Success (h', cap)"
    and "|memval_type v|\<^sub>\<tau> \<le> s"
    and "v \<noteq> Undef"
  shows "\<exists> h''. store h' cap v = Success h''"
  proof -
  let ?m = "\<lparr>bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>"
  have "tag cap = True"
    using assms(1) alloc_def 
    by fastforce
  moreover have "perm_store cap = True"
    using assms(1) alloc_def
    by fastforce
  moreover have "\<And>cv. \<lbrakk>v = Cap_v cv; tag cv\<rbrakk> \<Longrightarrow> perm_cap_store cap \<and> (perm_cap_store_local cap \<or> perm_global cv)"
  proof -
    have "\<not> (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store cap \<and> tag cv | _ \<Rightarrow> False)"
      using assms unfolding alloc_def
      by (simp split: ccval.split, force)
    moreover have "\<not> (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store_local cap \<and> tag cv \<and> \<not> perm_global cv | _ \<Rightarrow> False)"
      using assms unfolding alloc_def
      by (simp split: ccval.split, force)
    ultimately show "\<And>cv. \<lbrakk>v = Cap_v cv; tag cv\<rbrakk> \<Longrightarrow> perm_cap_store cap \<and> (perm_cap_store_local cap \<or> perm_global cv)" 
      by force
  qed
  moreover have "offset cap + |memval_type v|\<^sub>\<tau> \<le> base cap + len cap"
    using assms alloc_def 
    by fastforce
  moreover have "offset cap \<ge> base cap"
    using assms alloc_def
    by fastforce
  moreover have "offset cap mod |memval_type v|\<^sub>\<tau> = 0"
    using assms alloc_def
    by fastforce
  moreover have "Mapping.lookup (heap_map h') (block_id cap) = Some (Map ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset cap \<ge> fst (bounds ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset cap + |memval_type v|\<^sub>\<tau> \<le> snd (bounds ?m)"
    using assms alloc_def
    by fastforce
  ultimately show ?thesis
    using store_success[where ?c=cap and ?v=v and ?m="\<lparr>bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>" and ?h=h'] assms(3)
    by simp (blast) 
qed

lemma store_after_alloc_gen:
  assumes "alloc h True s = Success (h', cap)"
    and "|memval_type v|\<^sub>\<tau> \<le> s"
    and "v \<noteq> Undef"
    and "n mod |memval_type v|\<^sub>\<tau> = 0"
    and "offset cap + n + |memval_type v|\<^sub>\<tau> \<le> base cap + len cap"
  shows "\<exists> h''. store h' (cap \<lparr> offset := offset cap + n \<rparr>) v = Success h''"
  proof -
  let ?m = "\<lparr>bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>"
  have "tag cap = True"
    using assms(1) alloc_def 
    by fastforce
  moreover have "perm_store (cap \<lparr> offset := offset cap + n \<rparr>) = True"
    using assms(1) alloc_def
    by fastforce
  moreover have "\<And>cv. \<lbrakk>v = Cap_v cv; tag cv\<rbrakk> \<Longrightarrow> perm_cap_store (cap \<lparr> offset := offset cap + n \<rparr>) \<and> (perm_cap_store_local (cap \<lparr> offset := offset cap + n \<rparr>) \<or> perm_global cv)"
  proof -
    have "\<not> (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store (cap \<lparr> offset := offset cap + n \<rparr>) \<and> tag cv | _ \<Rightarrow> False)"
      using assms unfolding alloc_def
      by (simp split: ccval.split, force)
    moreover have "\<not> (case v of Cap_v cv \<Rightarrow> \<not> perm_cap_store_local (cap \<lparr> offset := offset cap + n \<rparr>) \<and> tag cv \<and> \<not> perm_global cv | _ \<Rightarrow> False)"
      using assms unfolding alloc_def
      by (simp split: ccval.split, force)
    ultimately show "\<And>cv. \<lbrakk>v = Cap_v cv; tag cv\<rbrakk> \<Longrightarrow> perm_cap_store (cap \<lparr> offset := offset cap + n \<rparr>) \<and> (perm_cap_store_local (cap \<lparr> offset := offset cap + n \<rparr>) \<or> perm_global cv)" 
      by force
  qed
  moreover have "offset (cap \<lparr> offset := offset cap + n \<rparr>) + |memval_type v|\<^sub>\<tau> \<le> base (cap \<lparr> offset := offset cap + n \<rparr>) + len (cap \<lparr> offset := offset cap + n \<rparr>)"
    using assms alloc_def 
    by fastforce
  moreover have "offset (cap \<lparr> offset := offset cap + n \<rparr>) \<ge> base (cap \<lparr> offset := offset cap + n \<rparr>)"
    using assms alloc_def
    by fastforce
  moreover have "offset (cap \<lparr> offset := offset cap + n \<rparr>) mod |memval_type v|\<^sub>\<tau> = 0"
    using assms alloc_def
    by fastforce
  moreover have "Mapping.lookup (heap_map h') (block_id (cap \<lparr> offset := offset cap + n \<rparr>)) = Some (Map ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset (cap \<lparr> offset := offset cap + n \<rparr>) \<ge> fst (bounds ?m)"
    using assms alloc_def
    by fastforce
  moreover have "offset (cap \<lparr> offset := offset cap + n \<rparr>) + |memval_type v|\<^sub>\<tau> \<le> snd (bounds ?m)"
    using assms alloc_def
    by fastforce
  ultimately show ?thesis
    using store_success[where ?c="(cap \<lparr> offset := offset cap + n \<rparr>)" and ?v=v and ?m="\<lparr>bounds = (0, s), content = Mapping.empty, tags = Mapping.empty\<rparr>" and ?h=h'] assms(3)
    by simp (blast) 
qed

subsection \<open>Well-formedness of actions\<close>
lemma alloc_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
    and "alloc h True s = Success (h', cap)"
  shows "\<W>\<^sub>\<ff>(heap_map h')"
  using assms
  by (simp add: alloc_def wellformed_def, safe, erule_tac x=b in allE, erule_tac x=obj in allE, simp)
    (smt (verit, best) Mapping.keys_empty Mapping.lookup_update Mapping.lookup_update_neq Set.filter_def bot_nat_0.not_eq_extremum empty_iff mem_Collect_eq object.select_convs(3) option.sel t.sel zero_less_diff)

lemma free_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
    and "free h cap = Success (h', cap')"
  shows "\<W>\<^sub>\<ff>(heap_map h')" 
proof -
  consider (null) "cap = NULL" | (non_null) "cap \<noteq> NULL" by blast
  then show ?thesis
  proof (cases)
    case null
    show ?thesis 
      using free_null assms null
      by simp
  next
    case non_null
    show ?thesis
      by (smt (z3) Mapping.lookup_update_neq assms(1) assms(2) free_cond_non_null(3) free_cond_non_null(4) free_cond_non_null(5) free_def free_non_null_correct fst_conv heap.select_convs(2) heap.surjective heap.update_convs(2) option.sel result.sel(1) t.discI wellformed_def)
    qed
qed

lemma load_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
    and "load h c t = Success v"
  shows "\<W>\<^sub>\<ff>(heap_map h)"
  using assms(1)
  by assumption

lemma store_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
    and "store h c v = Success h'"
  shows "\<W>\<^sub>\<ff>(heap_map h')"
 using store_cond_hard_cap(1)[where ?h=h and ?c=c and ?v=v and ?ret=h', OF assms(2)]
   store_cond_hard_cap(2)[where ?h=h and ?c=c and ?v=v and ?ret=h', OF assms(2)]
   store_cond_hard_cap(4)[where ?h=h and ?c=c and ?v=v and ?ret=h', OF assms(2)]
   store_cond_hard_cap(5)[where ?h=h and ?c=c and ?v=v and ?ret=h', OF assms(2)]
   store_cond_hard_cap(6)[where ?h=h and ?c=c and ?v=v and ?ret=h', OF assms(2)]
   assms
  apply (simp add: store_def wellformed_def split: option.split_asm t.split_asm if_split_asm del: memval_type.simps)
  apply safe
  apply (clarsimp simp del: memval_type.simps)
  apply (erule_tac x="block_id c" in allE)
  apply (rename_tac map nth block obj x)
  apply (erule_tac x=map in allE) 
  apply (clarsimp simp del: memval_type.simps)
  apply (subgoal_tac "Set.filter (\<lambda>x. 0 < x mod |Cap|\<^sub>\<tau>) (Mapping.keys (tags (store_tval map (nat (int |memval_type v|\<^sub>\<tau> * nth)) v))) = {}")
   apply (smt (verit, best) Mapping.lookup_update Mapping.lookup_update_neq Set.member_filter assms(1) emptyE option.sel rel_simps(70) t.sel wellformed_def)
  apply (simp add: store_tval_def del: memval_type.simps split: ccval.split_asm; fastforce)
  done (* WARNING: The last line takes a VERY LONG TIME to process, at least 30s *)

subsection \<open>memcpy formalisation\<close>
text \<open>We also formalise memcpy in Isabelle/HOL. While other higher level operations are defined
      in the GIL level, we formalise memcpy here and prove basic properties. 
      memcpy works as follows: we define a mutually recursive function memcpy\_prim and memcpy\_cap.
      memcpy\_prim attempts byte copies, where tags are invalidated, and memcpy\_cap attempts
      capability copies. memcpy initially calls memcpy\_cap. If either load or store fails, perhaps
      due to misalignment or other issues, memcpy\_prim will be called instead. If memcpy\_prim
      also fails from load or store, the operation will fail.\<close>
function memcpy_prim :: "heap \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> nat \<Rightarrow> heap result"
  and memcpy_cap :: "heap \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> nat \<Rightarrow> heap result"
  where
  "memcpy_prim h _ _ 0 = Success h"
| "memcpy_cap h _ _ 0 = Success h"
| "memcpy_prim h dst src (Suc n) = 
     (let x = load h src Uint8 in 
      if \<not> is_Success x then Error (err x) else
      let xs = res x in
      if xs = Undef then Error (LogicErr (Unhandled 0)) else
      let y = store h dst xs in
      if \<not> is_Success y then Error (err y) else
      let ys = res y in
      memcpy_cap ys (dst \<lparr> offset := (offset dst + 1) \<rparr>) (src \<lparr> offset := (offset src) + 1\<rparr>) n)"
| "memcpy_cap h dst src (Suc n) =
     (if (Suc n) < |Cap|\<^sub>\<tau> then memcpy_prim h dst src (Suc n)
      else
        let x = load h src Cap in
        if \<not> is_Success x then memcpy_prim h dst src (Suc n) else
        let xs = res x in
        if xs = Undef then memcpy_prim h dst src (Suc n) else
        let y = store h dst xs in
        if \<not> is_Success y then memcpy_prim h dst src (Suc n) else
        let ys = res y in
        memcpy_cap ys (dst \<lparr> offset := (offset dst + |Cap|\<^sub>\<tau>)\<rparr>) (src \<lparr> offset := (offset src + |Cap|\<^sub>\<tau>)\<rparr>) (Suc n - |Cap|\<^sub>\<tau>))"
  by (blast | metis old.nat.exhaust prod_cases3 sumE)+

text \<open>We prove that the mutually recursive function terminates.\<close>
context
  notes sizeof_def[simp]
begin
termination by size_change
end

text \<open>This is the definition of memcpy. We also check that src and dst do not overlap. \<close>
definition memcpy :: "heap \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> nat \<Rightarrow> heap result"
  where
  "memcpy h dst src n \<equiv> 
     if n = 0 then 
       Success h 
     else if block_id dst = block_id src \<and> 
             ((offset src \<ge> offset dst \<and> offset src < offset dst + n) \<or>
              (offset dst \<ge> offset src \<and> offset dst < offset src + n)) then
       Error (LogicErr (Unhandled 0))
     else memcpy_cap h dst src n"

lemma memcpy_rec_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
  shows "memcpy_prim h dst src n = Success h' \<Longrightarrow> \<W>\<^sub>\<ff>(heap_map h')"
    and "memcpy_cap h dst src n = Success h' \<Longrightarrow> \<W>\<^sub>\<ff>(heap_map h')"
  using assms 
proof(induct h dst src n and h dst src n rule: memcpy_prim_memcpy_cap.induct)
  case (1 h uu uv)
  then show ?case 
    by force
next
  case (2 h uw ux)
  then show ?case
    by force
next
  case (3 h dst src n)
  then show ?case 
    by clarsimp (smt (verit) result.disc(1) result.distinct(1) result.expand result.sel(1) store_wellformed)
next
  case (4 h dst src n)
  then show ?case 
    by clarsimp (smt (verit, best) "4.hyps"(1) "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) result.collapse(1) store_wellformed)
qed

text \<open>We also prove that memcpy preserves well-formedness.\<close>
lemma memcpy_wellformed:
  assumes "\<W>\<^sub>\<ff>(heap_map h)"
    and "memcpy h dst src n = Success h'"
  shows "\<W>\<^sub>\<ff>(heap_map h')"
  using assms unfolding memcpy_def
  by (metis memcpy_rec_wellformed(2) result.distinct(1) result.sel(1))

lemma memcpy_cond:
  assumes "memcpy h dst src n = Success h'"
  shows "n > 0 \<longrightarrow> \<not> (block_id dst = block_id src \<and> 
             ((offset src \<ge> offset dst \<and> offset src < offset dst + n) \<or>
              (offset dst \<ge> offset src \<and> offset dst < offset src + n)))"
  using assms unfolding memcpy_def
  by force

section \<open>Miscellaneous Definitions\<close>
text \<open>The following are used for catching memory leaks in Gillian.\<close>
definition get_block_size :: "heap \<Rightarrow> block \<Rightarrow> nat option"
  where
  "get_block_size h b \<equiv> 
     let ex = Mapping.lookup (heap_map h) b in
     (case ex of None \<Rightarrow> None | Some m \<Rightarrow>
     (case m of Freed \<Rightarrow> None | _ \<Rightarrow> Some (snd (bounds (the_map m)))))"

primrec get_memory_leak_size :: "heap \<Rightarrow> nat \<Rightarrow> nat"
  where
  "get_memory_leak_size _ 0 = 0"
| "get_memory_leak_size h (Suc n) = get_memory_leak_size h n +
     (case get_block_size h (integer_of_nat (Suc n)) of 
       None \<Rightarrow> 0
     | Some n \<Rightarrow> n)"

primrec get_unfreed_blocks :: "heap \<Rightarrow> nat \<Rightarrow> block list"
  where
  "get_unfreed_blocks _ 0 = []"
| "get_unfreed_blocks h (Suc n) =
    (let ex = Mapping.lookup (heap_map h) (integer_of_nat (Suc n)) in
    (case ex of None \<Rightarrow> get_unfreed_blocks h n | Some m \<Rightarrow>
    (case m of Freed \<Rightarrow> get_unfreed_blocks h n | _ \<Rightarrow> integer_of_nat (Suc n) # get_unfreed_blocks h n)))"

end
