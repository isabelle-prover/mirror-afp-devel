theory Abbrevs
imports PIMP SyntaxTweaks
begin


text \<open>now we can use dots as a term\<close>

consts dots::"'a" (\<open>\<dots>\<close>) 


lemma conj_to_impl: "(P \<and> Q \<longrightarrow> R) = (P \<longrightarrow> Q \<longrightarrow> R)"
  by auto


notation (in xvalid_program) (latex output)
barrier_inv (\<open>flush'_inv\<close>)


abbreviation
"acquire sb owns \<equiv> acquired True sb owns"
notation (latex output)
direct_memop_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}_\isa{d}}{\rightarrow}_{\isa{m}}$\<close> _\<close> [60,60] 100)
notation (latex output)
virtual_memop_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}}{\rightarrow}_{\isa{m}}$\<close> _\<close> [60,60] 100)



context program
begin
term "(ts, m) \<Rightarrow>\<^sub>s\<^sub>b (ts',m')"
notation (latex output) store_buffer.concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{sb}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
notation (latex output) virtual.concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
thm store_buffer.concurrent_step.Program
end


abbreviation (output)
"sbh_global_step \<equiv> computation.concurrent_step sbh_memop_step flush_step stmt_step (\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is])"

notation (latex output)
sbh_global_step (\<open>_ \<^latex>\<open>$\overset{\isa{sbh}}{\Rightarrow}$\<close> _\<close> [60,60] 100)


notation (latex output)
direct_pimp_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}}{\Rightarrow}$\<close> _\<close> [60,60] 100)


notation (latex output)
sbh_memop_step (\<open>_ \<^latex>\<open>$\overset{\isa{sbh}}{\rightarrow}_{\isa{m}}$\<close> _\<close> [60,60] 100)

notation (latex output)
sb_memop_step (\<open>_ \<^latex>\<open>$\overset{\isa{sb}}{\rightarrow}_{\isa{m}}$\<close> _\<close> [60,60] 100)


notation (output) 
sim_direct_config (\<open>_ \<sim> _ \<close> [60,60] 100)

notation (output) 
flush_step (\<open>_ \<rightarrow>\<^sub>s\<^sub>b\<^sub>h _\<close> [60,60] 100)

notation (output) 
store_buffer_step (\<open>_ \<rightarrow>\<^sub>s\<^sub>b _\<close> [60,60] 100)

notation (output)
outstanding_refs (\<open>refs\<close>)

notation (output)
is_volatile_Write\<^sub>s\<^sub>b (\<open>volatile'_Write\<close>)

abbreviation (output)
"not_volatile_write \<equiv> Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"

notation (output)
"flush_all_until_volatile_write" (\<open>exec'_all'_until'_volatile'_write\<close>)
notation (output)
"share_all_until_volatile_write" (\<open>share'_all'_until'_volatile'_write\<close>)

notation (output)
stmt_step (\<open>_\<turnstile> _ \<rightarrow>\<^sub>p _\<close> [60,60,60] 100)

notation (output)
augment_rels (\<open>aug\<close>)

context program
begin
notation (latex output)
direct_concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}_\isa{d}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
notation (latex output)
direct_concurrent_steps (\<open>_ \<^latex>\<open>$\overset{\isa{v}_\isa{d}}{\Rightarrow}^{*}$\<close> _\<close> [60,60] 100)

notation (latex output)
sbh_concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{sbh}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
notation (latex output) 
sbh_concurrent_steps (\<open>_ \<^latex>\<open>$\overset{\isa{sbh}}{\Rightarrow}^{*}$\<close> _\<close> [60,60] 100)

notation (latex output)
sb_concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{sb}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
notation (latex output) 
sb_concurrent_steps (\<open>_ \<^latex>\<open>$\overset{\isa{sb}}{\Rightarrow}^{*}$\<close> _\<close> [60,60] 100)

notation (latex output)
virtual_concurrent_step (\<open>_ \<^latex>\<open>$\overset{\isa{v}}{\Rightarrow}$\<close> _\<close> [60,60] 100)
notation (latex output) 
virtual_concurrent_steps (\<open>_ \<^latex>\<open>$\overset{\isa{v}}{\Rightarrow}^{*}$\<close> _\<close> [60,60] 100)
end


context xvalid_program_progress
begin

abbreviation
"safe_reach_virtual_free_flowing \<equiv> safe_reach virtual_concurrent_step safe_free_flowing"
notation (latex output)
"safe_reach_virtual_free_flowing" (\<open>safe'_reach\<close>)

abbreviation
"safe_reach_direct_delayed \<equiv> safe_reach direct_concurrent_step safe_delayed"

notation (latex output)
"safe_reach_direct_delayed" (\<open>safe'_reach'_delayed\<close>)

end



(* hide unit's in tuples *)

translations
 "x" <= "(x,())"
 "x" <= "((),x)"


translations
"CONST initial\<^sub>v xs ys" <= "CONST initial\<^sub>v xs ys zs"


end
