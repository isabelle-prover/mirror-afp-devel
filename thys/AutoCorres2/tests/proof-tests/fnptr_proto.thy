(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_proto
  imports 
    AutoCorres2_Main.AutoCorres_Main

begin

typedecl environment
consts callback_step::
  "8 word list \<Rightarrow> environment \<Rightarrow> (32 word * environment)"

consts callback_info::
  "8 word list \<Rightarrow> environment \<Rightarrow> (32 word)"

consts callback_void_step::
  "environment \<Rightarrow> environment"

ML \<open>IsarInstall.installed_C_files @{theory}\<close>


text \<open>When functions are called within expressions the C-parser analyses which global variables
are affected by those functions (read and write dependencies) and only accepts functions that
have no overlapping and thus potentially conflicting dependencies. 
To do this analysis the C-parser looks into the function bodies.
As function prototypes have no bodies the C-Parser by default assumes the "worst" for those 
functions: They are considered to read and write everything. So this by default prohibits the
use of function prototypes within expressions.
When you need more flexibility here you can specifiy the dependencies explicitly as demonstrated
in this file.
You can later define specifications for those prototypes and declare them to autocorres
via overloading and command \<open>declare_prototype\<close> or more low level with @{attribute autocorres_definition} 
Autocorres then generates a proof obligation that this specification behaves according to the
declared dependencies.
\<close>

setup \<open>
let
  open AstDatatype
in
IsarInstall.add_prototype_dependencies "fnptr_proto.c" 
  ("w", read_anything_write_phantom_machine_state) #>
IsarInstall.add_prototype_dependencies "fnptr_proto.c" 
  ("w1", read_heap_and_phantom_machine_state_write_phantom_machine_state)
end
\<close>


ML \<open>IsarInstall.installed_C_files @{theory}\<close>

install_C_file "fnptr_proto.c" [machinety=environment]

ML \<open>IsarInstall.installed_C_files @{theory}\<close>
ML \<open>
val embedded_fncall_exprs = ProgramAnalysis.get_embedded_fncall_exprs (the (CalculateState.get_csenv @{theory} "fnptr_proto.c"))
\<close>
ML \<open>
val deps = ProgramAnalysis.get_variable_dependencies (the (CalculateState.get_csenv @{theory} "fnptr_proto.c"))
\<close>


term w_body
context fnptr_proto_global_addresses
begin
thm fun_ptr_simps
end

init-autocorres [
    in_out_parameters = inc_ptr() and dec_ptr() and w() where disjoint [], 
    in_out_globals = w w_buf w2 w1 func do_call do_call_exit do_call_buff embedded_prototypes assign_w, 
    no_heap_abs = dec_ptr w w_buf w2 w1, 
    ts_force exit = do_call_exit] "fnptr_proto.c"

text \<open>\<close>

declare [[verbose=1]]
overloading w_body \<equiv> w_body
begin
definition 
  "w_body \<equiv> exec_spec_monad global_exn_var'_' global_exn_var'_'_update (globals) 
     (\<lambda>s. (clookup 0 (locals s), clookup 1 (locals s)))

     (\<lambda>(p::8 word ptr, n::32 word). 
        L2_pre_post (ptr_span_buffer p (unat n) \<subseteq> \<G>) (\<lambda>s. {(r, t). 
          \<exists>env. t = phantom_machine_state_'_update (\<lambda>_. env) s \<and> 
          (r, env) = callback_step (of_buffer_heap (hrs_mem (t_hrs_' s)) p (unat n)) (phantom_machine_state_' s) })) 

     (\<lambda>upd. locals_update (cupdate 2 upd))"
end

declare_prototype w_body_def 
  by read_write_confined


overloading w2_body \<equiv> w2_body
begin
definition 
  "w2_body \<equiv> exec_spec_monad global_exn_var'_' global_exn_var'_'_update (globals) 
     (\<lambda>s. (clookup 0 (locals s), clookup 1 (locals s)))

     (\<lambda>(p::8 word ptr, n::32 word). 
        L2_pre_post (ptr_span_buffer p (unat n) \<subseteq> \<G>) (\<lambda>s. {(r, t). 
          t = s \<and> 
          r = callback_info (of_buffer_heap (hrs_mem (t_hrs_' s)) p (unat n)) (phantom_machine_state_' s) })) 

     (\<lambda>upd. locals_update (cupdate 2 upd))"
end
declare_prototype w2_body_def 
  by read_write_confined

overloading w1_body \<equiv> w1_body
begin
definition 
  "w1_body \<equiv> exec_spec_monad global_exn_var'_' global_exn_var'_'_update (globals) 
     (\<lambda>s. (clookup 0 (locals s), clookup 1 (locals s)))

     (\<lambda>(p::8 word ptr, n::32 word). 
        L2_pre_post_read_write (\<lambda>s. (t_hrs_' s, phantom_machine_state_' s)) phantom_machine_state_'_update  
      (ptr_span_buffer p (unat n) \<subseteq> \<G>) (\<lambda>(h, env). {(v, env'). (v, env') = callback_step (of_buffer_heap (hrs_mem h) p (unat n)) env  })) 

     (\<lambda>upd. locals_update (cupdate 2 upd))"
end
declare_prototype w1_body_def 
  by read_write_confined



overloading w_buf_body \<equiv> w_buf_body
begin
definition 
  "w_buf_body \<equiv> exec_spec_monad global_exn_var'_' global_exn_var'_'_update (globals) 
     (\<lambda>s. (clookup 0 (locals s)))

     (\<lambda>(p0::buffer_C ptr). 
        L2_seq 
          (L2_gets (\<lambda>s. (buf_C (h_val (hrs_mem (t_hrs_' s)) p0))) [clocals_string_embedding ''p'']) (\<lambda>p.
          (L2_seq
            (L2_gets (\<lambda>s. (len_C (h_val (hrs_mem (t_hrs_' s)) p0))) [clocals_string_embedding ''n'']) (\<lambda>n. 
            L2_pre_post (ptr_span_buffer p (unat n) \<subseteq> \<G>) (\<lambda>s. {(r, t). 
             \<exists>env. t = phantom_machine_state_'_update (\<lambda>_. env) s \<and> 
             (r, env) = callback_step (of_buffer_heap (hrs_mem (t_hrs_' s)) 
             p (unat n)) (phantom_machine_state_' s) }))))) 

     (\<lambda>upd. locals_update (cupdate 1 upd))"
end

declare w_buf_body_def [autocorres_definition fnptr_proto CP w_buf]



overloading u_body \<equiv> u_body
begin
definition  
  "u_body \<equiv> exec_spec_monad global_exn_var'_' global_exn_var'_'_update (globals)
    (\<lambda>s. ())
    (\<lambda>(_::unit).
     L2_pre_post (True) (\<lambda>s. {(r::unit, t).
      \<exists>env. t = phantom_machine_state_'_update (\<lambda>_. env) s \<and>
       env = callback_void_step (phantom_machine_state_' s)}))
     (\<lambda>upd. (\<lambda>s. s))"
end
declare u_body_def [autocorres_definition fnptr_proto CP u]

declare [[verbose=0]]
autocorres [no_body = v] "fnptr_proto.c"

thm l1_v'_def
thm l1_w2'_def
thm l2_v'_def
thm io_v'_def
thm hl_v'_def
thm wa_v'_def
thm ts.v'_def
thm l1_u'_def
thm l2_u'_def
thm ts.u'_def
thm l1_w'_def
thm final_defs
thm \<P>_defs
context fnptr_proto_global_addresses
begin
thm io_corres
end

end