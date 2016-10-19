(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory sparc_init_state

imports Main sparc_state sparc_types sparc_execution

begin

definition emp_cpu_reg :: "cpu_context" where
"emp_cpu_reg r \<equiv> 0"

definition emp_user_reg :: "word5 \<Rightarrow> window_context" where
"emp_user_reg ws w5 \<equiv> 0"

definition emp_sys_reg :: "sys_context" where
"emp_sys_reg r \<equiv> 0"

definition emp_mem :: "mem_context" where
"emp_mem asi add \<equiv> None"

definition init_mmu:: "MMU_state" where
"init_mmu \<equiv> mmu_setup"

definition emp_cpu_cache :: "cpu_cache" where
"emp_cpu_cache \<equiv> \<lparr>dcache = empty_cache,icache = empty_cache\<rparr>"

definition emp_dw_pool :: "delayed_write_pool" where
"emp_dw_pool \<equiv> []"

definition emp_bbyte :: "virtua_address \<Rightarrow> bool" where
"emp_bbyte add \<equiv> False"

definition emp_bword :: "virtua_address \<Rightarrow> bool" where
"emp_bword add \<equiv> False"

text {* ANNUL = False, RESET_TRAP = False, EXECUTE_MODE = True,
  RESET_MODE = False, ERROR_MODE = False. *}
definition init_svar :: "sparc_state_var" where
"init_svar \<equiv> \<lparr>annul=False,resett=False,exe=True,
reset=False,err=False,ticc=(0b0000000::word7),
itrpt_lvl=(0b000::word3),st_bar=False,
atm_ldst_byte=emp_bbyte, atm_ldst_word=emp_bword\<rparr>"

definition emp_trap :: "Trap set" where
"emp_trap \<equiv> {}"

definition emp_state :: "leon3_state" where
"emp_state \<equiv> \<lparr>cpu_reg=emp_cpu_reg, user_reg=emp_user_reg, sys_reg=emp_sys_reg, 
mem=emp_mem, mmu=init_mmu, cache=emp_cpu_cache, dwrite=emp_dw_pool, 
state_var=init_svar, 
traps=emp_trap, undef=False\<rparr>"

text {* PSR.ET = 1, PS= 1, S = 1, in init_state. 
  By default, CWP = 0. 
  icc = 0000, ver = 0011, impl = 1111.
  This is the default setting of LEON3. *}
definition init_state0 :: "leon3_state" where
"init_state0 \<equiv> 
  let s1 = cpu_reg_mod (0b11110011000000000000000011100000) PSR emp_state in
  cpu_reg_mod (0b00000000000000000000000000000010) TBR s1"

text {* Initialise PC and nPC. 
  And initialise r[14] in window 0 to 0x4ffffff0,
  according to the LEON3 setup. *}
definition init_state1 :: "leon3_state" where
"init_state1 \<equiv> 
  let s1 = cpu_reg_mod (0b01000000000000000000000000000000) PC init_state0;
      s2 = cpu_reg_mod (0b01000000000000000000000000000100) nPC s1
  in
  user_reg_mod (0x4ffffff0) 0 (14) s2
(*  s1*)
"

text {* Initialise the memory address 
  0b01000000000000000000000000000000 
  and the following ones
  with an example sequence of instructions. *}
definition init_state2 :: "leon3_state" where
"init_state2 \<equiv> 
      (* ld r1 + r2 to r3*)
  let s1 = mem_mod_w32 8 (0b01000000000000000000000000000000) (0b1111) 
           (0b11000110000000000100000101000010) init_state1;
      (* ld r5 + r6 to r4*)
      s2 = mem_mod_w32 8 (0b01000000000000000000000000000100) (0b1111) 
           (0b11001000000000010100000101000110) s1;
      (* add r3 r4 to r8*)
      s3 = mem_mod_w32 8 (0b01000000000000000000000000001000) (0b1111) 
           (0b10010000000000001100000000000100) s2;
      (* st r8 to address at r1 + r2*)
      s4 = mem_mod_w32 8 (0b01000000000000000000000000001100) (0b1111) 
           (0b11010000001000000100000101000010) s3;
      (* ld r1 + r2 to r9*)
      s5 = mem_mod_w32 8 (0b01000000000000000000000000010000) (0b1111) 
           (0b11010010000000000100000101000010) s4
  in
  s5
"

definition init_state3:: "leon3_state" where
"init_state3 \<equiv>
  let curr_win = ucast (get_CWP (cpu_reg_val PSR init_state2));
      (* r1 = 0x40000000 *)
      s1 = user_reg_mod (0b01000000000000000000000000000000) 
           curr_win (0b00001) init_state2;
      (* r2 = 0x1000 *)
      s2 = user_reg_mod (0b00000000000000000001000000000000) 
           curr_win (0b00010) s1;
      (* r5 = 0x40000000 *)
      s3 = user_reg_mod (0b01000000000000000000000000000000) 
           curr_win (0b00101) s2;
      (* r6 = 0x1004 *)
      s4 = user_reg_mod (0b00000000000000000001000000000100) 
           curr_win (0b00110) s3;
      (* 0x40001000 = 1 *)
      s5 = mem_mod_w32 10 (0b01000000000000000001000000000000) (0b1111) 
           (0b00000000000000000000000000000010) s4;
      (* 0x40001004 = 2 *)
      s6 = mem_mod_w32 10 (0b01000000000000000001000000000100) (0b1111) 
           (0b00000000000000000000000000000100) s5
  in
  s6
"

end

