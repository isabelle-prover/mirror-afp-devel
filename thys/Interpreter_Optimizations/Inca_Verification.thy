theory Inca_Verification
  imports Inca 
begin

context inca begin


section \<open>Strongest postcondition\<close>

inductive sp_instr for F ret where
  Push:
    "sp_instr F ret (IPush d) \<Sigma> (Suc \<Sigma>)" |
  Pop:
    "sp_instr F ret IPop (Suc \<Sigma>) \<Sigma>" |
  Get:
    "sp_instr F ret (IGet n) \<Sigma> (Suc \<Sigma>)" |
  Set:
    "sp_instr F ret (ISet n) (Suc \<Sigma>) \<Sigma>" |
  Load:
    "sp_instr F ret (ILoad x) (Suc \<Sigma>) (Suc \<Sigma>)" |
  Store:
    "sp_instr F ret (IStore x) (Suc (Suc \<Sigma>)) \<Sigma>" |
  Op:
    "\<Sigma>i = \<AA>\<rr>\<ii>\<tt>\<yy> op + \<Sigma> \<Longrightarrow>
    sp_instr F ret (IOp op) \<Sigma>i (Suc \<Sigma>)" |
  OpInl:
    "\<Sigma>i = \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) + \<Sigma> \<Longrightarrow>
    sp_instr F ret (IOpInl opinl) \<Sigma>i (Suc \<Sigma>)" |
  CJump:
    "sp_instr F ret (ICJump l\<^sub>t l\<^sub>f) 1 0" |
  Call:
    "F f = Some (ar, r) \<Longrightarrow> \<Sigma>i = ar + \<Sigma> \<Longrightarrow> \<Sigma>o = r + \<Sigma> \<Longrightarrow>
    sp_instr F ret (ICall f) \<Sigma>i \<Sigma>o" |
  Return: "\<Sigma>i = ret \<Longrightarrow>
    sp_instr F ret IReturn \<Sigma>i 0"

text \<open>@{const sp_instr} calculates the strongest postcondition of the arity of the operand stack.\<close>

inductive sp_instrs for F ret where
  Nil:
    "sp_instrs F ret [] \<Sigma> \<Sigma>" |
  Cons:
    "sp_instr F ret instr \<Sigma>i \<Sigma> \<Longrightarrow> sp_instrs F ret instrs \<Sigma> \<Sigma>o \<Longrightarrow>
    sp_instrs F ret (instr # instrs) \<Sigma>i \<Sigma>o"


section \<open>Range validations\<close>

fun local_var_in_range where
  "local_var_in_range n (IGet k) \<longleftrightarrow> k < n" |
  "local_var_in_range n (ISet k) \<longleftrightarrow> k < n" |
  "local_var_in_range _ _ \<longleftrightarrow> True"

fun jump_in_range where
  "jump_in_range L (ICJump l\<^sub>t l\<^sub>f) \<longleftrightarrow> {l\<^sub>t, l\<^sub>f} \<subseteq> L" |
  "jump_in_range L _ \<longleftrightarrow> True"

fun fun_call_in_range where
  "fun_call_in_range F (ICall f) \<longleftrightarrow> f \<in> dom F" |
  "fun_call_in_range F instr \<longleftrightarrow> True"


section \<open>Basic block validation\<close>

definition wf_basic_block where
  "wf_basic_block F L ret n bblock \<longleftrightarrow>
    (let (label, instrs) = bblock in
     list_all (local_var_in_range n) instrs \<and>
     list_all (jump_in_range L) instrs \<and>
     list_all (fun_call_in_range F) instrs \<and>
     list_all (\<lambda>i. \<not> Inca.is_jump i \<and> \<not> Inca.is_return i) (butlast instrs) \<and>
     instrs \<noteq> [] \<and>
     sp_instrs F ret instrs 0 0)"


section \<open>Function definition validation\<close>

definition wf_fundef where
  "wf_fundef F fd \<longleftrightarrow>
    body fd \<noteq> [] \<and>
    list_all
      (wf_basic_block F (fst ` set (body fd)) (return fd) (arity fd + fundef_locals fd))
      (body fd)"


section \<open>Program definition validation\<close>

definition wf_prog where
  "wf_prog p \<longleftrightarrow>
    (let F = F_get (prog_fundefs p) in
     pred_map (wf_fundef (map_option funtype \<circ> F)) F)"

end

end