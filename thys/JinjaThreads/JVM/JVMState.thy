(*  Title:      JinjaThreads/JVM/JVMState.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

chapter {* Jinja Virtual Machine \label{cha:jvm} *}

section {* State of the JVM *}

theory JVMState
imports
  "../Common/Observable_Events"
begin

subsection {* Frame Stack *}

type_synonym 
  pc = nat

type_synonym
  'addr frame = "'addr val list \<times> 'addr val list \<times> cname \<times> mname \<times> pc"
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

(* pretty printing for frame type *)
print_translation {*
  let
    fun tr'
       [Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a1),
        Const (@{type_syntax "prod"}, _) $
          (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a2)) $
          (Const (@{type_syntax "prod"}, _) $
             Const (@{type_syntax "String.literal"}, _) $
             (Const (@{type_syntax "prod"}, _) $
                Const (@{type_syntax "String.literal"}, _) $
                Const (@{type_syntax "nat"}, _)))] =
      if a1 = a2 then Syntax.const @{type_syntax "frame"} $ a1
      else raise Match;
    in [(@{type_syntax "prod"}, K tr')]
  end
*}
typ "'addr frame"

subsection {* Runtime State *}
type_synonym
  ('addr, 'heap) jvm_state = "'addr option \<times> 'heap \<times> 'addr frame list"  
  -- "exception flag, heap, frames"

type_synonym
  'addr jvm_thread_state = "'addr option \<times> 'addr frame list"
  -- "exception flag, frames, thread lock state"

type_synonym
  ('addr, 'thread_id, 'heap) jvm_thread_action = "('addr, 'thread_id, 'addr jvm_thread_state,'heap) Jinja_thread_action"

type_synonym
  ('addr, 'thread_id, 'heap) jvm_ta_state = "('addr, 'thread_id, 'heap) jvm_thread_action \<times> ('addr, 'heap) jvm_state"

(* pretty printing for jvm_thread_action type *)
print_translation {*
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ 
           (Const (@{type_syntax "option"}, _) $ a2) $
           (Const (@{type_syntax "list"}, _) $ 
             (Const (@{type_syntax "prod"}, _) $
               (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a3)) $
               (* Next bit: same syntax translation as for frame *)
               (Const (@{type_syntax "prod"}, _) $
                 (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "val"}, _) $ a4)) $
                 (Const (@{type_syntax "prod"}, _) $
                   Const (@{type_syntax "String.literal"}, _) $
                   (Const (@{type_syntax "prod"}, _) $
                      Const (@{type_syntax "String.literal"}, _) $
                      Const (@{type_syntax "nat"}, _))))))
       , h] =
      if a1 = a2 andalso a2 = a3 andalso a3 = a4 then Syntax.const @{type_syntax "jvm_thread_action"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "Jinja_thread_action"}, K tr')]
  end
*}
typ "('addr, 'thread_id, 'heap) jvm_thread_action"

end
