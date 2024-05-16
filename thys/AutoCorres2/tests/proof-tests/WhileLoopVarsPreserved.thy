(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WhileLoopVarsPreserved imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "while_loop_vars_preserved.c"

autocorres [ts_force nondet = loop] "while_loop_vars_preserved.c"

lemmas runs_to_whileLoop5 =  runs_to_whileLoop_res' [split_tuple C and B arity: 5]
lemmas runs_to_partial_whileLoop5 =  runs_to_partial_whileLoop_res [split_tuple C and B arity: 5]


context while_loop_vars_preserved_all_impl begin
lemma "loop' var1 var2 var3 var4 \<bullet> s ?\<lbrace> \<lambda>r s. r = Result (var1 + var2 + var3 + var4) \<rbrace>"
  unfolding loop'_def
  apply (runs_to_vcg (trace))
  apply (rule runs_to_partial_whileLoop5 [where 
        I = 
        "\<lambda>(meow, woof, neigh, ii, squeek) s.  
         ii = (var1 + var2 + var3 + var4 - (meow + woof + neigh + squeek))"])
  subgoal by simp
  subgoal by (simp add: word_gt_0)
  subgoal 
    apply runs_to_vcg
                        apply (auto simp: word_gt_0 measure_unat  split: if_split_asm)
    done
  done

lemma "loop' var1 var2 var3 var4 \<bullet> s \<lbrace> \<lambda>r s. r = Result (var1 + var2 + var3 + var4) \<rbrace>"
  unfolding loop'_def
  apply (runs_to_vcg (trace))
  apply (rule runs_to_whileLoop5 [where 
        I = 
        "\<lambda>(meow, woof, neigh, ii, squeek) s.  
         ii = (var1 + var2 + var3 + var4 - (meow + woof + neigh + squeek))" and
        R = "measure (\<lambda>((meow, woof, neigh, ii, squeek), s).
                   unat meow + unat woof + unat neigh + unat squeek)"])
  subgoal by simp
  subgoal by simp
  subgoal 
    apply (clarsimp simp add: word_greater_zero_iff)
    done
  subgoal 
    apply (runs_to_vcg)
     apply (auto simp: measure_unat)
    apply (metis measure_unat word_not_simps(1))+
    done
  done

end


end
