(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Accessing nested structs.
 * Testcase for bug VER-321.
 *)
theory nested_struct imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "nested_struct.c"

autocorres "nested_struct.c"
context nested_struct_all_impl 
begin
thm f'_def test'_def g'_def g1'_def
end

lemma (in ts_definition_test) "ptr_valid (heap_typing s) p1 \<Longrightarrow> ptr_valid (heap_typing s) p2 \<Longrightarrow>
         test' p1 p2 \<bullet> s
       \<lbrace> \<lambda>_ s. num_C.n_C (point1_C.x_C (heap_point1_C s p1)) =
                 index (point2_C.n_C (heap_point2_C s p2)) 0 \<rbrace>"
  unfolding test'_def f'_def
  apply runs_to_vcg
  done


lemma (in ts_definition_g) "ptr_valid (heap_typing h) s \<Longrightarrow>
             s1_C.x_C (index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 0) = v \<Longrightarrow>
         g' s \<bullet> h
       \<lbrace> \<lambda>_ h. index (s4_C.x_C (heap_s4_C h s)) 0 = index (s4_C.x_C (heap_s4_C h s)) 1 \<and>
               s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0) = s3_C.y_C (index (s4_C.x_C (heap_s4_C h s)) 0) \<and>
               index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 0 =
                 index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 1 \<and>
               s1_C.x_C (index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 0) =
                 s1_C.y_C (index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 0) \<and>
               s1_C.x_C (index (s2_C.x_C (s3_C.x_C (index (s4_C.x_C (heap_s4_C h s)) 0))) 0) = v
       \<rbrace>"
  unfolding g'_def
  apply runs_to_vcg
  done

end
