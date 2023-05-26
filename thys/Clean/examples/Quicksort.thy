(******************************************************************************
 * Clean
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

(*
 * Quicksort : all at a glance. 
 *
 * Authors : Burkhart Wolff, Frédéric Tuong
 *)

chapter \<open> Clean Semantics : A Coding-Concept Example\<close>

text\<open>The following show-case introduces subsequently a non-trivial example involving
local and global variable declarations, declarations of operations with pre-post conditions as
well as direct-recursive operations (i.e. C-like functions with side-effects on global and
local variables. \<close>

theory Quicksort
  imports Clean.Clean
          Clean.Hoare_Clean
          Clean.Clean_Symbex
begin

section\<open>The Quicksort Example - At a Glance\<close>

text\<open> We present the following quicksort algorithm in some conceptual, high-level notation:

\begin{isar}
algorithm (A,i,j) =
    tmp := A[i];
    A[i]:=A[j];
    A[j]:=tmp

algorithm partition(A, lo, hi) is
    pivot := A[hi]
    i := lo
    for j := lo to hi - 1 do
        if A[j] < pivot then
            swap A[i] with A[j]
            i := i + 1
    swap A[i] with A[hi]
    return i

algorithm quicksort(A, lo, hi) is
    if lo < hi then
        p := partition(A, lo, hi)
        quicksort(A, lo, p - 1)
        quicksort(A, p + 1, hi)

\end{isar}
\<close>


section\<open>Clean Encoding of the Global State of Quicksort\<close>


global_vars (state)
    A :: "int list"

function_spec swap (i::nat,j::nat) \<comment> \<open>TODO: the hovering on parameters produces a number of report equal to the number of \<^ML>\<open>Proof_Context.add_fixes\<close> called in \<^ML>\<open>Function_Specification_Parser.checkNsem_function_spec\<close>\<close>
pre          "\<open>i < length A \<and> j < length A\<close>"    
post         "\<open>\<lambda>res. length A = length(old A) \<and> res = ()\<close>" 
local_vars   tmp :: int 
defines      " \<open> tmp := A ! i\<close>  ;-
               \<open> A := list_update A i (A ! j)\<close> ;- 
               \<open> A := list_update A j tmp\<close> " 


function_spec partition (lo::nat, hi::nat) returns nat
pre          "\<open>lo < length A \<and> hi < length A\<close>"    
post         "\<open>\<lambda>res::nat. length A = length(old A) \<and> res = 3\<close>" 
local_vars   pivot  :: int
             i      :: nat
             j      :: nat
defines      " \<open>pivot := A ! hi \<close>  ;- \<open>i := lo \<close> ;- \<open>j := lo \<close> ;-
               while\<^sub>C \<open>j \<le> hi - 1 \<close> 
                do if\<^sub>C \<open>A ! j < pivot\<close>  
                     then call\<^sub>C swap \<open>(i , j) \<close>  ;-
                          \<open>i := i + 1 \<close>
                     else skip\<^sub>S\<^sub>E 
                   fi ;-
                    \<open>j := j + 1 \<close> 
                od;-
                call\<^sub>C swap \<open>(i, j)\<close>  ;-
                return\<^bsub>local_partition_state.result_value_update\<^esub> \<open>i\<close>" 

thm partition_core_def


rec_function_spec quicksort (lo::nat, hi::nat) returns unit
pre          "\<open>lo \<le> hi \<and> hi < length A\<close>"
post         "\<open>\<lambda>res::unit. \<forall>i\<in>{lo .. hi}. \<forall>j\<in>{lo .. hi}. i \<le> j \<longrightarrow> A!i \<le> A!j\<close>"
variant      "hi - lo" 
local_vars   p :: "nat" 
defines      " if\<^sub>C \<open>lo < hi\<close>  
               then (p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C partition \<open>(lo, hi)\<close> ; assign_local p_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) ;-
                     call\<^sub>C quicksort \<open>(lo, p - 1)\<close> ;-
                     call\<^sub>C quicksort \<open>(lo, p + 1)\<close>  
               else skip\<^sub>S\<^sub>E 
               fi"


thm quicksort_core_def
thm quicksort_def
thm quicksort_pre_def
thm quicksort_post_def

section\<open>Possible Application Sketch\<close>

lemma quicksort_correct : 
  "\<lbrace>\<lambda>\<sigma>.   \<triangleright> \<sigma> \<and> quicksort_pre (lo, hi)(\<sigma>) \<and> \<sigma> = \<sigma>\<^sub>p\<^sub>r\<^sub>e \<rbrace> 
     quicksort (lo, hi) 
   \<lbrace>\<lambda>r \<sigma>. \<triangleright> \<sigma> \<and> quicksort_post(lo, hi)(\<sigma>\<^sub>p\<^sub>r\<^sub>e)(\<sigma>)(r) \<rbrace>"
   oops



end
