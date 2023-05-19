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
 * IsPrime-Test 
 *
 * Authors : Burkhart Wolff, Frédéric Tuong
 *)

chapter \<open> Clean Semantics : Another Clean Example\<close>


theory IsPrime
  imports Clean.Clean
          Clean.Hoare_Clean
          Clean.Clean_Symbex
          "HOL-Computational_Algebra.Primes"
begin

section\<open>The Primality-Test Example at a Glance\<close>

definition "SQRT_UINT_MAX = (65536::nat)"
definition "UINT_MAX = (2^32::nat) - 1"


function_spec isPrime(n :: nat) returns bool
pre          "\<open>n \<le> SQRT_UINT_MAX\<close>" 
post         "\<open>\<lambda>res. res \<longleftrightarrow> prime n \<close>"
local_vars   i :: nat
defines " if\<^sub>C \<open>n < 2\<close>  
            then return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>False\<close>
            else skip\<^sub>S\<^sub>E 
          fi ;-
          \<open>i := 2\<close> ;- 
          while\<^sub>C \<open>i < SQRT_UINT_MAX \<and> i*i \<le> n  \<close> 
            do if\<^sub>C \<open>n mod i = 0\<close>  
                  then return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>False\<close>
                  else skip\<^sub>S\<^sub>E 
                fi ;-
                \<open>i := i + 1 \<close> 
            od ;-
         return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>True\<close>"

find_theorems name:isPrime name:core
term\<open>isPrime_core\<close>
 
lemma XXX : 
"isPrime_core n \<equiv>
     if\<^sub>C (\<lambda>\<sigma>. n < 2) then (return\<^bsub>result_value_update\<^esub> (\<lambda>\<sigma>. False)) 
                     else skip\<^sub>S\<^sub>E fi;-
     i_update :==\<^sub>L (\<lambda>\<sigma>. 2) ;-
     while\<^sub>C (\<lambda>\<sigma>. (hd\<circ>i)\<sigma> < SQRT_UINT_MAX \<and> (hd\<circ>i)\<sigma> * (hd\<circ>i)\<sigma> \<le> n) 
     do
        (if\<^sub>C (\<lambda>\<sigma>. n mod (hd \<circ> i) \<sigma> = 0) 
         then (return\<^bsub>result_value_update\<^esub> (\<lambda>\<sigma>. False)) 
         else skip\<^sub>S\<^sub>E fi ;-
        i_update :==\<^sub>L (\<lambda>\<sigma>. (hd \<circ> i) \<sigma> + 1)) 
     od ;-
     return\<^bsub>result_value_update\<^esub> (\<lambda>\<sigma>. True)"

  by(simp add: isPrime_core_def)

lemma YYY:
"isPrime n \<equiv> block\<^sub>C push_local_isPrime_state 
                    (isPrime_core n) 
                    pop_local_isPrime_state"
  by(simp add: isPrime_def)

lemma isPrime_correct : 
  "\<lbrace>\<lambda>\<sigma>.   \<triangleright> \<sigma> \<and> isPrime_pre (n)(\<sigma>) \<and> \<sigma> = \<sigma>\<^sub>p\<^sub>r\<^sub>e \<rbrace> 
     isPrime n 
   \<lbrace>\<lambda>r \<sigma>. \<triangleright> \<sigma> \<and> isPrime_post(n) (\<sigma>\<^sub>p\<^sub>r\<^sub>e)(\<sigma>)(r) \<rbrace>"
   oops



end
