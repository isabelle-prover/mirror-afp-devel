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
 * Authors : Burkhart Wolff, Frédéric Tuong
 *)

chapter \<open> A Clean Semantics Example : Linear Search\<close>

text\<open>The following show-case introduces subsequently a non-trivial example involving
local and global variable declarations, declarations of operations with pre-post conditions as
well as direct-recursive operations (i.e. C-like functions with side-effects on global and
local variables. \<close>

theory LinearSearch
  imports Clean.Clean
          Clean.Hoare_MonadSE
begin


section\<open>The LinearSearch Example\<close>

definition bool2int where "bool2int x = (if x then 1::int else 0)"

global_vars (state)
    t :: "int list"

global_vars ("2")
    tt :: "int list"

find_theorems (160) name:"2" name:"Linear"

function_spec linearsearch (x::int, n::int) returns int
pre          "\<open> 0 \<le> n \<and> n < int(length t) \<and> sorted t\<close>"    
post         "\<open>\<lambda>res::int. res = bool2int (\<exists> i \<in> {0 ..< length t}. t!i = x) \<close>" 
local_vars   i  :: int
defines      " \<open>i := 0 \<close> ;- \<open>tt :=  [] \<close>;-
               while\<^sub>C \<open>i < n \<close> 
                 do if\<^sub>C \<open>t ! (nat i) < x\<close>  
                      then  \<open>i := i + 1 \<close>
                      else return\<^sub>C result_value_update \<open>bool2int(t!(nat i) = x)\<close> 
                    fi 
                 od " 

(*
C\<open>
/*@ requires "n >= 0"
    requires "valid(t+(0..n-1))"
    requires "(forall integer i,j; 0<=i<=j<n ==> t[i] <= t[j])"
    ensures "exists integer i; (0<=i<n && t[i] == x) <==> result == 1"
    ensures "(forall integer i; 0<=i<n ==> t[i] != x) <==> result == 0"
    assigns nothing
 */

int linearsearch(int x, int t[], int n) {
  int i = 0;

  /*@ loop invariant "0<=i<=n"
      loop invariant "forall integer j; 0<=j<i ==> (t[j] != x)"
      loop assigns i
      loop variant "n-i"
   */
  while (i < n) {
    if (t[i] < x) {
      i++;
    } else {
      return (t[i] == x);
    }
  }

  return 0;
}
\<close>

*)

end