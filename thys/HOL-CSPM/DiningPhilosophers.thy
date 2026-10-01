(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Dining Philosophers example
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
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
 ******************************************************************************\<close>
(*>*)


chapter\<open> Example: Dining Philosophers \<close>

(*<*)
theory DiningPhilosophers                                               
  imports "HOL-CSPM" "HOL-CSP.GenFixrec-HOLCF"
begin 
  (*>*)


section \<open>Classic version\<close>

text \<open>We formalize here the Dining Philosophers problem with a locale.\<close>


locale DiningPhilosophers =

fixes N::nat
assumes N_g1[simp] : \<open>N > 1\<close>  
  \<comment>\<open>We assume that we have at least one right handed philosophers
    (so at least two philosophers with the left handed one).\<close>

begin

text \<open>We use a datatype for representing the dinner's events.\<close>

datatype dining_event  = picks (phil:nat) (fork:nat) 
                       | putsdown (phil:nat) (fork:nat)


text \<open>We introduce the right handed philosophers, the left handed philosopher and the forks.\<close>

definition RPHIL:: \<open>nat \<Rightarrow> dining_event process\<close>
  where \<open>RPHIL i \<equiv> \<mu> X. (picks i i \<rightarrow> (picks i ((i-1) mod N) \<rightarrow>
                         (putsdown i ((i-1) mod N) \<rightarrow> (putsdown i i \<rightarrow> X))))\<close>

definition LPHIL0:: \<open>dining_event process\<close>
  where \<open>LPHIL0 \<equiv> \<mu> X. (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow>
                        (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> X))))\<close>

definition FORK  :: \<open>nat \<Rightarrow> dining_event process\<close>
  where \<open>FORK i \<equiv> \<mu> X. (picks i i \<rightarrow> (putsdown i i \<rightarrow> X)) \<box> 
                        (picks ((i+1) mod N) i \<rightarrow> (putsdown ((i+1) mod N) i \<rightarrow> X))\<close>


text \<open>Now we use the architectural operators for modelling the interleaving of
      the philosophers, and the interleaving of the forks.\<close>

definition \<open>PHILS \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># add_mset LPHIL0 (mset (map RPHIL [1..< N])). P\<close>
definition \<open>FORKS \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># mset (map FORK [0..< N]). P\<close>


corollary \<open>N = 3 \<Longrightarrow> PHILS = (LPHIL0 ||| RPHIL 1 ||| RPHIL 2)\<close>
  \<comment> \<open>just a test\<close>
  unfolding PHILS_def by (simp add: eval_nat_numeral upt_rec Sync_assoc)


text \<open>Finally, the dinner is obtained by putting forks and philosophers in parallel.\<close>

definition DINING :: \<open>dining_event process\<close>
  where   \<open>DINING = (FORKS || PHILS)\<close>


end


section \<open>Formalization with the Fixrec package\<close>

text \<open>The \<^verbatim>\<open>Fixrec\<close> package provides a more readable syntax
      (essentially, it allows us to "get rid of \<open>\<mu>\<close>" in equations like \<^term>\<open>\<mu> X. P X\<close>).
      In contrast to the \<^verbatim>\<open>fixrec\<close> package of \<^session>\<open>HOLCF\<close>, it does not require
      continuous function spaces: the processes are ordinary (total) HOL functions, and no
      \<^class>\<open>cpo\<close> instances of the argument types (like \<^typ>\<open>nat\<close>) are needed.
      \<^verbatim>\<open>Fixrec\<close> works inside the locale, the equations may refer to its parameter \<open>N\<close>.\<close>

locale DiningPhilosophers_fixrec =

fixes N::nat
assumes N_g1[simp] : \<open>N > 1\<close>  
  \<comment>\<open>We assume that we have at least one right handed philosophers
    (so at least two philosophers with the left handed one).\<close>

begin

text \<open>We use a datatype for representing the dinner's events.\<close>

datatype dining_event  =    picks (phil:nat) (fork:nat) 
                          | putsdown (phil:nat) (fork:nat)


text \<open>We introduce the right handed philosophers, the left handed philosopher and the forks.\<close>

Fixrec
      RPHIL   :: \<open>nat \<Rightarrow> dining_event process\<close>
  and LPHIL0  :: \<open>dining_event process\<close>
  and FORK    :: \<open>nat \<Rightarrow> dining_event process\<close>
  where 
    RPHIL_rec  : \<open>RPHIL i = (picks i i \<rightarrow> (picks i (i-1) \<rightarrow> 
                                 (putsdown i (i-1) \<rightarrow> (putsdown i i \<rightarrow> RPHIL i))))\<close>
  | LPHIL0_rec : \<open>LPHIL0 = (picks 0 (N-1) \<rightarrow> (picks 0 0 \<rightarrow> 
                                 (putsdown 0 0 \<rightarrow> (putsdown 0 (N-1) \<rightarrow> LPHIL0))))\<close>
  | FORK_rec   : \<open>FORK i  = (picks i i \<rightarrow> (putsdown i i \<rightarrow> FORK i)) \<box>
                            (picks ((i+1) mod N) i \<rightarrow> (putsdown ((i+1) mod N) i \<rightarrow> FORK i))\<close>


text \<open>Now we use the architectural operators for modelling the interleaving of
      the philosophers, and the interleaving of the forks.\<close>

definition \<open>PHILS \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># add_mset LPHIL0 (mset (map RPHIL [1..<N])). P\<close>
definition \<open>FORKS \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># mset (map FORK [0..<N]). P\<close>


corollary \<open>N = 3 \<Longrightarrow> PHILS = (LPHIL0 ||| RPHIL 1 ||| RPHIL 2)\<close>
  \<comment> \<open>just a test\<close>
  unfolding PHILS_def by (simp add: eval_nat_numeral upt_rec Sync_assoc)


text \<open>Finally, the dinner is obtained by putting forks and philosophers in parallel.\<close>

definition DINING :: \<open>dining_event process\<close>
  where   \<open>DINING = (FORKS || PHILS)\<close>


end

(*<*)
end
(*>*)