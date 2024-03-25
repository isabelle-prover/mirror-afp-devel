(***********************************************************************************
 * Copyright (c) University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 ***********************************************************************************)

chapter\<open>Extended Division on Multi-Intervals\<close>
theory
  Extended_Multi_Interval_Division_Core
imports
  Interval_Division_Non_Zero
  Multi_Interval
begin

section\<open>Division over List of Intervals\<close>

text\<open>
  In this theory, we define an extended division operation on intervals. This is a 
  formalization of the interval division given in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>.
\<close>

definition inverse_interval :: "('a::{linorder,minus_mono,zero,one,inverse,infinity,uminus}) interval \<Rightarrow> ('a interval) list"
  where "inverse_interval a = (
                                  if (\<not> 0 \<in>\<^sub>i a) then [mk_interval ( 1 / (upper a), 1 / (lower a))]
                                  else if lower a = 0 \<and> 0 < upper a then [mk_interval (1/ upper a, \<infinity>)]
                                  else if lower a < 0 \<and> 0 < upper a then [mk_interval (-\<infinity>, 1/lower a), mk_interval (1/upper a, \<infinity>)]
                                  else if lower a < upper a \<and> upper a = 0 then [mk_interval(-\<infinity>, 1 / lower a)]
                                  else undefined 
                              )"
definition \<open>minverse = concat o (map inverse_interval)\<close>

section\<open>Multi-Interval Division\<close>

end
