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

chapter\<open>Extended Division on Intervals\<close>
theory
  Extended_Interval_Division
imports
  Interval_Division_Non_Zero
begin

text\<open>
  In this theory, we define an extended division operation on intervals. This definition is inspired
  by the definition given in~\<^cite>\<open>"moore.ea:introduction:2009"\<close>, but we use an over-approximation
  for the case in which zero is an element of the divisor interval. By this, we avoid the need for multi-intervals.
 \<close>

instantiation "interval" :: ("{infinity, linordered_field, real_normed_algebra,linear_continuum_topology}") inverse
begin
  definition inverse_interval :: "'a interval \<Rightarrow> 'a interval"
    where "inverse_interval a = (
                                  if (\<not> 0 \<in>\<^sub>i a) then mk_interval ( 1 / (upper a), 1 / (lower a))
                                  else if lower a = 0 \<and> 0 < upper a then mk_interval (1/ upper a, \<infinity>)
                                  else if lower a < 0 \<and> 0 < upper a then mk_interval (-\<infinity>, \<infinity>)
                                  else if lower a < upper a \<and> upper a = 0 then mk_interval(-\<infinity>, 1 / lower a)
                                  else undefined 
                                )"

  definition divide_interval :: "'a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval"
    where "divide_interval a b = inverse b * a"
  instance ..
end

interpretation interval_division_inverse divide inverse
  apply(unfold_locales)
  subgoal
    by (simp add: inverse_interval_def)
  subgoal
    by(simp add: divide_interval_def)
  done

end
