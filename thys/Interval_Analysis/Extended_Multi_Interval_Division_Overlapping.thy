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

subsection\<open>Overlapping Multi-Intervals (\thy)\<close>
theory
  Extended_Multi_Interval_Division_Overlapping
imports
  Extended_Multi_Interval_Division_Core
begin

definition \<open>minterval_ovl_inverse x = mInterval_ovl (mk_mInterval_ovl(minverse (mlist_ovl x)))\<close>
definition \<open>minterval_ovl_divide x y = (minterval_ovl_inverse y) * x\<close>

lemma set_of_ovl_non_zero_map_inverse: 
  assumes \<open>0 \<notin> set_of_ovl xs\<close> 
  shows \<open>concat (map inverse_interval (mlist_ovl xs)) = map (\<lambda>i. mk_interval (1 / upper i, 1 / lower i)) (mlist_ovl xs)\<close>
proof(insert assms, induction "mlist_ovl xs")
  case Nil
  then show ?case 
    by simp 
next
  case (Cons a x)
  then show ?case 
    using set_of_ovl_non_zero_list_all[of xs, simplified Cons, simplified]
    by (metis (no_types, lifting) concat_map_singleton inverse_interval_def map_eq_conv) 
qed

interpretation minterval_ovl_division_inverse minterval_ovl_divide minterval_ovl_inverse
  apply(unfold_locales)
  subgoal 
    using set_of_ovl_non_zero_map_inverse
    unfolding minterval_ovl_inverse_def minverse_def o_def un_op_interval_list_def 
    by fastforce
  subgoal by(metis minterval_ovl_divide_def)
  done

end
