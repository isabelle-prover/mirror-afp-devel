(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Shift operations with traditional infix syntax\<close>

theory Bit_Shifts_Infix_Syntax
  imports "HOL-Library.Word"
begin

context semiring_bit_shifts
begin

abbreviation shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
  where \<open>a << n \<equiv> push_bit n a\<close>

abbreviation shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  where \<open>a >> n \<equiv> drop_bit n a\<close>

end

abbreviation sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  where \<open>w >>> n \<equiv> signed_drop_bit n w\<close>

end
