(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Prettier Printing for Programs"

theory PrettyProgs
imports "Simpl.Vcg"
begin

syntax (output)
  "_Assign"      :: "'b => 'b => ('a,'p,'f) com"    (\<open>(2_ :==/ _)\<close> [30, 30] 23)

  "_seq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" (\<open>_;;//_\<close> [20, 21] 20)

  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) com"
        (\<open>(0WHILE (_)//INV (_)//_)\<close>  [25, 0, 81] 71)

  "_Do" :: "('a,'p,'f) com \<Rightarrow> bdy" (\<open>DO//  (_)//OD\<close> [0] 1000)

  "_Cond"        :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF _ THEN//  (_)//ELSE//  (_)//FI)\<close> [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        (\<open>(0IF _ THEN//  (_)//FI)\<close> [0, 0] 71)

  "_Try_Catch":: "('a,'p,'f) com \<Rightarrow>('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
        (\<open>(0TRY//  (_)//CATCH _//END)\<close>  [0,0] 71)

end
