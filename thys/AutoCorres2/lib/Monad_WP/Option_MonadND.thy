(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Option monad syntax plus the connection between the option monad and the nondet monad *)

theory Option_MonadND
  imports
  Reader_Monad
begin


definition
 ogets :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b option)"
where
 "ogets f \<equiv> (\<lambda>s. Some (f s))"

definition
  ocatch :: "('s,('e + 'a)) lookup \<Rightarrow> ('e \<Rightarrow> ('s,'a) lookup) \<Rightarrow> ('s, 'a) lookup"
  (infix \<open><ocatch>\<close> 10)
where
  "f <ocatch> handler \<equiv> do {
     x \<leftarrow> f;
     case x of Inr b \<Rightarrow> oreturn b | Inl e \<Rightarrow> handler e
   }"


definition
  odrop :: "('s, 'e + 'a) lookup \<Rightarrow> ('s, 'a) lookup"
where
  "odrop f \<equiv> do {
     x \<leftarrow> f;
     case x of Inr b \<Rightarrow> oreturn b | Inl e \<Rightarrow> ofail
   }"

definition
  osequence_x :: "('s, 'a) lookup list \<Rightarrow> ('s, unit) lookup"
where
  "osequence_x xs \<equiv> foldr (\<lambda>x y. do { x; y }) xs (oreturn ())"

definition
  osequence :: "('s, 'a) lookup list \<Rightarrow> ('s, 'a list) lookup"
where
  "osequence xs \<equiv> let mcons = (\<lambda>p q. p |>> (\<lambda>x. q |>> (\<lambda>y. oreturn (x#y))))
                 in foldr mcons xs (oreturn [])"

definition
  omap :: "('a \<Rightarrow> ('s,'b) lookup) \<Rightarrow> 'a list \<Rightarrow> ('s, 'b list) lookup"
where
  "omap f xs \<equiv> osequence (map f xs)"

definition
  opt_cons :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr \<open>o#\<close> 65)
where
  "opt_cons x xs \<equiv> case x of None \<Rightarrow> xs | Some x' \<Rightarrow> x' # xs"


end
