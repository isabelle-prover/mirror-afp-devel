(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Example\<close>

theory LTL_Example
  imports Main "../LTL" "../LTL_Rewrite" "~~/src/HOL/Library/Code_Target_Numeral" "~~/src/HOL/Library/Code_Char"
begin

--\<open>The included parser always returns a @{typ "String.literal ltlc"}. If a different labelling is 
  needed one can use @{const ltlc.map_ltlc} to relabel the leafs. In our example we replace the 
  strings by their length.\<close>

definition rewrite :: "String.literal ltlc \<Rightarrow> nat ltln"
where
  "rewrite \<equiv> rewrite_iter_slow o ltlc_to_ltln o (ltlc.map_ltlc size)"

--\<open>Export rewriting engine (and also constructors)\<close>

export_code true\<^sub>c LTLcIff rewrite in SML file "rewrite_example.sml"

end