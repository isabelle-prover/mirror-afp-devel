(* Title: Verification Component Based on KAD: Programs with Pointers
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection{* KAD Component for Pointer Programs *}

theory Pointer_Examples
  imports VC_KAD_Examples2 "~~/src/HOL/Hoare/Heap"

begin

text {* This component supports the verification of simple while programs
with pointers in a partial correctness setting. *}

text{* All we do here is integrating Nipkow's implementation of pointers and heaps. *}

type_synonym 'a state = "string  \<Rightarrow> ('a ref + ('a \<Rightarrow> 'a ref))"

lemma list_reversal:
  "PRE (\<lambda>s :: 'a state. List (projr (s ''h'')) (projl (s ''p'')) Ps 
        \<and> List (projr (s ''h'')) (projl (s ''q'')) Qs 
        \<and> set Ps \<inter> set Qs = {})
    (WHILE (\<lambda>s. projl (s ''p'') \<noteq> Null) 
     INV (\<lambda>s. \<exists>ps qs. List (projr (s ''h'')) (projl (s ''p'')) ps 
              \<and> List (projr (s ''h'')) (projl (s ''q'')) qs 
              \<and> set ps \<inter> set qs = {} \<and> rev ps @ qs = rev Ps @ Qs)
     DO
      (''r'' ::= (\<lambda>s. s ''p''));
      (''p'' ::= (\<lambda>s. Inl (projr (s ''h'') (addr (projl (s ''p''))))) );
      (''h'' ::= (\<lambda>s. Inr ((projr (s ''h''))(addr (projl (s ''r'')) := projl (s ''q''))) ));
      (''q'' ::= (\<lambda>s. s ''r''))
     OD)
  POST (\<lambda>s. List (projr (s ''h'')) (projl (s ''q'')) (rev Ps @ Qs))"
  apply hoare 
  apply auto[2]
  by (clarsimp, fastforce intro: notin_List_update[THEN iffD2])

end