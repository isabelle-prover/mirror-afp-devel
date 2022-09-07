(* Title: thys/Numerals_Ex.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Further contributions by Franz Regensburger (FABR) 02/2022 :
   - Re-ordering of sections
 *)

theory Numerals_Ex
  imports Numerals
begin

subsection \<open>About the expansion of the numeral notation\<close>

(* Some spikes by FABR concerning the notation <...>:

   The notation <...> produces a proper list of cells
   where lists of natural numbers are monadic encoded as blocks of Oc\<up>(n+1) for all n in the list

   The empty list of natural numbers is encoded as the empty cell list 
 *)

lemma "<[]> == []" by auto
lemma "<[]::(nat list)> = ([]::(cell list))" by auto

(* value requests typed naturals. Otherwise, the syntactic expansion of <..> fails 

    value "<0>"   \<longrightarrow> Error: Term to be evaluated contains free dictionaries
    value "<1>"   \<longrightarrow> Error: Term to be evaluated contains free dictionaries
 *)

value "<0::nat>"  (* OK *)
value "<1::nat>"  (* OK *)

(* empty nat list \<longrightarrow> empty cell list \<longrightarrow> the empty word epsilon *)

value "<[]::(nat list)>"

value "<[1::nat, 2::nat]>"

(* tuples *)

value "<(0::nat)>"
value "<(1::nat)>"

value "<(1::nat, 2::nat)>"

(* the following yield identical expansions; nested tuples are flattened *)
value "<[1::nat, 2::nat, 3::nat]>"
value "<(1::nat, 2::nat, 3::nat)>"
value "<(1::nat, (2::nat, 3::nat))>"
value "<(1::nat, [2::nat, 3::nat])>"

(*
   However:, nested lists are not possible (no need for such things)
   value "<[1::nat, [2::nat, 3::nat]]>"  \<longrightarrow> Error
 *)

end
