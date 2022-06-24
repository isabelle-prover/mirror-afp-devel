(*******************************************************************************

  Agents and nonces (partly based on Paulson's Message.thy)


*******************************************************************************)

section \<open>Atomic messages\<close>

theory Agents imports Main 
begin

text \<open>The definitions below are moved here from the message theory, since
the higher levels of protocol abstraction do not know about cryptographic 
messages.\<close>


(******************************************************************************)
subsection \<open>Agents\<close>
(******************************************************************************)

type_synonym as = nat  (* We allow any number of agents (ASes). *)

type_synonym aso = "as option"

type_synonym ases = "as set"


locale compromised =
fixes 
  bad :: "as set"			      \<comment> \<open>compromised ASes\<close>
begin

abbreviation 
  good :: "as set"
where
  "good \<equiv> -bad"
end
        
(******************************************************************************)
subsection \<open>Nonces and keys\<close>
(******************************************************************************)

text \<open>We have an unspecified type of freshness identifiers. 
For executability, we may need to assume that this type is infinite.\<close>

typedecl fid_t

datatype fresh_t = 
  mk_fresh "fid_t" "nat"      (infixr "$" 65) 

fun fid :: "fresh_t \<Rightarrow> fid_t" where
  "fid (f $ n) = f"

fun num :: "fresh_t \<Rightarrow> nat" where
  "num (f $ n) = n"


text \<open>Nonces\<close>

type_synonym 
  nonce = "fresh_t"



end
