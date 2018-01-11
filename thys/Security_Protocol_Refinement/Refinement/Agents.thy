(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/Agents.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Agents.thy 133854 2017-03-20 17:53:50Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Agents and nonces (partly based on Paulson's Message.thy)

  Copyright (c) 2009-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section {* Atomic messages *}

theory Agents imports Main 
begin

text {* The definitions below are moved here from the message theory, since
the higher levels of protocol abstraction do not know about cryptographic 
messages. *}


(******************************************************************************)
subsection {* Agents *}
(******************************************************************************)

datatype  \<comment> \<open>We allow any number of agents plus an honest server.\<close>
  agent = Server | Agent nat

consts 
  bad :: "agent set"			      -- {*compromised agents*}

specification (bad)
  Server_not_bad [iff]: "Server \<notin> bad"
    by (rule exI [of _ "{Agent 0}"], simp)

abbreviation 
  good :: "agent set"
where
  "good \<equiv> -bad"

abbreviation 
  Sv :: "agent"
where
  "Sv \<equiv> Server"


(******************************************************************************)
subsection {* Nonces *}
(******************************************************************************)

text {* We have an unspecified type of freshness identifiers. 
For executability, we may need to assume that this type is infinite. *}

typedecl fid_t

datatype fresh_t = 
  mk_fresh "fid_t" "nat"      (infixr "$" 65) 

fun fid :: "fresh_t \<Rightarrow> fid_t" where
  "fid (f $ n) = f"

fun num :: "fresh_t \<Rightarrow> nat" where
  "num (f $ n) = n"


text {* Nonces *}

type_synonym 
  nonce = "fresh_t"


end
