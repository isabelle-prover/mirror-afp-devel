(*******************************************************************************
 
  Project: IsaNet

  Author:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  Version: JCSPaper.1.0
  Isabelle Version: Isabelle2021-1

  Copyright (c) 2022 Tobias Klenze, Christoph Sprenger
  Licence: Mozilla Public License 2.0 (MPL) / BSD-3-Clause (dual license)

*******************************************************************************)



This document outlines the differences between the formalization of our work in Isabelle/HOL, and its presentation in the paper (submitted to JCS'22). A number of simplifications have been made to improve the presentation.


Intermediate Model
--------------------------------------------------------------------------------
 - Our formalization includes an intermediate model which only has the interface check, but not the cryptographic check. The simulation relation maps the future path to the interface-valid prefix of the future path.

Extensions
--------------------------------------------------------------------------------
In the paper we present a number of "Extensions", which are additional abstractions that are actually part of our framework but that we left out of the previous sections for simplicity. Most important among these are:
 - updatable uinfo fields: We currently only support this for directed protocols. If needed, the undirected parametrized model could be extended by updatable uinfo fields.
 - oracle. Used in the strong attacker model in EPIC L1 and L2 instances. We have separate parameters for ik_add and ik_oracle that in the paper are presented as a single constant (their union).


Naming and Syntax between Paper and Isabelle
--------------------------------------------------------------------------------
 - We call our abstract model "parametrized", because it has the set of authorized segments and the function target as parameters. To avoid the confusion with the other parameters (which are the main topic in the concrete model section in the paper), we refrain from calling this model parametrized in the paper.
 - the int and ext state is called loc and chan in Isabelle. For the concrete state it is loc2 and chan2.
 - we use predicates that take a message, channel parameters and state to define receiving a message from a channel. Similarly with sending (but the sending predicate additionally has the successor state as parameter). We do not use the syntax used in the paper.
 - instead of writing m \in s, we have predicates soup and soup2 for the abstract and concrete models, respectively.
 - conditions and assumptions are named instead of numbered
 - Instead of using the term "packet token", we use the term "uinfo" (for unauthenticated info field). With unauthenticated we mean that this field does not contain protected forwarding information created on the control plane. In our formalization this is reflected by the fact that this field is not contained in the set of authorized paths of the abstract model, over which the security properties are expressed. 
 - Our Isabelle formalization contains an "empty message" epsilon in the datatype terms. This is used, e.g., to model interface options: an interface option embedded as a term is either a natural number or the empty message.
 - We use a predicate no_oracle that returns if a certain combination of ainfo and uinfo field are NOT part of an oracle query.
 - The term "terminated" is used in the paper to denote the property of the path that the first hop field has prev=⊥ and the last hop field has next=⊥. In the formalization we treat these two as two properties called terminated and rooted, respectively.
 - The XOR constructor is called "FS" (for finite set) in our Isabelle formalization.


Other Differences between Paper and Isabelle
--------------------------------------------------------------------------------
- instead of a single target function N x I -|-> N x I, there are two functions tgtas: N x I -|-> N and tgtif: N x I -|-> I
- We use an additional "observe" event with guard true and no update (i.e., it leaves the state modified). This event is used to turn state invariants into trace properties. The trace property corresponding to a state invariant is that whenever "observe(s)" is on the trace, then the invariant holds in s.
- HF_c does not contain the fields of HF_a (called AHI in the Isabelle formalization) directly, but contains an AHI record scheme. This record scheme allows additional authenticated per-hop information to be added (aahi). 
- The Message theory that defines our term algebra (called "msgterm" in Isabelle) contains more constructors than were presented in the paper but are not used by any of our instances.
- Our parametrized model has parameters term_ainfo and terms_hf that say what an intruder can learn from inspecting an ainfo or a hop field. In all of our instances, we instantiate the type variables of the parametrized model simply with the term algebra. Hence usually term_ainfo = id and terms_hf gives either the HVF or both the HVF and UHI.
- The definition of the interface check and the cryptographic check uses two different "Take While" theories that define the longest valid prefix of a sequence. In previous versions of this formalization, we only had a single theory. However, the introduction of updatable uinfo fields made it easier to split these up.
- The "Take While" formalizations that we use also includes a predicate "holds", which states that the entire sequence is valid w.r.t. the check. We often use this predicate in our formalization instead of writing that the longest valid (w.r.t to the check) prefix of a sequence is the sequence itself.


