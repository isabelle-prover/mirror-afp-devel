(*  Title:      Keyserver_Composition.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>The Composition of the Two Keyserver Protocols\<close>
theory Keyserver_Composition
  imports "../PSPSP"
begin

declare [[pspsp_timing]]

trac\<open>
Protocol: kscomp

Enumerations:
honest = {a,b,c}
dishonest = {i}
agent = honest ++ dishonest

Sets:
ring/1 valid/1 revoked/1 deleted/1
ring'/1 seen/1 pubkeys/0

Functions:
Public h/1 sign/2 crypt/2 scrypt/2 pair/2 update/3
Private inv/1 pw/1

Analysis:
sign(X,Y) -> Y
crypt(X,Y) ? inv(X) -> Y
scrypt(X,Y) ? X -> Y
pair(X,Y) -> X,Y
update(X,Y,Z) -> X,Y,Z


### The signature-based keyserver protocol
Transactions of p1:
intruderGen()
  new PK
* send PK, inv(PK).

outOfBand(A:honest)
  new PK
  insert PK ring(A)
* insert PK valid(A)
* send PK.

oufOfBandD(A:dishonest)
  new PK
* insert PK valid(A)
* send PK, inv(PK).

updateKey(A:honest,PK:value)
  PK in ring(A)
  new NPK
  delete PK ring(A)
  insert PK deleted(A)
  insert NPK ring(A)
  send sign(inv(PK),pair(A,NPK)).

updateKeyServer(A:agent,PK:value,NPK:value)
  receive sign(inv(PK),pair(A,NPK))
* PK in valid(A)
* NPK notin valid(_)
  NPK notin revoked(_)
* delete PK valid(A)
  insert PK revoked(A)
* insert NPK valid(A)
* send inv(PK).

authAttack(A:honest,PK:value)
  receive inv(PK)
* PK in valid(A)
  attack.


### The password-based keyserver protocol
Transactions of p2:
intruderGen'()
  new PK
* send PK, inv(PK).

passwordGenD(A:dishonest)
  send pw(A).

pubkeysGen()
  new PK
  insert PK pubkeys
* send PK.

updateKeyPw(A:honest,PK:value)
  PK in pubkeys
  new NPK
# NOTE: The ring' sets are not used elsewhere, but we have to avoid that the fresh keys generated
#       by this rule are abstracted to the empty abstraction, and so we insert them into a ring'
#       set. Otherwise the two protocols would have too many abstractions in common (in particular,
#       the empty abstraction) which leads to false attacks in the composed protocol (probably
#       because the term implication graphs of the two protocols then become 'linked' through the
#       empty abstraction)
  insert NPK ring'(A)
* send NPK
  send crypt(PK,update(A,NPK,pw(A))).

updateKeyServerPw(A:agent,PK:value,NPK:value)
  receive crypt(PK,update(A,NPK,pw(A)))
  PK in pubkeys
  NPK notin pubkeys
  NPK notin seen(_)
* insert NPK valid(A)
  insert NPK seen(A).

authAttack2(A:honest,PK:value)
  receive inv(PK)
* PK in valid(A)
  attack.
\<close>

subsection \<open>Proof: The composition of the two keyserver protocols is secure\<close>
protocol_model_setup spm: kscomp
setup_protocol_checks spm kscomp_protocol kscomp_protocol_p1 kscomp_protocol_p2
compute_fixpoint kscomp_protocol kscomp_fixpoint
manual_protocol_security_proof ssp: kscomp
  for kscomp_protocol kscomp_fixpoint
  apply check_protocol_intro
  subgoal by (timeit code_simp)
  subgoal
    apply coverage_check_intro
    subgoal by (timeit code_simp)
    subgoal by (timeit code_simp)
    subgoal by (timeit code_simp)
    subgoal by (timeit normalization)
    subgoal by (timeit eval)
    subgoal by (timeit eval)
    subgoal by (timeit code_simp)
    subgoal by (timeit code_simp)
    subgoal by (timeit code_simp)
    subgoal by (timeit normalization)
    subgoal by (timeit eval)
    subgoal by (timeit eval)
    done
  subgoal by (timeit eval)
  subgoal by (timeit eval)
  subgoal
    apply (unfold spm.wellformed_fixpoint_def Let_def case_prod_unfold; intro conjI)
    subgoal by (timeit code_simp)
    subgoal by (timeit eval)
    done
  done


subsection \<open>The generated theorems and definitions\<close>
thm ssp.protocol_secure

thm kscomp_enum_consts.nchotomy
thm kscomp_sets.nchotomy
thm kscomp_fun.nchotomy
thm kscomp_atom.nchotomy
thm kscomp_arity.simps
thm kscomp_public.simps
thm kscomp_\<Gamma>.simps
thm kscomp_Ana.simps

thm kscomp_transaction_p1_outOfBand_def
thm kscomp_transaction_p1_oufOfBandD_def
thm kscomp_transaction_p1_updateKey_def
thm kscomp_transaction_p1_updateKeyServer_def
thm kscomp_transaction_p1_authAttack_def
thm kscomp_transaction_p2_passwordGenD_def
thm kscomp_transaction_p2_pubkeysGen_def
thm kscomp_transaction_p2_updateKeyPw_def
thm kscomp_transaction_p2_updateKeyServerPw_def
thm kscomp_transaction_p2_authAttack2_def
thm kscomp_protocol_def

thm kscomp_fixpoint_def

end
