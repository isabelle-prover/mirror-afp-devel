(*  Title:      Keyserver2.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>A Variant of the Keyserver Protocol\<close>
theory Keyserver2
  imports "../PSPSP"
begin

declare [[pspsp_timing]]

trac\<open>
Protocol: keyserver2

Enumerations:
honest = {a,b,c}
dishonest = {i}
agent = honest ++ dishonest

Sets:
ring'/1 seen/1 pubkeys/0 valid/1

Functions:
Public h/1 sign/2 crypt/2 scrypt/2 pair/2 update/3
Private inv/1 pw/1

Analysis:
sign(X,Y) -> Y
crypt(X,Y) ? inv(X) -> Y
scrypt(X,Y) ? X -> Y
pair(X,Y) -> X,Y
update(X,Y,Z) -> X,Y,Z

Transactions:
passwordGenD(A:dishonest)
  send pw(A).

pubkeysGen()
  new PK
  insert PK pubkeys
  send PK.

updateKeyPw(A:honest,PK:value)
  PK in pubkeys
  new NPK
  insert NPK ring'(A)
  send NPK
  send crypt(PK,update(A,NPK,pw(A))).

updateKeyServerPw(A:agent,PK:value,NPK:value)
  receive crypt(PK,update(A,NPK,pw(A)))
  PK in pubkeys
  NPK notin pubkeys
  NPK notin seen(_)
  insert NPK valid(A)
  insert NPK seen(A).

authAttack2(A:honest,PK:value)
  receive inv(PK)
  PK in valid(A)
  attack.
\<close>


subsection \<open>Proof of security \<close>
protocol_model_setup spm: keyserver2
compute_fixpoint keyserver2_protocol keyserver2_fixpoint
protocol_security_proof ssp: keyserver2


subsection \<open>The generated theorems and definitions\<close>
thm ssp.protocol_secure

thm keyserver2_enum_consts.nchotomy
thm keyserver2_sets.nchotomy
thm keyserver2_fun.nchotomy
thm keyserver2_atom.nchotomy
thm keyserver2_arity.simps
thm keyserver2_public.simps
thm keyserver2_\<Gamma>.simps
thm keyserver2_Ana.simps

thm keyserver2_transaction_passwordGenD_def
thm keyserver2_transaction_pubkeysGen_def
thm keyserver2_transaction_updateKeyPw_def
thm keyserver2_transaction_updateKeyServerPw_def
thm keyserver2_transaction_authAttack2_def
thm keyserver2_protocol_def

thm keyserver2_fixpoint_def

end
