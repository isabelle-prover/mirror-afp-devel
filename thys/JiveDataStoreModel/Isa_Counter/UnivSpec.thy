(*  Title:       Jive Data and Store Model
    ID:          $Id: UnivSpec.thy,v 1.5 2008-10-07 14:07:44 fhaftmann Exp $
    Author:      Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

header {* The Universal Specification *}

theory UnivSpec imports JML  begin

text {* This theory contains the Isabelle formalization of the
program-dependent specification. This theory has to be provided by the user.
In later versions of Jive, one may be able to generate it from JML model
classes.
*}

constdefs
aCounter :: "Value \<Rightarrow> Store \<Rightarrow> JavaInt"

"aCounter x s == if x ~= nullV & (alive x s) & typeof x = CClassT CounterImpl then
  aI ( s@@(x..CounterImpl'value) )
 else undefined"

end
