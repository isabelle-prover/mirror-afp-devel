(*****************************************************************************
 * ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.
 *
 * Copyright (c) 1986-2015 University of Cambridge,
 *                         Technische Universitaet Muenchen,
 *                         and contributors.
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id:$ *)

chapter{* Part ... *}

theory Isabelle_metis_tactic
imports Main
begin

section{* ... *}

ML{*
structure Isabelle_Metis_Tactic =
struct
(*  Title:      HOL/Tools/Metis/metis_tactic.ML
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)
open ATP_Proof_Reconstruct

(* Whenever "X" has schematic type variables, we treat "using X by metis" as "by (metis X)" to
   prevent "Subgoal.FOCUS" from freezing the type variables. We don't do it for nonschematic facts
   "X" because this breaks a few proofs (in the rare and subtle case where a proof relied on
   extensionality not being applied) and brings few benefits. *)
val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o Thm.prop_of

fun metis_method ((override_type_encs, lam_trans), ths) ctxt facts =
  let val (schem_facts, nonschem_facts) = List.partition has_tvar facts in
    HEADGOAL (Method.insert_tac nonschem_facts THEN'
      CHANGED_PROP o Metis_Tactic.metis_tac (these override_type_encs)
        (the_default default_metis_lam_trans lam_trans) ctxt (schem_facts @ ths))
  end
end
*}

end
