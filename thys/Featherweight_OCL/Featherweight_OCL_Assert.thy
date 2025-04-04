(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Real.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

theory Featherweight_OCL_Assert
  imports Main
  keywords "Assert" :: thy_decl
       and "Assert_local" :: thy_decl
begin

(*<*)
section\<open>Miscelleaneous: ML assertions\<close>

text\<open>We introduce here a new command \emph{Assert} similar as \emph{value} for proving
 that the given term in argument is a true proposition. The difference with \emph{value} is that
\emph{Assert} fails if the normal form of the term evaluated is not equal to @{term True}. 
Moreover, in case \emph{value} could not normalize the given term, as another strategy of reduction
 we try to prove it with a single ``simp'' tactic.\<close>

ML\<open>
fun disp_msg title msg status = title ^ ": '" ^ msg ^ "' " ^ status

fun lemma msg specification_theorem concl in_local thy =
  SOME
    (in_local (fn lthy =>
           specification_theorem Thm.theoremK NONE (K I) Binding.empty_atts [] [] 
             (Element.Shows [(Binding.empty_atts, [(concl lthy, [])])])
             false lthy
        |> Proof.global_terminal_proof
             ((Method.Combinator ( Method.no_combinator_info
                                 , Method.Then
                                 , [Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac ctxt 1))]),
               (Position.none, Position.none)), NONE))
              thy)
  handle ERROR s =>
    (warning s; writeln (disp_msg "KO" msg "failed to normalize"); NONE)

fun outer_syntax_command command_spec theory in_local =
  Outer_Syntax.command command_spec "assert that the given specification is true"
    (Parse.term >> (fn elems_concl => theory (fn thy =>
      case
        lemma "nbe" (Specification.theorem true)
          (fn lthy => 
            let val expr = Nbe.dynamic_value lthy (Syntax.read_term lthy elems_concl)
                val thy = Proof_Context.theory_of lthy
                open HOLogic in
            if Sign.typ_equiv thy (fastype_of expr, @{typ "prop"}) then
              expr
            else mk_Trueprop (mk_eq (@{term "True"}, expr))
            end)
          in_local
          thy
      of  NONE => 
            let val attr_simp = "simp" in
            case lemma attr_simp (Specification.theorem_cmd true) (K elems_concl) in_local thy of
               NONE => raise (ERROR "Assertion failed")
             | SOME thy => 
                (writeln (disp_msg "OK" "simp" "finished the normalization");
                 thy)
            end
        | SOME thy => thy)))

val () = outer_syntax_command @{command_keyword Assert} Toplevel.theory Named_Target.theory_map
val () = outer_syntax_command @{command_keyword Assert_local} (Toplevel.local_theory NONE NONE) I
\<close>
(*>*)

end
