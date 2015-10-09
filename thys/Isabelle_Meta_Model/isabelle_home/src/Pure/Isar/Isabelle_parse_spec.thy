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

chapter{* Part ... *}

theory Isabelle_parse_spec
  imports Main
begin

ML{* 
structure Isabelle_Parse_Spec =
struct
(*  Title:      Pure/Isar/parse_spec.ML
    Author:     Makarius

Parsers for complex specifications.
*)
  val spec = Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche;
  
  val alt_specs =
    Parse.enum1 "|"
      (spec --| Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|")));
  
  val where_alt_specs = Parse.where_ |-- Parse.!!! alt_specs;

  val constdef = Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche);
end
*}

end
