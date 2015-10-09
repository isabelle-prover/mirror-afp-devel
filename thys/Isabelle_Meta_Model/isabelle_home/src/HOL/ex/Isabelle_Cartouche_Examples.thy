(*****************************************************************************
 * ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.
 * 
 * Copyright (c) 1986-2015 University of Cambridge,
 *                         Technische Universitaet Muenchen,
 *                         and contributors.
 *               2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
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

chapter{* Part ... *}

theory Isabelle_Cartouche_Examples
imports Main
begin

ML {*
(*  Title:      HOL/ex/Cartouche_Examples.thy
    Author:     Makarius
*)
  local
    val mk_nib =
      Syntax.const o Lexicon.mark_const o
        fst o Term.dest_Const o HOLogic.mk_nibble;

    fun mk_char f_char (s, _) accu =
        fold
          (fn c => fn (accu, l) =>
            (f_char c accu,
               Syntax.const @{const_syntax Cons}
             $ (Syntax.const @{const_syntax Char} $ mk_nib (c div 16) $ mk_nib (c mod 16))
             $ l))
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string _ accu [] = (accu, Const (@{const_syntax Nil}, @{typ "char list"}))
      | mk_string f_char accu (s :: ss) = mk_char f_char s (mk_string f_char accu ss);

  in
    fun string_tr f f_char accu content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_string f_char accu (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
*}

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  ("_")

end
