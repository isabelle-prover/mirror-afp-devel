(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
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
(* $Id:$ *)

chapter AFP

session Meta_Isabelle (AFP) = HOL +
  description {* Meta_Isabelle *}
  options [timeout = 600]
  theories [document = false]
    "~~/src/HOL/Library/Code_Char"
    "isabelle_home/src/HOL/Isabelle_Main0"
    "isabelle_home/src/HOL/Isabelle_Main1"
  theories
    "meta_isabelle/Parser_Pure"
    "meta_isabelle/Meta_Isabelle"
    "meta_isabelle/Printer_Isabelle"
  document_files
    "root.bib"
    "root.tex"

session Isabelle_Meta_Model (AFP) = Meta_Isabelle +
  description {* Toy_Example *}
  options [timeout = 600]
  theories [document = false]
    "~~/src/HOL/Library/List_lexord"
    "~~/src/HOL/Library/RBT"
    "isabelle_home/src/HOL/Isabelle_Main2"
    "toy_example/embedding/Printer"
  theories
    "toy_example/embedding/Generator_static"
    "toy_example/embedding/Generator_dynamic"
    "toy_example/generator/Design_deep"
    "toy_example/generator/Design_shallow"
    "toy_example/document_generated/Design_generated_generated"
    "document/Rail"
  document_files
    "root.bib"
    "root.tex"
