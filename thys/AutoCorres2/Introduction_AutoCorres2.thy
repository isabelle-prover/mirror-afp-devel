(*<*)

(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Introduction_AutoCorres2
  imports Main

begin
(*>*)

chapter \<open>Introduction\<close>

text \<open>
AutoCorres2 is a tool to facilitate the verification of C programs within Isabelle \<^cite>\<open>LNCS2283\<close>.
It is a fork of AutoCorres: \<^url>\<open>https://trustworthy.systems/projects/OLD/autocorres/\<close>.
Here some quick links into the document:
\<^item> Quickstart guide for users (\autoref{chap:Quickstart}):
   \<^file>\<open>doc/quickstart/Chapter1_MinMax.thy\<close>
\<^item> Background information, internals and some history of AutoCorres (\autoref{chap:AutoCorresInfrastructure}):
   \<^file>\<open>doc/AutoCorresInfrastructure.thy\<close> 
\<^item> C-Parser
  \<^item> Some internals (\autoref{chap:CTranslationInfrastructure}):
   \<^file>\<open>c-parser/CTranslationInfrastructure.thy\<close> 
  \<^item> Original documentation (outdated) (\autoref{chap:strictc}):
   The supported subset of C is extended. Moreover, the C-parser is integrated into Isabelle/ML and
   no standalone C-parser is supplied. The description of the design principles is
   still valid:
   \<^file>\<open>c-parser/doc/ctranslation_body.tex\<close>
\<close>

(*<*)
end
(*>*)

text_raw \<open>\part{Library}\<close>