(***********************************************************************************
 * Copyright (c) 2022 Achim D. Brucker
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>The Nano JSON Manual\<close>

theory 
  Nano_JSON_Manual
imports 
  Nano_JSON_Query
begin

subsection\<open>Isabelle/HOL\<close>
text\<open>
  On the Isabelle/HOL level, we provide three new commands for working with JSON formatted
  data.
\<close>

paragraph\<open>@{command "JSON"}.\<close> text\<open> For defining JSON data within HOL terms,
we provide the following command:
  \<^rail>\<open> @@{command "JSON"} json_data \<close>
where \emph{json-data} is a cartouche containing the JSON data.
\<close>

paragraph\<open>@{command "JSON_file"}.\<close> text\<open> For reading JSON data from an external 
file, we provide the command 
 \<^rail>\<open> @@{command "JSON_file"} json_filename 'defining' json_def \<close>
where \emph{json-filename} is the path (file name) of the JSON file that should be read
and  \emph{json-def} is the name the HOL definition representing the JSON data is bound to.\<close>

paragraph\<open>@{command "JSON_export"}.\<close> text\<open> For serializing (exporting) JSON 
encoded data, we provide the command
 \<^rail>\<open> @@{command "JSON_export"} json_def  ('file' json_filename)? \<close>
where \emph{json-def} is the definition of the JSON data that should be exported. Optionally
a file name (\emph{json-filename}) can be provided. If a file name is provided, it is used
for storing the serialized data in Isabelle's virtual file system. If no file name is provided, 
the serialized data is printed in Isabelle's output window.
\<close>

paragraph\<open>Configuration.\<close> text \<open>We provide three configuration attributes:
\<^item> The attribute @{attribute "JSON_num_type"} (default @{type "int"} allows for configuring the 
  HOL-type used representing JSON numerals.
\<^item> The attribute @{attribute "JSON_string_type"}  (default @{type "string"}) allows for configuring 
  the HOL-type used representing JSON string.
\<^item> The attribute @{attribute "JSON_verbose"} (default: false) allows for enabling warnings during the
  JSON processing.
\<close>

subsection\<open>Isabelle/ML\<close>
text\<open>
  We refer users who want to use or extend Nano JSON on the Isabelle/ML level to the ML signatures
  shown in the implementation chapter, i.e., \autoref{ch:implementation}. 
\<close>
end
