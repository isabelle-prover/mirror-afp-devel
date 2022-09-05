(***********************************************************************************
 * Copyright (c) 2019-2022 Achim D. Brucker
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


section\<open>Query Infrastructure\<close>

theory 
  Nano_JSON_Query
imports 
  Nano_JSON
begin
text\<open>
  In this theory, we define various functions for working with JSON data, i.e.,
  the data types defined in the theory @{theory "Nano_JSON.Nano_JSON"}. These
  query functions are useful for building more complex functionality of JSON
  encoded data. One could think of them as something like jq
  (\<^url>\<open>https://stedolan.github.io/jq/\<close>) for Isabelle. 
\<close>

subsubsection\<open>Isabelle/ML\<close>
ML\<open>
signature NANO_JSON_QUERY = sig
    val nj_filter: 
        string -> Nano_Json_Type.json 
                   -> (string list * Nano_Json_Type.json) list
    val nj_filterp: 
        string list -> Nano_Json_Type.json 
                    -> (string list * Nano_Json_Type.json) list
    val nj_filter_obj: 
        (string * Nano_Json_Type.json option) -> Nano_Json_Type.json 
                    -> (string list * Nano_Json_Type.json) list
    val nj_filterp_obj: 
        (string list * Nano_Json_Type.json option) -> Nano_Json_Type.json 
                    -> (string list * Nano_Json_Type.json) list
    val nj_first_value_of: 
        string -> Nano_Json_Type.json 
                    -> Nano_Json_Type.json option
    val nj_first_value_ofp:  
        string list -> Nano_Json_Type.json 
                    -> Nano_Json_Type.json option
    val nj_update: 
        (Nano_Json_Type.json -> Nano_Json_Type.json) -> string -> Nano_Json_Type.json 
                    -> Nano_Json_Type.json
    val nj_updatep: 
        (Nano_Json_Type.json -> Nano_Json_Type.json) -> string list -> Nano_Json_Type.json 
                    -> Nano_Json_Type.json
    val nj_convert: 
        (Nano_Json_Type.json -> 'a) -> string -> Nano_Json_Type.json 
                    -> 'a list
    val nj_string_of: 
        Nano_Json_Type.json 
                    -> string option  
    val nj_string_of': 
        string -> Nano_Json_Type.json -> string

    val nj_integer_of: 
        Nano_Json_Type.json -> int option  
    val nj_integer_of': 
        int -> Nano_Json_Type.json -> int
    val nj_real_of: 
        Nano_Json_Type.json -> IEEEReal.decimal_approx option  
    val nj_real_of': 
        IEEEReal.decimal_approx -> Nano_Json_Type.json -> IEEEReal.decimal_approx
    val nj_bool_of: 
        Nano_Json_Type.json -> bool option  
    val nj_bool_of': 
        bool -> Nano_Json_Type.json -> bool
  end

\<close>

ML_file Nano_JSON_Query.ML
text\<open>
  The file @{file \<open>Nano_JSON_Query.ML\<close>} provides the Isabelle/ML structure
  @{ML_structure \<open>Nano_Json_Query:NANO_JSON_QUERY\<close>}.
\<close>

subsubsection\<open>Isabelle/HOL\<close>

fun nj_filter':: \<open>'a \<Rightarrow> 'a list \<times> ('a, 'b) json \<Rightarrow> ('a list \<times> ('a, 'b) json) list\<close>
  where
    \<open>nj_filter' key (prfx, OBJECT json) = ((map (\<lambda> (k,v). (prfx@[k],v)) (filter (\<lambda> (k,_). key = k) json) )
                        @ (List.concat (map (nj_filter' key) (map (\<lambda> (k,v). (prfx,v)) json)))
                         )\<close> 
  | \<open>nj_filter' key (prfx, ARRAY json) = (List.concat (map (nj_filter' key) (map (\<lambda> v. (prfx,v)) json)))\<close> 
  | \<open>nj_filter' _ (_, NUMBER _) = []\<close>
  | \<open>nj_filter' _ (_, STRING _) = []\<close>
  | \<open>nj_filter' _ (_, BOOL _) = []\<close>
  | \<open>nj_filter' _ (_, NULL) = []\<close>

definition nj_filter::\<open>'a \<Rightarrow> ('a, 'b) json \<Rightarrow> ('a list \<times> ('a, 'b) json) list\<close> where
          \<open>nj_filter key json = nj_filter' key ([],json)\<close>

fun nj_update :: \<open>(('a, 'b) json \<Rightarrow> ('a, 'b) json) \<Rightarrow> 'a \<Rightarrow> ('a, 'b) json \<Rightarrow> ('a, 'b) json\<close>
  where 
    \<open>nj_update f key (OBJECT kjson) =  OBJECT (map (\<lambda> (k,json). if k = key 
                                                                then (k, f json) 
                                                                else (k, nj_update f key json)) kjson)\<close> 
  | \<open>nj_update f key (ARRAY json) = ARRAY (map (nj_update f key) json)\<close>
  | \<open>nj_update _ _ (NUMBER n) = NUMBER n\<close>
  | \<open>nj_update _ _ (STRING s) = STRING s\<close>
  | \<open>nj_update _ _ (BOOL b) = BOOL b\<close>
  | \<open>nj_update _ _ NULL = NULL\<close>


paragraph\<open>Examples.\<close>
text\<open>The following illustrates a simple example of the @{term "nj_filter"} function.\<close>

declare [[JSON_string_type=String.literal]]

JSON   \<open>
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}, "flag":true, "number":42}
\<close> defining example_literal_literal

value \<open>nj_filter (STR ''onclick'') example_literal_literal\<close>

end
