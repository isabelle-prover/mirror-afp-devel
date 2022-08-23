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

section\<open>Examples\<close>

theory
  Example
imports 
  Nano_JSON_Main
begin

text\<open>
  In this theory, we illustrate various small examples of importing or exporting
  of JSON data from Isabelle/HOL. The examples in this theory do not use the
  type @{term "real"} to avoid the need to depend on the theory
  ``Complex\_Main``.
\<close>

JSON \<open>
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
}, "flag":true, "number": -42}
\<close> defining example_default
thm example_default_def       
JSON_export example_default
JSON_export example_default file example_default

declare [[JSON_string_type=string, JSON_num_type = nat]]
JSON \<open>
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
}, "flag":true, "number": 42}
\<close> defining example_string_nat 
thm example_string_nat_def
JSON_export example_string_nat
JSON_export example_string_nat file example_string_nat

declare [[JSON_string_type=string, JSON_num_type = int]]
JSON \<open>
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
\<close> defining example_string_int

thm example_string_int_def
JSON_export example_string_int
JSON_export example_string_int file example_string_int

declare [[JSON_string_type=String.literal, JSON_num_type = int]]
JSON \<open>
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
\<close> defining example_literal_int
thm example_literal_int_def
JSON_export example_literal_int
JSON_export example_literal_int file example_literal_int


declare [[JSON_string_type=string, JSON_num_type = string]]
JSON \<open>
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
}, "flag":true, "number":-42}
\<close> defining example_string_string
thm example_string_string_def
JSON_export example_string_string
JSON_export example_string_string file example_string_string

declare [[JSON_string_type=String.literal, JSON_num_type = String.literal]]
JSON \<open>
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
thm example_literal_literal_def
JSON_export example_literal_literal
JSON_export example_literal_literal file example_literal_literal

text\<open>xxxx\<close>



text\<open>
  Using the top level Isar commands defined in the last section, we can now easily define
  JSON-like data: 
\<close>

JSON \<open>
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
\<close> defining example02


thm example02_def

declare [[JSON_string_type = String.literal]]
JSON \<open>
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
\<close> defining example02'

thm example02'_def


ML\<open> 
@{term \<open>JSON\<open>{"number":31}\<close>\<close>}
\<close>


text\<open>
  Moreover, we can import JSON from external files:
\<close>

lemma "example01 = example03"
  by(simp add: example01_def example03_def)


end
