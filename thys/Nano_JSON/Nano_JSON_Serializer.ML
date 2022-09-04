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


structure Nano_Json_Serializer : NANO_JSON_SERIALIZER = struct
     open Nano_Json_Type 

    fun escapeJsonString s =
        let fun bs c = "\\"^(Char.toString c)
            fun escape #"\"" = bs #"\"" 
              | escape #"\\" = bs #"\\" 
              | escape #"\b" = bs #"b"
              | escape #"\f" = bs #"f"
              | escape #"\n" = bs #"n"
              | escape #"\r" = bs #"r"
              | escape #"\t" = bs #"t"
              | escape c = 
                let val ord = Char.ord c
                in
                    if ord < 0x20
                    then let val hex = Word.toString (Word.fromInt ord)
                             val prfx = if ord < 0x10 then "\\u000" else "\\u00"
                         in  
                             prfx^hex
                         end
                    else
                    Char.toString c
                end
        in
            String.concat (map escape (String.explode s))
        end

    fun serialize pretty json = let 
            val nl = if pretty = NONE then "" else "\n"
            fun indent' 0 = ""
              | indent' n = " "^(indent' (n-1)) 
            fun indent n = (case pretty of NONE => "" 
                                         | SOME n' => indent' (n+n'))
            fun serialize' _ (OBJECT []) = "{}"
              | serialize' _ (ARRAY []) = "[]"
              | serialize' n (OBJECT pp) = "{"^nl^(indent (n+1)) ^ String.concatWith
                                   (","^nl^(indent (n+1))) 
                                   (map (fn (key, value) =>
                                                serialize' (n+1) (STRING key) ^ ":" ^
                                                serialize' (n+1) value) pp) ^
                                   nl^(indent n)^"}"
              | serialize' n (ARRAY arr) = "["^nl^(indent (n+1)) ^ String.concatWith
                                           (","^nl^(indent (n+1)))
                                           (map (serialize' (n+1) ) arr) ^
                                   nl^(indent n)^"]"
              | serialize' _ (NUMBER (REAL n)) = String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode (IEEEReal.toString n)))
              | serialize' _ (NUMBER (INTEGER n)) = String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode (Int.toString n)))
              | serialize' _ (STRING s) = "\"" ^ escapeJsonString s ^ "\""
              | serialize' _ (BOOL b) = Bool.toString b
              | serialize' _ NULL = "null"
            
        in
            (serialize' 0 json)^nl
        end

    val serialize_json = serialize NONE
    val serialize_json_pretty = serialize (SOME 0)
    val serialize_term = (serialize NONE) o json_of_term
    val serialize_term_pretty = (serialize (SOME 0)) o json_of_term
end

