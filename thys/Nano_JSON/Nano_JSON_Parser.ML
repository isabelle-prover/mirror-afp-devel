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

structure Nano_Json_Parser : NANO_JSON_PARSER  = struct 
    open Nano_Json_Type 
    open Nano_Json_Lexer

    fun show [] = "end of input"
      | show (tok :: _) = T.string_of_T tok

    val parse_error = error

    fun parseNumber digits =
        let open Char

            fun okExpDigits [] = false
              | okExpDigits (c :: []) = isDigit c
              | okExpDigits (c :: cs) = isDigit c andalso okExpDigits cs

            fun okExponent [] = false
              | okExponent (#"+" :: cs) = okExpDigits cs
              | okExponent (#"-" :: cs) = okExpDigits cs
              | okExponent cc = okExpDigits cc

            fun okFracTrailing [] = true
              | okFracTrailing (c :: cs) =
                (isDigit c andalso okFracTrailing cs) orelse
                (c = #"e" andalso okExponent cs)

            fun okFraction [] = false
              | okFraction (c :: cs) =
                isDigit c andalso okFracTrailing cs

            fun okPosTrailing [] = true
              | okPosTrailing (#"." :: cs) = okFraction cs
              | okPosTrailing (#"e" :: cs) = okExponent cs
              | okPosTrailing (c :: cs) =
                isDigit c andalso okPosTrailing cs
                                                      
            fun okPositive [] = false
              | okPositive (#"0" :: []) = true
              | okPositive (#"0" :: #"." :: cs) = okFraction cs
              | okPositive (#"0" :: #"e" :: cs) = okExponent cs
              | okPositive (#"0" :: _) = false
              | okPositive (c :: cs) = isDigit c andalso okPosTrailing cs
                    
            fun okNumber (#"-" :: cs) = okPositive cs
              | okNumber cc = okPositive cc
            fun getPositive (#"-" :: cs) = cs
              | getPositive  cc = cc

        in
            if okNumber digits then
              if List.all (Char.isDigit) (getPositive digits)
              then   (case Int.fromString (String.implode digits) of
                     NONE => parse_error "Number out of range"
                   | SOME i =>  INTEGER i)
              else   (case IEEEReal.fromString (String.implode digits) of
                     NONE => parse_error "Number out of range"
                   | SOME r => REAL r) 
            else parse_error ("Invalid number \"" ^ (String.implode digits) ^ "\"")
        end
                                     
    fun parseObject (T.CURLY_R :: xs) =  (OBJECT [], xs)
      | parseObject tokens =
        let fun parsePair (T.STRING key :: T.COLON :: xs) = let 
                    val (j, xs) = parseTokens xs
                in
                    ((key, j), xs)
                end
              | parsePair other =
                parse_error("Object key/value pair expected around \"" ^
                       show other ^ "\"")
            fun parseObject' _ [] = parse_error "End of input during object"
              | parseObject' acc tokens =
                case parsePair tokens of
                    (pair, T.COMMA :: xs) =>
                    parseObject' (pair :: acc) xs
                  | (pair, T.CURLY_R :: xs) =>
                    (OBJECT (rev (pair :: acc)), xs)
                  | (_, _) =>parse_error "Expected , or } after object element"
        in
            parseObject' [] tokens
        end

    and parseArray (T.SQUARE_R :: xs) =  (ARRAY [], xs)
      | parseArray tokens =
        let fun parseArray' _ [] = error "End of input during array"
              | parseArray' acc tokens =
                case parseTokens tokens of
                    (j, T.COMMA :: xs) => parseArray' (j :: acc) xs
                  | (j, T.SQUARE_R :: xs) => (ARRAY (rev (j :: acc)), xs)
                  | (_, _) => error "Expected , or ] after array element"
        in
            parseArray' [] tokens
        end

    and parseTokens [] = parse_error "Value expected"
      | parseTokens (tok :: xs) =
        (case tok of
             T.NUMBER d => (NUMBER ((parseNumber d)), xs)
           | T.STRING s => (STRING s, xs)
           | T.BOOL b   => (BOOL b, xs)
           | T.NULL     => (NULL, xs)
           | T.CURLY_L  => parseObject xs
           | T.SQUARE_L => parseArray xs
           | _ => parse_error ("Unexpected token " ^ T.string_of_T tok ^
                         " before " ^ show xs))
                                   
    fun json_of_string str = case parseTokens (Nano_Json_Lexer.tokenize_string str) of
                            (value, []) =>  value
                          | (_, _) => parse_error "Extra data after input"
    fun term_of_json_string verbose strT numT = (term_of_json verbose strT numT) o json_of_string

    fun checkReal thy = SOME (Thm.global_ctyp_of thy  HOLogic.realT)
                        handle ERROR _  => NONE (* Undeclared type constructor: "Real.real" *) 

    fun numT thy = case Config.get_global thy json_num_type of 
                     "int"  => @{typ \<open>int\<close>} 
                   | "nat"  => @{typ \<open>nat\<close>} 
                   | "real" =>  ( case checkReal thy of 
                                    SOME _ => HOLogic.realT
                                  | NONE   => error ("Using 'real' requires the import of the theory 'Main_Complex' ('Real')."))
                   | "string" =>  @{typ \<open>string\<close>} 
                   | "String.literal" => @{typ \<open>String.literal\<close>}
                   | "" => ( case checkReal thy of 
                               SOME _ => HOLogic.realT
                             | NONE   => @{typ \<open>int\<close>})
               | _ => error (String.concat ["Only 'nat', 'int', 'real', 'string', and 'String.literal' are supported for numbers, got '",
                                            Config.get_global thy json_num_type, "'"]) 

    fun stringT thy = case Config.get_global thy json_string_type of 
                        "" => @{typ \<open>string\<close>}
                      | "string" =>  @{typ \<open>string\<close>} 
                      | "String.literal" => @{typ \<open>String.literal\<close>}
                      | _ => error (String.concat ["Only 'string' and 'String.literal' are supported for strings, got '",
                                            Config.get_global thy json_string_type, "'"]) 

end

