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


structure Nano_Json_Lexer : NANO_JSON_LEXER = struct
    structure T = struct
        datatype token = NUMBER of char list
                       | STRING of string
                       | BOOL of bool
                       | NULL
                       | CURLY_L
                       | CURLY_R
                       | SQUARE_L
                       | SQUARE_R
                       | COLON
                       | COMMA

        fun string_of_T t =
            case t of NUMBER digits => String.implode digits
                    | STRING s => s
                    | BOOL b => Bool.toString b
                    | NULL => "null"
                    | CURLY_L => "{"
                    | CURLY_R => "}"
                    | SQUARE_L => "["
                    | SQUARE_R => "]"
                    | COLON => ":"
                    | COMMA => ","
    end

    fun lexer_error pos text = error (text ^ " at character position " ^
                                Int.toString (pos - 1))
    fun token_error pos = lexer_error pos ("Unexpected token")

    fun bmp_to_utf8 cp = map (Char.chr o Word.toInt)
                         (if cp < 0wx80 
                          then [cp]
                          else if cp < 0wx800 
                               then [Word.orb(0wxc0, Word.>>(cp,0w6)), 
                                      Word.orb(0wx8, Word.andb (cp, 0wx3f))]
                               else if cp < 0wx10000 
                                    then [Word.orb(0wxe0,Word.>>(cp, 0w12)),
                                          Word.orb(0wx80, Word.andb(Word.>>(cp,0w6), 0wx3f)),
                                          Word.orb(0wx80,Word.andb(cp, 0wx3f))]
                                    else error ("Invalid BMP point  in bmp_to_utf8 " ^ (Word.toString cp)))

    fun lexNull pos acc (#"u" :: #"l" :: #"l" :: xs) =
        lex (pos + 3) (T.NULL :: acc) xs
      | lexNull pos _  _ = token_error pos

    and lexTrue pos acc (#"r" :: #"u" :: #"e" :: xs) =
        lex (pos + 3) (T.BOOL true :: acc) xs
      | lexTrue pos _ _ = token_error pos

    and lexFalse pos acc (#"a" :: #"l" :: #"s" :: #"e" :: xs) =
        lex (pos + 4) (T.BOOL false :: acc) xs
      | lexFalse pos _ _ = token_error pos

    and lexChar tok pos acc xs =
        lex pos (tok :: acc) xs
        
    and lexString pos acc cc =
        let datatype escaped = ESCAPED | NORMAL
            fun lexString' pos _ ESCAPED [] =
                lexer_error pos "End of input during escape sequence"
              | lexString' pos _ NORMAL [] = 
                lexer_error pos "End of input during string"
              | lexString' pos text ESCAPED (x :: xs) =
                let fun esc c = lexString' (pos + 1) (c :: text) NORMAL xs
                in case x of
                       #"\"" => esc x
                     | #"\\" => esc x
                     | #"/"  => esc x
                     | #"b"  => esc #"\b"
                     | #"f"  => esc #"\f"
                     | #"n"  => esc #"\n"
                     | #"r"  => esc #"\r"
                     | #"t"  => esc #"\t"
                     | _     => lexer_error pos ("Invalid escape \\" ^
                                           Char.toString x)
                end
              | lexString' pos text NORMAL (#"\\" :: #"u" ::a::b::c::d:: xs) =
                if List.all Char.isHexDigit [a,b,c,d]
                then case Word.fromString ("0wx" ^ (String.implode [a,b,c,d])) of
                         SOME w => (let val utf = rev (bmp_to_utf8 w) in
                                        lexString' (pos + 6) (utf @ text)
                                                   NORMAL xs
                                    end
                                    handle Fail err => lexer_error pos err)
                       | NONE => lexer_error pos "Invalid Unicode BMP escape sequence"
                else lexer_error pos "Invalid Unicode BMP escape sequence"
              | lexString' pos text NORMAL (x :: xs) =
                if Char.ord x < 0x20
                then lexer_error pos "Invalid unescaped control character"
                else
                    case x of
                        #"\"" => (rev text, xs, pos + 1)
                      | #"\\" => lexString' (pos + 1) text ESCAPED xs
                      | _     => lexString' (pos + 1) (x :: text) NORMAL xs
          val (text, rest, newpos) = lexString' pos [] NORMAL cc
        in
                lex newpos (T.STRING (String.implode text) :: acc) rest
        end

    and lexNumber firstChar pos acc cc =
        let val valid = String.explode ".+-e"
            fun lexNumber' pos digits [] = (rev digits, [], pos)
              | lexNumber' pos digits (x :: xs) =
                if x = #"E" then lexNumber' (pos + 1) (#"e" :: digits) xs
                else if Char.isDigit x orelse List.exists (fn c => x = c) valid
                then lexNumber' (pos + 1) (x :: digits) xs
                else (rev digits, x :: xs, pos)
            val (digits, rest, newpos) =
                lexNumber' (pos - 1) [] (firstChar :: cc)
        in
            case digits of
                [] => token_error pos
              | _ => lex newpos (T.NUMBER digits :: acc) rest
        end
                                           
    and lex _ acc [] = rev acc
      | lex pos acc (x::xs) = 
        (case x of
             #" "  => lex
           | #"\t" => lex
           | #"\n" => lex
           | #"\r" => lex
           | #"{"  => lexChar T.CURLY_L
           | #"}"  => lexChar T.CURLY_R
           | #"["  => lexChar T.SQUARE_L
           | #"]"  => lexChar T.SQUARE_R
           | #":"  => lexChar T.COLON
           | #","  => lexChar T.COMMA
           | #"\"" => lexString
           | #"t"  => lexTrue
           | #"f"  => lexFalse
           | #"n"  => lexNull
           | x     => lexNumber x) (pos + 1) acc xs

    fun tokenize_string str = lex 1 [] (String.explode str)
end

