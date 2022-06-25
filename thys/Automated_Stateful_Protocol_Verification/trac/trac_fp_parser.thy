(*  Title:      trac_fp_parser.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Parser for Trac FP definitions\<close>
theory
  trac_fp_parser
  imports
    "trac_term"
begin

ML_file "trac_parser/trac_fp.grm.sig"
ML_file "trac_parser/trac_fp.lex.sml"
ML_file "trac_parser/trac_fp.grm.sml"

ML\<open>
structure TracFpParser : sig  
		   val parse_file: string -> (Trac_Term.Msg * (string * string) list) list
       val parse_str: string -> (Trac_Term.Msg * (string * string) list) list
end = 
struct

  open Trac_Term

  structure TracLrVals =
    TracLrValsFun(structure Token = LrParser.Token)

  structure TracLex =
    TracLexFun(structure Tokens = TracLrVals.Tokens)

  structure TracParser =
    Join(structure LrParser = LrParser
	 structure ParserData = TracLrVals.ParserData
	 structure Lex = TracLex)
  
  fun invoke lexstream =
      let fun print_error (s,i:(int * int * int),_) =
	      TextIO.output(TextIO.stdOut,
			    "Error, line .... " ^ (Int.toString (#1 i)) ^"."^(Int.toString (#2 i ))^ ", " ^ s ^ "\n")
       in TracParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
    val dummyEOF = TracLrVals.Tokens.EOF((0,0,0),(0,0,0))
    fun loop lexer =
      let 
        val _ = (TracLex.UserDeclarations.pos := (0,0,0);())
        val (res,lexer) = invoke lexer
        val (nextToken,lexer) = TracParser.Stream.get lexer
      in if TracParser.sameToken(nextToken,dummyEOF) then ((),res) else loop lexer end
  in #2(loop lexer)
  end

 fun parse_file tracFile = let
	     val infile = TextIO.openIn tracFile
	     val lexer = TracParser.makeLexer  (fn _ => case ((TextIO.inputLine) infile) of
                                                   SOME s => s
                                                 | NONE   => "")
     in
       parse_fp lexer
     end

 fun parse_str trac_fp_str = let  
       val parsed = Unsynchronized.ref false 
       fun input_string _  = if !parsed then "" else (parsed := true ;trac_fp_str)
	     val lexer = TracParser.makeLexer input_string
     in
       parse_fp lexer
     end
end
\<close>


end
