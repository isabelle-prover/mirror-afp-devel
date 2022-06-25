(*  Title:      trac_protocol_parser.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Parser for the Trac Format\<close>
theory
  trac_protocol_parser
  imports
    "trac_term"
begin

ML_file "trac_parser/trac_protocol.grm.sig"
ML_file "trac_parser/trac_protocol.lex.sml"
ML_file "trac_parser/trac_protocol.grm.sml"

ML\<open>
structure TracProtocolParser : sig  
		   val parse_file: string -> TracProtocol.protocol
       val parse_str:  string -> TracProtocol.protocol
end = 
struct

  structure TracLrVals =
    TracTransactionLrValsFun(structure Token = LrParser.Token)

  structure TracLex =
    TracTransactionLexFun(structure Tokens = TracLrVals.Tokens)

  structure TracParser =
    Join(structure LrParser = LrParser
	 structure ParserData = TracLrVals.ParserData
	 structure Lex = TracLex)
  
  fun invoke lexstream =
      let fun print_error (s,i:(int * int * int),_) =
	      error("Error, line .... " ^ (Int.toString (#1 i)) ^"."^(Int.toString (#2 i ))^ ", " ^ s ^ "\n")
       in TracParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
	  val dummyEOF = TracLrVals.Tokens.EOF((0,0,0),(0,0,0))
	  fun loop lexer =
	      let 
		  val _ = (TracLex.UserDeclarations.pos := (0,0,0);())
		  val (res,lexer) = invoke lexer
		  val (nextToken,lexer) = TracParser.Stream.get lexer
	       in if TracParser.sameToken(nextToken,dummyEOF) then ((),res)
		  else loop lexer
	      end
       in  (#2(loop lexer))
      end

 fun parse_file tracFile = 
     let
	        val infile = TextIO.openIn tracFile
	        val lexer = TracParser.makeLexer  (fn _ => case ((TextIO.inputLine) infile) of
                                                           SOME s => s
                                                          | NONE   => "")
     in
       parse_fp lexer
      handle LrParser.ParseError => TracProtocol.empty 
     end

 fun parse_str str = 
     let
          val parsed = Unsynchronized.ref false 
          fun input_string _  = if !parsed then "" else (parsed := true ;str)
	        val lexer = TracParser.makeLexer input_string
     in
       parse_fp lexer
      handle LrParser.ParseError => TracProtocol.empty 
     end

end
\<close>


end
