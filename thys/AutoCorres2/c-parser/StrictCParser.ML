(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

structure StrictCParser =
struct

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke ctxt lookahead source lexstream = let
  fun print_error (s, lpos, rpos) = Feedback.errorStr' ctxt (lpos, rpos, s)
in
  (#1 (StrictCParser.parse(lookahead, lexstream, print_error, (source, ctxt))), Feedback.get_num_errors_val ctxt)
end

fun single_shot s = let
  val m = Unsynchronized.ref s
in fn (n:int) => let 
     val r = !m
     val _ = m := "" 
   in r end
end
                 
local
  val lock = Thread.Mutex.mutex ();
in

fun SYNCHRONIZED name = Multithreading.synchronized name lock;

fun parse_raw ctxt docpp error_lookahead (includes : string list) path lines = let
  val cpped_lines = docpp {includes=includes,src_path=path, lines=lines}
  val fname = Path.file_name (Path.base path)
  val lexarg = StrictCLex.UserDeclarations.new_state ctxt fname
  val lexer = StrictCParser.makeLexer (single_shot (suffix "\n" (cat_lines cpped_lines))) lexarg
  val source = #source lexarg
  val result = invoke ctxt error_lookahead source lexer
  val included = SourceFile.get_included source
in
  (result, included)
end

fun parse ctxt docpp error_lookahead (includes : string list) path lines =
  SYNCHRONIZED "cparser" (fn () => parse_raw ctxt docpp error_lookahead (includes : string list) path lines)
end

end;
