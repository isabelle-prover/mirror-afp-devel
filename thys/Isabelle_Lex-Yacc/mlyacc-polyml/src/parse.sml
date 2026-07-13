(* Modified by Achim D. Brucker to work "in-memory" for improved Isabelle/PIDE integration. *)
(* Modified by Vesa Karvonen on 2007-12-18.
 * Create line directives in output.
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

functor ParseGenParserFun(structure Header : HEADER
                          structure Parser : ARG_PARSER
                            where type pos = Header.pos
                          sharing type Parser.result = Header.parseResult
                          sharing type Parser.arg = Header.inputSource =
                                          Parser.lexarg
                         ) : PARSE_GEN_PARSER =

 struct
      structure Header = Header
      val parse = fn position_map => fn spec =>
          let
              val spec_ref = ref spec
              val read_fn = fn i =>
                  let val current = !spec_ref
                      val len = String.size current
                      val take = Int.min(i, len)
                      val result = String.substring(current, 0, take)
                      val _ = spec_ref := String.extract(current, take, NONE)
                  in result end
              val source = Header.newSource("",TextIO.stdIn,TextIO.stdOut)
              val error = fn (s : string,left_pos:Header.pos,right_pos) =>
                              Header.error (left_pos, SOME right_pos) s
              val stream =  Parser.makeLexer read_fn source
              val (result,_) = (Header.text := nil;
                                Parser.parse(15,stream,error,source))
           in (result,source)
           end
  end;
