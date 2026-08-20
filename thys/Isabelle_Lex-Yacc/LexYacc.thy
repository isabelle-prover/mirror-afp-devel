(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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

theory LexYacc
  imports 
  YaccLib
keywords "ml_lex_yacc" :: thy_decl
    and  "lex_user_declarations" "lex_definitions" "lex_rules" 
    "yacc_user_declarations" "yacc_definitions" "yacc_rules" :: quasi_command
begin 

SML_import \<open>val pide_error = error \<close>
SML_import \<open>val pide_warning = warning \<close>
SML_import \<open>val pide_writeln = writeln \<close>


section\<open>ML Lex\<close>
SML_file \<open>mllex-polyml/LexGen.sml\<close>
SML_export \<open>structure MlLexExe = struct val run = LexGen.lexGen end\<close> 



section\<open>ML Yacc\<close>

SML_file\<open>mlyacc-polyml/src/utils.sig\<close>
SML_file\<open>mlyacc-polyml/src/utils.sml\<close> 
SML_file\<open>mlyacc-polyml/src/sigs.sml\<close>  
SML_file\<open>mlyacc-polyml/src/verbose.sml\<close> 
SML_file\<open>mlyacc-polyml/src/coreutils.sml\<close> 
SML_file\<open>mlyacc-polyml/src/grammar.sml\<close> 
SML_file\<open>mlyacc-polyml/src/graph.sml\<close> 
SML_file\<open>mlyacc-polyml/src/hdr.sml\<close> 
SML_file\<open>mlyacc-polyml/src/lalr.sml\<close>  
SML_file\<open>mlyacc-polyml/src/absyn.sig\<close> 
SML_file\<open>mlyacc-polyml/src/absyn.sml\<close> 
SML_file\<open>mlyacc-polyml/src/core.sml\<close>  
SML_file\<open>mlyacc-polyml/src/look.sml\<close>
SML_file\<open>mlyacc-polyml/src/mklrtable.sml\<close> 
SML_file\<open>mlyacc-polyml/src/shrink.sml\<close>  
SML_file\<open>mlyacc-polyml/src/yacc.sml\<close>  
SML_file\<open>mlyacc-polyml/src/mkprstruct.sml\<close>  
SML_file\<open>mlyacc-polyml/src/parse.sml\<close> 

text\<open>Generated: \<close>
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.grm.sig\<close> 
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.grm.sml\<close>             
SML_file\<open>mlyacc-polyml/src/bootstrap/yacc.lex.sml\<close>     

text\<open>Final linking and export\<close>
SML_file\<open>mlyacc-polyml/src/link.sml\<close>
SML_export \<open>structure MlYaccExe = struct val run = ParseGen.parseGen end\<close> 


text\<open>Runtime Setup\<close>
SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
ML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close>
ML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close>





section\<open>Glue Layer\<close>
ML\<open>
signature ML_LEX_YACC_HIGHLIGHTER =
  sig
    val scan_lex_defs: Proof.context -> Input.source -> unit
    val scan_lex_rules: Proof.context -> Input.source -> unit
    val scan_yacc_defs: Proof.context -> Input.source -> unit
    val scan_yacc_rules: Proof.context -> Input.source -> unit
  end

structure MlLexYaccHighlighter:ML_LEX_YACC_HIGHLIGHTER = struct
  fun is_alnum s = 
    Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse s = "_" orelse s = "'"
  
  fun take_word [] acc = (rev acc, [])
    | take_word ((s, p) :: ss) acc =
        if is_alnum s then take_word ss ((s, p) :: acc)
        else (rev acc, (s, p) :: ss)

  fun report ctxt markup syms =
    List.app (fn (_, p) => Context_Position.report ctxt p markup) syms

  fun consume_comment [] acc = (rev acc, [])
    | consume_comment ((s1, p1) :: (s2, p2) :: rest) acc =
        if s1 = "*" andalso s2 = ")" then 
          (rev ((s2, p2) :: (s1, p1) :: acc), rest)
        else 
          consume_comment ((s2, p2) :: rest) ((s1, p1) :: acc)
    | consume_comment (x :: rest) acc = 
        consume_comment rest (x :: acc)

  fun consume_string [] acc = (rev acc, [])
    | consume_string ((s1, p1) :: rest) acc =
        if s1 = "\"" then 
          (rev ((s1, p1) :: acc), rest)
        else if s1 = "\\" andalso not (null rest) then
          consume_string (tl rest) (hd rest :: (s1, p1) :: acc)
        else 
          consume_string rest ((s1, p1) :: acc)

  (* Quick and dirty parser for  ML code inside Yacc/Lex rules. *)
  fun scan_sml_action _ _  [] = []
    | scan_sml_action ctxt depth ((s, p) :: ss) =
        if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
          let
            val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
            val _ = report ctxt Markup.comment comment_syms
          in 
            scan_sml_action ctxt depth rest 
          end
        else if s = "\"" then
          let
            val (str_syms, rest) = consume_string ss [(s, p)]
            val _ = report ctxt Markup.string str_syms
          in 
            scan_sml_action ctxt depth rest 
          end
        else if s = "(" then
          (Context_Position.report ctxt p Markup.delimiter; 
           scan_sml_action ctxt (depth + 1) ss)
        else if s = ")" then
          (Context_Position.report ctxt p Markup.delimiter;
           if depth = 1 then ss 
           else scan_sml_action ctxt (depth - 1) ss)
        else if s = "=" andalso not (null ss) andalso #1 (hd ss) = ">" then
          (report ctxt Markup.keyword2 [(s, p), hd ss];
           scan_sml_action ctxt depth (tl ss))
        else if member (op =) ["+", "-", "*", "/", ":", "|", ",", ";", ".", "[", "]", "=", "<", ">", "~"] s then
          (Context_Position.report ctxt p Markup.delimiter;
           scan_sml_action ctxt depth ss)
        else if is_alnum s then
          let
            val (word_syms, rest) = take_word ss [(s, p)]
            val word = String.concat (map #1 word_syms)
            val ml_kws = [
              "val", "fun", "let", "in", "end", "case", "of", "if", "then", "else", 
              "SOME", "NONE", "true", "false", "structure", "sig", "struct", "open", "type"
            ]
            val markup = if member (op =) ml_kws word then Markup.keyword2 else Markup.free
          in
            report ctxt markup word_syms;
            scan_sml_action ctxt depth rest
          end
        else 
          scan_sml_action ctxt depth ss

  fun scan_lex_defs ctxt source =
    let
      val syms = Input.source_explode source
      fun scan _ [] = ()
        | scan awaiting_sml ((s, p) :: ss) =
            if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan awaiting_sml rest 
              end
            else if s = "\"" then
              let
                val (str_syms, rest) = consume_string ss [(s, p)]
                val _ = report ctxt Markup.string str_syms
              in 
                scan awaiting_sml rest 
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
                
                val is_sml_trigger = member (op =) ["%header", "%arg"] word
                val is_kw = member (op =) [
                  "%header", "%s", "%S", "%arg", "%pos", "%pure", "%reject", "%count"
                ] word
                val markup = if is_kw then Markup.keyword1 else Markup.keyword3
              in
                Context_Position.report ctxt p markup;
                report ctxt markup word_syms;
                scan is_sml_trigger rest 
              end
            else if s = "(" then
              (Context_Position.report ctxt p Markup.delimiter;
               if awaiting_sml then
                 let
                   val remaining_stream = scan_sml_action ctxt 1 ss
                 in
                   scan false remaining_stream
                 end
               else
                 scan awaiting_sml ss)
            else if s = ")" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_sml ss)
            else if s = "=" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan false ss)
            else if member (op =) ["{", "}", "[", "]", ";", "+", "*", "?", "|", "\\", "^", "$", "."] s then
              (Context_Position.report ctxt p Markup.keyword3; 
               scan awaiting_sml ss)
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in 
                scan awaiting_sml rest 
              end
            else 
              scan awaiting_sml ss
    in 
      scan false syms 
    end

  fun scan_lex_rules ctxt source =
    let
      val syms = Input.source_explode source
      fun scan _ [] = ()
        | scan awaiting_action ((s, p) :: ss) =
            if s = "<" orelse s = ">" orelse s = "{" orelse s = "}" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_action ss)
            else if s = "\"" then
              let
                val (str_syms, rest) = consume_string ss [(s, p)]
                val _ = report ctxt Markup.string str_syms
              in 
                scan awaiting_action rest 
              end
            else if s = "=" andalso not (null ss) andalso #1 (hd ss) = ">" then
              (report ctxt Markup.keyword2 [(s, p), hd ss]; 
               scan true (tl ss))
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) <> "*" then
              (Context_Position.report ctxt p Markup.delimiter;
               if awaiting_action then
                 let
                   val remaining_stream = scan_sml_action ctxt 1 ss
                 in
                   scan false remaining_stream
                 end
               else
                 scan awaiting_action ss)
            else if s = ")" then
              (Context_Position.report ctxt p Markup.delimiter; 
               scan awaiting_action ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan awaiting_action rest 
              end
            else if member (op =) ["+", "*", "?", "|", "\\", "^", "$", "."] s then
              (Context_Position.report ctxt p Markup.keyword3; 
               scan awaiting_action ss)
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in 
                scan awaiting_action rest 
              end
            else 
              scan awaiting_action ss
    in 
      scan false syms 
    end

  fun scan_yacc_defs ctxt source =
    let
      val syms = Input.source_explode source
      
      fun scan [] = ()
        | scan ((s, p) :: ss) =
            if s = "|" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan rest 
              end
            else if s = "(" then
              let
                val _ = Context_Position.report ctxt p Markup.delimiter
                val remaining_stream = scan_sml_action ctxt 1 ss
              in
                scan remaining_stream
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
                val is_kw = member (op =) [
                  "%name", "%term", "%nonterm", "%pos", "%eop", "%pure", 
                  "%noshift", "%left", "%right", "%nonassoc", "%keyword", 
                  "%prefer", "%subst", "%header", "%verbose", "%value"
                ] word
                val markup = if is_kw then Markup.keyword1 else Markup.keyword3
              in
                Context_Position.report ctxt p markup;
                report ctxt markup word_syms;
                scan rest
              end
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val word = String.concat (map #1 word_syms)
                val markup = if word = "of" then Markup.keyword2 else Markup.free
              in
                report ctxt markup word_syms;
                scan rest
              end
            else 
              scan ss
    in 
      scan syms 
    end


  fun scan_yacc_rules ctxt source =
    let
      val syms = Input.source_explode source
      
      fun scan [] = ()
        | scan ((s, p) :: ss) =
            if s = ":" orelse s = "|" orelse s = ";" then
              (Context_Position.report ctxt p Markup.keyword2; 
               scan ss)
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) <> "*" then
              let
                val _ = Context_Position.report ctxt p Markup.delimiter
                val remaining_stream = scan_sml_action ctxt 1 ss
              in
                scan remaining_stream
              end
            else if s = "%" then
              let
                val (word_syms, rest) = take_word ss []
                val word = "%" ^ String.concat (map #1 word_syms)
              in
                if word = "%prec" then 
                  report ctxt Markup.keyword1 ((s, p) :: word_syms) 
                else ();
                scan rest
              end
            else if s = "(" andalso not (null ss) andalso #1 (hd ss) = "*" then
              let
                val (comment_syms, rest) = consume_comment (tl ss) [hd ss, (s, p)]
                val _ = report ctxt Markup.comment comment_syms
              in 
                scan rest 
              end
            else if is_alnum s then
              let
                val (word_syms, rest) = take_word ss [(s, p)]
                val _ = report ctxt Markup.free word_syms
              in
                scan rest
              end
            else 
              scan ss
    in 
      scan syms 
    end

end
\<close>
ML\<open>
structure MlLexYacc = struct

  fun generate verbose expert no_reflect no_linking yacc_only lex_only name lex_decl lex_defs lex_rules yacc_decl yacc_defs yacc_rules thy = 
      let
        fun trace s = if verbose then writeln s else ()
        val no_linking = if no_reflect orelse yacc_only orelse lex_only then true else no_linking 
        fun store show_msg ext data  =
          let
            val dir_name = "lex_yacc"
            fun path_of ext = (Path.make [dir_name, name^"."^ext])
            val _ = Export.export thy (Path.binding0 (path_of ext)) (Bytes.contents_blob (Bytes.string data))
          in
            if show_msg then writeln(Export.message thy (Path.make [dir_name])) else ()
          end
        val ctxt = Proof_Context.init_global thy

        val _ = Option.map ML_Lex.read_source lex_decl
        val _ = Option.map ML_Lex.read_source yacc_decl

        val _ = MlLexYaccHighlighter.scan_yacc_defs ctxt yacc_defs
        val _ = MlLexYaccHighlighter.scan_yacc_rules ctxt yacc_rules
        val _ = MlLexYaccHighlighter.scan_lex_defs ctxt lex_defs
        val _ = MlLexYaccHighlighter.scan_lex_rules ctxt lex_rules

        val lex_decl_syms = case lex_decl of NONE => [] | SOME l => Input.source_explode l
        val lex_syms = if expert
                       then (lex_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_rules)
                       else (Symbol_Pos.explode(Isabelle_lex_yacc.header()^"\n", Position.none))@
                            (lex_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Symbol_Pos.explode("%header (functor "^name^"LexFun(structure Tokens: "^name^"_TOKENS));\n", Position.none))@
                            (Input.source_explode lex_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode lex_rules)
        val lex_spec_string = Symbol_Pos.content lex_syms;
        val lex_pos_vec = Vector.fromList (map #2 lex_syms @ [Position.none]);
        fun lex_pos_map offset = Vector.sub (lex_pos_vec, Int.min (Int.max (0, offset), Vector.length lex_pos_vec - 1));
        val lex_sml = if yacc_only 
                      then let val _ = (trace "Skipping lex ...") in  "" end  
                      else let
                        val _ = trace "Running lex ... "
                        val _ = Isabelle_lex_yacc.reset()
                        val _ = if verbose then store true "lex" lex_spec_string else ()
                        val lex_sml = MlLexExe.run verbose (SOME lex_pos_map) lex_spec_string
                        val _ = Isabelle_lex_yacc.reset()  
                        val _ = trace "  Storing lex.sml ... "
                        val _ = if verbose then store false "lex.sml" lex_sml else ()
                      in
                        lex_sml 
                      end 


        val yacc_decl_syms = case yacc_decl of NONE => [] | SOME l => Input.source_explode l
        val yacc_syms = if expert
                       then (yacc_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_rules)
                       else (yacc_decl_syms)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Symbol_Pos.explode("%name "^name^"\n", Position.none))@
                            (Symbol_Pos.explode("%pos Position.T\n", Position.none))@
                            (Input.source_explode yacc_defs)@
                            (Symbol_Pos.explode("\n%%\n", Position.none))@
                            (Input.source_explode yacc_rules)
        val yacc_spec_string = Symbol_Pos.content yacc_syms;
        val yacc_pos_vec = Vector.fromList (map #2 yacc_syms @ [Position.none]);
        fun yacc_pos_map offset = Vector.sub (yacc_pos_vec, Int.min (Int.max (0, offset), Vector.length yacc_pos_vec - 1));

        val (yacc_sig, yacc_sml) = if lex_only 
                      then let val _ = (trace "Skipping yacc ...") in  ("", "") end  
                      else let
                        val _ = trace "Running yacc ... "
                        val _ = if verbose then store false "grm" yacc_spec_string else ()
                        val _ = Isabelle_lex_yacc.reset()
                  
                        val yacc_res = MlYaccExe.run verbose (SOME yacc_pos_map) yacc_spec_string
                        val _ = Isabelle_lex_yacc.reset()  
                        val yacc_sig = #sigs yacc_res
                        val yacc_sml = #ml yacc_res
                        val yacc_desc = #desc yacc_res
                        val _ = Isabelle_lex_yacc.reset()  
                        val _ = trace "  Storing grm.sml, grm.sig, and grm.desc ... "
                        val _ = if verbose then store false "grm.sml" yacc_sml else ()
                        val _ = if verbose then store false "grm.sig" yacc_sig else ()
                        val _ = if verbose then case yacc_desc of SOME data => store false "grm.desc" data | NONE => () else ()
                      in
                        (yacc_sig, yacc_sml)
                      end

        val thy' = if no_reflect  
                      then let val _ = (trace "Skipping reflection code into ML environment ...") in  thy end  
                      else let
                        val generated_code = yacc_sig^"\n\n"^lex_sml^"\n\n"^yacc_sml 
                
                        val _ = trace "Reflecting generated code ... "
                        val toks =
                          ML_Lex.read generated_code
                          |> map (fn Antiquote.Text tok => tok 
                                   | _ => error "Unexpected antiquote in generated code")
                        val flags: ML_Compiler.flags =
                           {environment = ML_Env.SML_export, redirect = false, verbose = false, catch_all = true,
                            debug = NONE, writeln = writeln, warning = warning}
                        val thy' = Context.theory_map (
                          ML_Context.exec (fn () => 
                            ML_Compiler.eval flags Position.none toks
                          )
                        ) thy
                      in
                        thy'
                      end
        val thy'' = if expert orelse no_linking 
                    then let val _ = trace "Skipping linking ... " in thy' end
                    else let 
                      val link_sml = Isabelle_lex_yacc.linker name
                      val _ = if verbose then store false "link.sml" link_sml else ()
                      val _ = trace "Linking ... "
                      val toks =
                        ML_Lex.read link_sml
                        |> map (fn Antiquote.Text tok => tok 
                                 | _ => error "Unexpected antiquote in generated code")
                      val flags: ML_Compiler.flags =
                         {environment = ML_Env.Isabelle, redirect = false, verbose = false, catch_all = true,
                          debug = NONE, writeln = writeln, warning = warning}
                    in
                      Context.theory_map (
                        ML_Context.exec (fn () => 
                          ML_Compiler.eval flags Position.none toks
                        )
                      ) thy'
                    end
      in
        thy''
      end;

end
\<close>

ML \<open>
local
  val parse_options =
    Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.list Parse.name --| \<^keyword>\<open>]\<close>) []

  (* Parser for the lex specification blocks *)
  val parse_lex =
    Scan.optional (\<^keyword>\<open>lex_user_declarations\<close> |-- Parse.ML_source >> SOME) NONE --
    (\<^keyword>\<open>lex_definitions\<close> |-- Parse.input Parse.cartouche) --
    (\<^keyword>\<open>lex_rules\<close> |-- Parse.input Parse.cartouche)

  (* Parser for the yacc specification blocks *)
  val parse_yacc =
    Scan.optional (\<^keyword>\<open>yacc_user_declarations\<close> |-- Parse.ML_source >> SOME) NONE --
    (\<^keyword>\<open>yacc_definitions\<close> |-- Parse.input Parse.cartouche) --
    (\<^keyword>\<open>yacc_rules\<close> |-- Parse.input Parse.cartouche)
in
  val _ = Outer_Syntax.command @{command_keyword "ml_lex_yacc"}
          "Generate and load SML parser based on lex/yacc specifications." 
        (
          (parse_options -- Parse.name --| \<^keyword>\<open>where\<close> -- 
           parse_lex --| \<^keyword>\<open>and\<close> -- 
           parse_yacc)
        >> (fn (((opts, name), ((lex_user, lex_defs), lex_rules)), ((yacc_user, yacc_defs), yacc_rules)) =>
            let
              val is_verbose = member (op =) opts "verbose"
              val is_expert = member (op =) opts "expert" 
              val no_linking = member (op =) opts "no_linking" 
              val no_reflect = member (op =) opts "no_reflect" 
              val yacc_only = member (op =) opts "yacc_only" 
              val lex_only = member (op =) opts "lex_only" 
            in
              Toplevel.theory (fn thy => 
                MlLexYacc.generate is_verbose is_expert no_reflect no_linking lex_only yacc_only name 
                  lex_user lex_defs lex_rules 
                  yacc_user yacc_defs yacc_rules thy)
            end)
        )
end
\<close>



end
