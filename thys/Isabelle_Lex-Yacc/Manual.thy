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
(*<*)
theory Manual
  imports LexYacc Examples
keywords
  "simple_calc" :: diag
begin
(*>*)


text \<open>
\maketitle

\begin{abstract}\footnotesize
  Developing concrete syntax and parsers for Domain-Specific Languages (DSLs) within interactive 
  theorem provers, such as Isabelle, is a common task. Isabelle supports this through rich, yet 
  often brittle to configure, mixfix annotations and syntax translations. Moreover, Isabelle 
  provides parser combinators that can be used to build parsers for the content of cartouches. 
  An alternative to the latter are traditional parser generators, e.g., Lex and Yacc, that take a 
  formal grammar description as input and generate a parser.

  Traditionally, the use of parser generators for defining DSLs in Isabelle relies on invoking the 
  lexer and parser as external tools, often modifying the generated source code, and importing the 
  generated files. This requires users to manage complex external preprocessing toolchains.

  In this AFP entry, we address this challenge by providing a native integration of standard 
  ML-Lex and ML-Yacc into Isabelle/HOL. In more detail, we introduce an Isar-level interface, 
  @{command "ml_lex_yacc"}, that allows users to write lexical and grammatical specifications 
  directly within theory files. The framework compiles these specifications into Standard ML 
  structures on-the-fly, links them, and loads them into the current theory context. Moreover, the 
  integration automatically hooks into Isabelle’s Prover IDE (PIDE), empowering users to provide 
  real-time syntax highlighting, semantic tooltips, and precise error localization for their custom 
  languages.

  \<^medskip>\<^noindent>\<^bold>\<open>Key words:\<close> Isabelle/ML, Isabelle/PIDE, ML-Lex, ML-Yacc, Parser Generators

\end{abstract}
\clearpage
\tableofcontents
\clearpage
\<close>

section \<open>Introduction\<close>
text\<open>
  Developing concrete syntax and, hence, parsers for Domain-Specific Languages (DSLs) within 
  interactive theorem provers, such as Isabelle, is a common task. Isabelle supports this already 
  through various mechanisms such as:

  \<^item> Isabelle's mixfix annotations~\<^cite>\<open>"wenzel:isabelleisar"\<close> that allow us to define custom 
    concrete syntax for constants. For instance, if we use the @{command definition} command to 
    introduce a new constant, we can immediately assign a syntactic representation to it:%
    @{theory_text[display]\<open>      definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool"  (infixl "\<oplus>" 60) where
      "xor A B \<equiv> (A \<and> \<not> B) \<or> (\<not> A \<and> B)"\<close>}
  \<^item> Isabelle's syntax translations~\<^cite>\<open>"wenzel:isabelleisar"\<close> provide support 
    syntactic rewrite rules on term-representations, e.g.:%
    @{theory_text[display]\<open>      syntax 
        "_list" :: "args \<Rightarrow> 'a list" (\<open>(\<open>indent=1 notation=\<open>mixfix list enumeration\<close>\<close>[_])\<close>)
      syntax_consts  "_list" \<rightleftharpoons> Cons
      translations "[x, xs]" \<rightleftharpoons> "x#[xs]"
                       "[x]" \<rightleftharpoons> "x#[]"\<close>}
  \<^item> Isabelle's native ML-structures @{ML_structure "Scan"} and @{ML_structure "Parse"} implement 
    functional parser combinators~\<^cite>\<open>"wenzel:isabelleisar"\<close>. They are highly composable, 
    naturally handle context-dependent grammars, and allow dynamic parser construction. 

These mechanisms have the advantage that they are deeply integrated into the PIDE 
Framework~\<^cite>\<open>"wenzel:asynchronous:2014"\<close> in general and, in particular, 
Isabelle/jEdit~\<^cite>\<open>"wenzel:isabellejedit"\<close>. On the downside, Isabelle's mixfix notation and syntax translation 
can be brittle to configure and, moreover, share the ``syntactic universe'' with HOL, i.e., the 
syntax of the DSL needs to be disjoint from the already defined HOL syntax or one needs to overload 
syntactic constants (which can be brittle in itself). While parser combinators are powerful and 
flexible, they can, sometimes, be slow. 
In contrast, traditional lexer and parser generators, such as ML-Lex~\<^cite>\<open>"appel.ea:lexical:1994"\<close> 
and ML-Yacc~\<^cite>\<open>"tarditi.ea:ml-yacc:2000"\<close>, trade the flexibility of parser combinators 
for efficiency.

Using ML-Lex and ML-Yacc in the context of Isabelle is nothing new.  Prominent examples include:

  \<^item> The \<^emph>\<open>TPTP Parser\<close> (part of the Isabelle distribution)~\<^cite>\<open>"sultana:isabelletptp:2013"\<close>, which 
    is used for parsing the Thousands of Problems for Theorem Provers (TPTP) format. This is a critical 
    piece of infrastructure that allows Isabelle's automated reasoning tools to read and write 
    problem files. Technically, the TPTP Parser is built by executing 
    ML-Lex and ML-Yacc manually as external tools, manually adapting the generated files, which 
    are then loaded via the standard @{command "ML_file"}. A similar approach is also used by the 
    AFP entry \<^emph>\<open>Automated Stateful Protocol Verification (PSPSP)\<close>~\<^cite>\<open>"hess.ea:automated:2020" and "hess.ea:pspsp:2025"\<close>, 
    which uses ML-Lex and ML-Yacc generated parsing for security protocol specifications and their
    (often very large) fixed-points. 
  \<^item> \<^emph>\<open>AutoCorres2\<close>~\<^cite>\<open>"brecknell.ea:autocorres2:2024"\<close>, which uses ML-Lex and ML-Yacc generated 
    parsing for translating C code into the Simpl~\<^cite>\<open>"schirmer:sequential:2008"\<close> language for the 
    verification of low-level systems code (like the seL4 microkernel~\<^cite>\<open>"klein.ea:sel4:2009"\<close>).
    Technically, the C parsing component of AutoCorres also provides an integration of ML-Lex 
    and ML-Yacc providing the commands  \<^theory_text>\<open>mllex\<close> and  \<^theory_text>\<open>mlyacc\<close>. These commands read the lex and yacc
    specifications from an external file and invoke ml-lex and ml-yacc on them, which also generate
    external files on the physical file system. The generated files are modified ``on-the-fly'' 
    using the \<^verbatim>\<open>sed\<close> utility. This requires write access to the directory in which the files
    of the AutoCorres2 AFP entry are stored and, moreover, external file operations in Isabelle 
    need to be implemented carefully to avoid race conditions during concurrent operations. 
  \<^item> \<^emph>\<open>Isabelle/C\<close>~\<^cite>\<open>"tuong.ea:deeply:2019" and "tuong.ea:isabellec:2019"\<close> provides a deep integration of C11 syntax into 
    the Isabelle/PIDE document model, allowing for semantic annotations (comments containing HOL 
    assertions) directly inside C code. Technically, it relies on ML-Lex and ML-Yacc style grammars
    (originally developed for Happy~\<^cite>\<open>"marlow.ea:happy:1997"\<close>, a parser generator for Haskell) 
    that are heavily modified (and, therefore likely hard to maintain) to support syntax-highlighting 
    and semantic annotations.  

All of these integrations are focused on one specific use case and, except for Isabelle/C, do not 
support the error reporting, syntax-highlighting, and annotation infrastructure provided by 
PIDE in general and, in particular, Isabelle/jEdit. In contrast, we provide a highly reusable 
native integration of  ML-Lex~\<^cite>\<open>"appel.ea:lexical:1994"\<close> and 
ML-Yacc~\<^cite>\<open>"tarditi.ea:ml-yacc:2000"\<close> into Isabelle/HOL.\<^footnote>\<open>We started our work with the port of ML-Yacc and ML-Lex to Poly/ML, which are 
available at \<^url>\<open>https://github.com/eldesh/mllex-polyml\<close> and \<^url>\<open>https://github.com/eldesh/mlyacc-polyml\<close>.\<close> 

From an end-user perspective, we provide a new Isar command @{command "ml_lex_yacc"}, that allows 
users to write lexical and grammatical specifications directly within theory files. Generated 
lexers and parsers can support syntax highlighting and PIDE-style error reporting. 
The generated parser is directly reflected into 
the current theory context. This allows, for instance, using ML-Lex/ML-Yacc parsers as first-class
front ends for deeply embedded languages or within Isabelle/ML for the development of backend tools
(see \autoref{sec:examples} for an overview of the examples provided as part of this AFP entry).
Moreover, compared to standard ML-Lex and ML-Yacc, the generated parsers support, out-of-the-box,
syntax-highlighting, PIDE-style error reporting, and annotations within PIDE. Moreover, in most 
applications, the code for linking the lexer and parser is also automatically generated. 

From an Isabelle system-developer's perspective, we modified ML-Lex and ML-Yacc to work ``in memory'', 
i.e., avoiding the need for access to the physical file system completely and, therefore, minimizing 
the risk of race conditions. Furthermore, we provide an extended library that provides support 
for Isabelle's @{ML_type "Position.T"} type and also supports the generation of code linking the 
lexer and the parser. 

Notably, the integration of ML-Lex and ML-Yacc into Isabelle has been used in teaching a compiler construction 
module at Université Paris-Saclay/PolyTech~\<^cite>\<open>"brucker.ea:isabelle:2026"\<close>. Moreover, the 
development version of PSPSP~\<^cite>\<open>"hess.ea:automated:2020" and "hess.ea:pspsp:2025"\<close> has already been 
ported to this integrated framework.  

The rest of the manual is structured as follows: we start by showing how to implement a simple 
calculator (the ``Hello World'' example of parsing) in \autoref{sec:first-steps}. We then explain 
the new @{command "ml_lex_yacc"} in detail (\autoref{sec:command}), followed by revising  
the calculator in ``expert mode'' (\autoref{sec:expert}). Finally, we provide an overview
of the examples that are part of this AFP entry (\autoref{sec:examples}). 
\<close>

section\<open>First Steps: A Simple Calculator\<close>text\<open>\label{sec:first-steps}\<close>

text \<open>
  In this section, we present the ``Hello World!'' of parser generators: a calculator. This 
  example is taken directly from the ML-Lex/Yacc manuals~\<^cite>\<open>"appel.ea:lexical:1994" and "tarditi.ea:ml-yacc:2000"\<close>. 
  Hence, we recommend consulting them while working through this manual. 
\<close>

subsection\<open>The Lex/Yacc Specification\<close>
text\<open>
  Let us start with a brief recap of the high-level structure of ML-Lex and ML-Yacc specifications.
  Each of them consists of three parts: user declarations, definitions, and rules. When 
  ML-Lex and ML-Yacc specifications are stored in external files, these three parts are 
  separated by \<^verbatim>\<open>%%\<close>, i.e., a typical ML-Lex specification file is structured as follows:
  @{verbatim[display]\<open>    ML-Lex user declarations
    %%
    ML-Lex definitions
    %%
    ML-Lex rules\<close>}
  ML-Yacc files are structured similarly. We put every part into their own cartouche, as part of 
  a new Isar command @{command ml_lex_yacc}:\<close>

ml_lex_yacc "Calc" where
  lex_user_declarations\<open>\<close>
  lex_definitions\<open>
    alpha=[A-Za-z];
    digit=[0-9];
    ws = [\ \t\r];
  \<close>
  lex_rules\<open>
    \n       => (lex());
    {ws}+    => (lex());

    {digit}+ => (tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));

    "+"      => (tok (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
    ";"      => (tok (yypos, yytext, Markup.delimiter, "SEMI", "", Tokens.SEMI));

    .        => (lex());
  \<close>
  and yacc_user_declarations\<open>
    fun lookup "bogus" = 10000
      | lookup s = 0
  \<close> 
  yacc_definitions\<open>
    %eop EOF SEMI

    %left PLUS

    %term NUM of int | PLUS | SEMI | EOF
    %nonterm EXP of int | START of int option

    %noshift EOF
  \<close>
  yacc_rules\<open>
    START : EXP (SOME EXP)
          | (NONE)
    EXP : NUM             (NUM)
        | EXP PLUS EXP    (EXP1+EXP2)
\<close>

(*<*)ML\<open>open Isabelle_lex_yacc\<close>(*>*)

text \<open>
  Inside your \<open>lex_rules\<close> section, you should use the globally provided \<^ML>\<open>tok\<close> and \<^ML>\<open>tok_val\<close> 
  functions to emit tokens. These functions automatically register Isabelle markups for syntax 
  highlighting:

  \<^item> The function @{ML \<open>tok\<close>} is used for valueless tokens (like keywords and symbols): 
    @{ML[display]\<open>tok: int * string * Markup.T * string * string * (Position.T * Position.T -> 'a) -> 'a\<close>}
    This function takes six arguments. The first two are the \<open>yypos\<close> and \<open>yytext\<close> variables provided
    by the ML-Lex/Yacc tools. The next three arguments are PIDE-specific:

      \<^item> the markup that should be used in syntax highlighting (as defined in the ML structure
        @{ML_structure \<open>Markup\<close>}, e.g., @{ML\<open>Markup.keyword1\<close>}).
      \<^item> the information that should be displayed in the ``type'' part of the PIDE tooltip.
      \<^item> the information that should be displayed in the ``sort'' part of the PIDE tooltip.

    The final argument is the token parsed. For example:
    
    \<open>tok (yypos, yytext, Markup.keyword2, "Type Hint", "Sort Hint", Tokens.PLUS)\<close>

  \<^item> The function @{ML \<open>tok_val\<close>} is used for tokens that carry semantic values (like integers or identifiers):
     @{ML[display]\<open>tok_val : int * string * Markup.T * string * string * ('a * Position.T * Position.T -> 'b) * 'a -> 'b\<close>}
    It takes the same parameters (in the same order) as the @{ML\<open>tok\<close>} function plus one additional 
    argument, the value. For example: 

    \<open>tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext))\<close>
\<close>


text\<open>
Furthermore, the ML-Lex/Yacc for Isabelle framework automatically:
  \<^enum> Injects standard aliases and PIDE-reporting functions (like \<^ML>\<open>Isabelle_lex_yacc.tok\<close> and 
   \<^ML>\<open>Isabelle_lex_yacc.tok_val\<close>) via the \<^ML_structure>\<open>Isabelle_lex_yacc\<close> environment (as discussed
   previously).
  \<^enum> Provides the standard eof token definition.
  \<^enum> Generates the ML-Lex \<open>%header\<close> and ML-Yacc \<open>%name\<close> and \<open>%pos\<close> directives (which should be 
    omitted).
  \<^enum> Automatically applies the Join functor to fuse the Lexer and Parser components.
  \<^enum> Exposes a unified structure, based on the name provided to the @{command ml_lex_yacc} command. 

In this ``standard mode'', the aim is to minimize boilerplate and handle the tricky wiring of the 
lexer, parser, and Isabelle PIDE infrastructure automatically.
\<close>

subsection\<open>The Generated ML API\<close>
text \<open>
  The @{command ml_lex_yacc} generates the lexer and parser, as well as the necessary glue code for 
  linking them. Ultimately, it produces a unified ML structure named after your parser 
  (e.g., \<^ML_structure>\<open>Calc\<close>). The most important automatically generated function is:

  @{ML [display]\<open>Calc.parse_source: Proof.context -> Input.source -> int option\<close>}

  where the return type (here: @{ML_type \<open>int option\<close>}) matches the \<open>START\<close> nonterminal. 
\<close>

text\<open>
  You can use it directly in a custom Isar command:
\<close>

ML \<open>
  fun run_calc source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val res = Calc.parse_source ctxt source
      val _ = writeln (case res of SOME v => Int.toString v 
                                 | NONE => "No result")
    in thy end

  val _ = Outer_Syntax.command @{command_keyword "simple_calc"}
        "A simple inline calculator" 
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (run_calc source)))
\<close>

text\<open>
  We can now run simple calculations directly in Isabelle: 
\<close>

simple_calc\<open>21+21\<close> \<comment>\<open>Prints 42 in Isabelle's Output panel\<close>

text\<open>Note that the theory @{theory "Isabelle_Lex-Yacc.Calc"} contains an extended version of this 
simple calculator.\<close>

section\<open>Defining Lex/Yacc Specifications\<close>text\<open>\label{sec:command}\<close>

text \<open>

  The theory @{theory "Isabelle_Lex-Yacc.LexYacc"} (which also is the main entry point for the Isabelle 
  Lex/Yacc framework) provides @{command "ml_lex_yacc"} command provides an integrated, Isar-level 
  interface for defining and generating Standard ML parsers using ML-Lex and ML-Yacc directly within 
  Isabelle theories. It processes lexical and grammatical specifications, compiles them into SML 
  structures, and loads them into the current Isabelle theory context. Its general syntax is as follows:

  @{rail \<open>
    @@{command ml_lex_yacc} ('[' options ']')? name \<newline> 'where'
      lex_spec 'and' yacc_spec
    ;
    options: ('verbose' | 'lex_only' | 'yacc_only' | 'expert' | 'no_linking' | 'no_reflect') + ','
    ;
    lex_spec: ('lex_user_declarations' text)?
              'lex_definitions'  \<newline> text
              'lex_rules' text
    ;
    yacc_spec: ('yacc_user_declarations' text)?
               'yacc_definitions'  \<newline> text
               'yacc_rules' text
  \<close>}

  \<^item> \<^emph>\<open>name\<close>: Specifies the name of the parser. By default, it is also used as a prefix for the 
    generated SML structures. For example, providing the name "MyLang" will generate underlying 
    ML structures like \<open>MyLangLex\<close>, \<open>MyLangLrVals\<close>, and a unified \<open>MyLangParser\<close>. In expert mode 
    (see below), the SML structures will be named based on the lex and yacc directives that are 
    part of the lex and yacc specifications (e.g., \<open>%name\<close>). 

  \<^item> \<^emph>\<open>options\<close>:
    \<^item> \<open>verbose\<close>: Instructs the underlying ML-Yacc/ML-Lex generator to output verbose
      information. Generated artifacts  (such as SML code or the automaton description) are stored
      for inspection in Isabelle's virtual file system. 
    \<^item> \<open>lex_only\<close>: Only process the ML-Lex part of the specification. Useful during development 
                  for faster turn-around times. This implies \<open>no_linking\<close> and \<open>no_reflect\<close>.
    \<^item> \<open>yacc_only\<close>: Only process the ML-Yacc part of the specification. Useful during development 
                  for faster turn-around times. This implies \<open>no_linking\<close> and \<open>no_reflect\<close>.
    \<^item> \<open>expert\<close>: Enables advanced/expert mode where the specified lex and yacc specifications are 
                passed unmodified to ML-Lex and ML-Yacc (except adding the \<open>%%\<close> separators between the three blocks 
                of each specification). Furthermore, automated linking is disabled in expert mode. 
    \<^item> \<open>no_linking\<close>: Skips the automatic generation of the boilerplate "linking" structure 
                (the code that normally joins the Lexer, ParserData, and LrVals together). This is useful 
                if you intend to manually wire the generated ML functor blocks together later.
    \<^item> \<open>no_reflect\<close>: Does not reflect the generated code into the Isabelle/ML environment. This 
                    implies \<open>no_linking\<close>.
  \<^item> The lex specification is broken into three parts. In the original lex specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking: 

    \<^item> \<open>lex_user_declarations\<close> (optional): An embedded ML source block containing user-level
      SML code (e.g., token type aliases, state variables, or helper functions). 

    \<^item> \<open>lex_definitions\<close>: The ML-Lex definitions, such as regular expression macros (e.g., 
      \<open>alpha=[A-Za-z];\<close>) and lexer state declarations (e.g., \<open>%s COMMENT;\<close>). Only in expert 
      mode, a  \<open>%header\<close> declaration should be provided; i.e., when porting an ML-Lex 
      specification, remove the \<open>%header\<close> declaration.
    \<^item> \<open>lex_rules\<close>: The ML-Lex scanning rules and their corresponding SML semantic actions. The 
      structure @{ML_structure\<open>Isabelle_lex_yacc\<close>} provides the utility functions @{ML \<open>tok\<close>}
      and  @{ML \<open>tok_val\<close>}.
      \<^item> The function @{ML \<open>tok\<close>} is used for valueless tokens (like keywords and symbols): 
        @{ML[display]\<open>tok: int * string * Markup.T * string * string * (Position.T * Position.T -> 'a) -> 'a\<close>}
        This function takes six arguments. The first two are the \<open>yypos\<close> and \<open>yytext\<close> variables provided
        by the ML-Lex/Yacc tools. The next three arguments are PIDE-specific:
    
          \<^item> the markup that should be used in syntax highlighting (as defined in the ML structure
            @{ML_structure \<open>Markup\<close>}, e.g., @{ML\<open>Markup.keyword1\<close>}).
          \<^item> the information that should be displayed in the ``type'' part of the PIDE tooltip.
          \<^item> the information that should be displayed in the ``sort'' part of the PIDE tooltip.
    
        The final argument is the token parsed. For example:
        
        \<open>tok (yypos, yytext, Markup.keyword2, "Type Hint", "Sort Hint", Tokens.PLUS)\<close>
    
      \<^item> The function @{ML \<open>tok_val\<close>} is used for tokens that carry semantic values (like integers or identifiers):
         @{ML[display]\<open>tok_val : int * string * Markup.T * string * string * ('a * Position.T * Position.T -> 'b) * 'a -> 'b\<close>}:
        It takes the same parameters (in the same order) as the @{ML\<open>tok\<close>} function plus one additional 
        argument, the value. For example: 
    
        \<open>tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext))\<close>

      Note that in expert mode, these functions need to be called using their fully qualified
      name (e.g., @{ML \<open>Isabelle_lex_yacc.tok\<close>}) or, alternatively, the  \<open>lex_user_declarations\<close>
      needs to include an \<open>open Isabelle_lex_yacc\<close> statement.  

  \<^item> The yacc specification is broken into three parts. In the original yacc specification, these 
    parts are separated by \<open>%%\<close> (which should be omitted here). Furthermore, by default no directives
    specifying functors or names should be included, as they break the automated linking: 

    \<^item> \<open>yacc_user_declarations\<close> (optional): An embedded ML source block containing user-level 
      SML code to be injected at the top of the generated parser. Useful for defining custom 
      datatypes or helper functions used in semantic actions.

    \<^item> \<open>yacc_definitions\<close>: A cartouche containing ML-Yacc definitions, including \<open>%term\<close> and 
      \<open>%nonterm\<close> declarations, associativity, and start symbols. Only in expert 
      mode, the \<open>%name\<close> and \<open>%pos\<close> declarations should be provided; i.e., when porting an ML-Yacc 
      specification, remove the \<open>%name\<close> and \<open>%pos\<close> declarations.

    \<^item> \<open>yacc_rules\<close>: A cartouche containing the ML-Yacc grammar productions (BNF format) and 
      their corresponding SML semantic actions.

Note that the generated code is reflected into the SML environment of Isabelle. Hence, if your 
specification uses ML code defined within an @{command "ML"}-environment (i.e., Isabelle/ML), 
it needs to be imported into SML using the @{command "SML_import"} command. For example:

@{theory_text[display]\<open>SML_import \<open>structure Datalog_AST = Datalog_AST\<close>\<close>}

The theory @{theory "Isabelle_Lex-Yacc.Datalog"} contains an example of using  ML code defined 
within an @{command "ML"}-environment.
\<close>
section \<open>Expert Mode: The Calculator Example Revisited\<close>text\<open>\label{sec:expert}\<close>

text \<open>
  When you invoke @{command ml_lex_yacc} with the \<open>[expert]\<close> option, the integration backs off 
  and expects you to write a fully compliant, standalone ML-Lex/ML-Yacc specification. In 
  particular: 

  \<^enum> No Hidden Inclusions: You must declare \<open>Tokens\<close>, \<open>lexresult\<close>, \<open>pos\<close>, and \<open>svalue\<close> manually 
    in \<open>lex_user_declarations\<close>.
  \<^enum> No Auto-Directives: You must manually provide the \<open>%header\<close> directive for Lex and the \<open>%name\<close> 
    and \<open>%pos\<close> directives for Yacc.
  \<^enum> No Auto-Linking: The framework will compile the \<open>.lex.sml\<close> and \<open>.grm.sml\<close> files into the ML 
    environment, but it will **not** generate the final parser structure or the \<open>parse_source\<close> 
    function. You must write the Join functor application yourself.
  \<^enum> No Default PIDE hooks: The \<^ML>\<open>Isabelle_lex_yacc.tok\<close> and \<^ML>\<open>Isabelle_lex_yacc.tok_val\<close> 
    helpers from \<^ML_structure>\<open>Isabelle_lex_yacc\<close> are not automatically imported. If you want 
    syntax highlighting, you must implement the position lookup and report logic yourself.

  This mode allows for easily using already existing ML-Lex and ML-Yacc specifications, as it is 
  only necessary to split them up into their three parts (and omitting the \<open>%%\<close> separators).

  Expert Mode is recommended when you have highly customized lexer states, require bespoke 
  error-correction strategies directly within the Lexer, or are porting legacy SML codebases where 
  the automatic Isabelle-specific wrappers conflict with existing user declarations. 

  The theory @{theory "Isabelle_Lex-Yacc.CalcExpert"} provides a complete example of the calculator
  in expert mode.
\<close> 


subsection\<open>Lex and Yacc Specification\<close>

text\<open>
  The following is a simplified version. In direct comparison to the 
  standard use cases (e.g., recall \autoref{sec:first-steps}), notice the explicit declarations 
  that (in this example) provide similar functionality to standard mode (e.g., position computations
  using the type @{ML_type "Position.T"}). 
\<close>

ml_lex_yacc [expert] "CalcExpert" where
lex_user_declarations\<open>
  structure Tokens = Tokens
  type pos = Position.T
  type svalue = Tokens.svalue
  type ('a,'b) token = ('a,'b) Tokens.token
  type lexresult = (svalue, pos) token
  
  fun eof () = Tokens.EOF(Position.none, Position.none)
  fun error' (e, p: Position.T, _) = ()   
  (* 
     You must implement your own `tok` and `tok_val` equivalent methods or 
     use the Isabelle_lex_yacc provided functions manually, if you want PIDE support here 
  *)
  \<close>
lex_definitions\<open>
  %header (functor CalcExpertLexFun(structure Tokens: CalcExpert_TOKENS));
  digit=[0-9];
\<close>
lex_rules\<open>
  {digit}+ => (Tokens.NUM(valOf (Int.fromString yytext), Position.none, Position.none));
  "+"      => (Tokens.PLUS(Position.none, Position.none));
  ";"      => (Tokens.SEMI(Position.none, Position.none));
  .        => (lex());
\<close>
and yacc_definitions\<open>
  %name CalcExpert
  %pos Position.T
  %eop EOF SEMI
  
  %left PLUS
  %term NUM of int | PLUS | SEMI | EOF
  %nonterm EXP of int | START of int option
  %noshift EOF
\<close>
yacc_rules\<open>
  START : EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | EXP PLUS EXP    (EXP1+EXP2)
\<close>

subsection\<open>Linking Expert Mode Output\<close>
text \<open>
  Because Expert Mode disables auto-linking, you must manually assemble the parser in an ML block. 
  This requires using the ML-Yacc Join functor:
\<close>

ML \<open>
structure CalcExpertParser =
struct
  structure CalcExpertLrVals =
    CalcExpertLrValsFun(structure Token = LrParser.Token)

  structure CalcExpertLex =
    CalcExpertLexFun(structure Tokens = CalcExpertLrVals.Tokens)

  structure Parser =
    Join(structure LrParser = LrParser
         structure ParserData = CalcExpertLrVals.ParserData
         structure Lex = CalcExpertLex)

  (* In a real implementation, you would write your own 
     `parse_source` here, handling the Lexer initialization 
      and the `Stream.get` loop. *)
end
\<close>

section\<open>Examples\<close>text\<open>\label{sec:examples}\<close>

text\<open>
  \begin{figure}
    \centering
    \includegraphics[height=.6\textheight, width=\textwidth, keepaspectratio]{session_graph}
    \caption{The Dependency Graph of the Isabelle Theories.\label{fig:session-graph}}
  \end{figure}
  To demonstrate the versatility of our Lex/Yacc framework for Isabelle, we provide several 
  examples (see \autoref{fig:session-graph} for the session graph, listing all provided examples, 
  i.e., the direct predecessors of @{theory "Isabelle_Lex-Yacc.Examples"}):

  \<^item> The theory @{theory "Isabelle_Lex-Yacc.Calc"} provides an example of a simple arithmetic expression
    evaluator (calculator) in standard mode. This example is a port of the calculator example provided
    by the ML-Yacc distribution. 
  \<^item> The theory @{theory "Isabelle_Lex-Yacc.CalcExpert"} provides an example of a simple arithmetic 
    expression evaluator (calculator) in expert mode. This example is a port of the calculator example 
    provided by the ML-Yacc distribution. 
  \<^item> The theory @{theory "Isabelle_Lex-Yacc.Pascal"} provides a simple parser for the Pascal programming
    language. This example is a port of the Pascal example provided by the ML-Yacc distribution. 
  \<^item> The theory @{theory "Isabelle_Lex-Yacc.Datalog"} provides an example of a Lex/Yacc parser used 
    as a front-end for a language (Datalog) that is deeply embedded into Isabelle/HOL. It shows how 
    
    \<^item> to interact with ML code (here: the ML datatype defining the abstract syntax tree of Datalog) 
      defined in an @{command "ML"}-environment during parsing, 
    \<^item> how to translate the parsed expression into HOL-terms, and
    \<^item> how to define an Isar command that parses Datalog and binds the generated HOL-term to a 
      logical constant (i.e., a domain-specific definition command). 
\<close>

(*<*)
end
(*>*)
