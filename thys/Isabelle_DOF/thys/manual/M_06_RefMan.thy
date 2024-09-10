(*************************************************************************
 * Copyright (C) 
 *               2019-2022 University of Exeter 
 *               2018-2022 University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory 
  "M_06_RefMan"
  imports 
    "M_05_Proofs_Ontologies" 
begin

declare_reference*[infrastructure::technical]

(*>*)

chapter*[isadof_ontologies::technical]\<open>Ontologies and their Development\<close>

text\<open>
  In this chapter, we explain the concepts of \<^isadof> in a more systematic way, and give
  guidelines for modeling new ontologies, present underlying concepts for a mapping to a
  representation, and give hints for the development of new document templates. 

  \<^isadof> is embedded in the underlying generic document model of Isabelle as described in
  @{scholarly_paper.introduction \<open>dof\<close>}. Recall that the document language can be extended dynamically, \<^ie>, new
  \<^emph>\<open>user-defined\<close> can be introduced at run-time.  This is similar to the definition of new functions 
  in an interpreter. \<^isadof> as a system plugin provides a number of new command definitions in 
  Isabelle's document model.

  \<^isadof> consists consists basically of five components:
  \<^item> the \<^emph>\<open>core\<close> in \<^theory>\<open>Isabelle_DOF.Isa_DOF\<close> providing the \<^emph>\<open>ontology definition language\<close>
    (ODL) which allow for the definitions of document-classes
    and necessary datatypes,
  \<^item> the \<^emph>\<open>core\<close> also provides an own \<^emph>\<open>family of commands\<close> such as 
    \<^boxed_theory_text>\<open>text*\<close>, \<^boxed_theory_text>\<open>ML*\<close>, \<^boxed_theory_text>\<open>value*\<close> , \<^etc>.;
    They allow for the annotation of document-elements with meta-information defined in ODL,
  \<^item> the \<^isadof> library \<^theory>\<open>Isabelle_DOF.Isa_COL\<close> providing
    ontological basic (documents) concepts \<^bindex>\<open>ontology\<close> as well as supporting infrastructure, 
  \<^item> an infrastructure for ontology-specific \<^emph>\<open>layout definitions\<close>, exploiting this meta-information, 
    and 
  \<^item> an infrastructure for generic \<^emph>\<open>layout definitions\<close> for documents following, \<^eg>, the format 
    guidelines of publishers or standardization bodies. 
\<close>
text\<open>
  Similarly to Isabelle, which is based on a core logic \<^theory>\<open>Pure\<close> and then extended by libraries
  to major systems like \<^verbatim>\<open>HOL\<close>, \<^isadof> has a generic core infrastructure \<^dof> and then presents 
  itself to users via major library extensions,  which add domain-specific  system-extensions. 
  Ontologies\<^bindex>\<open>ontology\<close> in \<^isadof> are not just a sequence of descriptions in \<^isadof>'s Ontology 
  Definition Language (ODL)\<^bindex>\<open>ODL\<close>. Rather, they are themselves presented as integrated 
  sources that provide textual descriptions, abbreviations, macro-support and even ML-code. 
  Conceptually, the library of \<^isadof> is currently organized as follows\<^footnote>\<open>The \<^emph>\<open>technical\<close> 
  organization is slightly different and shown in 
  @{technical (unchecked) \<open>infrastructure\<close>}.\<close>
  \<^bindex>\<open>COL\<close>\<^bindex>\<open>scholarly\_paper\<close>\<^bindex>\<open>technical\_report\<close> \<^bindex>\<open>CENELEC\<close>: 
%
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.1 COL\DTcomment{The Common Ontology Library}.
.2 scholarly\_paper\DTcomment{Scientific Papers}.
.3 technical\_report\DTcomment{Extended Papers, Technical Reports}.
.4 CENELEC\_50128\DTcomment{Papers according to CENELEC\_50128}.
.4 CC\_v3\_1\_R5\DTcomment{Papers according to Common Criteria}. 
.4 \ldots.
}
\end{minipage}
\end{center}\<close>

 These libraries not only provide ontological concepts, but also syntactic sugar in Isabelle's
 command language Isar that is of major importance for users (and may be felt as \<^isadof> key 
 features by many authors). In reality, 
 they are derived concepts from more generic ones; for example, the commands
 \<^boxed_theory_text>\<open>title*\<close>, \<^boxed_theory_text>\<open>section*\<close>,  \<^boxed_theory_text>\<open>subsection*\<close>, \<^etc>,
 are in reality a kind of macros for \<^boxed_theory_text>\<open>text*[<label>::title]...\<close>,
 \<^boxed_theory_text>\<open>text*[<label>::section]...\<close>, respectively.
 These example commands are defined in \<^verbatim>\<open>COL\<close> (the common ontology library).

 As mentioned earlier, our ontology framework is currently particularly geared towards 
 \<^emph>\<open>document\<close> editing, structuring and presentation (future applications might be advanced
 "knowledge-based" search procedures as well as tool interaction). For this reason, ontologies
 are coupled with \<^emph>\<open>layout definitions\<close> allowing an automatic mapping of an integrated
 source into \<^LaTeX> and finally \<^pdf>. The mapping of an ontology to a specific representation
 in \<^LaTeX> is steered via associated  \<^LaTeX> style files which were included during Isabelle's
 document generation process. This mapping is potentially a one-to-many mapping;
 this implies a certain technical organization and some resulting restrictions 
 described in @{technical (unchecked) \<open>infrastructure\<close>} in more detail.
\<close>

section\<open>The Ontology Definition Language (ODL)\<close>
text\<open>
 ODL shares some similarities with meta-modeling languages such as UML class 
 models: It builds upon concepts like class, inheritance, class-instances, attributes, references 
 to instances, and class-invariants. Some concepts like  advanced type-checking, referencing to 
 formal entities of Isabelle, and monitors are due to its specific application in the 
 Isabelle context. Conceptually, ontologies specified in ODL consist of:
    \<^item> \<^emph>\<open>document classes\<close> (\<^boxed_theory_text>\<open>doc_class\<close>) \<^index>\<open>doc\_class\<close> that describe concepts,
      the keyword (\<^boxed_theory_text>\<open>onto_class\<close>) \<^index>\<open>onto\_class\<close> is syntactically equivalent,
    \<^item> an optional document base class expressing single inheritance  class extensions,
      restricting the class-hierarchy basically to a tree,
    \<^item> \<^emph>\<open>attributes\<close> specific to document classes, where
      \<^item> attributes are HOL-typed,
      \<^item> attributes of instances of document elements are mutable,
      \<^item> attributes can refer to other document classes, thus, document
        classes must also be HOL-types (such attributes are called  \<^emph>\<open>links\<close>),
      \<^item> attribute values were denoted by HOL-terms,
    \<^item> a special link, the reference to a super-class, establishes an
      \<^emph>\<open>is-a\<close> relation between classes,
    \<^item> classes may refer to other classes via a regular expression in an
      \<^emph>\<open>accepts\<close> clause, or via a list in a \<^emph>\<open>rejects\<close> clause,
    \<^item> attributes may have default values in order to facilitate notation.

\<^boxed_theory_text>\<open>doc_class\<close>'es and \<^boxed_theory_text>\<open>onto_class\<close>'es respectively, have a semantics,
\<^ie>, a logical representation as extensible records in HOL (\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>, 
pp. 11.6); there are therefore amenable to logical reasoning.
\<close>

text\<open>
  The \<^isadof> ontology specification language consists basically of a notation for document classes, 
  where the attributes were typed with HOL-types and can be instantiated by HOL-terms, \<^ie>, 
  the actual parsers and type-checkers of the Isabelle system were reused. This has the particular 
  advantage that \<^isadof> commands can be arbitrarily mixed with Isabelle/HOL commands providing the 
  machinery for type declarations and term specifications such
  as enumerations. In particular, document class definitions provide:
  \<^item> a HOL-type for each document class as well as inheritance, 
  \<^item> support for attributes with HOL-types and optional default values,
  \<^item> support for overriding of attribute defaults but not overloading, and
  \<^item> text-elements annotated with document classes; they are mutable 
    instances of document classes.
\<close>

text\<open>
  Attributes referring to other ontological concepts are called \<^emph>\<open>links\<close>. The HOL-types inside the 
  document specification language support built-in types for Isabelle/HOL \<^boxed_theory_text>\<open>typ\<close>'s,  
  \<^boxed_theory_text>\<open>term\<close>'s, and \<^boxed_theory_text>\<open>thm\<close>'s reflecting internal Isabelle's  internal 
  types for these entities; when denoted in HOL-terms to instantiate an attribute, for example, 
  there is a  specific syntax (called \<^emph>\<open>term antiquotations\<close>) that is checked by 
  \<^isadof> for consistency.

  Document classes\<^bindex>\<open>document class\<close>\<^index>\<open>class!document@see document class\<close> support 
  \<^boxed_theory_text>\<open>accepts\<close>-clauses\<^index>\<open>accepts\_clause@\<open>accepts_clause\<close>\<close> containing
  a regular expression over class names.
  Classes with an \<^boxed_theory_text>\<open>accepts\<close>-clause were called 
  \<^emph>\<open>monitor classes\<close>.\<^bindex>\<open>monitor class\<close>\<^index>\<open>class!monitor@see monitor class\<close> While document 
  classes and their inheritance relation structure meta-data of text-elements in an object-oriented 
  manner, monitor classes enforce structural organization of documents via the language specified 
  by the regular expression enforcing a sequence of text-elements.

  A major design decision of ODL is to denote attribute values by HOL-terms and HOL-types. 
  Consequently, ODL can refer to any predefined type defined in the HOL library, \<^eg>, 
  \<^typ>\<open>string\<close> or \<^typ>\<open>int\<close> as well as parameterized types, \<^eg>,
  \<^typ>\<open>_ option\<close>, \<^typ>\<open>_ list\<close>, \<^typ>\<open>_ set\<close>, or products
  \<^typ>\<open>_ \<times> _\<close>. As a consequence of the 
  document model, ODL definitions may be arbitrarily intertwined with standard HOL type definitions. 
  Finally, document class definitions result in themselves in a HOL-type in order to allow \<^emph>\<open>links\<close> 
  to and between ontological concepts.
\<close>

subsection*["odl_manual0"::technical]\<open>Some Isabelle/HOL Specification Constructs Revisited\<close>
text\<open>
  As ODL is an extension of Isabelle/HOL, document class definitions can therefore be arbitrarily 
  mixed with standard HOL specification constructs. To make this manual self-contained, we present 
  syntax and semantics of the specification constructs that are most likely relevant for the 
  developer of ontologies (for more details, see~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>).  Our 
  presentation is a simplification of the original sources following the needs of ontology developers 
  in \<^isadof>:
  \<^item> \<open>name\<close>:\<^index>\<open>name@\<open>name\<close>\<close>
     with the syntactic category of \<open>name\<close>'s we refer to alpha-numerical identifiers 
     (called \<open>short_ident\<close>'s in \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>) and identifiers
     in \<^boxed_theory_text>\<open>...\<close> which might contain certain ``quasi-letters'' such 
     as \<^boxed_theory_text>\<open>_\<close>, \<^boxed_theory_text>\<open>-\<close>, \<^boxed_theory_text>\<open>.\<close> (see~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close> for 
     details).
       % TODO
       % This phrase should be reviewed to clarify identifiers.
       % Peculiarly, "and identifiers in \<^boxed_theory_text>\<open> ... \<close>". 
  \<^item> \<open>tyargs\<close>:\<^index>\<open>tyargs@\<open>tyargs\<close>\<close> 
     \<^rail>\<open>  typefree | ('(' (typefree * ',') ')')\<close>
     \<open>typefree\<close> denotes fixed type variable (\<open>'a\<close>, \<open>'b\<close>, ...) (see~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>)
  \<^item> \<open>dt_name\<close>:\<^index>\<open>dt\_npurdahame@\<open>dt_name\<close>\<close>
     \<^rail>\<open>  (tyargs?) name (mixfix?)\<close>   
     The syntactic entity \<open>name\<close> denotes an identifier, \<open>mixfix\<close> denotes the usual 
     parenthesized mixfix notation (see \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>).
     The \<^emph>\<open>name\<close>'s referred here are type names such as \<^typ>\<open>int\<close>, \<^typ>\<open>string\<close>,
     \<^type>\<open>list\<close>, \<^type>\<open>set\<close>, etc. 
  \<^item> \<open>type_spec\<close>:\index{type_spec@\<open>type_spec\<close>}
     \<^rail>\<open>  (tyargs?) name\<close>
     The \<^emph>\<open>name\<close>'s referred here are type names such as \<^typ>\<open>int\<close>, \<^typ>\<open>string\<close>,
     \<^type>\<open>list\<close>, \<^type>\<open>set\<close>, etc. 
  \<^item> \<open>type\<close>:\<^index>\<open>type@\<open>type\<close>\<close>
     \<^rail>\<open>  (( '(' ( type * ',')  ')' )? name) | typefree \<close>     
  \<^item> \<open>dt_ctor\<close>:\<^index>\<open>dt\_ctor@\<open>dt_ctor\<close>\<close>
     \<^rail>\<open> name (type*) (mixfix?)\<close>
  \<^item> \<open>datatype_specification\<close>:\<^index>\<open>datatype\_specification@\<open>datatype_specification\<close>\<close>
     \<^rail>\<open> @@{command "datatype"} dt_name '=' (dt_ctor * '|' )\<close>
  \<^item> \<open>type_synonym_specification\<close>:\<^index>\<open>type\_synonym\_specification@\<open>type_synonym_specification\<close>\<close>
     \<^rail>\<open> @@{command "type_synonym"} type_spec '=' type\<close>
  \<^item> \<open>constant_definition\<close> :\<^index>\<open>constant\_definition@\<open>constant_definition\<close>\<close>
     \<^rail>\<open> @@{command "definition"} name '::' type 'where' '"' name '=' \<newline> expr '"'\<close>
  \<^item> \<open>expr\<close>:\<^index>\<open>expr@\<open>expr\<close>\<close>
     the syntactic category \<open>expr\<close> here denotes the very rich language of 
     mathematical  notations encoded in \<open>\<lambda>\<close>-terms in Isabelle/HOL. Example expressions are:
     \<^boxed_theory_text>\<open>1+2\<close> (arithmetics), \<^boxed_theory_text>\<open>[1,2,3]\<close> (lists), \<^boxed_theory_text>\<open>ab c\<close> (strings),
     % TODO
     % Show string in the document output for  \<^boxed_theory_text>\<open>ab c\<close> (strings) 
     \<^boxed_theory_text>\<open>{1,2,3}\<close> (sets), \<^boxed_theory_text>\<open>(1,2,3)\<close> (tuples), 
     \<^boxed_theory_text>\<open>\<forall> x. P(x) \<and> Q x = C\<close> (formulas). For comprehensive overview, 
     see~\<^cite>\<open>"nipkow:whats:2020"\<close>.
\<close>

text\<open>
  Advanced ontologies can, \<^eg>,  use recursive function definitions with 
  pattern-matching~\<^cite>\<open>"kraus:defining:2020"\<close>, extensible record 
  specifications~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>, and abstract type declarations.
\<close>

text\<open>\<^isadof> works internally with fully qualified names in order to avoid confusions 
occurring otherwise, for example, in disjoint class hierarchies. This also extends to names for
 \<^boxed_theory_text>\<open>doc_class\<close>es, which must be representable as type-names as well since they
can be used in attribute types. Since theory names are lexically very liberal 
(\<^boxed_theory_text>\<open>0.thy\<close> is a legal theory name), this can lead to subtle problems when 
constructing a class: \<^boxed_theory_text>\<open>foo\<close> can be a legal name for a type definition, the 
corresponding type-name \<^boxed_theory_text>\<open>0.foo\<close> is not. For this reason, additional checks at the 
definition of a \<^boxed_theory_text>\<open>doc_class\<close> reject problematic lexical overlaps.\<close>


subsection*["odl_manual1"::technical]\<open>Defining Document Classes\<close>
text\<open>
A document class\<^bindex>\<open>document class\<close> can be defined using the @{command "doc_class"} keyword: 
\<^item> \<open>class_id\<close>:\<^bindex>\<open>class\_id@\<open>class_id\<close>\<close> a type-\<open>name\<close> that has been introduced 
  via a \<open>doc_class_specification\<close>.
\<^item> \<open>doc_class_specification\<close>:\<^index>\<open>doc\_class\_specification@\<open>doc_class_specification\<close>\<close>
     We call document classes with an \<open>accepts_clause\<close> 
     \<^emph>\<open>monitor classes\<close> or \<^emph>\<open>monitors\<close> for short.
     \<^rail>\<open> (@@{command "doc_class"}| @@{command "onto_class"}) class_id '=' (class_id '+')? (attribute_decl+) \<newline>
           (invariant_decl *) (rejects_clause accepts_clause)? \<newline> (accepts_clause *)\<close>
\<^item> \<open>attribute_decl\<close>:\<^index>\<open>attribute\_decl@\<open>attribute_decl\<close>\<close>
     \<^rail>\<open> name '::' '"' type '"' default_clause? \<close>
\<^item> \<open>invariant_decl\<close>:\<^index>\<open>invariant\_decl@\<open>invariant_decl\<close>\<close>
     Invariants can be specified as predicates over document classes represented as 
     records in HOL. Sufficient type information must be provided in order to
     disambiguate the argument of the expression
     and the \<^boxed_text>\<open>\<sigma>\<close> symbol is reserved to reference the instance of the class itself. 
     \<^rail>\<open> 'invariant' (name '::' '"' term '"' + 'and') \<close>
\<^item> \<open>rejects_clause\<close>:\<^index>\<open>rejects\_clause@\<open>rejects_clause\<close>\<close>
     \<^rail>\<open> 'rejects' (class_id * ',') \<close>
\<^item> \<open>accepts_clause\<close>:\<^index>\<open>accepts\_clause@\<open>accepts_clause\<close>\<close>
     \<^rail>\<open> 'accepts' ('"' regexpr '"' + 'and')\<close>
\<^item> \<open>default_clause\<close>:\<^index>\<open>default\_clause@\<open>default_clause\<close>\<close> 
     \<^rail>\<open> '<=' '"' expr '"' \<close>
\<^item> \<open>regexpr\<close>:\<^index>\<open>regexpr@\<open>regexpr\<close>\<close>
     \<^rail>\<open> '\<lfloor>' class_id '\<rfloor>' | '(' regexpr ')' | (regexpr '||' regexpr) | (regexpr '~~' regexpr)
            | ('\<lbrace>' regexpr '\<rbrace>\<^sup>+') | ( '\<lbrace>' regexpr '\<rbrace>\<^sup>*')  \<close>
     % TODO
     % Syntax for class_id does not seem to work (\<lfloor> and \<rfloor> do not work)
     Regular expressions describe sequences of \<open>class_id\<close>s (and indirect sequences of document
     items corresponding to the \<open>class_id\<close>s). The constructors for alternative, sequence, 
     repetitions and non-empty sequence follow in the top-down order of the above diagram. 
\<close>

text\<open>
  \<^isadof> provides a default document representation (\<^ie>, content and layout of the generated 
  \<^pdf>) that only prints the main text, omitting all attributes. \<^isadof> provides the 
  \<^ltxinline>\<open>\newisadof[]{}\<close>\<^index>\<open>newisadof@\<^boxed_latex>\<open>\newisadof\<close>\<close>\<^index>\<open>document class!PDF\<close>
  command for defining a dedicated layout for a document class in \<^LaTeX>. Such a document 
  class-specific \<^LaTeX>-definition can not only provide a specific layout (\<^eg>, a specific 
  highlighting, printing of certain attributes), it can also generate entries in the table of 
  contents or an index. Overall, the  \<^ltxinline>\<open>\newisadof[]{}\<close> command follows the structure
  of the \<^boxed_theory_text>\<open>doc_class\<close>-command:

% bu: not embeddable macro: too many guillemots ...
\begin{ltx}[escapechar=ë]
\newisadof{ë\<open>class_id\<close>ë}[label=,type=, ë\<open>attribute_decl\<close>ë][1]{%
  % ë\LaTeXë-definition of the document class representation
  \begin{isamarkuptext}%
  #1%
  \end{isamarkuptext}%
}
\end{ltx}

  The \<open>class_id\<close> (or \<^emph>\<open>cid\<close>\<^index>\<open>cid!cid@\<open>see class_id\<close>\<close> for short) is the full-qualified name of the document class and the list of \<open>attribute_decl\<close>
  needs to declare all attributes of the document class. Within the \<^LaTeX>-definition of the document
  class representation, the identifier \<^boxed_latex>\<open>#1\<close> refers to the content of the main text of the 
  document class (written in \<^boxed_theory_text>\<open>\<open> ... \<close>\<close>) and the attributes can be referenced
  by their name using the  \<^ltxinline>\<open>\commandkey{...}\<close>-command (see the documentation of the 
  \<^LaTeX>-package ``keycommand''~\<^cite>\<open>"chervet:keycommand:2010"\<close> for details). Usually, the 
  representations definition needs to be wrapped in a 
  \<^ltxinline>\<open>\begin{isarmarkup}...\end{isamarkup}\<close>-environment, to ensure the correct context 
  within Isabelle's \<^LaTeX>-setup. 
  % TODO:
  % Clarify \newisadof signature: \newisadof[]{} vs \newisadof{}[]{}.
  Moreover, \<^isadof> also provides the following two variants of \inlineltx|\newisadof{}[]{}|:
  \<^item>  \<^ltxinline>\<open>\renewisadof{}[]{}\<close>\<^index>\<open>renewisadof@\<^boxed_latex>\<open>\renewisadof\<close>\<close> for re-defining 
     (over-writing) an already defined command, and  
  \<^item>  \<^ltxinline>\<open>\provideisadof{}[]{}\<close>\<^index>\<open>provideisadof@\<^boxed_latex>\<open>\provideisadof\<close>\<close> for providing 
     a definition if it is not yet defined. 
\<close>
text\<open>
  While arbitrary \<^LaTeX>-commands can be used within these commands,
  special care is required for arguments containing special characters (\<^eg>, the 
  underscore ``\_'') that do have a special meaning in \<^LaTeX>.  
  Moreover, as usual, special care has to be taken for commands that write into aux-files
  that are included in a following \<^LaTeX>-run. For such complex examples, we refer the interested 
  reader to  the style files provided in the \<^isadof> distribution. In particular 
  the definitions of the concepts \<^boxed_theory_text>\<open>title*\<close> and \<^boxed_theory_text>\<open>author*\<close> in \<^LaTeX>-style 
  for the ontology @{theory \<open>Isabelle_DOF.scholarly_paper\<close>} shows examples of protecting 
  special characters in definitions that need to make use of a entries in an aux-file. 
\<close>

section\<open>The main Ontology-aware Document Elements\<close>
text\<open>Besides the core-commands to define an ontology as presented in the previous section, 
the \<^isadof> core provides a number of mechanisms to \<^emph>\<open>use\<close> the resulting data to annotate
texts, code, and terms. As mentioned already in the introduction, this boils down two three major
groups of commands used to annotate text-. code-, and term contexts with instances of ontological
classes, \<^ie>, meta-information specified in an ontology. Representatives of these three groups,
which refer by name to equivalent standard Isabelle commands by their name suffixed with a \<open>*\<close>, 
are presented as follows in a railroad diagram:

   \<^item> \<open>annotated_text_element\<close> :
   \<^rail>\<open>( @@{command "text*"} '[' meta_args ']' '\<open>' text context '\<close>' )
     \<close>
   \<^item> \<open>annotated_code_element\<close> :
   \<^rail>\<open>( @@{command "ML*"} '[' meta_args ']' '\<open>' code context '\<close>' )
     \<close>
   \<^item> \<open>annotated_term_element\<close> :
   \<^rail>\<open>( @@{command "value*"} '[' meta_args ']' '\<open>' term context '\<close>' )
     \<close>

In the following, we will formally introduce the syntax of the core commands as 
supported on the Isabelle/Isar level. On this basis, concepts such as the freeform 
\<^theory_text>\<open>Definition*\<close> and \<^theory_text>\<open>Lemma*\<close> elements were derived from \<^theory_text>\<open>text*\<close>. Similarly,the
corresponding formal \<^theory_text>\<open>definition*\<close> and \<^theory_text>\<open>lemma*\<close> elements were built on top of 
functionality of the  \<^theory_text>\<open>value*\<close>-family.

\<close>

subsection\<open>General Syntactic Elements for Document Management\<close>

text\<open>Recall that except \<^theory_text>\<open>text*[]\<open>...\<close>\<close>, all \<^isadof> commands were mapped to visible
layout; these commands have to be wrapped into 
 \<^verbatim>\<open>(*<*) ... (*>*)\<close> if this is undesired. \<close>

text\<open>

\<^item> \<open>obj_id\<close>:\<^index>\<open>obj\_id@\<open>obj_id\<close>\<close> (or \<^emph>\<open>oid\<close>\<^index>\<open>oid!oid@\<open>see obj_id\<close>\<close> for short) a \<^emph>\<open>name\<close>
  as specified in @{technical \<open>odl_manual0\<close>}.
\<^item> \<open>meta_args\<close> : 
   \<^rail>\<open>obj_id ('::' class_id) ((',' attribute '=' HOL_term) *) \<close>
\<^item> \<^emph>\<open>evaluator\<close>: from \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>, evaluation is tried first using ML,
  falling back to normalization by evaluation if this fails. Alternatively a specific
  evaluator can be selected using square brackets; typical evaluators use the
  current set of code equations to normalize and include \<open>simp\<close> for fully
  symbolic evaluation using the simplifier, \<open>nbe\<close> for \<^emph>\<open>normalization by
  evaluation\<close> and \<^emph>\<open>code\<close> for code generation in SML.
\<^item> \<open>upd_meta_args\<close> :
   \<^rail>\<open> (obj_id ('::' class_id) ((',' attribute (':=' | '+=') HOL_term ) * ))\<close>

\<^item> \<open>annotated_text_element\<close> :
\<^rail>\<open>  
     (  @@{command "open_monitor*"}  
        | @@{command "close_monitor*"} 
        | @@{command "declare_reference*"} 
     ) '[' meta_args ']' 
     | change_status_command
     | inspection_command
     | macro_command
  \<close>
\<^item> \<^isadof> \<open>change_status_command\<close> :
  \<^rail>\<open>  (@@{command "update_instance*"} '[' upd_meta_args ']')\<close>

With respect to the family of text elements,
\<^theory_text>\<open>text*[oid::cid, ...] \<open> \<dots> text \<dots> \<close> \<close> is the core-command of \<^isadof>: it permits to create
an object of meta-data belonging to the class \<^theory_text>\<open>cid\<close>\<^index>\<open>cid!cid@\<open>see class_id\<close>\<close>.
This is viewed as the \<^emph>\<open>definition\<close> of an instance of a document class.
The class invariants were checked for all attribute values
at creation time if not specified otherwise. Unspecified attributed values were represented
by fresh free variables.
This instance object is attached to the text-element
and makes it thus ``trackable'' for  \<^isadof>, \<^ie>, it can be referenced
via the \<^theory_text>\<open>oid\<close>\<^index>\<open>oid!oid@\<open>see obj_id\<close>\<close>, its attributes
can be set by defaults in the class-definitions, or set at creation time, or modified at any
point after creation via  \<^theory_text>\<open>update_instance*[oid, ...]\<close>. The \<^theory_text>\<open>class_id\<close> is syntactically optional;
if ommitted, an object belongs to an anonymous superclass of all classes. 
The \<^theory_text>\<open>class_id\<close> is used to generate a \<^emph>\<open>class-type\<close> in HOL; note that this may impose lexical 
restrictions as well as to name-conflicts in the surrounding logical context. 
In many cases, it is possible to use the class-type to denote the \<^theory_text>\<open>class_id\<close>; this also
holds for type-synonyms on class-types.

References to text-elements can occur textually before creation; in these cases, they must be 
declared via \<^theory_text>\<open>declare_reference*[...]\<close> in order to compromise to Isabelle's fundamental 
``declaration-before-use" linear-visibility evaluation principle. The forward-declared class-type
must be identical with the defined class-type.

For a declared class \<^theory_text>\<open>cid\<close>, there exists a text antiquotation of the form \<^theory_text>\<open> @{cid \<open>oid\<close>} \<close>. 
The precise presentation is decided in the \<^emph>\<open>layout definitions\<close>, for example by suitable
\<^LaTeX>-template code. Declared but not yet defined instances must be referenced with a particular
pragma in order to enforce a relaxed checking \<^theory_text>\<open> @{cid (unchecked) \<open>oid\<close>} \<close>.
The choice of the default class in a @{command "declare_reference*"}-command
can be influenced by setting globally an attribute:
@{boxed_theory_text [display]
\<open>declare[[declare_reference_default_class = "definition"]]\<close>}
Then in this example:
@{boxed_theory_text [display]\<open>declare_reference*[def1]\<close>}
\<open>def1\<close> will be a declared instance of the class \<open>definition\<close>. 
\<close>

subsection\<open>Ontological Code-Contexts and their Management\<close>

text\<open>
\<^item> \<open>annotated_code_element\<close>:
\<^rail>\<open>(@@{command "ML*"}   '[' meta_args ']' '\<open>' SML_code '\<close>')\<close>

The \<^theory_text>\<open>ML*[oid::cid, ...] \<open> \<dots> SML-code \<dots> \<close>\<close>-document elements proceed similarly:
a referentiable meta-object of class \<^theory_text>\<open>cid\<close> is created, initialized with the optional 
 attributes and bound to \<^theory_text>\<open>oid\<close>. In fact, the entire the meta-argument list is optional.
The SML-code is type-checked and executed 
in the context of the SML toplevel of the Isabelle system as in the corresponding 
\<^theory_text>\<open>ML\<open> \<dots> SML-code \<dots> \<close>\<close>-command.
Additionally, ML antiquotations were added to check and evaluate terms with
term antiquotations:
\<^item> \<^theory_text>\<open>@{term_ \<open>term\<close> }\<close> parses and type-checks \<open>term\<close> with term antiquotations,
  for instance \<^theory_text>\<open>@{term_ \<open>@{technical \<open>odl-manual1\<close>}\<close>}\<close> will parse and check
  that \<open>odl-manual1\<close> is indeed an instance of the class \<^typ>\<open>technical\<close>,
\<^item> \<^theory_text>\<open>@{value_ \<open>term\<close> }\<close> performs the evaluation of \<open>term\<close> with term antiquotations,
  for instance \<^theory_text>\<open>@{value_ \<open>definition_list @{technical \<open>odl-manual1\<close>}\<close>}\<close>
  will get the value of the \<^const>\<open>definition_list\<close> attribute of the instance \<open>odl-manual1\<close>.
  \<^theory_text>\<open>value_\<close> may have an optional argument between square brackets to specify the evaluator:
  \<^theory_text>\<open>@{value_ [nbe] \<open>definition_list @{technical \<open>odl-manual1\<close>}\<close>}\<close> forces \<open>value_\<close> to evaluate
  the term using normalization by evaluation (see \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>).
\<close>

(*<*)
doc_class A =
   level :: "int option"
   x :: int
definition*[a1::A, x=5, level="Some 1"] xx' where "xx' \<equiv> A.x @{A \<open>a1\<close>}" if "A.x @{A \<open>a1\<close>} = 5"

doc_class E =
   x :: "string"              <= "''qed''"

doc_class cc_assumption_test =
a :: int
text*[cc_assumption_test_ref::cc_assumption_test]\<open>\<close>

definition tag_l :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where "tag_l \<equiv> \<lambda>x y. y"

lemma* tagged : "tag_l @{cc_assumption_test \<open>cc_assumption_test_ref\<close>} AAA \<Longrightarrow> AAA"
  by (simp add: tag_l_def)

find_theorems name:tagged "(_::cc_assumption_test \<Rightarrow> _ \<Rightarrow> _) _ _ \<Longrightarrow>_"

lemma*[e5::E] testtest : "xx + A.x @{A \<open>a1\<close>} = yy + A.x @{A \<open>a1\<close>} \<Longrightarrow> xx = yy" by simp

doc_class B'_test' =
b::int

text*[b::B'_test']\<open>\<close>

term*\<open>@{B'_test' \<open>b\<close>}\<close>

declare_reference*["text_elements_expls"::technical]
(*>*)

subsection*["subsec_onto_term_ctxt"::technical]\<open>Ontological Term-Contexts and their Management\<close>
text\<open> 
\<^item> \<open>annotated_term_element\<close>
\<^rail>\<open> 
    (@@{command "term*"} ('[' meta_args ']')? '\<open>' HOL_term  '\<close>'
     | (@@{command "value*"}
        | @@{command "assert*"}) \<newline> ('[' evaluator ']')? ('[' meta_args ']')? '\<open>' HOL_term '\<close>'
     | (@@{command "definition*"}) ('[' meta_args ']')?
        ('... see ref manual')
     | (@@{command "lemma*"} | @@{command "theorem*"} | @@{command "corollary*"}
       | @@{command "proposition*"} ) ('[' meta_args ']')?
         ('... see ref manual')
    )
  \<close>

For a declared class \<^theory_text>\<open>cid\<close>, there exists a term-antiquotation of the form \<^theory_text>\<open>@{cid \<open>oid\<close>}\<close>.
The major commands providing term-contexts are\<^footnote>\<open>The meta-argument list is optional.\<close>
  \<^item> \<^theory_text>\<open>term*[oid::cid, ...] \<open> \<dots> HOL-term \<dots> \<close>\<close>,
  \<^item> \<^theory_text>\<open>value*[oid::cid, ...] \<open> \<dots> HOL-term \<dots> \<close>\<close>, and
  \<^item> \<^theory_text>\<open>assert*[oid::cid, ...] \<open> \<dots> HOL-term \<dots> \<close>\<close>
  \<^item> \<^theory_text>\<open>definition*[oid::cid, ...] const_name where \<open> \<dots> HOL-term \<dots> \<close>\<close>, and
  \<^item> \<^theory_text>\<open>lemma*[oid::cid, ...] name :: \<open> \<dots> HOL-term \<dots> \<close>\<close>.


Wrt. creation, checking and traceability, these commands are analogous to the ontological text and
code-commands. However the argument terms may contain term-antiquotations stemming from an
ontology definition. Term-contexts were type-checked and \<^emph>\<open>validated\<close> against
the global context (so: in the term @{term_ [source] \<open>@{scholarly_paper.author \<open>bu\<close>}\<close>}, \<open>bu\<close>
is indeed a string which refers to a meta-object belonging to the document class \<^typ>\<open>author\<close>, 
for example). With the exception of the @{command "term*"}-command, the term-antiquotations 
 in the other term-contexts are additionally expanded (\<^eg> replaced) by the instance of the class,
\<^eg>, the HOL-term denoting this meta-object.
This expansion happens \<^emph>\<open>before\<close> evaluation of the term, thus permitting
executable HOL-functions to interact with meta-objects.
The @{command "assert*"}-command allows for logical statements to be checked in the global context
(see @{technical (unchecked) \<open>text_elements_expls\<close>}).
% TODO:
% Section reference @{docitem (unchecked) \<open>text_elements_expls\<close>} has not the right number
This is particularly useful to explore formal definitions wrt. their border cases.
For @{command "assert*"}, the evaluation of the term can be disabled
with the \<^boxed_theory_text>\<open>disable_assert_evaluation\<close> theory attribute:
  @{boxed_theory_text [display]\<open>
  declare[[disable_assert_evaluation]]\<close>}
Then @{command "assert*"} will act like @{command "term*"}.

The @{command "definition*"}-command allows \<open>prop\<close>, \<open>spec_prems\<close>, and \<open>for_fixes\<close>
(see the @{command "definition"} command in \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>) to contain
term-antiquotations. For example:
@{boxed_theory_text [display]
\<open>doc_class A =
   level :: "int option"
   x :: int
definition*[a1::A, x=5, level="Some 1"] xx' where "xx' \<equiv> A.x @{A \<open>a1\<close>}" if "A.x @{A \<open>a1\<close>} = 5"\<close>}

The @{term_ [source] \<open>@{A \<open>a1\<close>}\<close>} term-antiquotation is used both in \<open>prop\<close> and in \<open>spec_prems\<close>.

@{command "lemma*"}, @{command "theorem*"}, etc., are extended versions of the goal commands
defined in \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>. Term-antiquotations can be used either in
a \<open>long_statement\<close> or in a \<open>short_statement\<close>.
For instance:
@{boxed_theory_text [display]
\<open>lemma*[e5::E] testtest : "xx + A.x @{A \<open>a1\<close>} = yy + A.x @{A \<open>a1\<close>} \<Longrightarrow> xx = yy"
 by simp\<close>}

This @{command "lemma*"}-command is defined using the @{term_ [source] \<open>@{A \<open>a1\<close>}\<close>}
term-antiquotation and attaches the @{docitem_name "e5"} instance meta-data to the \<open>testtest\<close>-lemma.

@{boxed_theory_text [display]
\<open>doc_class cc_assumption_test =
a :: int
text*[cc_assumption_test_ref::cc_assumption_test]\<open>\<close>

definition tag_l :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where "tag_l \<equiv> \<lambda>x y. y"

lemma* tagged : "tag_l @{cc-assumption-test \<open>cc_assumption_test_ref\<close>} AA \<Longrightarrow> AA"
  by (simp add: tag_l_def)

find_theorems name:tagged "(_::cc_assumption_test \<Rightarrow> _ \<Rightarrow> _) _ _ \<Longrightarrow>_"\<close>}

In this example, the definition \<^const>\<open>tag_l\<close> adds a tag to the \<open>tagged\<close> lemma using
the term-antiquotation @{term_ [source] \<open>@{cc_assumption_test \<open>cc_assumption_test_ref\<close>}\<close>}
inside the \<open>prop\<close> declaration.

Note unspecified attribute values were represented by free fresh variables which constrains \<^dof>
to choose either the normalization-by-evaluation strategy \<^theory_text>\<open>nbe\<close> or a proof attempt via
the \<^theory_text>\<open>auto\<close> method. A failure of these strategies will be reported and regarded as non-validation
of this meta-object. The latter leads to a failure of the entire command.
\<close>

(*<*)
declare_reference*["sec_advanced"::technical]
(*>*)

subsection\<open>Status and Query Commands\<close>

text\<open>
\<^item> \<^isadof> \<open>inspection_command\<close> :
  \<^rail>\<open>    @@{command "print_doc_classes"}
        |  @@{command "print_doc_items"} 
        |  @@{command "check_doc_global"}\<close>
\<^isadof> provides a number of inspection commands.
\<^item> \<^theory_text>\<open>print_doc_classes\<close> allows to view the status of the internal
  class-table resulting from ODL definitions,
\<^item> \<^ML>\<open>DOF_core.print_doc_class_tree\<close> allows for presenting (fragments) of
  class-inheritance trees (currently only available at ML level),
\<^item> \<^theory_text>\<open>print_doc_items\<close> allows  to view the status of the internal
  object-table of text-elements that were tracked.
  The theory attribute \<^theory_text>\<open>object_value_debug\<close> allows to inspect
  the term of instances value before its elaboration and normalization.
  Adding:
  @{boxed_theory_text [display]\<open>
  declare[[object_value_debug = true]]\<close>}
  ... to the theory
  will add the raw value term to the instance object-table for all the subsequent
  declared instances (using \<^theory_text>\<open>text*\<close> for instance).
  The raw term will be available in the \<open>input_term\<close> field of \<^theory_text>\<open>print_doc_items\<close> output and,
\<^item> \<^theory_text>\<open>check_doc_global\<close> checks if all declared object references have been
  defined, all monitors are in a final state, and checks the final invariant  
  on all objects (cf. @{technical (unchecked) \<open>sec_advanced\<close>})
\<close>

subsection\<open>Macros\<close>
text\<open>
\<^item> \<^isadof> \<open>macro_command\<close> :
  \<^rail>\<open>   @@{command "define_shortcut*"} name ('\<rightleftharpoons>' | '==') '\<open>' string '\<close>' 
        |  @@{command "define_macro*"}  name ('\<rightleftharpoons>' | '==') 
           \<newline> '\<open>' string '\<close>' '_' '\<open>' string '\<close>' \<close>

There is a mechanism to define document-local macros which
were PIDE-supported but lead to an expansion in the integrated source; this feature
can be used to define 
\<^item> \<^theory_text>\<open>shortcuts\<close>, \<^ie>, short names that were expanded to, for example,
  \<^LaTeX>-code,
\<^item> \<^theory_text>\<open>macro\<close>'s (= parameterized short-cuts), which allow for 
  passing an argument to the expansion mechanism.
\<close>
text\<open>The argument can be checked by an own SML-function with respect to syntactic
as well as semantic regards; however, the latter feature is currently only accessible at
the SML level and not directly in the Isar language. We would like to stress, that this 
feature is basically an abstract interface to existing Isabelle functionality in the document 
generation.
\<close>
subsubsection\<open>Examples\<close>
text\<open>
\<^item> common short-cut hiding \<^LaTeX> code in the integrated source:
    @{theory_text [display]
      \<open>define_shortcut* eg  \<rightleftharpoons> \<open>\eg\<close>  (* Latin: "exempli gratia"  meaning  "for example". *)
                      clearpage \<rightleftharpoons> \<open>\clearpage{}\<close>\<close>}
\<^item> non-checking macro:
    @{theory_text [display]
      \<open>define_macro* index  \<rightleftharpoons> \<open>\index{\<close> _ \<open>}\<close>\<close>}
\<^item> checking macro:
    @{theory_text [display]
      \<open>setup\<open> DOF_lib.define_macro \<^binding>\<open>vs\<close>  "\\vspace{" "}" (check_latex_measure) \<close>\<close>}
  where \<^ML>\<open>check_latex_measure\<close> is a hand-programmed function that checks 
  the input for syntactical and static semantic constraints.
\<close>

section\<open>The Standard Ontology Libraries\<close>
text\<open> We will describe the backbone of the Standard Library with the
already mentioned hierarchy \<^verbatim>\<open>COL\<close> (the common ontology library),
 \<^verbatim>\<open>scholarly_paper\<close> (for MINT-oriented scientific papers) or 
 \<^verbatim>\<open>technical_report\<close> (for MINT-oriented technical reports).
\<close>

subsection\<open>Common Ontology Library (COL)\<close>
(*<*)
ML\<open>writeln (DOF_core.print_doc_class_tree @{context} (fn (_,l) => String.isPrefix "Isa_COL" l) I)\<close>
(*>*)
text\<open> 

 \<^isadof> provides a Common Ontology Library (COL)\<^index>\<open>Common Ontology Library!COL@see COL\<close>
 \<^bindex>\<open>COL\<close> \<^footnote>\<open>contained in \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>\<close>
 that introduces several ontology concepts; its  overall class-tree it provides looks as follows:
%
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.0 .
.1 Isa\_COL.text\_element.
.2 Isa\_COL.chapter.
.2 Isa\_COL.section.
.2 Isa\_COL.subsection.
.2 Isa\_COL.subsubsection.
.1 Isa\_COL.float{...}.
.2 Isa\_COL.figure{...}.
.2 Isa\_COL.listing{...}.
.1 \ldots.
}
\end{minipage}
\end{center}\<close>\<close>

text\<open>
In particular it defines the super-class \<^typ>\<open>text_element\<close>: the root of all 
text-elements:
@{boxed_theory_text [display]\<open>
doc_class text_element = 
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 
\<close>}

As mentioned in @{scholarly_paper.technical \<open>sss\<close>},
\<^const>\<open>level\<close> defines the section-level (\<^eg>, using a \<^LaTeX>-inspired hierarchy:
from \<^boxed_theory_text>\<open>Some -1\<close> (corresponding to \<^boxed_latex>\<open>\part\<close>) to 
\<^boxed_theory_text>\<open>Some 0\<close> (corresponding to \<^boxed_latex>\<open>\chapter\<close>, respectively, \<^boxed_theory_text>\<open>chapter*\<close>) 
to \<^boxed_theory_text>\<open>Some 3\<close> (corresponding to \<^boxed_latex>\<open>\subsubsection\<close>, respectively, 
\<^boxed_theory_text>\<open>subsubsection*\<close>). Using an invariant, a derived ontology could, \<^eg>, require that
any sequence of technical-elements must be introduced by a text-element with a higher level
(this requires that technical text section are introduce by a section element).

The attribute \<^const>\<open>referentiable\<close> captures the information if a text-element can be a target
for a reference, which is the case for sections or subsections, for example, but not arbitrary
elements such as, \<^ie>, paragraphs (this mirrors restrictions of the target \<^LaTeX> representation).
The attribute  \<^const>\<open>variants\<close> refers to an Isabelle-configuration attribute that permits
to steer the different versions of a \<^LaTeX>-presentation of the integrated source.

For further information of the root classes such as \<^bindex>\<open>float\<close> \<^typ>\<open>float\<close>'s, please consult 
the ontology in \<^theory>\<open>Isabelle_DOF.Isa_COL\<close> directly and consult the Example I and II for 
their pragmatics. The  \<^theory>\<open>Isabelle_DOF.Isa_COL\<close> also provides  the subclasses
\<^typ>\<open>figure\<close> \<^bindex>\<open>figure\<close> and \<^bindex>\<open>listing\<close> \<^typ>\<open>listing\<close> which together with specific 
text-antiquotations like:
   \<^enum> \<open>@{theory_text [options] "path"}\<close>  (Isabelle)
   \<^enum> \<open>@{fig_content (width=\<dots>, height=\<dots>, caption=\<dots>) "path"}\<close> (COL)
   \<^enum> \<open>@{boxed_theory_text [display] \<open> ... \<close> }\<close> (local, e.g. manual)
   \<^enum> \<open>@{boxed_sml [display] \<open> ... \<close> }\<close> (local, e.g. manual)
   \<^enum> \<open>@{boxed_pdf [display] \<open> ... \<close> }\<close> (local, e.g. manual)
   \<^enum> \<open>@{boxed_latex [display] \<open> ... \<close> }\<close> (local, e.g. manual)
   \<^enum> \<open>@{boxed_bash [display] \<open> ... \<close> }\<close> (local, e.g. manual)\<close>

(*<*)
text\<open>With these primitives, it is possible to compose listing-like text-elements or 
side-by-side-figures as shown in the subsequent example:
  
@{boxed_theory_text [display]\<open>
text*[inlinefig::float, 
      main_caption="\<open>The Caption.\<close>"]
     \<open>@{theory_text [display, margin = 5] \<open>lemma A :: "a \<longrightarrow> b"\<close>}\<close>

text*[dupl_graphics::float, 
      main_caption="\<open>The Caption.\<close>"]
\<open>
@{fig_content (width=40, height=35, caption="This is a left test") "figures/A.png"
}\<^hfill>@{fig_content (width=40, height=35, caption="This is a right \<^term>\<open>\<sigma>\<^sub>i + 1\<close> test") "figures/B.png"} 
\<close>\<close>}\<close>

text\<open>The \<^theory_text>\<open>side_by_side_figure*\<close>-command  \<^bindex>\<open>side\_by\_side\_figure\<close> has been deprecated.\<close>
(*>*)

text\<open>
\<^verbatim>\<open>COL\<close> finally provides macros that extend the command-language of the DOF core by the following
abbreviations:

\<^item> \<open>derived_text_element\<close> :
\<^rail>\<open>
    (  ( @@{command "chapter*"} 
       | @@{command "section*"}   | @@{command "subsection*"} | @@{command "subsubsection*"} 
       | @@{command "paragraph*"} 
       | @@{command "figure*"}    | @@{command "listing*"} 
       ) 
       \<newline>
       '[' meta_args ']' '\<open>' text '\<close>'
     ) 
  \<close>
\<close>
text\<open>The command syntax follows the implicit convention to add a ``*''
to distinguish them from the (similar) standard Isabelle text-commands
which are not ontology-aware.\<close>

subsection*["text_elements"::technical]\<open>The Ontology \<^verbatim>\<open>scholarly_paper\<close>\<close>
(*<*)
ML\<open>val toLaTeX = String.translate (fn c => if c = #"_" then "\\_" else String.implode[c])\<close>     
ML\<open>writeln (DOF_core.print_doc_class_tree 
                 @{context} (fn (_,l) =>        String.isPrefix "scholarly_paper" l 
                                         orelse String.isPrefix "Isa_COL" l) 
                 toLaTeX)\<close>
(*>*)
text\<open> The \<^verbatim>\<open>scholarly_paper\<close> ontology is oriented towards the classical domains in science:
mathematics, informatics, natural sciences, technology, or engineering.

It extends \<^verbatim>\<open>COL\<close> by the following concepts:
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.0 .
.1 scholarly\_paper.title.
.1 scholarly\_paper.subtitle.
.1 scholarly\_paper.author\DTcomment{An Author Entity Declaration}.
.1 scholarly\_paper.abstract.
.1 Isa\_COL.text\_element.
.2 scholarly\_paper.text\_section\DTcomment{Major Paper Text-Elements}.    
.3 scholarly\_paper.introduction\DTcomment{...}.
.3 scholarly\_paper.conclusion\DTcomment{...}.
.4 scholarly\_paper.related\_work\DTcomment{...}.
.3 scholarly\_paper.bibliography\DTcomment{...}.
.3 scholarly\_paper.annex\DTcomment{...}.
.3 scholarly\_paper.example\DTcomment{Example in General Sense}.
.3 scholarly\_paper.technical\DTcomment{Root for Technical Content}.
.4 scholarly\_paper.math\_content\DTcomment{...}.
.5 scholarly\_paper.definition\DTcomment{Freeform}.
.5 scholarly\_paper.lemma\DTcomment{Freeform}.
.5 scholarly\_paper.theorem\DTcomment{Freeform}.
.5 scholarly\_paper.corollary\DTcomment{Freeform}.
.5 scholarly\_paper.math\_example\DTcomment{Freeform}.
.5 scholarly\_paper.math\_semiformal\DTcomment{Freeform}.
.5 scholarly\_paper.math\_formal\DTcomment{Formal Content}.
.6 scholarly\_paper.assertion\DTcomment{Assertions}.
.4 scholarly\_paper.tech\_example\DTcomment{...}.
.4 scholarly\_paper.math\_motivation\DTcomment{...}.
.4 scholarly\_paper.math\_explanation\DTcomment{...}.
.4 scholarly\_paper.engineering\_content\DTcomment{...}.
.5 scholarly\_paper.data.
.5 scholarly\_paper.evaluation.
.5 scholarly\_paper.experiment.
.4 ... 
.1 ... 
.1 scholarly\_paper.article\DTcomment{The Paper Monitor}.
.1 \ldots.
}
\end{minipage}
\end{center}
\<close>\<close>


text\<open>Recall that \<^emph>\<open>Formal Content\<close> means \<^emph>\<open>machine-checked, validated content\<close>.\<close>

text\<open>A pivotal abstract class in the hierarchy is:
@{boxed_theory_text [display]
\<open>
doc_class text_section = text_element +
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"  
\<close>}

Besides attributes of more practical considerations like a \<^const>\<open>fixme_list\<close>, that can be modified
during the editing process but is only visible in the integrated source but usually ignored in the
\<^LaTeX>, this class also introduces the possibility to assign an ``ownership'' or ``responsibility'' of 
a \<^typ>\<open>text_element\<close> to a specific \<^typ>\<open>author\<close>. Note that this is possible since \<^isadof> assigns to each
document class also a class-type which is declared in the HOL environment.\<close>

text*[s23::example, main_author = "Some(@{scholarly_paper.author \<open>bu\<close>})"]\<open>
Recall that concrete authors can be denoted by term-antiquotations generated by \<^isadof>; for example,
this may be for a text fragment like
@{boxed_theory_text [display]
\<open>text*[\<dots>::example, main_author = "Some(@{author ''bu''})"] \<open> \<dots> \<close>\<close>}
or 
@{boxed_theory_text [display]
\<open>text*[\<dots>::example, main_author = "Some(@{author \<open>bu\<close>})"] \<open> \<dots> \<close>\<close>}

where \<^boxed_theory_text>\<open>"''bu''"\<close> is a string presentation of the reference to the author 
text element (see below in @{docitem (unchecked) \<open>text_elements_expls\<close>}).
% TODO:
% Section reference @{docitem (unchecked) \<open>text_elements_expls\<close>} has not the right number
\<close>

text\<open>Some of these concepts were supported as command-abbreviations leading to the extension
of the \<^isadof> language:

\<^item> \<open>derived_text_elements \<close> :
\<^rail>\<open>
    (  ( @@{command "author*"}     | @@{command "abstract*"} 
       | @@{command "Definition*"} | @@{command "Lemma*"}      | @@{command "Theorem*"} 
       | @@{command "Proposition*"}| @@{command "Proof*"}      | @@{command "Example*"}  
       | @@{command "Premise*"}    | @@{command "Assumption*"} | @@{command "Hypothesis*"}
       | @@{command "Corollary*"}  | @@{command "Consequence*"}| @@{command "Assertion*"}
       | @@{command "Conclusion*"} 
       ) 
       \<newline>
       '[' meta_args ']' '\<open>' text '\<close>'
     ) 
     
  \<close>
\<close>




text\<open>Usually, command macros for text elements will assign the generated instance
to the default class corresponding for this class.
For pragmatic reasons, \<^theory_text>\<open>Definition*\<close>,  \<^theory_text>\<open>Lemma*\<close> and  \<^theory_text>\<open>Theorem*\<close> represent an exception
to this rule and are set up such that the default class is the super class @{typ \<open>math_content\<close>}
(rather than to the class @{typ \<open>definition\<close>}).
This way, it is possible to use these macros for several  sorts of the very generic
concept ``definition'', which can be used as a freeform mathematical definition but also for a
freeform terminological definition as used in certification standards. Moreover, new subclasses
of @{typ \<open>math_content\<close>} might be introduced in a derived ontology with an own specific layout
definition. 
\<close>

text\<open>While this library is intended to give a lot of space to freeform text elements in
order to counterbalance Isabelle's standard view, it should not be forgotten that the real strength
of Isabelle is its ability to handle both, and to establish links between both worlds. 
Therefore, the formal assertion command has been integrated to capture some form of formal content.\<close>


subsubsection*["text_elements_expls"::example]\<open>Examples\<close>

text\<open>
  While the default user interface for class definitions via the  
  \<^boxed_theory_text>\<open>text*\<open> ... \<close>\<close>-command allow to access all features of the document 
  class, \<^isadof> provides short-hands for certain, widely-used, concepts such as 
  \<^boxed_theory_text>\<open>title*\<open> ... \<close>\<close> or \<^boxed_theory_text>\<open>section*\<open> ... \<close>\<close>, \<^eg>:

@{boxed_theory_text [display]\<open>
title*[title::title]\<open>Isabelle/DOF\<close>
subtitle*[subtitle::subtitle]\<open>User and Implementation Manual\<close>
author*[adb::author, email="\<open>a.brucker@exeter.ac.uk\<close>",
        orcid="\<open>0000-0002-6355-1200\<close>", http_site="\<open>https://brucker.ch/\<close>",
        affiliation="\<open>University of Exeter, Exeter, UK\<close>"] \<open>Achim D. Brucker\<close>
author*[bu::author, email = "\<open>wolff@lri.fr\<close>",
         affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Burkhart Wolff\<close>\<close>}

\<close>

text\<open>Assertions allow for logical statements to be checked in the global context.
This is particularly useful to explore formal definitions wrt. their border cases.
@{boxed_theory_text [display]\<open>
assert*[ass1::assertion, short_name = "\<open>This is an assertion\<close>"] \<open>last [3] < (4::int)\<close>\<close>}
\<close>

text\<open>We want to check the consequences of this definition and can add the following statements:
@{boxed_theory_text [display]\<open>
text*[claim::assertion]\<open>For non-empty lists, our definition yields indeed 
                               the last element of a list.\<close>
assert*[claim1::assertion] \<open>last[4::int] = 4\<close>    
assert*[claim2::assertion] \<open>last[1,2,3,4::int] = 4\<close>\<close>}
\<close>

text\<open>
As mentioned before, the command macros of  \<^theory_text>\<open>Definition*\<close>,  \<^theory_text>\<open>Lemma*\<close> and  \<^theory_text>\<open>Theorem*\<close> 
set the default class to the super-class of \<^typ>\<open>definition\<close>.
However, in order to avoid the somewhat tedious consequence:
@{boxed_theory_text [display]
\<open>Theorem*[T1::"theorem", short_name="\<open>DF definition captures deadlock-freeness\<close>"]  \<open> \<dots> \<close>\<close>}

the choice of the default class can be influenced by setting globally an attribute such as
@{boxed_theory_text [display]
\<open>declare[[Definition_default_class = "definition"]]
declare[[Theorem_default_class = "theorem"]]\<close>}

which allows the above example be shortened to:
@{boxed_theory_text [display]
\<open>Theorem*[T1, short_name="\<open>DF definition captures deadlock-freeness\<close>"]  \<open> \<dots> \<close>\<close>}
\<close>

subsection\<open>The Ontology \<^verbatim>\<open>technical_report\<close>\<close>
(*<*)
ML\<open>val toLaTeX = String.translate (fn c => if c = #"_" then "\\_" else String.implode[c])\<close>     
ML\<open>writeln (DOF_core.print_doc_class_tree 
                 @{context} (fn (_,_) =>  true (*     String.isPrefix "technical_report" l 
                                         orelse String.isPrefix "Isa_COL" l *)) 
                 toLaTeX)\<close>
(*>*)
text\<open> The \<^verbatim>\<open>technical_report\<close> \<^bindex>\<open>technical\_report\<close> ontology in
 \<^theory>\<open>Isabelle_DOF.technical_report\<close> extends
\<^verbatim>\<open>scholarly_paper\<close>  \<^bindex>\<open>scholarly\_paper\<close> \<^bindex>\<open>ontology\<close> by concepts needed 
for larger reports in the domain of mathematics and engineering. The concepts are fairly 
high-level arranged at root-class level,

%
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.0 .
.1 technical\_report.front\_matter\DTcomment{...}.
.1 technical\_report.table\_of\_contents\DTcomment{...}.
.1 Isa\_COL.text\_element\DTcomment{...}.
.2 scholarly\_paper.text\_section\DTcomment{...}.
.4 technical\_report.code\DTcomment{...}.
.5 technical\_report.SML\DTcomment{...}.
.5 technical\_report.ISAR\DTcomment{...}.
.5 technical\_report.LATEX\DTcomment{...}.
.1 technical\_report.index\DTcomment{...}.
.1 ... 
.1 technical\_report.report\DTcomment{...}.
}
\end{minipage}
\end{center}
\<close>\<close>




subsubsection\<open>For Isabelle Hackers: Defining New Top-Level Commands\<close>

text\<open>
  Defining such new top-level commands requires some Isabelle knowledge as well as 
  extending the dispatcher of the \<^LaTeX>-backend. For the details of defining top-level 
  commands, we refer the reader to the Isar manual~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>. 
  Here, we only give a brief example how the \<^boxed_theory_text>\<open>section*\<close>-command is defined; we 
  refer the reader to the source code of \<^isadof> for details.

  First, new top-level keywords need to be declared in the \<^boxed_theory_text>\<open>keywords\<close>-section of 
  the theory header defining new keywords:

@{boxed_theory_text [display]\<open>
theory 
    ...
  imports
    ... 
  keywords
    "section*"
begin 
...
end
\<close>}

Second, given an implementation of the functionality of the new keyword (implemented in SML), 
the new keyword needs to be registered, together with its parser, as outer syntax:
\<^latex>\<open>
\begin{sml}
val _ =
  Outer_Syntax.command ("section*", <@>{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 1)) 
           {markdown = false} )));
\end{sml}\<close>
\<close>

text\<open>
Finally, for the document generation, a new dispatcher has to be defined in \<^LaTeX>---this is 
mandatory, otherwise the document generation will break. These dispatchers always follow the same 
schemata:
\<^latex>\<open>
\begin{ltx}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% begin: section*-dispatcher
\NewEnviron{isamarkupsection*}[1][]{\isaDof[env={section},#1]{\BODY}}
% end: section*-dispatcher
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{ltx}
\<close>
  After the definition of the dispatcher, one can, optionally, define a custom representation 
  using the \<^boxed_latex>\<open>\newisadof\<close>-command, as introduced in the previous section: 
\<^latex>\<open>
\begin{ltx}
\newisadof{section}[label=,type=][1]{%
  \isamarkupfalse%
    \isamarkupsection{#1}\label{\commandkey{label}}%
  \isamarkuptrue%
}
\end{ltx}\<close>
\<close>



section*["sec_advanced"::technical]\<open>Advanced ODL Concepts\<close>
(*<*)
doc_class title =
  short_title :: "string option" <= "None"
doc_class author =
  email :: "string" <= "''''"
datatype classification = SIL0 | SIL1 | SIL2 | SIL3 | SIL4
doc_class abstract =
  keywordlist :: "string list" <= "[]"
  safety_level :: "classification" <= "SIL3"
doc_class text_section =
  authored_by :: "author set" <= "{}"
  level :: "int option" <= "None"
type_synonym notion = string
doc_class introduction = text_section +
  authored_by :: "author set"  <= "UNIV"
  uses :: "notion set"
doc_class claim = introduction +
  based_on :: "notion list"
doc_class technical = text_section +
  formal_results :: "thm list"
doc_class "definition" = technical +
  is_formal :: "bool"
  property  :: "term list" <= "[]"
datatype kind = expert_opinion | argument | "proof"
doc_class result = technical +
  evidence :: kind
  property :: "thm list" <= "[]"
doc_class example = technical +
  referring_to :: "(notion + definition) set" <= "{}"
doc_class "conclusion" = text_section +
  establish :: "(claim \<times> result) set"
(*>*)

subsection*["sec_example"::technical]\<open>Example\<close>
text\<open>We assume in this section the following local ontology: 

@{boxed_theory_text [display]\<open>
doc_class title =
  short_title :: "string option" <= "None"
doc_class author =
  email :: "string" <= "''''"
datatype classification = SIL0 | SIL1 | SIL2 | SIL3 | SIL4
doc_class abstract =
  keywordlist :: "string list" <= "[]"
  safety_level :: "classification" <= "SIL3"
doc_class text_section =
  authored_by :: "author set" <= "{}"
  level :: "int option" <= "None"
type_synonym notion = string
doc_class introduction = text_section +
  authored_by :: "author set"  <= "UNIV" 
  uses :: "notion set"
doc_class claim = introduction +
  based_on :: "notion list" 
doc_class technical = text_section +
  formal_results :: "thm list" 
doc_class "definition" = technical +
  is_formal :: "bool"
  property  :: "term list" <= "[]" 
datatype kind = expert_opinion | argument | "proof"
doc_class result = technical +
  evidence :: kind
  property :: "thm list" <= "[]"
doc_class example = technical +
  referring_to :: "(notion + definition) set" <= "{}"
doc_class "conclusion" = text_section +
  establish :: "(claim \<times> result) set"
\<close>}
\<close>

subsection\<open>Meta-types as Types\<close>
(* TODO: Update the previous example and this section by importing an ontology
   and using checking antiquotations like \<^const> ans \<^typ> *)
text\<open>
  To express the dependencies between text elements to the formal
  entities, \<^eg>, \<^ML_type>\<open>term\<close> (\<open>\<lambda>\<close>-term), \<^ML_type>\<open>typ\<close>, or
   \<^ML_type>\<open>thm\<close>, we represent the types of the implementation language
  \<^emph>\<open>inside\<close> the HOL type system.  We do, however, not reflect the data of
  these types. They are just types declared in HOL, 
  which are ``inhabited'' by special constant symbols carrying strings, for
  example of the format \<^boxed_theory_text>\<open>@{thm <string>}\<close>.
  When HOL
  expressions were used to denote values of \<^boxed_theory_text>\<open>doc_class\<close>
  instance attributes, this requires additional checks after
  conventional type-checking that this string represents actually a
  defined entity in the context of the system state
  \<^boxed_theory_text>\<open>\<theta>\<close>.  For example, the \<^boxed_theory_text>\<open>establish\<close>
  attribute in our example is the power of the ODL: here, we model
  a relation between \<^emph>\<open>claims\<close> and \<^emph>\<open>results\<close> which may be a
  formal, machine-check theorem of type \<^ML_type>\<open>thm\<close> denoted by, for
  example: \<^boxed_theory_text>\<open>property = "[@{thm "system_is_safe"}]"\<close> in a
  system context \<^boxed_theory_text>\<open>\<theta>\<close> where this theorem is
  established. Similarly, attribute values like 
  \<^boxed_theory_text>\<open>property = "@{term \<open>A \<longleftrightarrow> B\<close>}"\<close>
  require that the HOL-string \<^boxed_theory_text>\<open>A \<longleftrightarrow> B\<close> is 
  again type-checked and represents indeed a formula in \<open>\<theta>\<close>. Another instance of 
  this process, which we call \<^emph>\<open>second-level type-checking\<close>, are term-constants
  generated from the ontology such as 
  \<^boxed_theory_text>\<open>@{definition <string>}\<close>. 
\<close>

(*<*)
declare_reference*["sec_monitors"::technical]
declare_reference*["sec_low_level_inv"::technical]
(*>*)

subsection*["sec_class_inv"::technical]\<open>ODL Class Invariants\<close>

text\<open>
  Ontological classes as described so far are too liberal in many situations.
  There is a first high-level syntax implementation for class invariants.
  These invariants are checked when an instance of the class is defined,
  and trigger warnings.
  The checking is enabled by default but can be disabled with the
  \<^boxed_theory_text>\<open>invariants_checking\<close> theory attribute:
  @{boxed_theory_text [display]\<open>
  declare[[invariants_checking = false]]\<close>}

  To enable the strict checking of the invariants,
  that is to trigger errors instead of warnings,
  the \<^boxed_theory_text>\<open>invariants_strict_checking\<close>
  theory attribute must be set:
  @{boxed_theory_text [display]\<open>
  declare[[invariants_strict_checking = true]]\<close>}

  For example, let's define the following two classes:
  @{boxed_theory_text [display]\<open>
  doc_class class_inv1 =
    int1 :: "int"
    invariant inv1 :: "int1 \<sigma> \<ge> 3"

  doc_class class_inv2 = class_inv1 +
    int2 :: "int"
    invariant inv2 :: "int2 \<sigma> < 2"
  \<close>}

  The \<^boxed_theory_text>\<open>\<sigma>\<close> symbol is reserved and references the future instance class.
  By relying on the implementation of the Records
  in Isabelle/HOL~\<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>,
  one can reference an attribute of an instance using its selector function.
  For example, \<^boxed_theory_text>\<open>int1 \<sigma>\<close> denotes the value
  of the \<^boxed_theory_text>\<open>int1\<close> attribute
  of the future instance of the class \<^boxed_theory_text>\<open>class_inv1\<close>.

  Now let's define two instances, one of each class:

  @{boxed_theory_text [display]\<open>
  text*[testinv1::class_inv1, int1=4]\<open>lorem ipsum...\<close>
  text*[testinv2::class_inv2, int1=3, int2=1]\<open>lorem ipsum...\<close>
  \<close>}

  The value of each attribute defined for the instances is checked against their classes invariants.
  As the class \<^boxed_theory_text>\<open>class_inv2\<close> is a subsclass
  of the class \<^boxed_theory_text>\<open>class_inv1\<close>, it inherits \<^boxed_theory_text>\<open>class_inv1\<close> invariants.
  Hence, the \<^boxed_theory_text>\<open>inv1\<close> invariant is checked
  when the instance \<^boxed_theory_text>\<open>testinv2\<close> is defined.

  Now let's add some invariants to our example in \<^technical>\<open>sec_example\<close>.
  For example, one
  would like to express that any instance of a \<^boxed_theory_text>\<open>result\<close> class finally has
  a non-empty  property list, if its \<^boxed_theory_text>\<open>kind\<close> is \<^boxed_theory_text>\<open>proof\<close>, or that 
  the \<^boxed_theory_text>\<open>establish\<close> relation between \<^boxed_theory_text>\<open>claim\<close> and
  \<^boxed_theory_text>\<open>result\<close> is total.
  In a high-level syntax, this type of constraints could be expressed, \<^eg>, by:
  @{boxed_theory_text [display]\<open>
  doc_class introduction = text_section +
    authored_by :: "author set"  <= "UNIV" 
    uses :: "notion set"
    invariant author_finite :: "finite (authored_by \<sigma>)"
  doc_class result = technical +
    evidence :: kind
    property :: "thm list" <= "[]"
    invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"
  doc_class example = technical +
    referring_to :: "(notion + definition) set" <= "{}"
  doc_class conclusion = text_section +
    establish :: "(claim \<times> result) set"
    invariant total_rel :: "\<forall> x. x \<in> Domain (establish \<sigma>)
                                             \<longrightarrow> (\<exists> y \<in> Range (establish \<sigma>). (x, y) \<in> establish \<sigma>)"
  \<close>}
  All specified constraints are already checked in the IDE of \<^dof> while editing.
  The invariant \<^boxed_theory_text>\<open>author_finite\<close> enforces that the user sets the 
  \<^boxed_theory_text>\<open>authored_by\<close> set.
  The invariants \<^theory_text>\<open>author_finite\<close> and \<^theory_text>\<open>establish_defined\<close> can not be checked directly
  and need a little help.
  We can set the \<open>invariants_checking_with_tactics\<close> theory attribute to help the checking.
  It will enable a basic tactic, using unfold and auto:
  @{boxed_theory_text [display]\<open>
  declare[[invariants_checking_with_tactics = true]]\<close>}
  There are still some limitations with this high-level syntax.
  For now, the high-level syntax does not support the checking of
  specific monitor behaviors (see @{technical (unchecked) "sec_monitors"}).
  For example, one would like to delay a final error message till the
  closing of a monitor.
  For this use-case you can use low-level class invariants
  (see @{technical (unchecked) "sec_low_level_inv"}).
  Also, for now, term-antiquotations can not be used in an invariant formula.
\<close>


subsection*["sec_low_level_inv"::technical]\<open>ODL Low-level Class Invariants\<close>

text\<open>
  If one want to go over the limitations of the actual high-level syntax of the invariant,
  one can define a function using SML.
  A formulation, in SML, of the class-invariant \<^boxed_theory_text>\<open>has_property\<close>
  in \<^technical>\<open>sec_class_inv\<close>, defined in the supposedly \<open>Low_Level_Syntax_Invariants\<close> theory
  (note the long name of the class),
  is straight-forward:

@{boxed_sml [display]
\<open>fun check_result_inv oid {is_monitor:bool} ctxt =
  let
    val kind =
      ISA_core.compute_attr_access ctxt "evidence" oid NONE @{here}
    val prop =
      ISA_core.compute_attr_access ctxt "property" oid NONE @{here}
    val tS = HOLogic.dest_list prop
  in  case kind of
       @{term "proof"} => if not(null tS) then true
                          else error("class result invariant violation")
      | _ => true
  end
val cid_long = DOF_core.get_onto_class_name_global "result" @{theory}
val bind = Binding.name "Check_Result"
val _ = Theory.setup (DOF_core.make_ml_invariant (check_result_inv, cid_long)
                     |> DOF_core.add_ml_invariant bind)\<close>}

  The \<^ML>\<open>Theory.setup\<close>-command (last line) registers the \<^boxed_theory_text>\<open>check_result_inv\<close> function 
  into the \<^isadof> kernel, which activates any creation or modification of an instance of 
  \<^boxed_theory_text>\<open>result\<close>. We cannot replace \<^boxed_theory_text>\<open>compute_attr_access\<close> by the 
  corresponding antiquotation \<^boxed_theory_text>\<open>\<^value_>\<open>evidence @{result \<open>oid\<close>}\<close>\<close>, since
  \<^boxed_theory_text>\<open>oid\<close> is bound to a  variable here and can therefore not be statically expanded.
\<close>

subsection*["sec_monitors"::technical]\<open>ODL Monitors\<close>
text\<open>
  We call a document class with an \<open>accepts_clause\<close> a \<^emph>\<open>monitor\<close>.\<^bindex>\<open>monitor\<close>  Syntactically, an 
  \<open>accepts_clause\<close>\<^index>\<open>accepts\_clause@\<open>accepts_clause\<close>\<close> contains a regular expression over class identifiers. 
  For example:

  @{boxed_theory_text [display]\<open>
  doc_class article = 
     style_id :: string                <= "''LNCS''"
     version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
     accepts "(title ~~ \<lbrakk>subtitle\<rbrakk> ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ abstract ~~ \<lbrace>introduction\<rbrace>\<^sup>+
                   ~~ \<lbrace>background\<rbrace>\<^sup>* ~~ \<lbrace>technical || example \<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+
                   ~~ bibliography ~~ \<lbrace>annex\<rbrace>\<^sup>* )"
  \<close>}

  Semantically, monitors introduce a behavioral element into ODL:

  @{boxed_theory_text [display]\<open>
  open_monitor*[this::article]  (* begin of scope of monitor "this" *)
    ...
  close_monitor*[this]          (* end of scope of monitor "this"   *)
  \<close>}

  Inside the scope of a monitor, all instances of classes mentioned in its \<^verbatim>\<open>accepts_clause\<close> (the
  \<^emph>\<open>accept-set\<close>) have to appear in the order specified by the regular expression; instances not 
  covered by an accept-set may freely occur. Monitors may additionally contain a \<^verbatim>\<open>rejects_clause\<close> 
  with a list of class-ids (the reject-list). This allows specifying ranges of
  admissible instances along the class hierarchy:
  \<^item> a superclass in the reject-list and a subclass in the
    accept-expression forbids instances superior to the subclass, and
  \<^item> a subclass $S$ in the reject-list and a superclass \<open>T\<close> in the
    accept-list allows instances of superclasses of \<open>T\<close> to occur freely,
    instances of \<open>T\<close> to occur in the specified order and forbids
    instances of \<open>S\<close>.
\<close>
text\<open>
  Should the specified ranges of admissible instances not be observed, warnings will be triggered.
  To forbid the violation of the specified ranges,
  one can enable the \<^boxed_theory_text>\<open>strict_monitor_checking\<close> theory attribute:
  @{boxed_theory_text [display]\<open>declare[[strict_monitor_checking = true]]\<close>}
  It is possible to enable the tracing of free classes occurring inside the scope of a monitor by
  enabling the \<^boxed_theory_text>\<open>free_class_in_monitor_checking\<close>
  theory attribute:
  @{boxed_theory_text [display]\<open>declare[[free_class_in_monitor_checking = true]]\<close>}
  Then a warning will be triggered when defining an instance of a free class
  inside the scope of a monitor.
  To forbid free classes inside the scope of a monitor, one can enable the
  \<^boxed_theory_text>\<open>free_class_in_monitor_strict_checking\<close> theory attribute:
  @{boxed_theory_text [display]\<open>declare[[free_class_in_monitor_strict_checking = true]]\<close>}

  Monitored document sections can be nested and overlap; thus, it is
  possible to combine the effect of different monitors. For example, it
  would be possible to refine the \<^boxed_theory_text>\<open>example\<close> section by its own
  monitor and enforce a particular structure in the presentation of
  examples.
  
  Monitors manage an implicit attribute \<^boxed_theory_text>\<open>trace\<close> containing
  the list of ``observed'' text element instances belonging to the
  accept-set. Together with the concept of ODL class invariants, it is
  possible to specify properties of a sequence of instances occurring in
  the document section. For example, it is possible to express that in
  the sub-list of \<^boxed_theory_text>\<open>introduction\<close>-elements, the first has an
  \<^boxed_theory_text>\<open>introduction\<close> element with a \<^boxed_theory_text>\<open>level\<close> strictly
  smaller than the others. Thus, an introduction is forced to have a
  header delimiting the borders of its representation. Class invariants
  on monitors allow for specifying structural properties on document
  sections.
  For now, the high-level syntax of invariants does not support the checking of
  specific monitor behaviors like the one just described and you must use 
  the low-level class invariants (see @{technical "sec_low_level_inv"}).

  Low-level invariants checking can be set up to be triggered
  when opening a monitor, when closing a monitor, or both
  by using the \<^ML>\<open>DOF_core.add_opening_ml_invariant\<close>,
  \<^ML>\<open>DOF_core.add_closing_ml_invariant\<close>, or \<^ML>\<open>DOF_core.add_ml_invariant\<close> commands
  respectively, to add the invariants to the theory context
  (See @{technical "sec_low_level_inv"} for an example).
\<close>

(*<*)
value*\<open>map (result.property) @{instances_of \<open>result\<close>}\<close>
value*\<open>map (text_section.authored_by) @{instances_of \<open>introduction\<close>}\<close>
value*\<open>filter (\<lambda>\<sigma>. result.evidence \<sigma> = proof) @{instances_of \<open>result\<close>}\<close>
value*\<open>filter (\<lambda>\<sigma>. the (text_section.level \<sigma>) > 1) @{instances_of \<open>introduction\<close>}\<close>
(*>*)

subsection*["sec_queries_on_instances"::technical]\<open>Queries On Instances\<close>

text\<open>
  Any class definition generates term antiquotations checking a class instance or
  the set of instances in a particular logical context; these references were
  elaborated to objects they refer to.
  This paves the way for a new mechanism to query the ``current'' instances presented as a
  HOL \<^type>\<open>list\<close>.
  Arbitrarily complex queries can therefore be defined inside the logical language.
  To get the list of the properties of the instances of the class \<open>result\<close>,
  or to get the list of the authors of the instances of \<open>introduction\<close>,
  it suffices to treat this meta-data as usual:
  @{theory_text [display,indent=5, margin=70] \<open>
value*\<open>map (result.property) @{instances_of \<open>result\<close>}\<close>
value*\<open>map (text_section.authored_by) @{instances_of \<open>introduction\<close>}\<close>
  \<close>}
  In order to get the list of the instances of the class \<open>myresult\<close>
  whose \<open>evidence\<close> is a \<open>proof\<close>, one can use the command:
  @{theory_text [display,indent=5, margin=70] \<open>
value*\<open>filter (\<lambda>\<sigma>. result.evidence \<sigma> = proof) @{instances_of \<open>result\<close>}\<close>
  \<close>}
  The list of the instances of the class \<open>introduction\<close> whose \<open>level\<close> > 1,
  can be filtered by:
  @{theory_text [display,indent=5, margin=70] \<open>
value*\<open>filter (\<lambda>\<sigma>. the (text_section.level \<sigma>) > 1) @{instances_of \<open>introduction\<close>}\<close>
  \<close>}
\<close>

section*[infrastructure::technical]\<open>Technical Infrastructure\<close>

subsection\<open>The Previewer\<close>

figure*[ 
  global_DOF_view::figure
  , relative_width="95" 
  , file_src="''figures/ThisPaperWithPreviewer.png''" 
]\<open>A Screenshot while editing this Paper in \<^dof> with Preview.\<close>
text\<open>A screenshot of the editing environment is shown in \<^figure>\<open>global_DOF_view\<close>. It supports 
incremental continuous PDF generation which  improves  usability. Currently, the granularity 
is restricted to entire theories (which have to be selected in a specific document pane). 
The response times can not (yet) compete
with a Word- or Overleaf editor, though, which is mostly due to the checking and 
evaluation overhead (the turnaround of this section is about 30 s). However, we believe
that better parallelization and evaluation techniques will decrease this gap substantially for the 
most common cases in future versions. \<close>


subsection\<open>Developing Ontologies and their Representation Mappings\<close>
text\<open>
  The document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not use Isabelle definitions or proofs for checking the 
  formal content---this manual is actually an example of a document not containing any proof.
  Consequently, the document editing and checking facility provided by \<^isadof> addresses the needs 
  of common users for an advanced text-editing environment, neither modeling nor proof knowledge is 
  inherently required.

  We expect authors of ontologies to have experience in the use of \<^isadof>, basic modeling (and, 
  potentially, some basic SML programming) experience, basic \<^LaTeX> knowledge, and, last but not 
  least, domain knowledge of the ontology to be modeled. Users with experience in UML-like 
  meta-modeling will feel familiar with most concepts; however, we expect  no need for insight in 
  the Isabelle proof language, for example, or other more advanced concepts.

  Technically, ontologies\<^index>\<open>ontology!directory structure\<close> are stored in a directory 
  \<^boxed_bash>\<open>ontologies\<close> and consist of an Isabelle theory file and a \<^LaTeX>-style file:
%
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.1 .
.2 ontologies\DTcomment{Ontologies}.
.3 ontologies.thy\DTcomment{Ontology Registration}.
.3 scholarly\_paper\DTcomment{scholarly\_paper}.
.4 scholarly\_paper.thy.
.4 DOF-scholarly\_paper.sty.
.3 technical\_report\DTcomment{technical\_paper}.
.4 technical\_report.thy.
.4 DOF-technical\_report.sty.
}
\end{minipage}
\end{center}\<close>
\<close>
text\<open>
  Developing a new ontology ``\<^boxed_bash>\<open>foo\<close>'' requires the 
  following steps:
  \<^item> definition of the ontological concepts, using \<^isadof>'s Ontology Definition Language (ODL), in 
    a new theory file \<^path>\<open>ontologies/foo/foo.thy\<close>.  
  \<^item> definition of the document representation for the ontological concepts in a \LaTeX-style 
    stored in the same directory as the theory file containing the ODL definitions. The file name should 
    start with the prefix ``DOF-``. For instance: \<^path>\<open>DOF-foo.sty\<close>
  \<^item> registration of the \LaTeX-style by adding a suitable \<^theory_text>\<open>define_ontology\<close> 
    command to the theory containing the ODL definitions.
\<close>

subsection\<open>Document Templates\<close>
text\<open>
  Document-templates\<^index>\<open>document template\<close> define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents. Document-templates 
  are stored in a directory 
  \<^path>\<open>src/document-templates\<close>:\<^index>\<open>document template!directory structure\<close>
\<^latex>\<open>
\begin{center}
\begin{minipage}{.9\textwidth}\footnotesize
\dirtree{%
.1 .
.2 document-templates\DTcomment{Document templates}.
.3 root-lncs.tex.
.3 root-scrartcl.tex.
.3 root-scrreprt-modern.tex.
.3 root-scrreprt.tex.
}
\end{minipage}
\end{center}\<close>
\<close>

text\<open>
  Developing a new document template ``\<^boxed_bash>\<open>bar\<close>'' requires the following steps:
  \<^item> develop a new \<^LaTeX>-template \<^boxed_bash>\<open>src/document-templates/root-bar.tex\<close>
  \<^item> add a suitable \<^theory_text>\<open>define_template\<close> command to a theory that is 
   imported by the project that shall use the new document template. 
\<close>


text\<open>
  As the document generation of \<^isadof> is based on \<^LaTeX>, the \<^isadof> document templates can (and 
  should) make use of any \<^LaTeX>-classes provided by publishers or standardization bodies.
\<close>


section*["document_templates"::technical]\<open>Defining Document Templates\<close>
subsection\<open>The Core Template\<close>

text\<open>
  Document-templates\<^bindex>\<open>document template\<close> define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents.
  If a new layout is already supported by a \<^LaTeX>-class, then developing basic support for it 
  is straightforward: In most cases, it is 
  sufficient to replace the document class in \autoref{lst:dc} of the template and add the 
  \<^LaTeX>-packages that are (strictly) required by the used \<^LaTeX>-setup. In general, we recommend
  to only add \<^LaTeX>-packages that are always necessary for this particular template, as loading
  packages in the templates minimizes the freedom users have by adapting the \<^path>\<open>preample.tex\<close>.
  The file name of the new template should start with the prefix \<^path>\<open>root-\<close> and need to be 
  registered using the \<^theory_text>\<open>define_template\<close> command.
  a typical \<^isadof> document template looks as follows: 

\<^latex>\<open>
\begin{ltx}[escapechar=ë, numbers=left,numberstyle=\tiny,xleftmargin=5mm]
\documentclass{article}        % The LaTeX-class of your template ë\label{lst:dc}ë  
\usepackage{DOF-core}
\usepackage{subcaption}
\usepackage[size=footnotesize]{caption}
\usepackage{hyperref}

%% Main document, do not modify
\begin{document}
\maketitle
\IfFileExists{dof_session.tex}{\input{dof_session}}{\input{session}}
\IfFileExists{root.bib}{\bibliography{root}}{}
\end{document}
\end{ltx}\<close>
\<close>

subsection\<open>Tips, Tricks, and Known Limitations\<close>
text\<open>
  In this section, we will discuss several tips and tricks for developing 
  new or adapting existing document templates or \<^LaTeX>-representations of ontologies.
\<close>

subsubsection\<open>Getting Started\<close>
text\<open>
  In general, we recommend creating a test project (\<^eg>, using \<^boxed_bash>\<open>isabelle dof_mkroot\<close>)
  to develop new document templates or ontology representations. The default setup of the \<^isadof>
  build system generated a \<^path>\<open>output/document\<close> directory with a self-contained \<^LaTeX>-setup. In 
  this directory, you can directly use \<^LaTeX> on the main file, called \<^path>\<open>root.tex\<close>:
  @{boxed_bash [display] \<open>ë\prompt{MyProject/output/document}ë lualatex root.tex\<close>}

  This allows you to develop and check your \<^LaTeX>-setup without the overhead of running 
   \<^boxed_bash>\<open>isabelle build\<close> after each change of your template (or ontology-style). Note that 
  the content of the \<^path>\<open>output\<close> directory is overwritten by executing 
   \<^boxed_bash>\<open>isabelle build\<close>.
\<close>

subsubsection\<open>Truncated Warning and Error Messages\<close>
text\<open>
  By default, \<^LaTeX> cuts of many warning or error messages after 79 characters. Due to the 
  use of full-qualified names in \<^isadof>, this can often result in important information being 
  cut off. Thus, it can be very helpful to configure \<^LaTeX> in such a way that it prints 
  long error or warning messages. This can easily be done for individual 
  \<^LaTeX> invocations: 
  @{boxed_bash [display] \<open>ë\prompt{MyProject/output/document}ë max_print_line=200 error_line=200 half_error_line=100  lualatex root.tex\<close>}
\<close>

subsubsection\<open>Deferred Declaration of Information\<close>
text\<open>
  During document generation, sometimes, information needs to be printed prior to its 
  declaration in a \<^isadof> theory. This violation of the declaration-before-use-principle
  requires that information is written into an auxiliary file during the first run of \<^LaTeX>
  so that the information is available at further runs of \<^LaTeX>. While, on the one hand, 
  this is a standard process (\<^eg>, used for updating references), implementing it correctly
  requires a solid understanding of \<^LaTeX>'s expansion mechanism. 
  Examples of this can be found, \<^eg>, in the ontology-style 
  \<^file>\<open>../../ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close>.
  For details about the expansion mechanism
  in general, we refer the reader to the \<^LaTeX> literature (\<^eg>,~\<^cite>\<open>"knuth:texbook:1986"
  and "mittelbach.ea:latex:1999" and "eijkhout:latex-cs:2012"\<close>).  
\<close>


subsubsection\<open>Authors and Affiliation Information\<close>
text\<open>
  In the context of academic papers, the defining of the representations for the author and
  affiliation information is particularly challenging as, firstly, they inherently are breaking
  the declare-before-use-principle and, secondly, each publisher uses a different \<^LaTeX>-setup 
  for their declaration. Moreover, the mapping from the ontological modeling to the document
  representation might also need to bridge the gap between different common modeling styles of 
  authors and their affiliations, namely: affiliations as attributes of authors vs. authors and 
  affiliations both as entities with a many-to-many relationship.

  The ontology representation
  \<^file>\<open>../../ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close> contains an example that, firstly, 
  shows how to write the author and affiliation information into the auxiliary file for re-use 
  in the next \<^LaTeX>-run and, secondly, shows how to collect the author and affiliation 
  information into an \<^boxed_latex>\<open>\author\<close> and a \<^boxed_latex>\<open>\institution\<close> statement, each of 
  which containing the information for all authors. The collection of the author information 
  is provided by the following \<^LaTeX>-code:
\<^latex>\<open>
\begin{ltx}
\def\dof@author{}%
\newcommand{\DOFauthor}{\author{\dof@author}}
\AtBeginDocument{\DOFauthor}
\def\leftadd#1#2{\expandafter\leftaddaux\expandafter{#1}{#2}{#1}}
\def\leftaddaux#1#2#3{\gdef#3{#1#2}}
\newcounter{dof@cnt@author}
\newcommand{\addauthor}[1]{%
  \ifthenelse{\equal{\dof@author}{}}{%
    \gdef\dof@author{#1}%
  }{%
    \leftadd\dof@author{\protect\and #1}%
  }
}
\end{ltx}\<close>

The new command \<^boxed_latex>\<open>\addauthor\<close> and a similarly defined command \<^boxed_latex>\<open>\addaffiliation\<close>
can now be used in the definition of the representation of the concept 
\<^boxed_theory_text>\<open>text.scholarly_paper.author\<close>, which writes the collected information in the 
job's aux-file. The intermediate step of writing this information into the job's aux-file is necessary,
as the author and affiliation information is required right at the beginning of the document 
while  \<^isadof> allows defining  authors at  any place within a document:

\<^latex>\<open>
\begin{ltx}
\provideisadof{text.scholarly_paper.author}%
[label=,type=%
,scholarly_paper.author.email=%
,scholarly_paper.author.affiliation=%
,scholarly_paper.author.orcid=%
,scholarly_paper.author.http_site=%
][1]{%
  \stepcounter{dof@cnt@author}
  \def\dof@a{\commandkey{scholarly_paper.author.affiliation}}
  \ifthenelse{\equal{\commandkey{scholarly_paper.author.orcid}}{}}{%
    \immediate\write\@auxout%
       {\noexpand\addauthor{#1\noexpand\inst{\thedof@cnt@author}}}%
  }{%
    \immediate\write\@auxout%
        {\noexpand\addauthor{#1\noexpand%
            \inst{\thedof@cnt@author}%
                 \orcidID{\commandkey{scholarly_paper.author.orcid}}}}%
  }
  \protected@write\@auxout{}{%
               \string\addaffiliation{\dof@a\\\string\email{%
                    \commandkey{scholarly_paper.author.email}}}}%
}
\end{ltx}\<close>

Finally, the collected information is used in the  \<^boxed_latex>\<open>\author\<close> command using the 
\<^boxed_latex>\<open>AtBeginDocument\<close>-hook:
\<^latex>\<open>
\begin{ltx}
\newcommand{\DOFauthor}{\author{\dof@author}}
\AtBeginDocument{%
  \DOFauthor
}

\end{ltx}\<close>

\<close>

subsubsection\<open>Restricting the Use of Ontologies to Specific Templates\<close>

text\<open>
  As ontology representations might rely on features only provided by certain templates 
  (\<^LaTeX>-classes), authors of ontology representations might restrict their use to 
  specific classes. This can, \<^eg>, be done using the \<^ltxinline>\<open>\@ifclassloaded{}\<close> command:
\<^latex>\<open>
\begin{ltx}
\@ifclassloaded{llncs}{}%
{% LLNCS class not loaded
    \PackageError{DOF-scholarly_paper}
    {Scholarly Paper only supports LNCS as document class.}{}\stop%
}
\end{ltx}\<close>

  We encourage this clear and machine-checkable enforcement of restrictions while, at the same
  time, we also encourage to provide a package option to overwrite them. The latter allows 
  inherited ontologies to overwrite these restrictions and, therefore, to provide also support
  for additional document templates. For example, the ontology \<^boxed_theory_text>\<open>technical_report\<close>
  extends the \<^boxed_theory_text>\<open>scholarly_paper\<close> ontology and its \<^LaTeX> supports provides support
  for the \<^boxed_latex>\<open>scrrept\<close>-class which is not supported by the \<^LaTeX> support for 
  \<^boxed_theory_text>\<open>scholarly_paper\<close>.
\<close>

(*<*)
end
(*>*) 
  
