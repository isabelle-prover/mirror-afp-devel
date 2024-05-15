(*************************************************************************
 * Copyright (C) 
 *               2019-2023 The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory "M_02_Background"
  imports "M_01_Introduction"
begin
(*>*)

chapter*[background::text_section]\<open> Background\<close>
section*[bgrnd1::introduction]\<open>The Isabelle System Architecture\<close>

figure*[architecture::figure,relative_width="95",file_src="''figures/isabelle-architecture.pdf''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>

text*[bg::introduction]\<open>
While Isabelle is widely perceived as an interactive theorem 
prover for HOL (Higher-order Logic)~\<^cite>\<open>"nipkow.ea:isabelle:2002"\<close>, we would like to emphasize
the view that Isabelle is far more than that: it is the \<^emph>\<open>Eclipse of Formal Methods Tools\<close>.  This 
refers to the ``\<^emph>\<open>generic system framework of Isabelle/Isar underlying recent versions of Isabelle.  
Among other things, Isabelle provides an infrastructure for Isabelle plug-ins, comprising extensible 
state components and extensible syntax that can be bound to SML programs. Thus, the Isabelle 
architecture may be understood as an extension and refinement of the traditional `LCF approach', 
with explicit infrastructure for building derivative systems.\<close>''~\<^cite>\<open>"wenzel.ea:building:2007"\<close> 

The current system framework offers moreover the following features:
\<^item> a build management grouping components into to pre-compiled sessions,
\<^item> a prover IDE (PIDE) framework~\<^cite>\<open>"wenzel:asynchronous:2014"\<close> with various front-ends, 
\<^item> documentation-generation,
\<^item> code generators for various target languages,
\<^item> an extensible front-end language Isabelle/Isar, and,
\<^item> last but not least, an LCF style, generic theorem prover kernel as 
  the most prominent and deeply integrated system component.
\<close>
text\<open>
The Isabelle system architecture shown in @{figure \<open>architecture\<close>} comes with many layers, 
with Standard ML (SML) at the bottom layer as implementation  language. The architecture actually 
foresees a \<^emph>\<open>Nano-Kernel\<close> (our terminology) which resides in the SML structure \<^boxed_sml>\<open>Context\<close>. 
This structure provides a kind of container called \<^emph>\<open>context\<close> providing an identity, an 
ancestor-list as well as typed, user-defined state for plugins such as \<^isadof>. 
On top of the latter, the LCF-Kernel, tactics, automated proof procedures as well as specific 
support for higher specification constructs were built.\<^footnote>\<open>We use the term \<^emph>\<open>plugin\<close> for a collection 
of HOL-definitions, SML and Scala code in order to distinguish it from the official Isabelle 
term \<^emph>\<open>component\<close> which implies a particular format and support by the Isabelle build system.\<close>
\<close>

section*[dof::introduction]\<open>The Document Model Required by \<^dof>\<close>
text\<open>
  In this section, we explain the assumed document model underlying our Document Ontology Framework 
  (\<^dof>) in general. In particular we discuss the concepts 
   \<^emph>\<open>integrated document\<close>\<^bindex>\<open>integrated document\<close>, \<^emph>\<open>sub-document\<close>\<^bindex>\<open>sub-document\<close>,  
  \<^emph>\<open>document-element\<close>\<^bindex>\<open>document-element\<close>, and \<^emph>\<open>semantic macros\<close>\<^bindex>\<open>semantic macros\<close> occurring 
  inside document-elements. This type of document structure is quite common for scripts interactively
  evaluated in an incremental fashion. 
  Furthermore, we assume a bracketing mechanism that unambiguously allows to separate different 
  syntactic fragments and that can be nested. In the case of Isabelle, these are the guillemot 
  symbols \<open>\<open>...\<close>\<close>, which represent the begin and end of a \<^emph>\<open>cartouche\<close>\<^bindex>\<open>cartouche\<close>.\<close>


(*<*)
declare_reference*[docModGenConcr::figure]
(*>*)
text\<open>
  The Isabelle Framework is based on a \<^emph>\<open>document-centric view\<close>\<^bindex>\<open>document-centric view\<close> of 
  a document, treating the input in its integrality as set of (user-programmable) \<^emph>\<open>document element\<close> 
  that may mutually depend on and link to each other; A \<^emph>\<open>document\<close> in our sense is what is configured 
  in a set of  \<^verbatim>\<open>ROOT\<close>- and \<^verbatim>\<open>ROOTS\<close>-files.

  Isabelle assumes a hierarchical document model\<^index>\<open>document model\<close>, \<^ie>, an \<^emph>\<open>integrated\<close> document 
  consist of a hierarchy of \<^emph>\<open>sub-documents\<close>  (files); dependencies are restricted to be
  acyclic at this level (c.f. @{figure (unchecked) "docModGenConcr"}). 
  Document parts can have different document types in order to capture documentations consisting of 
  documentation, models, proofs, code of various forms and other technical artifacts.  We call the 
  main sub-document type, for historical reasons, \<^emph>\<open>theory\<close>-files.  A theory file\<^bindex>\<open>theory!file\<close>
  consists of a \<^emph>\<open>header\<close>\<^bindex>\<open>header\<close>, a \<^emph>\<open>context definition\<close>\<^index>\<open>context\<close>, and a body 
  consisting of a sequence of document elements called
  \<^emph>\<open>command\<close>s (see @{figure (unchecked) "docModGenConcr"} (left-hand side)). Even
  the header consists of a sequence of commands used for introductory text elements not depending on 
  any context. The context-definition contains an \<^boxed_theory_text>\<open>import\<close> and a 
  \<^boxed_theory_text>\<open>keyword\<close> section, for example:
@{boxed_theory_text [display]\<open>
  theory Example         \<comment>\<open>Name of the 'theory'\<close>
    imports              \<comment>\<open>Declaration of 'theory' dependencies\<close>
      Main               \<comment>\<open>Imports a library called 'Main'\<close>
    keywords             \<comment>\<open>Registration of keywords defined locally\<close>
      requirement        \<comment>\<open>A command for describing requirements\<close> \<close>}
  where \<^boxed_theory_text>\<open>Example\<close> is the abstract name of the text-file, \<^boxed_theory_text>\<open>Main\<close> 
  refers to an imported theory (recall that the import relation must be acyclic) and 
  \<^boxed_theory_text>\<open>keywords\<close> are used to separate commands from each other.
\<close>

text*[docModGenConcr::float, 
      main_caption="\<open>A Representation of a Document Model.\<close>"]
\<open>
@{fig_content (width=45, caption="Schematic Representation.") "figures/doc-mod-generic.pdf"
}\<^hfill>@{fig_content (width=45, caption="The Isar Instance.") "figures/doc-mod-isar.pdf"} 
\<close>

text\<open>The body of a theory file consists of a sequence of \<^emph>\<open>commands\<close> that must be introduced
by a command keyword such as \<^boxed_theory_text>\<open>requirement\<close> above. Command keywords may mark 
the the begin of a text that is parsed by a command-specific parser;  the end of the 
command-span is defined by the next keyword. Commands were used to define definitions, lemmas, 
code and text-elements (see @{float "docModGenConcr"} (right-hand side)).  \<close>

text\<open> A simple text-element \<^index>\<open>text-element\<close> may look like this:

  @{boxed_theory_text [display]\<open>
text\<open> This is a simple text.\<close>\<close>}
\ldots so it is a command \<^theory_text>\<open>text\<close> followed by an argument (here in  \<open>\<open> ... \<close>\<close> parenthesis) which 
contains characters. While \<^theory_text>\<open>text\<close>-elements play a major role in this manual---document 
generation is the main use-case of \<^dof> in its current stage---it is important to note that there 
are actually three families of ``ontology aware'' document elements with analogous 
syntax to standard ones. The difference is a bracket with meta-data of the form:
@{theory_text [display,indent=5, margin=70] 
\<open>
text*[label::classid, attr\<^sub>1=E\<^sub>1, ... attr\<^sub>n=E\<^sub>n]\<open> some semi-formal text \<close>
ML*[label::classid, attr\<^sub>1=E\<^sub>1, ... attr\<^sub>n=E\<^sub>n]\<open> some SML code \<close>
value*[label::classid, attr\<^sub>1=E\<^sub>1, ... attr\<^sub>n=E\<^sub>n]\<open> some annotated \<lambda>-term \<close>
\<close>}

Other instances of document elements belonging to these families are, for example, the free-form
\<^theory_text>\<open>Definition*\<close> and \<^theory_text>\<open>Lemma*\<close> as well as their formal counterparts \<^theory_text>\<open>definition*\<close> and \<^theory_text>\<open>lemma*\<close>,
which allow in addition to their standard Isabelle functionality the creation and management of
ontology-generated meta-data associated to them (cf. -@{text_section (unchecked) "writing_doc"}).

Depending on the family, we will speak about \<^emph>\<open>(formal) text-contexts\<close>,\<^bindex>\<open>formal text-contexts\<close> 
\<^emph>\<open>(ML) code-contexts\<close>\<^bindex>\<open>code-contexts\<close> and \<^emph>\<open>term-contexts\<close>\<^bindex>\<open>term-contexts\<close> if we refer 
to sub-elements inside the \<open>\<open>...\<close>\<close> cartouches of these command families. 

Text- code- or term contexts may contain a special form comment, that may be considered as a
"semantic macro" or a machine-checked annotation: the so-called antiquotations\<^bindex>\<open>antiquotation\<close>. 
Its Its general syntactic format reads as follows:

@{boxed_theory_text [display]\<open> @{antiquotation_name (args) [more_args] \<open>sub-context\<close> }\<close>}

The sub-context may be different from the surrounding one; therefore, it is possible
to switch from a text-context to a term-context, for example. Therefore, antiquotations allow
 the nesting of cartouches, albeit not all combinations are actually supported.\<^footnote>\<open>In the 
literature, this concept has been referred to \<open>Cascade-Syntax\<close> and was used in the 
Centaur-system and is existing in some limited form in some Emacs-implementations these days. \<close> 
Isabelle comes with a number of built-in antiquotations for text- and code-contexts;
a detailed overview can be found in \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>. \<^dof> reuses this general
infrastructure but \<^emph>\<open>generates\<close> its own families of antiquotations from ontologies.\<close>

text\<open> An example for a text-element \<^index>\<open>text-element\<close> using built-in antoquotations 
may look like this:

@{boxed_theory_text [display]\<open>
text\<open> According to the \<^emph>\<open>reflexivity\<close> axiom @{thm refl}, 
   we obtain in \<Gamma> for @{term "fac 5"} the result @{value "fac 5"}.\<close>\<close>}
... so it is a command \<^theory_text>\<open>text\<close> followed by an argument (here in  \<open>\<open> ... \<close>\<close> parenthesis) which 
contains characters and a special notation for semantic macros \<^bindex>\<open>semantic macros\<close> 
(here \<^theory_text>\<open>@{term "fac 5"}\<close>).

The above text element is represented in the final document (\<^eg>, a PDF) by:

@{boxed_pdf [display]
\<open>According to the $\emph{reflexivity}$ axiom $\mathrm{x = x}$, we obtain in $\Gamma$ 
for $\operatorname{fac} \text{\textrm{5}}$ the result $\text{\textrm{120}}$.\<close>
 }\<close>


text\<open>Antiquotations seen as semantic macros are partial functions of type \<open>logical_context \<rightarrow> text\<close>; 
  since they can use the system state, they can perform all sorts of specific checks or evaluations 
  (type-checks, executions of code-elements, references to text-elements or proven theorems such as 
  \<open>refl\<close>, which is the reference to the axiom of reflexivity).

  Therefore, semantic macros can establish \<^emph>\<open>formal content\<close> inside informal content; they can be 
  type-checked before being displayed and can be used for calculations before being 
  typeset. They represent the device for linking formal with the informal content. 
\<close>

text*[docModOnto::float, 
      main_caption="\<open>Documents conform to Ontologies.\<close>"]
\<open>
@{fig_content (width=47, caption="A Document with Ontological Annotations.") "figures/doc-mod-DOF.pdf"
}\<^hfill>@{fig_content (width=47, caption="Ontological References.") "figures/doc-mod-onto-docinst.pdf"} 
\<close>

text\<open>Since Isabelle's commands are freely programmable, it is possible to implement  \<^dof> as an 
extension of the system. In particular, the ontology language of \<^dof> provides an  ontology 
definition language ODL\<^bindex>\<open>ODL\<close> that \<^emph>\<open>generates\<close> anti-quotations and the infrastructure to check and evaluate 
them. This allows for checking an annotated document with respect to a given ontology, which may be 
specific for  a given domain-specific universe of discourse (see @{float "docModOnto"}). ODL will 
be described in  @{text_section (unchecked) "isadof_tour"} in more detail.\<close>

section*[bgrnd21::introduction]\<open>Implementability of the Document Model in other ITP's\<close>
text\<open> 
  Batch-mode checkers for \<^dof> can be implemented in all systems of the LCF-style prover family, 
  \<^ie>, systems with a type-checked \<open>term\<close>, and abstract \<open>thm\<close>-type for theorems 
  (protected by a kernel).  This includes, \<^eg>, ProofPower, HOL4, HOL-light, Isabelle, or Coq
  and its derivatives. \<^dof> is, however, designed for fast interaction in an IDE. If a user wants
  to benefit from this experience, only Isabelle and Coq have the necessary infrastructure of 
  asynchronous proof-processing and support by a PIDE~\<^cite>\<open>"wenzel:asynchronous:2014" and 
  "wenzel:system:2014" and "barras.ea:pervasive:2013" and "faithfull.ea:coqoon:2018"\<close> which 
  in many features over-accomplishes the required  features of \<^dof>. 
\<close>

figure*["fig_dof_ide",relative_width="95",file_src="''figures/cicm2018-combined.png''"]\<open> 
     The \<^isadof> IDE (left) and the corresponding PDF (right), showing the first page
      of~\<^cite>\<open>"brucker.ea:isabelle-ontologies:2018"\<close>.\<close>

text\<open> 
  We call the present implementation of \<^dof> on the Isabelle platform  \<^isadof> . 
  @{figure  "fig_dof_ide"} shows a screenshot of an introductory paper on 
  \<^isadof>~\<^cite>\<open>"brucker.ea:isabelle-ontologies:2018"\<close>: the \<^isadof> PIDE can be seen on the left, 
  while the generated presentation in PDF is shown on the right.

  Isabelle provides, beyond the features required for \<^dof>, a lot of additional benefits. 
  Besides UTF8-support for characters used in text-elements, Isabelle offers built-in already a 
  mechanism for user-programmable antiquotations \<^index>\<open>antiquotations\<close> which we use to implement
  semantic macros \<^index>\<open>semantic macros\<close> in \<^isadof> (We will actually use these two terms
  as synonym in the context of \<^isadof>). Moreover, \<^isadof> allows for the asynchronous 
  evaluation and checking of the document content~\<^cite>\<open>"wenzel:asynchronous:2014" and 
  "wenzel:system:2014" and "barras.ea:pervasive:2013"\<close> and is dynamically extensible. Its PIDE 
  provides a  \<^emph>\<open>continuous build, continuous check\<close>  functionality, syntax highlighting, and 
  auto-completion. It also provides infrastructure for displaying meta-information (\<^eg>, binding 
  and type annotation) as pop-ups, while hovering over sub-expressions.  A fine-grained dependency 
  analysis allows the processing of individual parts of theory files asynchronously, allowing 
  Isabelle to interactively process large (hundreds of theory files) documents.  Isabelle can group 
  sub-documents into sessions, \<^ie>, sub-graphs of the document-structure that can be ``pre-compiled'' 
  and loaded instantaneously, \<^ie>, without re-processing, which is an important means to scale up. \<close>

(*<*) 
end
(*>*) 
  
