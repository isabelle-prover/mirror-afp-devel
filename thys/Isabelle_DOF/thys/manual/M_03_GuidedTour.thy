(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2018-2022 The University of Paris-Saclay
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
    "M_03_GuidedTour" 
  imports 
    "M_02_Background"
begin
(*>*)

chapter*[isadof_tour::text_section]\<open>\<^isadof>: A Guided Tour\<close>

text\<open>
  In this chapter, we will give an introduction into using \<^isadof> for users that want to create and 
  maintain documents following an existing document ontology\<^bindex>\<open>ontology\<close> in ODL\<^bindex>\<open>ODL\<close>.
\<close>

section*[getting_started::technical]\<open>Getting Started\<close>

subsection*[installation::technical]\<open>Installation\<close>
text\<open>
  In this section, we will show how to install \<^isadof>. We assume a basic familiarity with a 
  Linux/Unix-like command line (i.e., a shell). 
  We focus on the installation of the latest official release of  \<^isadof> as 
  available in the Archive of Formal Proofs (AFP).\<^footnote>\<open>If you want to work with the development version 
  of \<^isadof>, please obtain its source code from the \<^isadof> Git repostitory 
  (\<^url>\<open>https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF\<close> and follow the instructions
  in provided \<^verbatim>\<open>README.MD\<close> file.\<close>
  \<^isadof> requires Isabelle\<^bindex>\<open>Isabelle\<close> with a recent \<^LaTeX>-distribution
  (e.g., Tex Live 2022 or later).    
\<close>

paragraph\<open>Installing Isabelle and the AFP.\<close>
text\<open>
  Please download and install the latest official Isabelle release from the Isabelle Website 
  (\<^url>\<open>https://isabelle.in.tum.de\<close>). After the successful installation of Isabelle, you should be 
  able to call the \<^boxed_bash>\<open>isabelle\<close> tool on the command line:
@{boxed_bash [display]\<open>ë\prompt{}ë isabelle version\<close>}

Depending on your operating system and depending if you put Isabelle's  \<^boxed_bash>\<open>bin\<close> directory
in your  \<^boxed_bash>\<open>PATH\<close>, you will need to invoke  \<^boxed_bash>\<open>isabelle\<close> using its
full qualified path.
\<close>

text\<open>
Next, download the the AFP from \<^url>\<open>https://www.isa-afp.org/download/\<close> and 
follow the instructions given at \<^url>\<open>https://www.isa-afp.org/help/\<close> for installing the AFP as an 
Isabelle component.\<close>

paragraph\<open>Installing \<^TeXLive>.\<close>
text\<open>
 On a Debian-based Linux system (\<^eg>, Ubuntu), the following command 
  should install all required \<^LaTeX> packages:
@{boxed_bash [display]\<open>ë\prompt{}ë sudo aptitude install texlive-full\<close>}
\<close>

subsubsection*[isadof::technical]\<open>Installing \<^isadof>\<close>
text\<open>
By installing the AFP in the previous steps, you already installed \<^isadof>. In fact, \<^isadof> 
is currently consisting out of three AFP entries:

\<^item> \<^verbatim>\<open>Isabelle_DOF\<close>: This entry
  contains the \<^isadof> system itself, including the \<^isadof> manual.
\<^item> \<^verbatim>\<open>Isabelle_DOF-Example-I\<close>: This entry contains an example of 
  an academic paper written using the \<^isadof> system oriented towards an 
  introductory paper. The text is based on~\<^cite>\<open>"brucker.ea:isabelle-ontologies:2018"\<close>;
  in the document, we deliberately  refrain from integrating references to formal content in order 
  to demonstrate that \<^isadof> can be used for writing documents with very little direct use of
 \<^LaTeX>.
\<^item> \<^verbatim>\<open>Isabelle_DOF-Example-II\<close>: This entry contains another example of 
  a mathematics-oriented academic paper. It is based on~\<^cite>\<open>"taha.ea:philosophers:2020"\<close>.
  It represents a typical mathematical text, heavy in definitions with complex mathematical notation 
  and a lot of non-trivial cross-referencing between statements, definitions, and proofs which 
  are ontologically tracked. However, with respect to the possible linking between the underlying formal theory 
  and this mathematical presentation, it follows a pragmatic path without any ``deep'' linking to 
  types, terms and theorems, and therefore does deliberately not exploit \<^isadof> 's full potential.\<close>


section*[writing_doc::technical]\<open>Writing Documents\<close>

subsection*[document::example]\<open>Document Generation\<close>

text\<open>\<^isadof> provides an enhanced setup for generating PDF document. In particular, it does 
not make use of a file called \<^verbatim>\<open>document/root.tex\<close>. Instead, the use of document templates and 
ontology represenations is done within theory files. To make use of this feature, one needs
to add the option \<^verbatim>\<open>document_build = dof\<close> to the \<^verbatim>\<open>ROOT\<close> file. 
An example \<^verbatim>\<open>ROOT\<close> file looks as follows:
\<close>
text\<open>
\begin{config}{ROOT}
session example = Isabelle_DOF +
  options [document = pdf, document_output = "output", document_build = dof]
(*theories [document = false]
    A
  theories
    B*)
\end{config}

The document template and ontology can be selected as follows:
@{boxed_theory_text [display]
\<open>
theory C imports Isabelle_DOF.technical_report Isabelle_DOF.scholarly_paper begin
  list_templates
  use_template "scrreprt-modern"
  list_ontologies
  use_ontology "technical_report" and "scholarly_paper"
end
\<close>}

The commands @{boxed_theory_text 
\<open>
list_templates
\<close>} and 
@{boxed_theory_text 
\<open>
list_ontologies
\<close>}
can be used for inspecting (and selecting) the available ontologies and templates: 
@{boxed_theory_text [display]
\<open>
list_templates
list_ontologies
\<close>}

Note that you need to import the theories that define the ontologies that you 
want to use. Otherwise, they will not be available.
\<close>

paragraph\<open>Warning.\<close>
text\<open>
Note that the session \<^session>\<open>Isabelle_DOF\<close> needs to be part of the ``main'' session 
hierarchy. Loading the \<^isadof> theories as part of a session section, e.g., 
\<close>
text\<open>\<^latex>\<open>
\begin{config}{ROOT}
session example = HOL +
  options [document = pdf, document_output = "output", document_build = dof]
  session 
    Isabelle_DOF.scholarly_paper
  theories
    C
\end{config}
\<close>\<close>
text\<open>
will not work. Trying to build a document using such a setup will result in the 
following error message:

@{boxed_bash [display]\<open>ë\prompt{}ë
  isabelle build -D . 
  Running example ... 
  Bad document_build engine "dof"
  example FAILED\<close>}
\<close> 

subsection*[naming::example]\<open>Name-Spaces, Long- and Short-Names\<close>
text\<open>\<^isadof> is built upon the name space and lexical conventions of Isabelle. Long-names were 
composed of a name of the session, the name of the theory, and a sequence of local names referring
to, \<^eg>, nested specification constructs that were used to identify types, constant symbols, 
definitions, \<^etc>. The general format of a long-name is 

 \<^boxed_theory_text>\<open> session_name.theory_name.local_name. ... .local_name\<close>

By lexical conventions, theory-names must be unique inside a session
(and session names must be unique too), such that long-names are unique by construction.
There are actually different name categories that form a proper name space, \<^eg>, the name space for
constant symbols and type symbols are distinguished.
Additionally, \<^isadof> objects also come with a proper name space: classes (and monitors), instances,
low-level class invariants (SML-defined invariants) all follow the lexical conventions of
Isabelle. For instance, a class can be referenced outside its theory using
its short-name or its long-name if another class with the same name is defined
in the current theory.
Isabelle identifies names already with the shortest suffix that is unique in the global 
context and in the appropriate name category. This also holds for pretty-printing, which can
at times be confusing since names stemming from the same specification construct may
be printed with different prefixes according to their uniqueness.
\<close>

subsection*[cartouches::example]\<open>Caveat: Lexical Conventions of Cartouches, Strings, Names, ... \<close>
text\<open>WARNING: The embedding of strings, terms, names \<^etc>, as parts of commands, anti-quotations,
terms, \<^etc>, is unfortunately not always so consistent as one might expect, when it comes
to variants that should be lexically equivalent in principle. This can be a nuisance for
users, but is again a consequence that we build on existing technology that has been developed
over decades. 
\<close>

text\<open>At times, this causes idiosyncrasies like the ones cited in the following incomplete list: 
\<^item> text-antiquotations
  \<^theory_text>\<open>text\<open>@{thm \<doublequote>srac\<^sub>1_def\<doublequote>}\<close>\<close>  
  while \<^theory_text>\<open>text\<open>@{thm \<open>srac\<^sub>1_def\<close>}\<close>\<close> fails
\<^item> commands \<^theory_text>\<open>thm fundamental_theorem_of_calculus\<close> and
  \<^theory_text>\<open>thm \<doublequote>fundamental_theorem_of_calculus\<doublequote>\<close> 
  or \<^theory_text>\<open>lemma \<doublequote>H\<doublequote>\<close> and \<^theory_text>\<open>lemma \<open>H\<close>\<close> and  \<^theory_text>\<open>lemma H\<close>
\<^item> string expressions
  \<^theory_text>\<open>term\<open>\<quote>\<quote>abc\<quote>\<quote> @ \<quote>\<quote>cd\<quote>\<quote>\<close>\<close> and equivalent
  \<^theory_text>\<open>term \<open>\<open>abc\<close> @ \<open>cd\<close>\<close>\<close>;
  but \<^theory_text>\<open>term\<open>\<open>A \<longrightarrow> B\<close>\<close>\<close> not equivalent to \<^theory_text>\<open>term\<open>\<quote>\<quote>A \<longrightarrow> B\<quote>\<quote>\<close>\<close>
  which fails. 
\<close>

section*[scholar_onto::example]\<open>Writing Academic Publications in \<^boxed_theory_text>\<open>scholarly_paper\<close>\<close>  
subsection\<open>Editing Major Examples\<close>
text\<open> 
  The ontology \<^verbatim>\<open>scholarly_paper\<close>  \<^index>\<open>ontology!scholarly\_paper\<close> is an ontology modeling 
  academic/scientific papers, with a slight bias towards texts in the domain of mathematics and
  engineering. 

  You can inspect/edit the example in Isabelle's IDE, by either 
     \<^item> starting Isabelle/jEdit using your graphical user interface (\<^eg>, by clicking on the 
       Isabelle-Icon provided by the Isabelle installation) and loading the file 
       \<^nolinkurl>\<open>Isabelle_DOF-Example-I/IsaDofApplications.thy"\<close>
\<close>
text\<open> You can build the \<^pdf>-document at the command line by calling:
@{boxed_bash [display] \<open>ë\prompt{}ë isabelle build Isabelle_DOF-Example-I\<close>}
\<close>

subsection*[sss::technical]\<open>A Bluffers Guide to the \<^verbatim>\<open>scholarly_paper\<close> Ontology\<close>
text\<open> In this section we give a minimal overview of the ontology formalized in 
 \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>. We start by modeling the usual text-elements of an 
 academic paper: the title and author information, abstract, and text section: 
@{boxed_theory_text [display]
\<open>doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev ::      "string option"   <=  "None"
   
doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"

doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"\<close>}
\<close>

text\<open>Note \<^const>\<open>short_title\<close> and \<^const>\<open>abbrev\<close> are optional and have the default \<^const>\<open>None\<close>
(no value). Note further, that \<^typ>\<open>abstract\<close>s may have a \<^const>\<open>principal_theorems\<close> list, where
the built-in \<^isadof> type \<^typ>\<open>thm list\<close> contains references to formally proven theorems that must
exist in the logical context of this document; this is a decisive feature of \<^isadof> that
conventional ontological languages lack.\<close>

text\<open>We continue by the introduction of a main class: the text-element \<^typ>\<open>text_section\<close>
(in contrast to \<^typ>\<open>figure\<close> or \<open>table\<close> or similar). Note that
the \<^const>\<open>main_author\<close> is typed with the class \<^typ>\<open>author\<close>, a HOL type that is automatically
derived from the document class definition \<^typ>\<open>author\<close> shown above. It is used to express which
author currently ``owns'' this \<^typ>\<open>text_section\<close>, an information that can give rise to
presentational or even access-control features in a suitably adapted front-end.
 
@{boxed_theory_text [display] \<open>
doc_class text_section = text_element +
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"
\<close>}

The \<^const>\<open>Isa_COL.text_element.level\<close>-attibute \<^index>\<open>level\<close> enables doc-notation support for
headers, chapters, sections, and subsections; we follow here the \<^LaTeX> terminology on levels to 
which \<^isadof> is currently targeting at. The values are interpreted accordingly to the \<^LaTeX> 
standard. The correspondence between the levels and the structural entities is summarized 
as follows:

   \<^item> part          \<^index>\<open>part\<close>          \<open>Some -1\<close> \<^vs>\<open>-0.3cm\<close>
   \<^item> chapter       \<^index>\<open>chapter\<close>       \<open>Some 0\<close>  \<^vs>\<open>-0.3cm\<close>
   \<^item> section       \<^index>\<open>section\<close>       \<open>Some 1\<close>  \<^vs>\<open>-0.3cm\<close>
   \<^item> subsection    \<^index>\<open>subsection\<close>    \<open>Some 2\<close>  \<^vs>\<open>-0.3cm\<close>
   \<^item> subsubsection \<^index>\<open>subsubsection\<close> \<open>Some 3\<close>  \<^vs>\<open>-0.3cm\<close>

Additional means assure that the following invariant is maintained in a document 
conforming to \<^verbatim>\<open>scholarly_paper\<close>: \<open>level > 0\<close>.
\<close>

text\<open> The rest of the ontology introduces concepts for \<^typ>\<open>introduction\<close>, \<^typ>\<open>conclusion\<close>,
\<^typ>\<open>related_work\<close>, \<^typ>\<open>bibliography\<close> etc. More details can be found in \<^verbatim>\<open>scholarly_paper\<close>
contained in the theory \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>. \<close>

subsection\<open>Writing Academic Publications: A Freeform Mathematics Text \<close>
text*[csp_paper_synthesis::technical, main_author = "Some bu"]\<open>We present a typical mathematical
paper focusing on its form, not referring in any sense to its content which is out of scope here.
As mentioned before, we chose the paper~\<^cite>\<open>"taha.ea:philosophers:2020"\<close> for this purpose,
which is written in the so-called free-form style: Formulas are superficially parsed and 
type-set, but no deeper type-checking and checking with the underlying logical context
is undertaken. \<close>

figure*[fig0::figure,relative_width="85",file_src="''figures/header_CSP_source.png''"]
       \<open> A mathematics paper as integrated document source ... \<close>  

figure*[fig0B::figure,relative_width="85",file_src="''figures/header_CSP_pdf.png''"]
       \<open> ... and as corresponding \<^pdf>-output. \<close>  

text\<open>The integrated source of this paper-excerpt is shown in \<^figure>\<open>fig0\<close>, while the
document build process converts this to the corresponding \<^pdf>-output shown in \<^figure>\<open>fig0B\<close>.\<close>


text\<open>Recall that the standard syntax for a text-element in \<^isadof> is 
\<^theory_text>\<open>text*[<id>::<class_id>,<attrs>]\<open> ... text ...\<close>\<close>, but there are a few built-in abbreviations like
\<^theory_text>\<open>title*[<id>,<attrs>]\<open> ... text ...\<close>\<close> that provide special command-level syntax for text-elements. 
The other text-elements provide the authors and the abstract as specified by their
\<^emph>\<open>class\_id\<close>\<^index>\<open>class\_id@\<open>class_id\<close>\<close>
referring to the \<^theory_text>\<open>doc_class\<close>es of \<^verbatim>\<open>scholarly_paper\<close>;
we say that these text elements are \<^emph>\<open>instances\<close> 
\<^bindex>\<open>instance\<close> of the \<^theory_text>\<open>doc_class\<close>es \<^bindex>\<open>doc\_class\<close> of the underlying ontology. \<close>

text\<open>The paper proceeds by providing instances for introduction, technical sections, 
examples, \<^etc>. We would like to concentrate on one --- mathematical paper oriented --- detail in the 
ontology \<^verbatim>\<open>scholarly_paper\<close>: 

@{boxed_theory_text [display]
\<open>doc_class technical = text_section +  ...

type_synonym tc = technical (* technical content *)

datatype math_content_class = "defn" | "axm" | "thm"  | "lem" | "cor" | "prop" | ...
                           
doc_class math_content = tc +   ...

doc_class "definition"  = math_content +
   mcc           :: "math_content_class" <= "defn"  ...

doc_class "theorem"     = math_content +
   mcc           :: "math_content_class" <= "thm"   ... 
\<close>}\<close>


text\<open>The class \<^typ>\<open>technical\<close> regroups a number of text-elements that contain typical 
technical content in mathematical or engineering papers: code, definitions, theorems, 
lemmas, examples. From this class, the stricter class of @{typ \<open>math_content\<close>} is derived,
which is grouped into @{typ "definition"}s and @{typ "theorem"}s (the details of these
class definitions are omitted here). Note, however, that class identifiers can be abbreviated by 
standard \<^theory_text>\<open>type_synonym\<close>s for convenience and enumeration types can be defined by the 
standard inductive \<^theory_text>\<open>datatype\<close> definition mechanism in Isabelle, since any HOL type is admitted
for attribute declarations. Vice-versa, document class definitions imply a corresponding HOL type 
definition. \<close>

figure*[fig01::figure,relative_width="95",file_src="''figures/definition-use-CSP.png''"]
       \<open> A screenshot of the integrated source with definitions ...\<close>  
text\<open>An example for a sequence of (Isabelle-formula-)texts, their ontological declarations as 
\<^typ>\<open>definition\<close>s in terms of the \<^verbatim>\<open>scholarly_paper\<close>-ontology and their type-conform referencing 
later is shown in \<^figure>\<open>fig01\<close> in its presentation as the integrated source.

Note that the use in the ontology-generated antiquotation \<^theory_text>\<open>@{definition X4}\<close>
is type-checked; referencing \<^verbatim>\<open>X4\<close> as \<^theory_text>\<open>theorem\<close> would be a type-error and be reported directly
by \<^isadof> in Isabelle/jEdit. Note further, that if referenced correctly wrt. the sub-typing 
hierarchy makes \<^verbatim>\<open>X4\<close> \<^emph>\<open>navigable\<close> in Isabelle/jEdit; a click will cause the IDE to present the 
defining occurrence of this text-element in the integrated source.

Note, further, how \<^isadof>-commands like \<^theory_text>\<open>text*\<close> interact with standard Isabelle document
antiquotations described in the Isabelle Isar Reference Manual in Chapter 4.2 in great detail. 
We refrain ourselves here to briefly describe three freeform antiquotations used in this text:

\<^item>  the freeform term antiquotation, also called \<^emph>\<open>cartouche\<close>, written by
   \<open>@{cartouche [style-parms] \<open>...\<close>}\<close> or just by \<open>\<open>...\<close>\<close> if the list of style parameters
   is empty,
\<^item>  the freeform antiquotation for theory fragments written \<open>@{theory_text [style-parms] \<open>...\<close>}\<close>
   or just \<^verbatim>\<open>\<^theory_text>\<close>\<open>\<open>...\<close>\<close> if the list of style parameters is empty,  
\<^item>  the freeform antiquotations for verbatim, emphasized, bold, or footnote text elements.
\<close>

figure*[fig02::figure,relative_width="95",file_src="''figures/definition-use-CSP-pdf.png''"]
       \<open> ... and the corresponding \<^pdf>-output.\<close>  

text\<open>
\<^isadof> text-elements such as \<^theory_text>\<open>text*\<close> allow to have such standard term-antiquotations inside their
text, permitting to give the whole text entity a formal, referentiable status with typed
meta-information attached to it that may be used for presentation issues, search,
or other technical purposes.
The corresponding output of this snippet in the integrated source is shown in \<^figure>\<open>fig02\<close>. 
\<close>


subsection*[scholar_pide::example]\<open>More Freeform Elements, and Resulting Navigation\<close>
text\<open> In the following, we present some other text-elements provided by the Common Ontology Library
in @{theory "Isabelle_DOF.Isa_COL"}. It provides a document class for figures:

@{boxed_theory_text [display]\<open>
datatype placement = h | t | b | ht | hb   
doc_class figure   = text_section +
   relative_width  :: "int" (* percent of textwidth *)    
   src             :: "string"
   placement       :: placement 
   spawn_columns   :: bool <= True 
\<close>}
\<close>
figure*[fig_figures::figure,relative_width="85",file_src="''figures/Dogfood-figures.png''"]
       \<open> Declaring figures in the integrated source.\<close>

text\<open> 
  The document class \<^typ>\<open>figure\<close> (supported by the \<^isadof> command abbreviation
  \<^boxed_theory_text>\<open>figure*\<close>) makes it possible to express the pictures and diagrams 
  as shown in \<^figure>\<open>fig_figures\<close>, which presents its own representation in the 
  integrated source as screenshot.\<close>

text\<open>
  Finally, we define a \<^emph>\<open>monitor class\<close> \<^index>\<open>monitor class\<close> that enforces a textual ordering
  in the document core by a regular expression:

  @{boxed_theory_text [display]\<open>
  doc_class article = 
     style_id :: string                <= "''LNCS''"
     version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
     accepts "(title ~~ \<lbrakk>subtitle\<rbrakk> ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ abstract ~~ \<lbrace>introduction\<rbrace>\<^sup>+
                   ~~ \<lbrace>background\<rbrace>\<^sup>* ~~ \<lbrace>technical || example \<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+
                   ~~ bibliography ~~ \<lbrace>annex\<rbrace>\<^sup>* )"
  \<close>}\<close>

text\<open>
  In a integrated document source, the body of the content can be paranthesized into:

  @{boxed_theory_text [display]\<open>
  open_monitor* [this::article] 
  ...
  close_monitor*[this]
  \<close>} 

which signals to \<^isadof> begin and end of the part of the integrated source 
in which the text-elements instances are expected to appear in the textual ordering 
defined by \<^typ>\<open>article\<close>.
\<close>
text*[exploring::float, 
      main_caption="\<open>Exploring text elements.\<close>"]
\<open>
@{fig_content (width=45, caption="Exploring a reference of a text-element.") "figures/Dogfood-II-bgnd1.png"
}\<^hfill>@{fig_content (width=45, caption="Exploring the class of a text element.") "figures/Dogfood-III-bgnd-text_section.png"} 
\<close>

text*[hyperlinks::float, 
      main_caption="\<open>Navigation via generated hyperlinks.\<close>"]
\<open>
@{fig_content (width=45, caption="Hyperlink to class-definition.") "figures/Dogfood-IV-jumpInDocCLass.png"
}\<^hfill>@{fig_content (width=45, caption="Exploring an attribute (hyperlinked to the class).") "figures/Dogfood-V-attribute.png"} 
\<close>

text\<open> 
  From these class definitions, \<^isadof> also automatically generated editing 
  support for Isabelle/jEdit. In 
  @{float "exploring"}(left)
  % \autoref{fig-Dogfood-II-bgnd1} 
  and
  @{float "exploring"}(right)
  % \autoref{fig-bgnd-text_section} 
  we show how hovering over links permits to explore its 
  meta-information. Clicking on a document class identifier permits to hyperlink into the 
  corresponding class definition (
  @{float "hyperlinks"}(left)
  %\autoref{fig:Dogfood-IV-jumpInDocCLass})
  ; hovering over an attribute-definition (which is qualified in order to disambiguate; cf.
  @{float "hyperlinks"}(right)
  %\autoref{fig:Dogfood-V-attribute}
  ) shows its type.
\<close>

figure*[figDogfoodVIlinkappl::figure,relative_width="80",file_src="''figures/Dogfood-VI-linkappl.png''"]
       \<open>Exploring an ontological reference.\<close> 

text\<open> 
An ontological reference application in @{figure "figDogfoodVIlinkappl"}: the 
ontology-dependant antiquotation \<^boxed_theory_text>\<open>@{example \<open>ex1\<close>}\<close> refers to the corresponding 
text-element \<^boxed_theory_text>\<open>ex1\<close>. Hovering allows for inspection, clicking for jumping to the 
definition. If the  link does not exist or  has a non-compatible type, the text is not validated,
 \<^ie>, Isabelle/jEdit will respond with an error.\<close>

text\<open>We advise users to experiment with different notation variants.
Note, further, that the Isabelle \<^latex>\<open>@\{cite ...\}\<close>-text-anti-quotation makes its checking
on the level of generated \<^verbatim>\<open>.aux\<close>-files, which are not necessarily up-to-date. Ignoring the PIDE
error-message and compiling it with a consistent bibtex usually makes disappear this behavior. 
\<close>

subsection*["using_term_aq"::technical, main_author = "Some @{author ''bu''}"]
   \<open>Using Term-Antiquotations\<close>

text\<open>The present version of \<^isadof> is the first version that supports the novel feature of
\<^dof>-generated term-antiquotations\<^bindex>\<open>term-antiquotations\<close>, \<^ie>, antiquotations embedded
in HOL-\<open>\<lambda>\<close>-terms possessing arguments that were validated in the ontological context.
These \<open>\<lambda>\<close>-terms may occur in definitions, lemmas, or in values to define attributes 
in class instances. They have the format: \<open>@{name arg\<^sub>1 ... arg\<^sub>n\<^sub>-\<^sub>1} arg\<^sub>n\<close>\<close>

text\<open>Logically, they are defined as an identity in the last argument \<open>arg\<^sub>n\<close>; thus,
ontologically checked prior arguments \<open>arg\<^sub>1 ... arg\<^sub>n\<^sub>-\<^sub>1\<close> can be ignored during a proof
process; ontologically, they can be used to assure the traceability of, \<^eg>, semi-formal 
assumptions throughout their way to formalisation and use in lemmas and proofs. \<close> 

figure*[doc_termAq::figure,relative_width="35",file_src="''figures/doc-mod-term-aq.pdf''"]
                      \<open>Term-Antiquotations Referencing to Annotated Elements\<close>
text\<open>As shown in @{figure \<open>doc_termAq\<close>}, this feature of  \<^isadof> substantially increases
the expressibility of links between the formal and the informal in \<^dof> documents.\<close>

text\<open> In the following, we describe a common scenario linking semi-formal assumptions and
formal ones:

@{boxed_theory_text [display]
\<open>
declare_reference*[e2::"definition"]

Assumption*[a1::"assumption", short_name="\<open>safe environment.\<close>"]
\<open>The system shall only be used in the temperature range from 0 to 60 degrees Celsius.
 Formally, this is stated as follows in @{definition (unchecked) \<open>e2\<close>}.\<close>

definition*[e2, status=formal] safe_env :: "state \<Rightarrow> bool" 
   where "safe_env \<sigma> \<equiv> (temp \<sigma> \<in> {0 .. 60})"

theorem*[e3::"theorem"] safety_preservation::" @{assumption \<open>a1\<close>} (safe_env \<sigma>) \<Longrightarrow> ...  "
\<close>}
\<close>
text\<open>Note that Isabelle procedes in a strict ``declaration-before-use''-manner, \<^ie> assumes
linear visibility on all references. This also holds for the declaration of ontological 
references. In order to represent cyclic dependencies, it is therefore necessary to 
start with the forward declaration \<^theory_text>\<open>declare_reference*\<close>. From there on, this reference
can be used in text, term, and code-contexts, albeit its definition appears textually later.
The corresponding freeform-formulation of this assumption can be explicitly referred in the
assumption of a theorem establishing the link. The \<^theory_text>\<open>theorem*\<close>-variant of the common 
Isabelle/Isar  \<^theory_text>\<open>theorem\<close>-command will in contrast to the latter not ignore \<open>\<open>a1\<close>\<close>,
 \<^ie> parse just as string, but also validate it in the previous context.

Note that the \<^theory_text>\<open>declare_reference*\<close> command will appear in the \<^LaTeX> generated from this 
document fragment. In order to avoid this, one has to enclose this command into the 
document comments : \<open>(*<*) ... (*>*)\<close>.\<close>


section*[tech_onto::example]\<open>Writing Technical Reports in \<^boxed_theory_text>\<open>technical_report\<close>\<close>  
text\<open>While it is perfectly possible to write documents in the
\<^verbatim>\<open>technical_report\<close> ontology in freeform-style (this manual is mostly such an
example), we will briefly explain here the tight-checking-style in which
most Isabelle reference manuals themselves are written. 

The idea has already been put forward by Isabelle itself; besides the general infrastructure on 
which this work is also based, current Isabelle versions provide around 20 built-in 
document and code antiquotations described in the Reference Manual pp.75 ff. in great detail.

Most of them provide strict-checking, \<^ie> the argument strings were parsed and machine-checked in the
underlying logical context, which turns the arguments into \<^emph>\<open>formal content\<close> in the integrated
source, in contrast to the free-form antiquotations which basically influence the presentation.

We still mention a few of these document antiquotations here:
\<^item> \<^theory_text>\<open>@{thm \<doublequote>refl\<doublequote>}\<close> or \<^theory_text>\<open>@{thm [display] \<doublequote>refl\<doublequote>}\<close>
  check that \<^theory_text>\<open>refl\<close> is indeed a reference
  to a theorem; the additional ``style" argument changes the presentation by printing the 
  formula into the output instead of the reference itself,
\<^item> \<^theory_text>\<open>@{lemma \<open>prop\<close> by method} \<close> allows deriving \<open>prop\<close> on the fly, thus guarantee 
  that it is a corollary of the current context,
\<^item> \<^theory_text>\<open>@{term \<open>term\<close> }\<close> parses and type-checks \<open>term\<close>,
\<^item> \<^theory_text>\<open>@{value \<open>term\<close> }\<close> performs the evaluation of \<open>term\<close>,
\<^item> \<^theory_text>\<open>@{ML \<open>ml-term\<close> }\<close> parses and type-checks \<open>ml-term\<close>,
\<^item> \<^theory_text>\<open>@{ML_file \<open>ml-file\<close> }\<close> parses the path for \<open>ml-file\<close> and
  verifies its existance in the (Isabelle-virtual) file-system.
\<close>

text\<open>There are options to display sub-parts of formulas etc., but it is a consequence
of tight-checking that the information must be given complete and exactly in the syntax of
Isabelle. This may be over-precise and a burden to readers not familiar with Isabelle, which may
motivate authors to choose the aforementioned freeform-style.

Additionally, documents antiquotations were added to check and evaluate terms with
term antiquotations:
\<^item> \<^theory_text>\<open>@{term_ \<open>term\<close> }\<close> parses and type-checks \<open>term\<close> with term antiquotations,
  for instance \<^theory_text>\<open>\<^term_> \<open>@{technical \<open>isadof\<close>}\<close>\<close> will parse and check
  that \<open>isadof\<close> is indeed an instance of the class \<^typ>\<open>technical\<close>,
\<^item> \<^theory_text>\<open>@{value_ \<open>term\<close> }\<close> performs the evaluation of \<open>term\<close> with term antiquotations,
  for instance \<^theory_text>\<open>@{value_ \<open>definition_list @{technical \<open>isadof\<close>}\<close>}\<close>
  will print the value of the \<^const>\<open>definition_list\<close> attribute of the instance \<open>isadof\<close>.
  \<^theory_text>\<open>value_\<close> may have an optional argument between square brackets to specify the evaluator but this
  argument must be specified after a default optional argument already defined
  by the text antiquotation implementation.
  So one must use the following syntax if he does not want to specify the first optional argument:
  \<^theory_text>\<open>@{value_ [] [nbe] \<open>definition_list @{technical \<open>isadof\<close>}\<close>}\<close>. Note the empty brackets.
\<close>

(*<*)
declare_reference*["subsec_onto_term_ctxt"::technical]
(*>*)

text\<open>They are text-contexts equivalents to the \<^theory_text>\<open>term*\<close> and \<^theory_text>\<open>value*\<close> commands
     for term-contexts introduced in @{technical (unchecked) \<open>subsec_onto_term_ctxt\<close>}\<close>

subsection\<open>A Technical Report with Tight Checking\<close>
text\<open>An example of tight checking is a small programming manual to document programming trick 
discoveries while implementing in Isabelle. While not necessarily a meeting standards of a scientific text, it appears to us that this information
is often missing in the Isabelle community. 

So, if this text addresses only a very limited audience and will never be famous for its style,
it is nevertheless important to be \<^emph>\<open>exact\<close> in the sense that code-snippets and interface descriptions
should be accurate with the most recent version of Isabelle in which this document is generated.
So its value is that readers can just reuse some of these snippets and adapt them to their 
purposes.
\<close>

figure*[strict_em::figure, relative_width="95", file_src="''figures/MyCommentedIsabelle.png''"] 
\<open>A table with a number of SML functions, together with their type.\<close>

text\<open>
This manual  is written according to the \<^verbatim>\<open>technical_report\<close> ontology in
\<^theory>\<open>Isabelle_DOF.technical_report\<close>.
\<^figure>\<open>strict_em\<close> shows a snippet from this integrated source and gives an idea why 
its tight-checking allows for keeping track of underlying Isabelle changes:
Any reference to an SML operation in some library module is type-checked, and the displayed
SML-type really corresponds to the type of the operations in the underlying SML environment.
In the \<^pdf> output, these text-fragments were displayed verbatim.
\<close>



section\<open>Some Recommendations: A little Style Guide\<close>
text\<open>
  The document generation of \<^isadof> is based on Isabelle's document generation framework, 
  using \<^LaTeX>{} as the underlying back-end. As Isabelle's document generation framework, it is 
  possible to embed (nearly) arbitrary \<^LaTeX>-commands in text-commands, \<^eg>:

@{boxed_theory_text [display]\<open>
text\<open> This is \emph{emphasized} and this is a 
       citation~\cite{brucker.ea:isabelle-ontologies:2018}\<close>
\<close>}

  In general, we advise against this practice and, whenever positive, use the \<^isadof> (respetively
  Isabelle) provided alternatives:

@{boxed_theory_text [display]\<open>
text\<open> This is *\<open>emphasized\<close> and this is a 
        citation @{cite "brucker.ea:isabelle-ontologies:2018"}.\<close>
\<close>}
The list of standard Isabelle document antiquotations, as well as their options and styles,
can be found in the Isabelle reference manual \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>, 
section 4.2.

In practice,  \<^isadof> documents with ambitious layout will contain a certain number of
\<^LaTeX>-commands, but this should be restricted to layout improvements that otherwise are (currently)
not possible. As far as possible, raw \<^LaTeX> should be restricted to the definition 
of ontologies and  macros (see @{docitem (unchecked) \<open>isadof_ontologies\<close>}). If raw 
 \<^LaTeX> commands can not be avoided, it is recommended to use the Isabelle document comment
\<^latex>\<open>\verb+\+\verb+<^latex>+\<close>\<open>\<open>argument\<close>\<close> to isolate these parts
(cf.  \<^cite>\<open>"wenzel:isabelle-isar:2020"\<close>).

Restricting the use of \<^LaTeX> has two advantages: first, \<^LaTeX> commands can circumvent the 
consistency checks of \<^isadof> and, hence, only if no \<^LaTeX> commands are used, \<^isadof> can 
ensure that a document that does not generate any error messages in Isabelle/jEdit also generated
a \<^pdf> document. Second, future version of \<^isadof> might support different targets for the 
document generation (\<^eg>, HTML) which, naturally, are only available to documents not using 
too complex native \<^LaTeX>-commands. 

Similarly, (unchecked) forward references should, if possible, be avoided, as they also might
create dangling references during the document generation that break the document generation.  

Finally, we recommend using the @{command "check_doc_global"} command at the end of your 
document to check the global reference structure. 

\<close>

(*<*)
end
(*>*) 
  
