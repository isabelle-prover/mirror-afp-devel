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
  "M_05_Proofs_Ontologies"
  imports 
    "M_04_Document_Ontology" 
begin

(*>*)

chapter*[onto_proofs::technical]\<open>Proofs over Ontologies\<close>

text\<open>It is a distinguishing feature of \<^dof> that it does not directly generate meta-data rather
than generating a \<^emph>\<open>theory of meta-data\<close> that can be used in HOL-terms on various levels
of the Isabelle-system and its document generation technology. Meta-data theories can be 
converted into executable code and efficiently used in validations, but also used for theoretic
reasoning over given ontologies. While the full potential of this latter possibility still
needs to be explored, we present in the following sections two applications:

  \<^enum> Verified ontological morphisms, also called \<^emph>\<open>ontological mappings\<close> in the literature
    \<^cite>\<open>"books/daglib/0032976" and "atl" and "BGPP95"\<close>, \<^ie> proofs of invariant preservation
    along translation-functions of all instances of \<^verbatim>\<open>doc_class\<close>-es.
  \<^enum> Verified refinement relations between the structural descriptions of theory documents,
    \<^ie> proofs of language inclusions of monitors of global ontology classes.   
\<close>

section*["morphisms"::scholarly_paper.text_section] \<open>Proving Properties over Ontologies\<close>

subsection\<open>Ontology-Morphisms: a Prototypical Example\<close>

text\<open>We define a small ontology with the following classes:\<close>

doc_class AA = aa :: nat
doc_class BB = bb :: int
doc_class CC = cc :: int

doc_class DD = dd :: int
doc_class EE = ee :: int
doc_class FF = ff :: int

onto_morphism (AA, BB) to CC  and (DD, EE) to FF
  where "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C \<sigma> = \<lparr> CC.tag_attribute = 1::int, 
                                           CC.cc = int(aa (fst \<sigma>)) + bb (snd \<sigma>)\<rparr>"
  and   "convert\<^sub>D\<^sub>D\<^sub>\<times>\<^sub>E\<^sub>E\<^sub>\<Rightarrow>\<^sub>F\<^sub>F \<sigma> = \<lparr> FF.tag_attribute = 1::int, 
                                           FF.ff = dd (fst \<sigma>) + ee (snd \<sigma>) \<rparr>"

text\<open>Note that the \<^term>\<open>convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C\<close>-morphism involves a data-format conversion, and that the
resulting transformation of @{doc_class AA}-instances and @{doc_class BB}-instances is surjective 
but not injective. The \<^term>\<open>CC.tag_attribute\<close> is used to potentially differentiate instances with
equal attribute-content and is irrelevant here.\<close>

(*<*) (* Just a test, irrelevant for the document.*)

doc_class A_A = aa :: nat
doc_class BB' = bb :: int
onto_morphism (A_A, BB', CC, DD, EE) to FF
  where "convert\<^sub>A\<^sub>_\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>'\<^sub>\<times>\<^sub>C\<^sub>C\<^sub>\<times>\<^sub>D\<^sub>D\<^sub>\<times>\<^sub>E\<^sub>E\<^sub>\<Rightarrow>\<^sub>F\<^sub>F \<sigma> = \<lparr> FF.tag_attribute = 1::int, 
                                      FF.ff = int(aa (fst \<sigma>)) + bb (fst (snd \<sigma>))\<rparr>"

(*>*)

text\<open>This specification construct  introduces the following constants and definitions:
   \<^item> @{term [source] \<open>convert\<^sub>A\<^sub>A\<^sub>_\<^sub>B\<^sub>B\<^sub>_\<^sub>C\<^sub>C :: AA \<times> BB \<Rightarrow> CC\<close>}
   \<^item> @{term [source] \<open>convert\<^sub>D\<^sub>D\<^sub>_\<^sub>E\<^sub>E\<^sub>_\<^sub>F\<^sub>F :: DD \<times> EE \<Rightarrow> FF\<close>}
   % @{term [source] \<open>convert\<^sub>A\<^sub>_\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>'\<^sub>\<times>\<^sub>C\<^sub>C\<^sub>\<times>\<^sub>D\<^sub>D\<^sub>\<times>\<^sub>E\<^sub>E\<^sub>\<Rightarrow>\<^sub>F\<^sub>F :: A_A \<times> BB' \<times> CC \<times> DD \<times> EE \<Rightarrow> FF\<close>}

and corresponding definitions. \<close>

subsection\<open>Proving the Preservation of Ontological Mappings : A Document-Ontology Morphism\<close>

text\<open>\<^dof> as a system is currently particularly geared towards \<^emph>\<open>document\<close>-ontologies, in 
particular for documentations generated from Isabelle theories. We used it meanwhile for the
generation of various conference and journal papers, notably using the
 \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close> and  \<^theory>\<open>Isabelle_DOF.technical_report\<close>-ontologies, 
targeting a (small) variety of \<^LaTeX> style-files. A particular aspect of these ontologies,
especially when targeting journals from publishers such as ACM, Springer or Elsevier, is the
description of publication meta-data. Publishers tend to have their own styles on what kind 
meta-data should be associated with a journal publication; thus, the depth and 
precise format of affiliations, institution, their relation to authors, and author descriptions
(with photos or without, hair left-combed or right-combed, etcpp...)  varies.

In the following, we present an attempt to generalized ontology with several ontology mappings 
to more specialized ones such as concrete journals and/or the  \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>-
ontology which we mostly used for our own publications. 
\<close>


doc_class elsevier_org =
  organization :: string
  address_line :: string
  postcode :: int
  city :: string
  
doc_class acm_org =
  position :: string
  institution :: string
  department :: int
  street_address :: string
  city :: string
  state :: int
  country :: string
  postcode :: int

doc_class lncs_inst =
  institution :: string

doc_class author =
    name   :: string
    email  :: "string"   <= "''''"
    invariant ne_fsnames :: "name \<sigma> \<noteq> ''''"

doc_class elsevierAuthor = "author" +
  affiliations :: "elsevier_org list"
  firstname   :: string
  surname     :: string
  short_author :: string
  url :: string
  footnote :: string
  invariant ne_fsnames :: "firstname \<sigma> \<noteq> '''' \<and> surname \<sigma> \<noteq> ''''"

(*<*)
text*[el1:: "elsevier_org"]\<open>An example elsevier-journal affiliation.\<close>
term*\<open>@{elsevier_org \<open>el1\<close>}\<close>
text*[el_auth1:: "elsevierAuthor", affiliations = "[@{elsevier_org \<open>el1\<close>}]"]\<open>\<close>
(*>*)
text\<open>\<close>

doc_class acmAuthor = "author" +
  affiliations :: "acm_org list"
  firstname   :: string
  familyname     :: string
  orcid :: int
  footnote :: string
  invariant ne_fsnames :: "firstname \<sigma> \<noteq> '''' \<and> familyname \<sigma> \<noteq> ''''"

(*<*)
text*[acm1:: "acm"]\<open>An example acm-style affiliation\<close>
(*>*)
text\<open>\<close>

doc_class lncs_author = "author" +
  affiliations :: "lncs list"
  orcid :: int
  short_author :: string
  footnote :: string

(*<*)
text*[lncs1:: "lncs"]\<open>An example lncs-style affiliation\<close>
text*[lncs_auth1:: "lncs_author", affiliations = "[@{lncs \<open>lncs1\<close>}]"]\<open>Another example lncs-style affiliation\<close>
find_theorems elsevier.tag_attribute
(*>*)
text\<open>\<close>

definition acm_name where "acm_name f s = f @ '' '' @ s"

fun concatWith :: "string \<Rightarrow> string list \<Rightarrow> string"
  where "concatWith str [] = ''''"
       |"concatWith str [a] = a"
       |"concatWith str (a#R) = a@str@(concatWith str R)"

lemma concatWith_non_mt : "(S\<noteq>[] \<and> (\<exists> s\<in>set S. s\<noteq>'''')) \<longrightarrow>  (concatWith sep S) \<noteq> ''''"
proof(induct S)
  case Nil
  then show ?case by simp
next
  case (Cons a S)
  then show ?case by (cases a; cases S; auto)
qed

onto_morphism (acm) to elsevier
  where "convert\<^sub>a\<^sub>c\<^sub>m\<^sub>\<Rightarrow>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r \<sigma> =  
               \<lparr>elsevier.tag_attribute = acm.tag_attribute \<sigma>, 
                organization = acm.institution \<sigma>,
                address_line = concatWith '','' [acm.street_address \<sigma>, acm.city \<sigma>], 
                postcode     =  acm.postcode \<sigma> , 
                city         =  acm.city \<sigma> \<rparr>"

text\<open>Here is a more basic, but equivalent definition for the other way round:\<close>

definition elsevier_to_acm_morphism :: "elsevier_org \<Rightarrow> acm_org"
          (\<open>_ \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r\<close> [1000]999)
          where "\<sigma> \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r = \<lparr> acm_org.tag_attribute = 1::int,
                                   acm_org.position = ''no position'',
                                   acm_org.institution = organization \<sigma>,
                                   acm_org.department = 0,
                                   acm_org.street_address = address_line \<sigma>,
                                   acm_org.city = elsevier_org.city \<sigma>,
                                   acm_org.state = 0,
                                   acm_org.country = ''no country'',
                                   acm_org.postcode = elsevier_org.postcode \<sigma>  \<rparr>"

text\<open>The following onto-morphism links \<^typ>\<open>elsevierAuthor\<close>'s and \<^typ>\<open>acmAuthor\<close>. Note that
the conversion implies trivial data-conversions (renaming of attributes in the classes), 
string-representation conversions, and conversions of second-staged, referenced instances.\<close>

onto_morphism (elsevierAuthor) to acmAuthor
  where "convert\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r\<^sub>\<Rightarrow>\<^sub>a\<^sub>c\<^sub>m\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r \<sigma> =  
               \<lparr>author.tag_attribute = undefined, 
                name = concatWith '','' [elsevierAuthor.firstname \<sigma>,elsevierAuthor.surname \<sigma>], 
                email = author.email \<sigma>,
                acmAuthor.affiliations = (elsevierAuthor.affiliations \<sigma>)
                                         |> map (\<lambda>x. x \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r),
                firstname = elsevierAuthor.firstname \<sigma>, 
                familyname = elsevierAuthor.surname \<sigma>,
                orcid = 0,  \<comment> \<open>la triche ! ! !\<close>
                footnote = elsevierAuthor.footnote \<sigma>\<rparr>"


lemma elsevier_inv_preserved :
  "elsevierAuthor.ne_fsnames_inv \<sigma> 
   \<Longrightarrow> acmAuthor.ne_fsnames_inv (convert\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r\<^sub>\<Rightarrow>\<^sub>a\<^sub>c\<^sub>m\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r \<sigma>) 
       \<and> author.ne_fsnames_inv (convert\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r\<^sub>\<Rightarrow>\<^sub>a\<^sub>c\<^sub>m\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r \<sigma>)"
  unfolding elsevierAuthor.ne_fsnames_inv_def acmAuthor.ne_fsnames_inv_def
            convert\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r\<^sub>_\<^sub>a\<^sub>c\<^sub>m\<^sub>A\<^sub>u\<^sub>t\<^sub>h\<^sub>o\<^sub>r_def author.ne_fsnames_inv_def
  by auto  

text\<open>The proof is, in order to quote Tony Hoare, ``as simple as it should be''. Note that it involves
the lemmas like @{thm concatWith_non_mt} which in itself require inductions, \<^ie>, which are out of
reach of pure ATP proof-techniques. \<close>

subsection\<open>Proving the Preservation of Ontological Mappings : A Domain-Ontology Morphism\<close>
text\<open>The following example is drawn from a domain-specific scenario: For conventional data-models,
be it represented by UML-class diagrams or SQL-like "tables" or Excel-sheet like presentations
of uniform data, we can conceive an ontology (which is equivalent here to a conventional style-sheet)
and annotate textual raw data. This example describes how meta-data can be used to 
calculate and transform this kind of representations in a type-safe and verified way. \<close>

(*<*)
(* Mapped_PILIB_Ontology example *)
(* rethink examples: should we "morph" providence too ? ? ? Why not ? bu *)

term\<open>fold (+) S 0\<close>  

definition sum 
  where "sum S = (fold (+) S 0)"
(*>*)

text\<open>We model some basic enumerations as inductive data-types: \<close>
datatype Hardware_Type = 
  Motherboard     |  Expansion_Card |  Storage_Device |   Fixed_Media | 
  Removable_Media | Input_Device    | Output_Device

datatype Software_Type =
  Operating_system |  Text_editor | Web_Navigator |  Development_Environment

text\<open>In the sequel, we model a ''Reference Ontology'', \<^ie> a data structure in which we assume
that standards or some de-facto-standard data-base refer to the data in the domain of electronic
devices:\<close>

onto_class Resource =
  name :: string

onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string

onto_class Component = Electronic +
  mass :: int

onto_class Simulation_Model = Electronic +
  simulate :: Component
  composed_of :: "Component list" 
  version :: int

onto_class Informatic = Resource +
  description :: string

onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component list" 
  invariant c1 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"

onto_class Software = Informatic +
  type ::  Software_Type
  version :: int

text\<open>Finally, we present a \<^emph>\<open>local ontology\<close>,  \<^ie> a data structure used in a local store
in its data-base of cash-system:\<close>

onto_class Item =
  name :: string

onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int

onto_class Electronic_Component = Product +
  serial_number :: int

onto_class Monitor = Product +
  composed_of :: "Electronic_Component list" 
  invariant c2 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"

term\<open>Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))\<close>

onto_class Computer_Software = Item +
  type ::  Software_Type
  version :: int

text\<open>These two example ontologies were linked via conversion functions called \<^emph>\<open>morphisms\<close>.
The hic is that we can prove for the morphisms connecting these ontologies, that the conversions
are guaranteed to preserve the data-invariants, although the data-structures (and, of course,
the presentation of them) is very different. Besides, morphisms functions can be ``forgetful''
(\<^ie> surjective), ``embedding'' (\<^ie> injective) or even ``one-to-one'' ((\<^ie> bijective).\<close>

definition Item_to_Resource_morphism :: "Item \<Rightarrow> Resource"
          (\<open>_ \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m\<close> [1000]999)
          where "  \<sigma> \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m = 
                                   \<lparr> Resource.tag_attribute = 1::int ,
                                    Resource.name = name \<sigma> \<rparr>" 

definition Product_to_Resource_morphism :: "Product \<Rightarrow> Resource"
           (\<open>_ \<langle>Resource\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t\<close> [1000]999)
           where "  \<sigma> \<langle>Resource\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t = 
                                \<lparr> Resource.tag_attribute = 2::int ,
                                  Resource.name = name \<sigma> \<rparr>" 

definition Computer_Software_to_Software_morphism :: "Computer_Software \<Rightarrow> Software" 
             (\<open>_ \<langle>Software\<rangle>\<^sub>S\<^sub>o\<^sub>f\<^sub>t\<^sub>C\<^sub>m\<^sub>p\<close> [1000]999)
             where "\<sigma> \<langle>Software\<rangle>\<^sub>S\<^sub>o\<^sub>f\<^sub>t\<^sub>C\<^sub>m\<^sub>p = 
                                \<lparr> Resource.tag_attribute = 3::int ,
                                  Resource.name = name \<sigma> ,
                                  Informatic.description = ''no description'', 
                                  Software.type  = type  \<sigma> ,
                                  Software.version = version \<sigma> \<rparr>"

definition Electronic_Component_to_Component_morphism :: "Electronic_Component \<Rightarrow> Component" 
             (\<open>_ \<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p\<close> [1000]999)
             where "\<sigma> \<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p = 
                                \<lparr> Resource.tag_attribute = 4::int ,
                                  Resource.name = name \<sigma> ,
                                  Electronic.provider = provider  \<sigma>  ,
                                  Electronic.manufacturer = ''no manufacturer'' ,
                                  Component.mass = mass  \<sigma> \<rparr>"

definition Monitor_to_Hardware_morphism :: "Monitor \<Rightarrow> Hardware"
           (\<open>_ \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e\<close> [1000]999)
           where "\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e =
                  \<lparr>  Resource.tag_attribute = 5::int ,
                     Resource.name = name \<sigma> ,
                     Informatic.description = ''no description'', 
                     Hardware.type = Output_Device,
                     Hardware.mass = mass \<sigma> ,
                     Hardware.composed_of = map  Electronic_Component_to_Component_morphism (composed_of \<sigma>)
                   \<rparr>" 

text\<open>On this basis, we can state the following invariant preservation theorems:\<close>

lemma inv_c2_preserved :
  "c2_inv \<sigma> \<Longrightarrow> c1_inv (\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)"
  unfolding c1_inv_def c2_inv_def 
            Monitor_to_Hardware_morphism_def Electronic_Component_to_Component_morphism_def
  by (auto simp: comp_def)

lemma Monitor_to_Hardware_morphism_total :
  "Monitor_to_Hardware_morphism ` ({X::Monitor. c2_inv X}) \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved 
  by auto

type_synonym local_ontology = "Item * Electronic_Component * Monitor"
type_synonym reference_ontology = "Resource * Component * Hardware"

fun ontology_mapping :: "local_ontology \<Rightarrow> reference_ontology" 
  where "ontology_mapping (x, y, z) = (x\<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m, y\<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p, z\<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)" 

lemma ontology_mapping_total :
        "ontology_mapping ` {X.  c2_inv (snd (snd X))} \<subseteq> {X.  c1_inv (snd (snd X))}"
  using  inv_c2_preserved 
  by auto

text\<open>Note that in contrast to conventional data-translations, the preservation of a class-invariant
is not just established by a validation of the result, it is proven once and for all for all instances
of the classes.\<close>

subsection\<open>Proving Monitor-Refinements\<close>

(*<*)
(* switch on regexp syntax *)
notation Star  (\<open>\<lbrace>(_)\<rbrace>\<^sup>*\<close> [0]100)
notation Plus  (infixr \<open>||\<close> 55)
notation Times (infixr \<open>~~\<close> 60)
notation Atom  (\<open>\<lfloor>_\<rfloor>\<close> 65)
(*>*)


text\<open>Monitors are regular-expressions that allow for specifying instances of classes to appear in 
a particular order in a document. They are used to specify some structural aspects of a document.
Based on an AFP theory by Tobias Nipkow on Functional Automata
(\<^ie> a characterization of regular automata using functional polymorphic descriptions of transition
functions avoiding any of the ad-hoc finitizations commonly used in automata theory), which 
comprises also functions to generate executable deterministic and non-deterministic automata,
this theory is compiled to SML-code that was integrated in the \<^dof> system. The necessary
adaptions of this integration can be found in the theory \<^theory>\<open>Isabelle_DOF.RegExpInterface\<close>,
which also contains the basic definitions and theorems for the concepts used here.

Recall that the monitor of \<^term>\<open>scholarly_paper.article\<close> is defined by:  \<^vs>\<open>0.5cm\<close>

@{thm [indent=20, margin=70, names_short] scholarly_paper.article_monitor_def}

 \<^vs>\<open>0.5cm\<close> However, it is possible to reason over the language of monitors and prove classical 
refinement notions such as trace-refinement on the monitor-level, so once-and-for-all for all 
instances of validated documents conforming to a particular ontology. The primitive recursive 
operators \<^term>\<open>RegExpInterface.Lang\<close> and \<^term>\<open>RegExpInterface.L\<^sub>s\<^sub>u\<^sub>b\<close> generate the languages of the
regular expression language, where \<^term>\<open>L\<^sub>s\<^sub>u\<^sub>b\<close> takes the sub-ordering relation of classes into 
account. 

The proof of : \<^vs>\<open>0.5cm\<close>

  @{thm [indent=20,margin=70,names_short] articles_sub_reports}

 \<^vs>\<open>0.5cm\<close> can be found in theory  \<^theory>\<open>Isabelle_DOF.technical_report\<close>; 
it is, again, "as simple as it should be" (to cite Tony Hoare). 

The proof of: \<^vs>\<open>0.5cm\<close>

  @{thm [indent=20,margin=70,names_short] articles_Lsub_reports}

 \<^vs>\<open>0.5cm\<close> is slightly more evolved; this is due to the fact that \<^dof> does not generate a proof of 
the acyclicity of the graph of the class-hierarchy @{term doc_class_rel} automatically. For a given 
hierarchy, this proof will always succeed (since  \<^dof> checks this on the meta-level, of course), 
which permits to deduce the anti-symmetry of the transitive closure of @{term doc_class_rel} 
and therefore to establish that the doc-classes can be organized in an order (\<^ie> the
type \<^typ>\<open>doc_class\<close> is an instance of the type-class \<^class>\<open>order\<close>). On this basis, the proof
of the above language refinement is quasi automatic. This proof is also part of 
 \<^theory>\<open>Isabelle_DOF.technical_report\<close>.
\<close>

(*<*)

(* switch off regexp syntax *)
no_notation Star  (\<open>\<lbrace>(_)\<rbrace>\<^sup>*\<close> [0]100)
no_notation Plus  (infixr \<open>||\<close> 55)
no_notation Times (infixr \<open>~~\<close> 60)
no_notation Atom  (\<open>\<lfloor>_\<rfloor>\<close> 65)

end
(*>*) 