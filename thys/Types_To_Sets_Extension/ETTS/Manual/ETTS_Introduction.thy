(* Title: ETTS/Manual/ETTS_Introduction.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

chapter\<open>ETTS: Reference Manual\<close>

section\<open>Introduction\<close>
theory ETTS_Introduction
  imports 
    Manual_Prerequisites  
    "HOL-Library.Conditional_Parametricity"
begin



subsection\<open>Background\<close>


text\<open>
The \textit{standard library} that is associated with the object logic 
Isabelle/HOL and provided as a part of the standard distribution of Isabelle 
\cite{noauthor_isabellehol_2020} 
contains a significant number of formalized results from a variety of 
fields of mathematics (e.g., order theory, algebra, topology).
Nevertheless, using the vocabulary that was promoted in the original article on
Types-To-Sets \cite{blanchette_types_2016}, the formalization is 
performed using a type-based approach. Thus, for example, the carrier sets 
associated with the algebraic structures and the underlying sets of the 
topological spaces consist of all terms of an arbitrary type. This restriction 
can create an inconvenience when working with mathematical objects 
induced on a subset of the carrier set/underlying set associated with 
the original object (e.g., see \cite{immler_smooth_2019}).

To address this limitation, several additional libraries were developed 
upon the foundations provided by the the standard library 
(e.g., \textit{HOL-Algebra}
\cite{ballarin_isabellehol_2020} and \textit{HOL-Analysis} 
\cite{noauthor_isabellehol_2020-1}). 
In terms of the vocabulary associated with 
Types-To-Sets, these libraries provide the set-based counterparts of many
type-based theorems in the standard library, along with a plethora of 
additional results. Nonetheless, the proofs of the majority of the theorems 
that are available in the standard library are restated explicitly in the 
libraries that contain the set-based results. This unnecessary duplication of 
efforts is one of the primary problems that the framework Types-To-Sets is 
meant to address. 

The framework Types-To-Sets offers a unified approach to structuring 
mathematical knowledge formalized in Isabelle/HOL: every type-based theorem 
can be converted to a set-based theorem in a semi-automated manner and the 
relationship between such type-based and set-based theorems can be 
articulated clearly and explicitly \cite{blanchette_types_2016}. 
In this article, we describe a particular implementation of the framework 
Types-To-Sets in Isabelle/HOL that takes the form of a further extension of 
the language Isabelle/Isar with several new commands and attributes 
(e.g., see \cite{wenzel_isabelle/isar_2019-1}).
\<close>



subsection\<open>Previous work\<close>


subsubsection\<open>Prerequisites and conventions\<close>


text\<open>
A reader of this document is assumed to be familiar with 
the proof assistant Isabelle, the proof language Isabelle/Isar,
the meta-logic Isabelle/Pure and
the object logic Isabelle/HOL, as described in, 
\cite{paulson_natural_1986, wenzel_isabelle/isar_2019-1},
\cite{bertot_isar_1999, wenzel_isabelleisar_2007, wenzel_isabelle/isar_2019-1},
\cite{paulson_foundation_1989, wenzel_isabelle/isar_2019-1} and
\cite{yang_comprehending_2017}, respectively. Familiarity with the
content of the original articles about Types-To-Sets
\cite{blanchette_types_2016,kuncar_types_2019} and
the first large-scale application of Types-To-Sets
(as described in \cite{immler_smooth_2019}) 
is not essential but can be useful.

The notational conventions that are used in this document are
approximately equivalent to the conventions that were suggested in
\cite{blanchette_types_2016}, \cite{yang_comprehending_2017} and
\cite{kuncar_types_2019}; nonetheless, we try to provide 
explanations whenever deemed essential in an attempt to make this body of work
self-contained. As a side note, the types of the 
typed variables and constant-instances may be omitted
at will, if it is deemed that they can be inferred from the
context of the discussion.
\<close>


subsubsection\<open>A note on global schematic polymorphism\<close>


text\<open>
In Isabelle/Pure, a distinction is made between schematic and fixed
variables (for example, see \cite{paulson_foundation_1989} or
\cite{wenzel_isabelle/isar_2001}).
Implicitly, Isabelle/HOL also inherits this distinction.
More specifically, free variables that occur in the theorems at the top-level
of the theory context are generalized implicitly, which may be expressed by
replacing fixed variables by schematic variables
(e.g., see \cite{wenzel_isabelle/isar_2001}).
However, from the perspective of logic,
the distinction between the fixed and the schematic variables
is superficial: they are merely distinct syntactic expressions
of the same formal concept of variables 
(e.g., see \cite{wenzel_isabelle/isar_2001}).

In this document, following a standard convention, 
the names of the schematic variables will be prefixed with the question 
mark ``$?$''. Thus, $?a$, $?b$, $\ldots$ will be used for the denotation 
of schematic term variables and $?\alpha$, $?\beta$, $\ldots$ will be used 
for the denotation of the schematic type variables. 
Like in the previous work on Types-To-Sets, by abuse of notation, 
explicit quantification over the type variables at the top level is allowed: 
$\forall \alpha. \phi\left[\alpha\right]$. However, 
the schematic variables will nearly always be treated 
explicitly, like they are treated in the programmatic implementation 
of the algorithms. It should also be noted that, apart from the 
conventional use of the square brackets for the denotation of substitution,
they may be used informally to indicate that certain 
types and/or terms are a part of a term, e.g., 
$t\left[?\alpha\right]$, $t\left[\sigma, c_{\tau}\right]$.
\<close>


subsubsection\<open>Relativization Algorithm\label{sec:ra}\<close>


text\<open>
Let ${}_{\alpha}(\beta \approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}$ denote
\[
\begin{aligned}
& (\forall x_{\beta}. \mathsf{Rep}\ x \in A)\ \wedge\\
& (\forall x_{\beta}. \mathsf{Abs}\ (\mathsf{Rep}\ x) = x)\ \wedge\\
& (\forall y_{\alpha}. y \in A \longrightarrow \mathsf{Rep}\ (\mathsf{Abs}\ y) = y)
\end{aligned},
\]
let $\rightsquigarrow$ denote the constant/type dependency relation 
(see subsection 2.3 in \cite{blanchette_types_2016}), 
let $\rightsquigarrow^{\downarrow}$ 
be a substitutive closure of the constant/type dependency relation, 
let $R^{+}$ denote the transitive closure of 
the binary relation $R$, let $\Delta_c$ denote the set of all types for which 
$c$ is overloaded and let $\sigma\not\leq S $ mean that $\sigma$ is not an 
instance of any type in $S$ (see \cite{blanchette_types_2016} and 
\cite{yang_comprehending_2017}).

The framework Types-To-Sets extends Isabelle/HOL with two axioms: 
Local Typedef Rule (LT) and the Unoverloading Rule (UO). 
The consistency of Isabelle/HOL augmented with the LT and
the UO is proved in Theorem 11 in \cite{yang_comprehending_2017}.

The LT is given by
\[
\begin{aligned}
\scalebox{1.0}{
\infer[\beta \not\in A, \phi, \Gamma]{\Gamma \vdash \phi}{%
\Gamma\vdash A \neq\emptyset
& \Gamma
  \vdash
  \left( 
    \exists \mathsf{Abs}\ \mathsf{Rep}. {}_{\sigma}(\beta\approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}\longrightarrow\phi 
  \right)
} 
}
\end{aligned}
\]

Thus, if $\beta$ is fresh for the non-empty set $A_{\sigma\ \mathsf{set}}$, 
the formula $\phi$ and the context $\Gamma$, then $\phi$ can be proved in 
$\Gamma$ by assuming the existence of a type $\beta$ isomorphic to $A$.

The UO is given by
\[
\infer[\text{$\forall u$ in $\phi$}. \neg(u\rightsquigarrow^{\downarrow+}c_{\sigma});\ \sigma\not\leq\Delta_c]{\forall x_{\sigma}. \phi\left[x_{\sigma}/c_{\sigma}\right]}{\phi}
\]
Thus, a constant-instance $c_{\sigma}$ may be replaced by a universally 
quantified variable $x_{\sigma}$ in $\phi$, if all types and 
constant-instances in $\phi$ do not semantically depend on $c_{\sigma}$ 
through a chain of constant and type definitions and there is no 
matching definition for $c_{\sigma}$.

The statement of the \textit{original relativization algorithm} (ORA) can be 
found in subsection 5.4 in \cite{blanchette_types_2016}. Here, we present
a variant of the algorithm that includes some of the amendments that were 
introduced in \cite{immler_smooth_2019}, which will be referred to as the 
\textit{relativization algorithm} (RA). 
The differences between the ORA and 
the RA are implementation-specific and have no effect on the output 
of the algorithm, if applied to a conventional input.
Let $\bar{a}$ denote $a_1,\ldots,a_n$ for some positive integer $n$; 
let $\Upsilon$ be a type class 
\cite{nipkow_type_1991,wenzel_type_1997,altenkirch_constructive_2007} 
that depends on the overloaded constants $\bar{*}$ and 
let $A\downarrow\bar{f}$ be used 
to state that $A$ is closed under the operations $\bar{f}$; 
then the RA is given by 
\[
\scalebox{0.75}{
\infer[(7)]
{
\vdash ?A_{?\alpha\ \mathsf{set}} \neq\emptyset\longrightarrow
?A\downarrow?\bar{f}\left[?\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ ?A\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[?\alpha,?A,?\bar{f}\right]
}
{
\infer[(6)]
{
A\neq\emptyset
\vdash A\downarrow?\bar{f}\left[\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ A\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,A,?\bar{f}\right]
}
{
\infer[(5)]
{
A\neq\emptyset,{}_{\alpha}(\beta\approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash A\downarrow?\bar{f}\left[\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ A\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,A,?\bar{f}\right]
}
{
\infer[(4)]
{
A\neq\emptyset,{}_{\alpha}(\beta\approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[\beta\right]\longrightarrow
\phi_{\mathsf{with}}\left[\beta,?\bar{f}\right]
}
{
\infer[(3)]
{
A\neq\emptyset,{}_{\alpha}(\beta\approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[?\alpha\right]\longrightarrow
\phi_{\mathsf{with}}\left[?\alpha,?\bar{f}\right]
}
{
\infer[(2)]
{
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[?\alpha\right]\longrightarrow
\phi_{\mathsf{with}}\left[?\alpha,?\bar{f}\right]
}
{
\infer[(1)]
{\vdash\phi_{\mathsf{with}}\left[?\alpha_{\Upsilon},\bar{*}\right]}
{\vdash\phi\left[?\alpha_{\Upsilon}\right]}
}
}
}
}
}
}
}
\]
The input to the RA
is assumed to be a theorem $\vdash\phi\left[?\alpha_{\Upsilon}\right]$ 
such that all of its unbound term and type variables are schematic.
Step 1 will be referred to as the first step of the dictionary 
construction (it is similar to the first step of the 
dictionary construction, as described in subsection 5.2 in
\cite{blanchette_types_2016});
step 2 will be described as unoverloading of the type $?\alpha_{\Upsilon}$ 
and includes class internalization 
(see subsection 5.1 in \cite{blanchette_types_2016} and 
\cite{altenkirch_constructive_2007}) 
and the application of the UO (step 2 corresponds to the application of the
attribute @{attribute unoverload_type} that will be 
described in the next subsection); step 3 provides the assumptions
\mbox{$A_{\alpha\ \mathsf{set}}\neq\emptyset$} and 
\mbox{${}_{\alpha}(\beta\approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}$} 
(the prerequisites for the application of the LT); step 4 is reserved
for the concrete type instantiation; 
step 5 refers to the application of transfer 
(see section 6 in \cite{blanchette_types_2016}); step 6 refers to the 
application of the LT; step 7 refers to the export of the theorem
from the local context (e.g., see \cite{wenzel_isabelle/isar_2019}).
\<close>


subsubsection\<open>Implementation of Types-To-Sets\label{subsec:ITTS}\<close>


text\<open>
In \cite{blanchette_types_2016}, the authors provided the first
programmatic implementation of the framework Types-To-Sets for Isabelle/HOL 
in the form of several Isabelle/ML modules 
(see \cite{milner_definition_1997} and \cite{wenzel_isabelle/isar_2019}). 
These modules extended the 
implementation of the object logic Isabelle/HOL with the
LT and UO. Moreover, they introduced several attributes that provided a 
convenience layer for the application of the ORA:
@{attribute internalize_sort}, @{attribute unoverload}
and @{attribute cancel_type_definition}. 
These attributes could be used to perform steps 1, 3 and 7 (respectively) of 
the ORA. Other steps could be performed using the technology that already 
existed, but required a significant effort and knowledge on behalf of the users 
(e.g., see \cite{immler_smooth_2019}).

The examples of the application of the ORA to theorems in 
Isabelle/HOL that were developed in \cite{blanchette_types_2016}
already contained an implicit suggestion that the constants and theorems 
needed for the first step of the dictionary construction in step 2 of 
the ORA and the transfer rules needed for step 6 of the ORA can and should 
be obtained prior to the application of the algorithm. Thus, using the notation
from subsection \ref{sec:ra},
for each constant-instance $c_{\sigma}$ 
that occurs in the type-based theorem 
$\vdash\phi\left[?\alpha_{\Upsilon}\right]$
prior to the application of the ORA with respect to 
${}_{\alpha}(\beta \approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}$, 
the users were expected to provide
an unoverloaded constant $c_{\mathsf{with}}$ such that 
$c_{\sigma} = c_{\mathsf{with}}\ \bar{*}$, and a constant $c^{\mathsf{on}}_{\mathsf{with}}$ 
such that $R\left[T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}\right]
\ (c^{\mathsf{on}}_{\mathsf{with}}\ A_{\alpha\ \mathsf{set}})\ c_{\mathsf{with}}$ 
($\mathbb{B}$ denotes the built-in Isabelle/HOL type $bool$
\cite{kuncar_types_2015})
is a conditional transfer rule (e.g., see \cite{gonthier_lifting_2013}), 
with $T$ being a binary 
relation that is at least right-total and bi-unique 
(see \cite{kuncar_types_2015}), assuming the default order on predicates
in Isabelle/HOL. 
In \cite{immler_smooth_2019}, the implementation of the framework Types-To-Sets
was amended by providing the attribute @{attribute unoverload_type}, 
which subsumed the functionality of the attributes 
@{attribute internalize_sort} and 
@{attribute unoverload}. The RA presented above already includes this
amendment.

Potentially, the unoverloaded constants $c_{\mathsf{with}}$ and the 
associated theorems $c_{\sigma} = c_{\mathsf{with}}\ \bar{*}$ 
can be obtained via the application of the algorithm for unoverloading 
of definitions that was proposed in 
\cite{kaufmann_mechanized_2010}.
However, to the best knowledge of the author, a working implementation of this 
\textit{classical overloading elimination algorithm} 
is not publicly available for the most recent version of Isabelle.
In \cite{immler_automation_2019}, an alternative
algorithm that serves a similar purpose is provided and  
made available via the interface of the Isabelle/Isar command
@{command unoverload_definition}. 
Effectively, the command applies the algorithm used
in the attribute @{attribute unoverload_type}
to a definition of the constant $c$ and uses the right-hand-side 
of the resulting theorem to form a definition for $c_{\mathsf{with}}$.
Thus, technically, unlike the classical overloading elimination
algorithm, this algorithm requires the axiom UO to be available and it is 
not capable of unoverloading the constants that were not overloaded 
using the Isabelle's type class infrastructure. Furthermore,
the command is applicable only to the definitions provided by the user, 
which could be seen as an obstacle in the automation of unoverloading of 
the constants that are defined using the definitional packages other 
than @{command definition} (the classical overloading elimination 
algorithm relies on the definitional axioms instead of arbitrary 
theorems provided by the user \cite{kaufmann_mechanized_2010}). 
Of course, none of these limitations hinder the usefulness of the command, 
if it is applicable. 

The transfer rules for the constants that are conditionally parametric 
can be synthesized automatically using the existing command 
@{command parametric_constant}
\cite{gilcher_conditional_2017} 
that is available from the standard distribution of Isabelle;
the framework \textit{autoref} that was developed in 
\cite{lammich_automatic_2013} allows for the synthesis of transfer rules 
$R\ t\ t'$, including both the transfer relation $R$ and the term $t$,
based on $t'$, under favorable conditions;
lastly, in \cite{lammich_automatic_2013} and \cite{immler_smooth_2019}, 
the authors suggest an outline of another feasible algorithm for the 
synthesis of the transfer rules based on the functionality of the framework 
\textit{transfer} \cite{gonthier_lifting_2013} of Isabelle/HOL, 
but do not provide an implementation (the main algorithm presented
in \cite{lammich_automatic_2013} is independent of the standard transfer 
framework of Isabelle/HOL).

Lastly, the assumption ${}_{\alpha}(\beta \approx A)_{\mathsf{Rep}}^{\mathsf{Abs}}$ can be 
stated using the 
constant \isa{type{\isacharunderscore}definition}
from the standard library of Isabelle/HOL as 
\isa{type{\isacharunderscore}definition\ $\mathsf{Rep}$\ $\mathsf{Abs}$\ $A$}; 
the instantiation of types required in step 4 of the RA can 
be performed using the standard attributes of Isabelle; 
step 6 can be performed using the attribute 
@{attribute cancel_type_definition} developed in 
\cite{blanchette_types_2016}; step 7 is expected to be performed manually
by the user.
\<close>



subsection\<open>Purpose and scope\<close>


text\<open>
The extension of the framework Types-To-Sets that is described in this manual
adds a further layer of automation to the existing implementation
of the framework Types-To-Sets. The primary functionality of the extension 
is available via the following Isar commands: 
@{command tts_context}, @{command tts_lemmas} and @{command tts_lemma} (and the
synonymous commands @{command tts_corollary}, @{command tts_proposition} and
@{command tts_theorem}\footnote{In what follows, any reference to the 
command @{command tts_lemma} should be viewed as a reference to the 
entire family of the commands with the identical functionality.}).
The commands @{command tts_lemmas} and @{command tts_lemma}, when invoked inside
an appropriately defined @{command tts_context} provide the 
functionality that is approximately equivalent to the application of all 
steps of the RA and several additional steps of 
pre-processing of the input and post-processing of the result
(collectively referred to as the \textit{extended relativization algorithm} 
or ERA).

The extension was designed under a policy of non-intervention with the  
existing implementation of the framework Types-To-Sets. Therefore, it does
not reduce the scope of the applicability of the framework. 
However, the functionality that is provided by the commands associated with the 
extension is a proper subset of the functionality provided by the existing 
implementation. Nevertheless, the author of the extension believes that there 
exist very few practical applications of the relativization algorithm that 
can be solved using the original interface but cannot be solved using 
the commands that are introduced within the scope of the 
extension.
\<close>

text\<open>\newpage\<close>

end