(*  Title:       An example submission to the Archive of Formal Proof
    ID:          $Id: Submission.thy,v 1.9 2008-05-17 19:48:25 makarius Exp $
    Author:      Gerwin Klein <kleing at cse.unsw.edu.au>, 2004
    Maintainer:  Gerwin Klein <kleing at cse.unsw.edu.au>
*)

header "An Example Submission"

theory Submission 
  imports Main 
begin

text {*
  This is an example submission to the Archive of Formal Proof.

  The scope of the archive encompasses examples, textbook-style
  proofs, libraries and larger scientific developments.
*}

section "Format of a submission"

text {*
  Submission should be by email to \texttt{afp-submit at in.tum.de} and contain
  the following:
  \begin{itemize}
  \item Title, authors, and abstract.
  The abstract should be in plain text or plain html (no images/styles).
  \item A short name that will become the directory name of the
  submission.
  \item The Isabelle theories: a tar.gz file with the theory files,
  ROOT.ML, and a README file or document directory. 
  The theories should work with the current release of Isabelle. 
  Each theory file should include a header comment like the one 
  in this theory.
  \item A statement whether you would like to release your submission
  under the BSD or the LGPL license.
  \end{itemize}

  The submission of the example you are reading is at
  \url{http://afp.sf.net/release/afp-Example-Submission-current.tar.gz}.  
*}

section "Proof styles"

text {*
  We accept proofs in \isakeyword{apply}-script style like the
  following.
*}

lemma true: "True" 
  apply blast
  done

text {*
  We encourage structured proofs with comments and
  explanations. The Isabelle document preparation tools support
  antiquotations like @{thm true}, normal {\LaTeX} commands and BibTeX
  citations. See \cite{LNCS2283} and the Isabelle documentation for
  more information.  
*}
lemma very_true: "True"
proof -
  -- "a very roundabout way"
  fix P have "P \<longrightarrow> True" by blast
  -- "to show @{term True}"
  thus True by blast
qed

section "The anatomy of a submission"

text {*
  The directory structure of this example submission is the following  
\begin{verbatim}
Example-Submission/
    document/
        root.tex
        root.bib
    config
    IsaMakefile
    ROOT.ML
    README.html
    Submission.thy
\end{verbatim}

The document directory contains the {\LaTeX} master file
\texttt{root.tex} and the bibliography \texttt{root.bib}. Your
submission should contain this {\LaTeX} setup or a \texttt{README.html}
(or both) with title, abstract, author, and any further documentation
you wish to provide. We encourage {\LaTeX} style documentation over
\texttt{README.html}.

The file \texttt{config} contains maintenance information. This is
optional. If you do not submit one, we will create one for you.

The \texttt{IsaMakefile} tells the automated build scripts how to test
your Isabelle theories. For a usual setup you only need to copy the
version from this example and adjust the variable
\texttt{SESSION-NAME}. If you need support with this, please contact
us or ask on the \texttt{isabelle-users} mailing list.

\texttt{ROOT.ML} controls which theories should be loaded. If you have
one main theory that depends on all the others, you only need to
include this one. You can also use \texttt{ROOT.ML} to control the
order in which theories are read. If you would like to build on other
entries in the archive, which we encourage, you can use the
\texttt{add\_path} command in \texttt{ROOT.ML} to add the directory of
the other entry to the theory search path. See the \texttt{ROOT.ML} of
this submission for an example.

The file \texttt{Submission.thy} is the Isabelle theory containing
this text. A usual submission has more than one theory file. You can
devise your own subdirectory structure if you have more theories and
one directory becomes too crowded. You can also build on existing articles
in the AFP by importing them. For example, if you build on theory W in 
the article MiniML, the way to import it is:

\begin{verbatim}
theory MyTheory
  imports "../MiniML/W"
begin
\end{verbatim}

To build on a theory that is in the Isabelle distribtion, but not in
one of the standard images like HOL, use something like the following:

\begin{verbatim}
theory MyTheory
  imports "~~/src/HOL/NumberTheory"
begin
\end{verbatim}
*}

end

