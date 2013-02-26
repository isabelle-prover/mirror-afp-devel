(*<*)
theory Everything
imports DenotationalEquivalences Correctness CorrectnessUpd "Correctness-Counterexample" "~~/src/HOL/Library/LaTeXsugar" 
begin

notation (latex output) DenotationalUpd.ESem ("\<lbrakk>_\<rbrakk>\<^bsup>u\<^esup>\<^bsub>_\<^esub>"  [60,60] 60)
notation (latex output) "Denotational-PropsUpd.HSem_syn" ("\<lbrace>_\<rbrace>\<^bsup>u\<^esup>_"  [60,60] 60)

translations
  "xs" <= "CONST set xs"
translations
  "xs" <= "CONST asToHeap xs"
translations
  "a" <= "CONST atom a"

lemma Terms:
  "\<exists> x assn e'. (e = (Lam [x]. e') \<or> (e = Var x) \<or> (e = App e' x) \<or> (e = Let assn e'))"
  by (metis Terms.exp_assn.exhaust(1))
lemma expressions_grammar:
"(\<forall> var. y = Var var \<longrightarrow> P) \<longrightarrow>
(\<forall> exp var. y = App exp var \<longrightarrow> P) \<longrightarrow>
(\<forall> assn exp. y = Terms.Let assn exp \<longrightarrow> P) \<longrightarrow> (\<forall> var exp. y = Lam [var]. exp \<longrightarrow> P) \<longrightarrow> P"
  by (metis exp_assn.exhaust(1)) 

abbreviation (Grammar output)
  "grammar_imp"
where
  "grammar_imp \<equiv> op \<longrightarrow>"

syntax (Grammar output)
  "_grapats" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ | _")
  "_grafirst" :: "term \<Rightarrow> term \<Rightarrow> term" ("_ ::= _")
  "_grarest" :: "term \<Rightarrow> term \<Rightarrow> term"
  "_firsteq" :: "term \<Rightarrow> term \<Rightarrow> term"
  "_resteq" :: "term \<Rightarrow> term \<Rightarrow> term"

translations
  "_grapats (_firsteq all) (_grarest (CONST grammar_imp rest1 rest2))" <= "CONST grammar_imp all (CONST grammar_imp rest1 rest2)"
  "_grapats (_resteq all) (_grarest (CONST grammar_imp rest1 rest2))" <= "_grarest (CONST grammar_imp all (CONST grammar_imp rest1 rest2))"
  "_resteq all" <= "_grarest (CONST grammar_imp all rest)"
  "_resteq all" <= "_resteq (CONST grammar_imp all rest)"
  "_firsteq all" <= "_firsteq (CONST grammar_imp all rest)"
  "_firsteq imp" <= "_firsteq (ALL x. imp)"
  "_resteq imp" <= "_resteq (ALL x. imp)"
  "_grafirst x t" <= "_firsteq (x = t)"
  "t" <= "_resteq (x = t)"

(*
thm expressions_grammar[no_vars]
thm (Grammar) expressions_grammar[no_vars]
thm (latex) expressions_grammar[no_vars]
thm (latex Grammar) expressions_grammar[no_vars]
*)

declare [[names_short]]

(*>*)
subsection {* Main definitions and theorems *}

text {*
For your convenience, the main definitions and theorems of the present work are assembled in this section. The following 
formulas are mechanically pretty-printed versions of the statements as defined resp.\ proven in Isabelle.
Free variables are all-quantified. Some type conversion functions (like @{term_type set}) are omitted.
The relations @{text \<sharp>} and @{text "\<sharp>*"} come from the Nominal package and express freshness of the
variables on the left with regard to the expressions on the right.

\input{map.tex}
*}

subsubsection {* Expressions *}

text {*
The type @{typ var} of variables is abstract and provided by the Nominal package. All we know about
it is that it is countably infinite.
Expressions of type @{typ exp} are given by the following grammar:
\begin{alignatstar}{2}
@{term e} \Coloneqq {}& @{term "Lam [x]. e"} &\quad& \text{lambda abstraction}\\
\mid {} & @{term "App e x"} && \text{application}\\
\mid {} & @{term "Var x"} && \text{variable} \\
\mid {} & @{term "Let as e"} && \text{recursive let}
\end{alignatstar}
In the introduction we pretty-print expressions to match the notation in \cite{launchbury} and omit
the constructor names @{term Var}, @{term App}, @{text Lam} and @{term Let}. In the actual theories, these are visible.
These expressions are, due to the machinery of the Nominal package, actually alpha-equivalency classes, so @{thm alpha_test[no_vars]} holds provably. This differs from Launchbury's original definition, which expects distinctly-named expressions and performs explicit alpha-renaming in the semantics.

The type @{type heap} is an abbreviation for @{typ "(var \<times> exp) list"}. These are \emph{not} alpha-equivalency classes, i.e.\ we manage the bindings in heaps explicitly.
*}

subsubsection {* The natural semantics *}

text_raw {*
\newlength{\rulelen}
\setlength{\rulelen}{\linewidth}
\newlength{\rulenamelen}
\settowidth{\rulenamelen}{~{\sc Application}}
\addtolength{\rulelen}{-\rulenamelen}
*}

text {*
Launchbury's original semantics, extended with some technical overhead related to name binding,
is defined as follows:\\
%\begin{center}
\parbox[t]{\rulelen}{\centering@{thm[mode=Axiom] Launchbury.reds.Lambda[no_vars]}}~{\sc Lambda}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Application[no_vars]}}~{\sc Application}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Variable[no_vars]}}~{\sc Variable}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Let[no_vars]}}~{\sc Let}
%\end{center}
*}

subsubsection {* The stacked semantics *}

text {*
This is our modified semantics that allows the correctness theorem to go through without generalisation:\\
\parbox[t]{\rulelen}{\centering@{thm[mode=Axiom] LaunchburyStacked.reds.Lambda[no_vars]}}~{\sc Lambda}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] LaunchburyStacked.reds.Application[no_vars]}}~{\sc Application}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] LaunchburyStacked.reds.Variable[no_vars]}}~{\sc Variable}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] LaunchburyStacked.reds.Let[no_vars]}}~{\sc Let}
*}
subsubsection {* The denotational semantics *}

text {*
The value domain of the denotational semantics is the initial solution to
\[
D = [D \to D]_\bot
\]
as introduced in \cite{abramsky}. The type @{typ Value}, together with the bottom value @{term_type "\<bottom>::Value"}, the
injection @{term_type "Fn"} and the projection @{term "DUMMY \<down>Fn DUMMY"}@{text "::"}@{typeof "Fn_project"},
is constructed as a pointed chain-complete partial order from this equation by the HOLCF package.
The type of semantic environments, @{typ Env}, is an abbreviation for @{typ "var f\<rightharpoonup> Value"}.

The semantics of an expression @{term_type "e :: exp"} in an environment @{term "\<rho>"}@{text "::"}@{typ Env} is 
written \mbox{@{term_type "Denotational.ESem e \<rho>"}} and defined by the following equations:
\begin{alignstar}
@{thm (lhs) Denotational.ESem.simps(1)[no_vars]} & = @{thm (rhs) Denotational.ESem.simps(1)[no_vars]} && \text{if } @{thm (prem 1) Denotational.ESem.simps(1)[no_vars]} \\
@{thm (lhs) Denotational.ESem.simps(2)[no_vars]} & = @{thm (rhs) Denotational.ESem.simps(2)[no_vars]} \\
@{thm (lhs) Denotational.ESem.simps(3)[no_vars]} & = @{thm (rhs) Denotational.ESem.simps(3)[no_vars]} \\
@{thm (lhs) Denotational.ESem.simps(4)[no_vars]} & = @{thm (rhs) Denotational.ESem.simps(4)[no_vars]} && \text{if } @{thm (prem 1) Denotational.ESem.simps(4)[no_vars]}.
\end{alignstar}
*}

text {*
We study two alternatives for the semantics @{term "Denotational.HSem \<Gamma> \<rho>"}@{text "::"}@{typ Env} of a
heap @{term "\<Gamma> :: heap"}@{text "::"}@{typ heap}
in an environment @{term "\<rho>"}@{text "::"}@{typ Env}. As this is used in denotations of a Let expression,
we have also two expression semantics. Their defining equations are, besides the choice of heap semantics, identical.

The first involves a least upper bound ($\sqcup$) and is defined by the recursive equation
\[ @{thm (concl) Denotational.HSem_eq[no_vars]}, \]
where the set in the index position indicates the expansion of the map to the given domain and
@{term "heapToEnv:: heap \<Rightarrow> (exp \<Rightarrow> Value) \<Rightarrow> Env"}@{text "::"}@{typ "heap \<Rightarrow> (exp \<Rightarrow> Value) \<Rightarrow> Env"}
maps the given expression semantics over the heap, producing a semantic environment.

The other, here shown with a superscript @{text "u"}, uses the right-sided update operator @{text "f++"}
and is defined by the recursive equation
\[ @{thm "Denotational-PropsUpd.HSem_eq"[no_vars]}. \]

The semantics of the heap in the empty environment @{term "fempty"} is abbreviated as @{abbrev "HSem_fempty \<Gamma>"}.

It is worth noting that the two semantics agree on expressions, i.e. @{thm HSem_join_update(1)[no_vars] },
but obviously not on heaps that bind variables that also occur in the environment.
*}

subsubsection {* Equivalences *}
text {*
The stacked semantics is equivalent to the original semantics in the following sense:
\begin{itemize}
\item If @{thm[mode=IfThen] (prem 1) forget_stack_nice[no_vars] } is derivable in the stacked semantics,
and @{term L} is chosen such that @{thm[mode=IfThen] (prem 2) forget_stack_nice[no_vars]} holds, then
 @{thm[mode=IfThen] (concl) forget_stack_nice[no_vars]} is derivable in the original semantics.
\item If @{thm[mode=IfThen] (prem 1) add_stack[no_vars]} is derivable in the original semantics and
@{term "x"} and @{term "\<Gamma>'"} are chosen such that @{thm[mode=IfThen] (prem 2) add_stack[no_vars]} and
@{thm[mode=IfThen] (prem 3) add_stack[no_vars]} holds, then  @{thm[mode=IfThen] (concl) add_stack[no_vars]}
is derivable in the stacked semantics.
\end{itemize}
*}

subsubsection {* Correctness *}
text {* The statement of correctness for the stacked semantics reads:
If @{thm [mode=IfThen] (prem 1) CorrectnessStacked.correctness[no_vars]} and, as a side condition,
@{thm [mode=IfThen] (prem 2) CorrectnessStacked.correctness[no_vars]} holds, then @{thm [mode=IfThen] (concl) CorrectnessStacked.correctness(1)[no_vars]}. *}

text {* By the stated equivalency, we obtain the correctness of the original semantics:
If \mbox{@{thm [mode=IfThen] (prem 1) Correctness.correctness(1)[no_vars]}} and, as a side condition,
@{thm [mode=IfThen] (prem 2) Correctness.correctness(1)[no_vars]} holds, then @{thm [mode=IfThen] (concl) Correctness.correctness(1)[no_vars]} and 
 @{thm [mode=IfThen] (concl) Correctness.correctness(2)[no_vars]} *}

text {* The generalization introduced by Launchbury is true if the update-based semantics is chosen:
If @{thm [mode=IfThen] (prem 1) CorrectnessUpd.correctness(1)[no_vars]} and, as a side condition,
@{thm [mode=IfThen] (prem 2) CorrectnessUpd.correctness(1)[no_vars]} and
\mbox{@{thm [mode=IfThen] (prem 3) CorrectnessUpd.correctness(1)[no_vars]}} hold,
then @{thm [mode=IfThen] (concl) CorrectnessUpd.correctness(1)[no_vars]} and  @{thm [mode=IfThen] (concl) CorrectnessUpd.correctness(2)[no_vars]}. *}


(*<*)

end
(*>*)
