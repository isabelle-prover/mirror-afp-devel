(*  Title:      Notation for hotel key card system
    Author:     Tobias Nipkow, TU Muenchen
*)

(*<*)
theory Notation
imports "~~/src/HOL/Library/LaTeXsugar"
begin

abbreviation
 "SomeFloor" ("(\<lfloor>_\<rfloor>)") where "\<lfloor>x\<rfloor> \<equiv> Some x"
(*>*)

subsection{*Notation*}

text{*
HOL conforms largely to everyday mathematical notation.
This section introduces further non-standard notation and in particular
a few basic data types with their primitive operations.
\sloppy
\begin{description}

\item[Types] The type of truth values is called @{typ bool}.  The
space of total functions is denoted by @{text"\<Rightarrow>"}. Type variables
start with a quote, as in @{typ"'a"}, @{typ"'b"} etc. The notation
$t$~@{text"::"}~$\tau$ means that term $t$ has type $\tau$.

\item[Functions] can be updated at @{text x} with new value @{text y},
written @{term"f(x:=y)"}.  The range of a function is @{term"range f"},
@{prop"inj f"} means @{text f} is injective.

\item[Pairs] come with the two projection functions
@{text"fst :: 'a \<times> 'b \<Rightarrow> 'a"} and @{text"snd :: 'a \<times> 'b \<Rightarrow> 'b"}.

\item[Sets] have type @{typ"'a set"}.

\item[Lists] (type @{typ"'a list"}) come with the empty list
@{term"[]"}, the infix constructor @{text"\<cdot>"}, the infix @{text"@"}
that appends two lists, and the conversion function @{term set} from
lists to sets.  Variable names ending in ``s'' usually stand for
lists.

\item[Records] are constructed like this @{text"\<lparr>f\<^sub>1 = v\<^sub>1, \<dots>\<rparr>"}
and updated like this \mbox{@{text"r\<lparr>f\<^sub>i := v\<^sub>i, \<dots>\<rparr>"}},
where the @{text f\<^sub>i} are the field names,
the @{text v\<^sub>i} the values and @{text r} is a record.

\end{description}\fussy
Datatype @{text option} is defined like this
\begin{center}
\isacommand{datatype} @{text"'a option = None | Some 'a"}
\end{center}
and adjoins a new element @{term None} to a type @{typ 'a}. For
succinctness we write @{term"Some a"} instead of @{term[source]"Some a"}.

Note that @{text"\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> A"}
abbreviates @{text"A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> A"}, which is the same as
``If @{text A\<^sub>1} and \dots\ and @{text A\<^sub>n} then @{text A}''.
*}

(*<*)
end
(*>*)
