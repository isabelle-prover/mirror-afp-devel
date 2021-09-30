(* Title: CTR_Introduction.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

section\<open>Introduction\<close>
theory CTR_Introduction
  imports Main
begin



subsection\<open>Background\<close>

text\<open>
The framework \<open>Conditional Transfer Rule\<close> provides several experimental
Isabelle/Isar commands that are aimed at the automation of unoverloading
of definitions and synthesis of conditional transfer rules in Isabelle/HOL.
\<close>



subsection\<open>Structure and organization\<close>

text\<open>
The remainder of the reference manual is organized into two explicit sections,
one for each sub-framework of the CTR:
\begin{itemize}
\item \<open>Unoverload Definition\<close> (UD): automated elimination of sort
constraints and unoverloading of definitions
\item \<open>Conditional Transfer Rule\<close> (CTR): automated synthesis of 
relativized definitions and transfer rules
\end{itemize}
It should be noted that the abbreviation CTR will be used to 
refer both to the general framework and the sub-framework.
\<close>

text\<open>\newpage\<close>

end