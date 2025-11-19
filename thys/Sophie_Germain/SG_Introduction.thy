
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory SG_Introduction
  imports Main
begin

context fixes n p :: nat and x y z :: int
begin

(*>*)



section \<open>Introduction\<close>

text \<open>
Fermat's Last Theorem (often abbreviated to FLT) states that for any integer 
\<^term>\<open>2 < n\<close>, the equation \<^term>\<open>x ^ n + y ^ n = z ^ n\<close> has no nontrivial solution in the integers.
Pierre de Fermat first conjectured this result in the 17th century,
claiming to have a proof that did not fit in the margin of his notebook.
However, it remained an open problem for centuries until Andrew Wiles and Richard Taylor provided
a complete proof in 1995 using advanced techniques from algebraic geometry and modular forms.

But in the meantime, many mathematicians have made partial progress on the problem.
In particular, Sophie Germain's theorem states that \<^term>\<open>p\<close> is a prime
such that \<^term>\<open>2 * p + 1\<close> is also a prime, then there are no integer
solutions to the equation \<^term>\<open>x ^ p + y ^ p = z ^ p\<close> such that \<^term>\<open>p\<close>
divides neither \<^term>\<open>x\<close>, \<^term>\<open>y\<close> nor \<^term>\<open>z\<close>.

This result is not only included in the extended list of Freek's ``Top 100 theorems''
\<^footnote>\<open>\<^url>\<open>http://www.cs.ru.nl/~freek/100/\<close>\<close>,
but is also very familiar to students taking the French
``agrégation'' mathematics competitive examination.
Hoping that this submission might also be useful to them,
we developed separately the classical version of the theorem
as presented in \<^cite>\<open>Francinou_Gianella_Nicolas_2014\<close>
and a generalization that one can find for example in \<^cite>\<open>kiefer2012theoreme\<close>.\<close>

text \<open>
\begin{figure}[h]
\label{sessionGraph}
\centering
\includegraphics[scale=0.5]{session_graph} 
\caption{Dependency graph of the session \<^session>\<open>Sophie_Germain\<close>}
\end{figure}
\newpage
\<close>

text \<open>
The session displayed in \ref{sessionGraph} is organized as follows:
  \<^item> \<^verbatim>\<open>FLT_Sufficient_Conditions\<close> provides sufficient conditions for proving FLT,
  \<^item> \<^verbatim>\<open>SG_Premilinaries\<close> establish some useful lemmas and introduces the concept
    of Sophie Germain prime,
  \<^item> \<^verbatim>\<open>SG_Theorem\<close> proves Sophie Germain's theorem and
  \<^item> \<^verbatim>\<open>SG_Generalization\<close> gives a generalization of it.
\<close>



(*<*)
end

end
  (*>*)
