theory Traceback_Intro
  imports "../Safety_Properties"
begin


section \<open>Traceback Properties\<close>

text \<open>In this section, we prove traceback properties. These properties
trace back the actions leading to:
\begin{itemize}
\item the current visibility status of a post
\item the current friendship status of two users
\end{itemize}
They state that the current status can only occur via a ``legal'' sequence of actions.
Because the BD properties have (dynamic triggers within) declassification bounds
that refer to such statuses, the traceback properties complement BD Security in adding
confidentiality assurance. \<^cite>\<open>\<open>Section 5.2\<close> in "cosmed-itp2016"\<close> gives more details and explanations.
\<close>



end