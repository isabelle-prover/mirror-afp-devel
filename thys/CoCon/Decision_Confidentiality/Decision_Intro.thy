theory Decision_Intro
imports "../Safety_Properties"
begin

section \<open>Decision Confidentiality\<close>

text \<open>
In this section, we prove confidentiality properties for the accept-reject decision
of papers submitted to a conference. The secrets (values) of interest are therefore
the different updates of the decision of a given paper with id PID.

Here, we have two points of compromise between
the bound and the trigger (which yield two properties).
%
Let
\begin{itemize}
\item T1 denote ``PC membership having no conflict with that paper
and the conference having moved to the discussion stage''
\item T2 denote ``PC membership or authorship, and the conference having moved to the notification phase''
\end{itemize}
The two trigger-bound combinations are:
\begin{itemize}
\item weak trigger (T1 or T2)
paired with
strong bound
(allowing to learn almost nothing)
%
%
\item strong trigger (T1)
paired with weak bound
(allowing to learn the last updated version of the decision)
\end{itemize}
\<close>


end