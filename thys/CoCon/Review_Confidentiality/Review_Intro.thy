theory Review_Intro
imports "../Safety_Properties"
begin

section \<open>Review Confidentiality\<close>

text \<open>
In this section, we prove confidentiality properties for the reviews
of papers submitted to a conference. The secrets (values) of interest are therefore
the different versions of a given review for a given paper,
identified as the N'th review of the paper with id PID.

Here, we have three points of compromise between
the bound and the trigger (which yield three properties).
Let
\begin{itemize}
\item T1 denote
``review authorship''
\item T2 denote
``PC membership having no conflict with that paper and the conference having moved to the discussion phase''
\item T3 denote
``PC membership or authorship and the conference having moved to the notification phase''
\end{itemize}
%
The three bound-trigger combinations are:
\begin{itemize}
\item weak trigger (T1 or T2 or T3)
paired with
strong bound (allowing to learn almost nothing)
%
\item medium trigger (T1 or T2)
paired with
medium bound (allowing to learn the last edited version before notification)
%
\item strong trigger (T1)
paired with
weak bound
(allowing to learn the last edited version before discussion and all the later versions)
\end{itemize}
\<close>


end