theory Reviewer_Assignment_Intro
imports "../Safety_Properties"
begin

section \<open>Reviewer Assignment Confidentiality\<close>

text \<open>
In this section, we prove confidentiality properties for the
assignment of reviewers to a paper PID submitted to a conference.

The secrets (values) of interest are taken to be pairs (uid,Uids),
where uid is a user and Uids is a set of users. The pairs arise
from actions that appoint reviewers to the paper PID:
\begin{itemize}
\item uid is the appointed reviewer
\item Uids is the set of PC members having no conflict with the paper
\end{itemize}
The use of the second component, which turns out to be the same for the
entire sequence of values\footnote{This is because conflicts can no longer be changed
at the time when reviewers can be appointed, i.e., in the reviewing phase.}
is needed in order to express the piece of information
(knowledge) that the appointed reviewers are among the non-conflicted
PC members.\footnote{In CoCon, only PC members can be appointed as reviewers;
there is no subreviewing facility.}

Here, we have two points of compromise between
the bound and the trigger (which yield two properties).
%
Let
\begin{itemize}
\item T1 denote
``PC membership having no conflict with that paper and the conference having moved to the reviewing phase''
\item T2 denote
``authorship of the paper and the conference having moved to the notification phase''
\end{itemize}
%
The two trigger-bound combinations are:
\begin{itemize}
\item weak trigger (T1 or T2)
paired with strong bound
(allowing to learn nothing beyond the public knowledge that the reviewers are among
PC members having no conflict with that paper)
%
\item strong trigger (T1)
paired with weak bound
(allowing to additionally learn the number of reviewers)
\end{itemize}
\<close>


end