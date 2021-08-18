theory Paper_Intro
imports "../Safety_Properties"
begin

section \<open>Paper Confidentiality\<close>

text \<open>
In this section, we prove confidentiality properties for the papers
submitted to a conference. The secrets (values) of interest are therefore
the different versions of a given paper (with identifier PID)
uploaded into the system.

The two properties that we prove represent points of ``compromise'' between
the strength of the declassification bound and that of the declassification trigger.
%
Let
\begin{itemize}
\item T1 denote ``the paper's authorship''
\item T2 denote ``PC membership and the conference having reached the bidding phase''
\end{itemize}
%
The two bound-trigger combinations are:
\begin{itemize}
\item weak trigger (T1 or T2)
paired with strong bound (nothing can be learned, save for some harmless
information, namely the non-existence of any upload);
%
\item strong trigger (T1)
paired with weak bound
(allowing to learn the last submitted version of the paper (but nothing more than that)).
\end{itemize}
\<close>


end