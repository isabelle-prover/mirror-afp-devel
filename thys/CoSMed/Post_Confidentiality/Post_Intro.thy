theory Post_Intro
  imports "../Safety_Properties" "../Observation_Setup"
begin

section \<open>Post confidentiality\<close>

text \<open>We prove the following property:

\ \\
Given a group of users \<open>UIDs\<close> and a post \<open>PID\<close>,

that group cannot learn anything about the different versions of the post \<open>PID\<close>
(the initial created version and the later ones obtained by updating the post)

beyond the updates performed while or last before one of the following holds:
\begin{itemize}
\item either a user in \<open>UIDs\<close> is the post's owner, a friend of the owner, or the admin
\item or \<open>UIDs\<close> has at least one registered user and the post is marked as ``public''.
\end{itemize}
\<close>


end