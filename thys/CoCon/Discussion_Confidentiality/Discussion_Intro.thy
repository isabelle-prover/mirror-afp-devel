theory Discussion_Intro
imports "../Safety_Properties"
begin

section \<open>Discussion Confidentiality\<close>

text \<open>
In this section, we prove confidentiality for the discussion log
(with comments made by PC members) on submitted papers.
The secrets (values) of interest are therefore
the different updates of (i.e., comments posted as part of)
the discussion of a given paper with id PID.

Here, we have only one point of compromise between
the bound and the trigger (which yields one property):
the trigger being
``PC membership having no conflict with that paper and the conference having moved to the discussion stage''
and
the bound allowing to learn almost nothing.
\<close>


end