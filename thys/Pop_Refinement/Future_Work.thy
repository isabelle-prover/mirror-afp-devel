chapter {* Future Work *}

theory %invisible Future_Work
imports Main
begin

text {* \label{chap:future} *}


section {* Populating the Framework *}
text {* \label{sec:populate} *}

text {* Pop-refinement provides a framework,
which must be populated with re-usable
concepts, methodologies, and theorem prover libraries
for full fruition.
The simple examples in \chapref{chap:exampleI} and \chapref{chap:exampleII},
and the discussion in \chapref{chap:general},
suggests a few initial ideas.
Working out examples of increasing complexity should suggest more ideas. *}


section {* Automated Transformations *}
text {* \label{sec:xform} *}

text {* A pop-refinement step from @{term spec\<^sub>i} can be performed manually,
by writing down @{text "spec\<^sub>i\<^sub>+\<^sub>1"} and proving @{text "spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p"}.
It is sometimes possible to generate @{text "spec\<^sub>i\<^sub>+\<^sub>1"} from @{term spec\<^sub>i},
along with a proof of @{text "spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p"},
using automated transformation techniques like
term rewriting,
application of algorithmic templates,
and term construction by witness finding,
e.g.\ \cite{SmithMarktoberdorf,SpecwareWebSite}.
Automated transformations may require
parameters to be provided and applicability conditions to be proved,
but should generally save effort
and make derivations more robust against changes in requirement specifications.
Extending existing theorem provers with automated transformation capabilities
would be advantageous for pop-refinement. *}


section {* Other Kinds of Design Objects *}
text {* \label{sec:otherdesign} *}

text {* It has been suggested~\cite{LambertPrivate}
that pop-refinement could be used
to develop other kinds of design objects than programs,
e.g.\ protocols, digital circuits, and hybrid systems.
Perhaps pop-refinement could be used to develop
engines, cars, buildings, etc.
So long as these design objects can be described
by languages amenable to formalization,
pop-refinement should be applicable. *}


end %invisible
