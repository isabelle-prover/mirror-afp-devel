theory LTS
imports Graph Labels SymExec
begin

section{* Labelled Transition Systems *}

text{* This theory is motivated by the need of an  abstract representation of control-flow graphs
(CFG). It is a refinement of the prior theory of (unlabelled) graphs and proceeds by decorating
their edges with \emph{labels} expressing assumptions and effects (assignments) on an underlying 
state. In this theory, we define LTSs and introduce a number of abbreviations that will ease 
stating and proving lemmas in the following theories. *}

subsection{* Basic definitions *}

text{* The labelled transition systems (LTS) we are heading for are constructed by
extending  @{text "rgraph"}'s by a labelling function of the edges, using Isabelle extensible 
records. *}

record ('vert,'var,'d) lts = "'vert rgraph" +
  labelling :: "'vert edge \<Rightarrow> ('var,'d) label"

text {* We call \emph{initial location} the root of the underlying graph. *}

abbreviation init :: 
"('vert,'var,'d,'x) lts_scheme \<Rightarrow> 'vert" 
where
  "init lts \<equiv> root lts"

text {* The set of labels of a LTS is the image set of its labelling function over its set of edges. 
*}

abbreviation labels :: 
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) label set" 
where
  "labels lts \<equiv> labelling lts ` edges lts"

text {* In the following, we will sometimes need to use the notion of \emph{trace} of 
a given sequence of edges with respect to the transition relation of an LTS. *}

abbreviation trace :: 
  "'vert edge list \<Rightarrow> ('vert edge \<Rightarrow> ('var,'d) label) \<Rightarrow> ('var,'d) label list" 
where
  "trace as L \<equiv> map L as"


text{* We are interested in a special form of Labelled Transition Systems; the prior
record definition is too liberal. We will constrain it to \emph{well-formed labelled transition
systems}. *}

text {* We first define an application that, given an LTS, returns its underlying graph. *}

abbreviation graph :: 
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> 'vert rgraph"
where
  "graph lts \<equiv> rgraph.truncate lts"

text{* An LTS is well-formed if its underlying @{text "rgraph"} is well-formed. *}

abbreviation wf_lts :: 
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> bool" 
where 
  "wf_lts lts \<equiv> wf_rgraph (graph lts)"

text {* In the following theories, we will sometimes need to account for the fact that we consider 
LTSs with a finite number of edges. *}

abbreviation finite_lts :: 
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> bool" 
where
  "finite_lts lts \<equiv> \<forall> l \<in> range (labelling lts). finite_label l"


subsection {* Feasible sub-paths and paths *}

text {* A sequence of edges is a feasible sub-path of an LTS @{text "lts"} from a configuration 
@{text "c"} if it is a sub-path of the underlying graph of @{text "lts"} and if it is feasible 
from the configuration @{text "c"}.  *}

abbreviation feasible_subpath ::
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) conf \<Rightarrow> 'vert \<Rightarrow> 'vert edge list \<Rightarrow> 'vert \<Rightarrow> bool"
where
  "feasible_subpath lts pc l1 as l2 \<equiv> Graph.subpath lts l1 as l2 
                                    \<and> feasible pc (trace as (labelling lts))"
  
text {* Similarly to sub-paths in rooted-graphs, we will not be always interested in the final 
vertex of a feasible sub-path. We use the following notion when we are not interested in this 
vertex. *}

abbreviation feasible_subpath_from ::
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) conf \<Rightarrow> 'vert \<Rightarrow> 'vert edge list \<Rightarrow> bool"
where
  "feasible_subpath_from lts pc l as \<equiv> \<exists> l'. feasible_subpath lts pc l as l'"

abbreviation feasible_subpaths_from ::
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) conf \<Rightarrow> 'vert \<Rightarrow> 'vert edge list set"
where
  "feasible_subpaths_from lts pc l \<equiv> {ts. feasible_subpath_from lts pc l ts}"

text {* As earlier, feasible paths are defined as feasible sub-paths starting at the initial 
location of the LTS. *}

abbreviation feasible_path ::
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) conf \<Rightarrow> 'vert edge list \<Rightarrow> 'vert \<Rightarrow> bool"
where
  "feasible_path lts pc as l \<equiv> feasible_subpath lts pc (init lts) as l"

abbreviation feasible_paths ::
  "('vert,'var,'d,'x) lts_scheme \<Rightarrow> ('var,'d) conf \<Rightarrow> 'vert edge list set"
where
  "feasible_paths lts pc \<equiv> {as. \<exists> l. feasible_path lts pc as l}"

end
