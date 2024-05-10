section \<open>Example\<close>

text \<open>\label{sec:example}\<close>

theory Example
  imports TD_plain TD_equiv
begin

text \<open>As an example, let us consider a program analysis, namely the analysis of must-be initialized
  program variables for the following program:\<close>

text \<open>\<^verbatim>\<open>a = 17
while true:
  b = a * a
  if b < 10: break
  a = a - 1\<close>\<close>

text \<open>The program corresponds to the following control-flow graph.\newline\includegraphics{cfg.pdf}\<close>

text \<open>From the control-flow graph of the program, we generate the equation system to be solved by
  the TD. The left-hand side of an equation consists of an unknown which represents a program point.
  The right-hand side for some unknown describes how the set of must-be initialized variables at the
  corresponding program point can be computed from the sets of must-be initialized variables at the
  predecessors.\<close>

subsection\<open>Definition of the Domain\<close>

datatype pv = a | b

text \<open>A fitting domain to describe possible values for the must-be initialized analysis, is an
  inverse power set lattice of the set of all program variables. The least informative value which
  is always a true over-approximation for the must-be initialized analysis is the empty set
  (called top), whereas the initial value to start fixpoint iteration from is the set
  @{term "{a, b}"} (called bot). The join operation, which is used to combine the values of
  several incoming edges to obtain a sound over-approximation over all paths, corresponds to the
  intersection of sets.\<close>

typedef D = "Pow ({a, b})"
  by auto

setup_lifting D.type_definition_D

lift_definition top :: "D" is "{}" by simp
lift_definition bot :: D is "{a, b}" by simp
lift_definition join :: "D \<Rightarrow> D \<Rightarrow> D" is Set.inter by blast

text\<open>Additionally, we define some helper functions to create values of type D.\<close>

lift_definition insert :: "pv \<Rightarrow> D \<Rightarrow> D"
  is "\<lambda>e d. if e \<in> {a, b} then Set.insert e d else d"
  by auto
definition set_to_D :: "pv set \<Rightarrow> D" where
  "set_to_D = (\<lambda>s. fold (\<lambda>e acc. if e \<in> s then insert e acc else acc) [a, b] top)"


text\<open>We show that the considered domain fulfills the sort constraints bot and equal as expected by
  the solver.\<close>

instantiation D :: bot
begin
  definition bot_D :: D
  where "bot_D = bot"

  instance ..
end

instantiation D :: equal
begin
  definition equal_D :: "D \<Rightarrow> D \<Rightarrow> bool"
  where "equal_D d1 d2 = ((Rep_D d1) = (Rep_D d2))"

  instance by standard (simp add: equal_D_def Rep_D_inject)
end


subsection\<open>Definition of the Equation System\<close>

text \<open>The following equation system can be generated for the must-be initialized analysis and the
  program from above.$$
   \mathcal{T}:\quad
   \begin{aligned}
     \mathrm{w} &= \emptyset \\
     \mathrm{z} &= \left(\mathrm{y}\,\cup\,\{\mathtt{a}\}\right)\,\cap\,\left(\mathrm{w}\,\cup\,
                   \{\mathtt{a}\}\right) \\
     \mathrm{y} &= \mathrm{z}\,\cup\,\{\mathtt{b}\} \\
     \mathrm{x} &= \mathrm{y}\,\cap\,\mathrm{z}
   \end{aligned}
$$
Below we define this equation system and express the right-hand sides with strategy trees.\<close>

datatype Unknown = X | Y | Z | W

fun ConstrSys :: "Unknown \<Rightarrow> (Unknown, D) strategy_tree" where
  "ConstrSys X = Query Y (\<lambda>d1. if d1 = top then Answer top
    else Query Z (\<lambda>d2. Answer (join d1 d2)))"
| "ConstrSys Y = Query Z (\<lambda>d. if d \<in> {top, set_to_D {b}}
    then Answer (set_to_D {b}) else Answer bot)"
| "ConstrSys Z = Query Y (\<lambda>d1. if d1 \<in> {top, set_to_D {a}}
    then Answer (set_to_D {a})
    else Query W (\<lambda>d2. if d2 \<in> {top, set_to_D {a}}
      then Answer (set_to_D {a}) else Answer bot))"
| "ConstrSys W = Answer top"


subsection \<open>Solve the Equation System with TD\_plain\<close>

text \<open>We solve the equation system for each unknown, first with the TD\_plain and in the following
also with the TD.
Note, that we use a finite map that defaults to bot for keys that are not contained in the map.
This can happen in two cases: (1) when the value computed for that unknown is equal to bot, or (2)
if the unknown was not queried during the solving and therefore no value was stored in the finite
map for it.\<close>

definition solution_plain_X where
  "solution_plain_X = TD_plain_Interp_solve ConstrSys X"
value "(solution_plain_X X, solution_plain_X Y, solution_plain_X Z, solution_plain_X W)"

definition solution_plain_Y where
  "solution_plain_Y = TD_plain_Interp_solve ConstrSys Y"
value "(solution_plain_Y X, solution_plain_Y Y, solution_plain_Y Z, solution_plain_Y W)"

definition solution_plain_Z where
  "solution_plain_Z = TD_plain_Interp_solve ConstrSys Z"
value "(solution_plain_Z X, solution_plain_Z Y, solution_plain_Z Z, solution_plain_Z W)"

definition solution_plain_W where
  "solution_plain_W = TD_plain_Interp_solve ConstrSys W"
value "(solution_plain_W X, solution_plain_W Y, solution_plain_W Z, solution_plain_W W)"


subsection\<open>Solve the Equation System with TD\<close>

definition solutionX where "solutionX = TD_Interp_solve ConstrSys X"
value "((snd solutionX) X, (snd solutionX) Y, (snd solutionX) Z, (snd solutionX) W)"

definition solutionY where "solutionY = TD_Interp_solve ConstrSys Y"
value "((snd solutionY) X, (snd solutionY) Y, (snd solutionY) Z, (snd solutionY) W)"

definition solutionZ where "solutionZ = TD_Interp_solve ConstrSys Z"
value "((snd solutionZ) X, (snd solutionZ) Y, (snd solutionZ) Z, (snd solutionZ) W)"

definition solutionW where "solutionW = TD_Interp_solve ConstrSys W"
value "((snd solutionW) X, (snd solutionW) Y, (snd solutionW) Z, (snd solutionW) W)"


end
