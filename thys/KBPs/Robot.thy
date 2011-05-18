(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Robot
imports SPRViewSingle
begin

(*>*)
subsection{* The Robot *}

text{*
\label{sec:robot}

We now feed the algorithm, the simulated operations of the previous
section and a model of the autonomous robot of
\S\ref{sec:introduction} to the Isabelle/HOL code generator. To obtain
a finite environment we truncate the number line at 5. This is
intuitively sound for the purposes of determinining the robot's
behaviour due to the synchronous view and the observation that if it
reaches this rightmost position then it can never satisfy its
objective.  Running the resulting Haskell code yields this automaton,
which we have minimised using Hopcroft's algorithm
\cite{DBLP:journals/acta/Gries73}:
\begin{center}
 \includegraphics[width=\textwidth]{robot_spr}
\end{center}
The inessential labels on the states indicate the robot's
knowledge about its position, and those on the transitions are the
observations yielded by the sensor. Double-circled states are those in
which the robot performs the Halt action, the others Nothing. We can
see that if the robot learns that it is in the goal region then it
halts for all time, and that it never overshoots the goal region. We
can also see that traditional minimisation does not yield the smallest
automaton we could hope for. This is because the algorithm does not
specify what happens on invalid observations, which are modelled as
errors instead of don't-cares.

*}(*<*)

(*

The environment protocol does nothing if the robot has signalled halt,
or chooses a new position and sensor reading if it hasn't.

We need a finite type to represent positions and observations. It is
sufficient to go to 5, for by then we are either halted in the goal
region or have gone past it.

*)

datatype digit = A ("0") | B ("1") | C ("2") | D ("3") | E ("4") | F ("5")

lemma digit_univ: "(UNIV :: digit set) = {0,1,2,3,4,5}"
  unfolding UNIV_def
  apply auto
  apply (case_tac x)
  apply auto
  done

instance digit :: finite
  apply intro_classes
  apply (auto iff: digit_univ)
  done

fun
  digit_less :: "digit \<Rightarrow> digit \<Rightarrow> bool"
where
  "digit_less 0 0 = False"
| "digit_less 0 x = True"
| "digit_less 1 0 = False"
| "digit_less 1 1 = False"
| "digit_less 1 x = True"
| "digit_less 2 0 = False"
| "digit_less 2 1 = False"
| "digit_less 2 2 = False"
| "digit_less 2 x = True"
| "digit_less 3 4 = True"
| "digit_less 3 5 = True"
| "digit_less 3 x = False"
| "digit_less 4 5 = True"
| "digit_less 4 x = False"
| "digit_less 5 x = False"

lemma digit_less_irrefl:
  "\<not> digit_less x x"
  by (cases x, simp_all)

lemma digit_less_assym:
  "\<not> (digit_less x y \<and> digit_less y x)"
  by (cases x) (cases y, simp_all)+

lemma digit_less_trans:
  "\<lbrakk> digit_less x y; digit_less y z \<rbrakk> \<Longrightarrow> digit_less x z"
  apply (cases x)
  apply simp_all
  apply (cases y)
  apply simp_all
  apply (cases z, simp_all)
  apply (cases z, simp_all)
  apply (cases z, simp_all)
  apply (cases z, simp_all)

  apply (cases y, simp_all)
  apply (cases z, simp_all)
  apply (cases z, simp_all)
  apply (cases z, simp_all)

  apply (cases y, simp_all)
  apply (cases z, simp_all)
  apply (cases z, simp_all)

  apply (cases y, simp_all)
  apply (cases z, simp_all)

  apply (cases y, simp_all)
  done

instantiation digit :: linorder
begin

definition
  less_digit_def: "x < y \<equiv> digit_less x y"

definition
  less_eq_digit_def: "x \<le> y \<equiv> x = y \<or> digit_less x y"

instance
  apply intro_classes
  unfolding less_digit_def less_eq_digit_def
  using digit_less_irrefl digit_less_assym
  apply auto[1]
  apply auto[1]
  apply (blast dest: digit_less_trans)[1]
  using digit_less_irrefl digit_less_assym
  apply auto[1]

  using digit_less_irrefl digit_less_assym
  apply auto[1]

  apply (case_tac x)
  apply simp_all
  apply (case_tac y, simp_all)+
  done
end

fun
  digit_succ :: "digit \<Rightarrow> digit"
where
  "digit_succ 0 = 1"
| "digit_succ 1 = 2"
| "digit_succ 2 = 3"
| "digit_succ 3 = 4"
| "digit_succ 4 = 5"
| "digit_succ 5 = 5"

fun
  digit_pred :: "digit \<Rightarrow> digit"
where
  "digit_pred 0 = 0"
| "digit_pred 1 = 0"
| "digit_pred 2 = 1"
| "digit_pred 3 = 2"
| "digit_pred 4 = 3"
| "digit_pred 5 = 4"

datatype Agent = Robot
datatype EnvAct = Stay | MoveRight
datatype ObsError = Left | On | Right
datatype Proposition = Halted | InGoal
datatype RobotAct = NOP | Halt

type_synonym Halted = bool
type_synonym Pos = digit
type_synonym Obs = digit
type_synonym EnvState = "Pos \<times> Obs \<times> Halted"

definition
  envInit :: "EnvState list"
where
  "envInit \<equiv> [(0, 0, False), (0, 1, False)]"

definition
  envAction :: "EnvState \<Rightarrow> (EnvAct \<times> ObsError) list"
where
  "envAction \<equiv> \<lambda>_. [ (x, y) . x \<leftarrow> [Stay, MoveRight], y \<leftarrow> [Left, On, Right] ]"

definition
  newObs :: "digit \<Rightarrow> ObsError \<Rightarrow> digit"
where
  "newObs pos obserr \<equiv>
              case obserr of Left \<Rightarrow> digit_pred pos | On \<Rightarrow> pos | Right \<Rightarrow> digit_succ pos"

definition
  envTrans :: "EnvAct \<times> ObsError \<Rightarrow> (Agent \<Rightarrow> RobotAct) \<Rightarrow> EnvState \<Rightarrow> EnvState"
where
  "envTrans \<equiv> \<lambda>(move, obserr) aact (pos, obs, halted).
    if halted
      then (pos, newObs pos obserr, halted)
      else
        case aact Robot of
           NOP \<Rightarrow> (case move of
                      Stay \<Rightarrow> (pos, newObs pos obserr, False)
                    | MoveRight \<Rightarrow> (digit_succ pos, newObs (digit_succ pos) obserr, False))
         | Halt \<Rightarrow> (pos, newObs pos obserr, True)"
definition "envObs \<equiv> \<lambda>(pos, obs, halted). obs"
definition "envVal \<equiv> \<lambda>(pos, obs, halted) p.
   case p of Halted \<Rightarrow> halted
           | InGoal \<Rightarrow> 2 < pos \<and> pos < 4"

(* The KBP, clearly subjective. *)

definition
  kbp :: "(Agent, Proposition, RobotAct) KBP"
where
  "kbp \<equiv> [ \<lparr> guard = \<^bold>K\<^sub>Robot (Kprop InGoal),        action = Halt \<rparr>,
           \<lparr> guard = Knot (\<^bold>K\<^sub>Robot (Kprop InGoal)), action = NOP \<rparr> ]"

interpretation Robot!:
  SingleAgentEnvironment "\<lambda>_. kbp" envInit envAction envTrans envVal "\<lambda>_. envObs" "Robot"
  unfolding envInit_def envAction_def envTrans_def envObs_def
  apply unfold_locales
  apply (auto simp: kbp_def)
  apply (case_tac a, simp)+
  done

definition
  robotDFS :: "(EnvState, RobotAct list) trie \<times> (EnvState, (digit, EnvState odlist) mapping) trie"
where
  [code]: "robotDFS \<equiv> SPRSingleAutoDFS kbp envInit envAction envTrans envVal (\<lambda>_. envObs) Robot"

definition
  robotAlg :: "Agent \<Rightarrow> (digit, RobotAct, EnvState odlist) Protocol"
where
  "robotAlg \<equiv> mkSPRSingleAuto kbp envInit envAction envTrans envVal (\<lambda>_. envObs)"

lemma (in SingleAgentEnvironment)
  "Robot.Robot.implements robotAlg"
  unfolding robotAlg_def by (rule Robot.Robot.mkSPRSingleAuto_implements)

(*
export_code "robotDFS" "robotAlg" in Haskell file "/tmp/" (string_classes)
*)

end
(*>*)
