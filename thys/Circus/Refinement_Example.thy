(*  Title:       Isabelle/Circus
    Author:      Abderrahmane Feliachi, Burkhart Wolff, Marie-Claude Gaudel
                 Univ. Paris-Sud / LRI
    Maintainer:  Abderrahmane Feliachi
*)

theory Refinement_Example
imports Refinement
begin

subsection {* Concrete example *}

text {*
We describe the front-end interface of Isabelle/\Circus .
In order to support a maximum of common \Circus\ syntactic look-and-feel, we have programmed
at the SML level of Isabelle a compiler that parses and (partially) pretty prints \Circus\ process 
given in the syntax presented in Figure \ref{figure:CircSynt}.

\subsubsection{Writing specifications}
A specification is a sequence of paragraphs.
Each paragraph may be a declaration of alphabet, state, channels, name sets, channel sets, schema 
expressions or actions. 
The main action is introduced by the keyword \inlineisar+where+.
Below, we illustrate how to use the environment to write a \Circus\ specification using the 
@{term FIG} process example presented in Figure \ref{figure:Fig}.

\begin{isar}
circusprocess FIG =
  alphabet = [v::nat, x::nat]
  state = [idS::nat set]
  channel = [req, ret nat, out nat]
  schema Init = idS := {}
  schema Out = \<exists> a. v' = a \<and>   v' \<notin>  idS \<and>  idS' = idS \<union>  {v'}
  schema Remove = x \<notin>   idS \<and>  idS' = idS - {x}
  where var v \<bullet>  Schema Init; (\<mu> X \<bullet> (req \<rightarrow> Schema Out; out!v \<rightarrow> Skip) 
                                  \<box>  (ret?x \<rightarrow> Schema Remove); X)
\end{isar}
%DFIG MOVED FORWARD
Each line of the specification is translated into the corresponding semantic operator given in 
Section \ref{ActionsAndP}. 
We describe below the result of executing each command of @{term FIG}:

\begin{itemize}
\item the compiler introduces a scope of local components whose names are qualified by the process 
name (@{term FIG} in the example).
\item \inlineisar+alphabet+ generates a list of record fields to represent the binding. These fields 
map names to value lists.
\item \inlineisar+state+ generates a list of record fields that corresponds to the state variables. 
The names are mapped to single values. 
This command, together with \inlineisar+alphabet+ command, generates a record that 
represents all the variables (for the @{term FIG} example the command generates the record 
\inlineisar+FIG_alphabet+, that contains the fields \inlineisar+v+ and \inlineisar+x+ of type 
@{typ "nat list"} and the field \inlineisar+idS+ of type @{typ "nat set"}).
\item \inlineisar+channel+ introduces a datatype of typed communication channels (for the 
@{term FIG} example the command generates the datatype \inlineisar+FIG_channels+ that contains 
the constructors \inlineisar+req+ without communicated value and \inlineisar+ret+ and 
\inlineisar+out+ that communicate natural values). \item \inlineisar+schema+ allows the definition 
of schema expressions represented as an alphabetized relation over the process variables (in the 
example the schema expressions \inlineisar+FIG.Init+, \inlineisar+FIG.Out+ and 
\inlineisar+FIG.Remove+ are generated). \item \inlineisar+action+ introduces definitions for 
\Circus\ actions in the process. These definitions are based on the denotational semantics of 
\Circus\ actions. The type parameters of the action type are instantiated with the locally defined 
channels and alphabet types. \item \inlineisar+where+ introduces the main action as in 
\inlineisar+action+ command (in the example the main action is \inlineisar+FIG.FIG+ of type \\
\inlineisar+(FIG_channels, FIG_alphabet) action+).
\end{itemize}
 *}


text{* The semantic representation of this process in Isabelle/\Circus looks as follows: *}

datatype FIG_channels = out nat | req | ret nat
record FIG_alphabet = v::"nat list" x::"nat list" idS::"nat set"

instantiation FIG_channels :: ev_eq
begin
fun equ_ev where
  "equ_ev (out a) (out b) = True"
| "equ_ev (req) (req) = True"
| "equ_ev (ret a) (ret b) = True"
| "equ_ev a b = False"

instance ..
end

locale FIG

context FIG
begin

definition "Init \<equiv> \<lambda> (A, A'). idS A' = {}"
definition "Out \<equiv> \<lambda> (A, A'). \<exists> a. (hd (v A')) = a & a \<notin> idS A & idS A' = idS A \<union> {hd (v A')}"
definition "Remove \<equiv> \<lambda> (A, A'). hd (x A) \<in> idS A & idS A' = idS A - {hd (x A)}"
definition "FIG \<equiv> var v \<bullet> (Schema FIG.Init`;`
                \<mu> X \<bullet> (((((req \<rightarrow> (Schema FIG.Out))`;` out`!`(hd o v) \<rightarrow> Skip))
                          \<box> (ret`?`x \<rightarrow> (Schema FIG.Remove)))`;` X))"
end

text {* In the following, we state a deterministic version of the fresh number generator.
Here, the management of the identifiers via the set  @{term idS} is refined into a 
set of removed identifiers  \@{term retidS} and a number  @{term max}, 
which is the rank of the last issued identifier. In Isabelle/\Circus/ high-level 
syntax, this reads as follows:
\begin{isar}
circusprocess DFIG =
  alphabet = [w::nat, y::nat]
  state = [retidS::nat set, max::nat]
  schema Init = retidS' = {} \<and>   max' = 0
  schema Out = w' = max \<and>    max' = max+1 \<and>   retidS' = retidS - {max}
  schema Remove = y < max \<and>    y \<notin>  retidS \<and>   retidS' = retidS \<union>   {y} 
                      \<and> max' = max
  where var w \<bullet>  Schema Init; (\<mu> X \<bullet> (req \<rightarrow> Schema Out; out!w \<rightarrow> Skip)
                                  \<box>  (ret?y \<rightarrow> Schema Remove); X)
\end{isar}
*}

text{* The semantic presentation of this process looks as follows: *}

type_synonym DFIG_channels = FIG_channels
record DFIG_alphabet = v::"nat list" x::"nat list" retidS::"nat set" max::nat

locale DFIG

context DFIG
begin

definition "Init \<equiv> \<lambda> (A, A').retidS A' = {} \<and> max A' = 0"
definition "Out \<equiv> \<lambda> (A, A'). hd (v A') = max A \<and> max A' = (max A + 1) \<and> retidS A' = retidS A - {max A}"
definition "Remove \<equiv> \<lambda> (A, A'). hd (x A) < max A \<and> hd (x A) \<notin> retidS A \<and> retidS A' = retidS A \<union> {hd (x A)} \<and> max A' = max A"
definition "DFIG \<equiv> var v \<bullet> (Schema DFIG.Init`;`
         \<mu> X \<bullet> ((((req \<rightarrow> (Schema DFIG.Out))`;` (out`!`(hd o v) \<rightarrow> Skip))
               \<box> (ret`?`x \<rightarrow> (Schema DFIG.Remove)))`;` X))"
end

text{* As can be seen, the representational distance between the syntactic notation and
the semantic presentation is quite close.*}

subsubsection {* Proving simulation *}

text {*
We provide the proof of refinement of @{term FIG} by @{term DFIG}  
just instantiating the simulation function @{term S} by the following abstraction function, 
that maps the underlying concrete states to abstract states:
*}

definition Sim where
  "Sim A = FIG_alphabet.make (DFIG_alphabet.v A) (DFIG_alphabet.x A)
   ({a. a < (DFIG_alphabet.max A) \<and> a \<notin> (DFIG_alphabet.retidS A)})"

text{*
where A is the alphabet of \inlineisar+DFIG+, and \inlineisar+FIG_alphabet.make+ 
yields an alphabet of type \inlineisar+FIG_Alphabet+ initializing the values of \inlineisar+v+, 
\inlineisar+x+ and \inlineisar+idS+ by their corresponding values from 
\inlineisar+DFIG_alphabet+: \inlineisar+w+, \inlineisar+y+ and 
\inlineisar+{a. a < max \<and>   a \<notin> retidS}+).
*}

text {* For the simulation proof, we give first proofs for simulation over the schema expressions.
The proof is then given over the main actions of the processes.*}

lemma SimInit: "(Schema FIG.Init) \<preceq>Sim (Schema DFIG.Init)"
  apply (auto simp: Sim_def Pre_def design_defs DFIG.Init_def FIG.Init_def rp_defs  alpha_rp.defs
                    DFIG_alphabet.defs FIG_alphabet.defs intro!: Sch_Sim)
  apply (rule_tac x="A\<lparr>max := 0, retidS := {}\<rparr>" in exI, simp)
done

lemma SimOut: "(Schema FIG.Out) \<preceq>Sim (Schema DFIG.Out)"
  apply (rule Sch_Sim)
  apply (auto simp: Pre_def DFIG_alphabet.defs FIG_alphabet.defs
                     alpha_rp.defs Sim_def FIG.Out_def DFIG.Out_def)
  apply (rule_tac x="a\<lparr>v := [DFIG_alphabet.max a], max := (Suc (DFIG_alphabet.max a)), 
                     retidS := retidS a - {DFIG_alphabet.max a}\<rparr>" in exI, simp)+
done


lemma SimRemove: "(Schema FIG.Remove) \<preceq>Sim (Schema DFIG.Remove)"
  apply (rule Sch_Sim)
  apply (auto simp: Pre_def DFIG_alphabet.defs FIG_alphabet.defs alpha_rp.defs Sim_def)
  apply (simp add: DFIG.Remove_def FIG.Remove_def)
  apply (rule_tac x="a\<lparr>retidS := insert (hd (DFIG_alphabet.x a)) (retidS a)\<rparr>" in exI, simp)
  apply (auto simp add: DFIG.Remove_def FIG.Remove_def)
done

text{*
To prove that @{term DFIG} is a refinement of @{term FIG} one must prove that 
the main action @{const DFIG.DFIG} refines the main action @{const FIG.FIG}. 
The definition is then simplified, and the refinement laws are applied to simplify the proof goal.
Thus, the full proof consists of a few lines in ISAR:
*}


lemma "FIG.FIG \<preceq>Sim DFIG.DFIG"
by (auto simp: DFIG.DFIG_def FIG.FIG_def mono_Seq SimRemove SimOut SimInit Sim_def FIG_alphabet.defs
         intro!:Var_Sim Seq_Sim Mu_Sim Det_Sim Sync_Sim Write_Sim Read_Sim Skip_Sim)

text{*
First, the definitions of @{const FIG.FIG} and @{term DFIG.DFIG} are simplified and 
the defined refinement laws are used by the \inlineisar+auto+ tactic as introduction rules. 
The second step replaces the definition of the simulation function and uses some proved lemmas 
to finish the proof. The three lemmas used in this proof: \inlineisar+SimInit+, 
\inlineisar+SimOut+ and \inlineisar+SimRemove+ give proofs of simulation for the schema 
@{const FIG.Init}, @{const FIG.Out} and @{const FIG.Remove}.
*}


end