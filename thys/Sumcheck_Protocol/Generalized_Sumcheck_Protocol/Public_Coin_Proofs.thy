(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Generic Public-coin Interactive Proofs\<close>

theory Public_Coin_Proofs
  imports Probability_Tools 
begin

subsection \<open>Generic definition\<close>

type_synonym ('i, 'r, 'a, 'resp, 'ps) prv = "'i \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'r \<Rightarrow> 'ps \<Rightarrow> 'resp \<times> 'ps" 

locale public_coin_proof =
  fixes ver0 :: "'i \<Rightarrow> 'vs \<Rightarrow> bool"
    and ver1 :: "'i \<Rightarrow> 'resp \<Rightarrow> 'r \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'vs \<Rightarrow> bool \<times> 'i \<times> 'vs"
begin

fun prove :: "'vs \<Rightarrow> ('i, 'r, 'a, 'resp, 'ps) prv \<Rightarrow> 'ps \<Rightarrow> 'i \<Rightarrow> 'r \<Rightarrow> ('a \<times> 'r) list \<Rightarrow> bool" where
  "prove vs prv ps I r [] \<longleftrightarrow> ver0 I vs" |
  "prove vs prv ps I r ((x, r')#rm) \<longleftrightarrow> 
     (let (resp, ps') = prv I x (map fst rm) r ps in 
      let (ok, I', vs') = ver1 I resp r' x (map fst rm) vs in 
        ok \<and> prove vs' prv ps' I' r' rm)"

text \<open>
The parameters are
\begin{itemize}
\item @{term "(ver0, ver1)"} and @{term "vs"} are the verifier and its current state,
\item @{term "prv"} and @{term "ps"} are the prover and its current state,
\item @{term "I \<in> S"} is the problem instance,
\item @{term "r"} is the verifier's randomness for the current round.
\item @{term "rs"} is the (list of) randomness for the remaining rounds, and
\item @{term "xs"} is a list of public per-round information/
\end{itemize}
We assume that @{term "rs"} and @{term "xs"} have the same length.
\<close>

end


subsection \<open>Generic soundness and completeness\<close>

locale public_coin_proof_security = 
  public_coin_proof ver0 ver1
  for ver0 :: "'i \<Rightarrow> 'vs \<Rightarrow> bool" 
  and ver1 :: "'i \<Rightarrow> 'resp \<Rightarrow> 'r \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'vs \<Rightarrow> bool \<times> 'i \<times> 'vs" + 
  fixes S :: "'i set"            \<comment> \<open>problem specification\<close>
    and honest_pr :: "('i, 'r, 'a, 'resp, 'ps) prv"
    and compl_err :: "'i \<Rightarrow> real"
    and sound_err :: "'i \<Rightarrow> real"
    and compl_assm :: "'vs \<Rightarrow> 'ps \<Rightarrow> 'i \<Rightarrow> 'a list \<Rightarrow> bool"
    and sound_assm :: "'vs \<Rightarrow> 'ps \<Rightarrow> 'i \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes
    completeness:  
       "\<lbrakk> I \<in> S; compl_assm vs ps I xs \<rbrakk> \<Longrightarrow>
          measure_pmf.prob 
            (pmf_of_set (tuples UNIV (length xs)))
            {rs. prove vs honest_pr ps I r (zip xs rs)} \<ge> 1 - compl_err I" and

    soundness:
       "\<lbrakk> I \<notin> S; sound_assm vs ps I xs \<rbrakk> \<Longrightarrow> 
          measure_pmf.prob 
            (pmf_of_set (tuples UNIV (length xs)))
            {rs. prove vs pr ps I r (zip xs rs)} \<le> sound_err I" 


locale public_coin_proof_strong_props = 
  public_coin_proof ver0 ver1 
  for ver0 :: "'i \<Rightarrow> 'vs \<Rightarrow> bool" 
  and ver1 :: "'i \<Rightarrow> 'resp \<Rightarrow> 'r::finite \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'vs \<Rightarrow> bool \<times> 'i \<times> 'vs" + 
  fixes S :: "'i set"            \<comment> \<open>problem specification\<close>
    and honest_pr :: "('i, 'r, 'a, 'resp, 'ps) prv"
    and sound_err :: "'i \<Rightarrow> real"
    and compl_assm :: "'vs \<Rightarrow> 'ps \<Rightarrow> 'i \<Rightarrow> 'a list \<Rightarrow> bool"
    and sound_assm :: "'vs \<Rightarrow> 'ps \<Rightarrow> 'i \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes
    completeness:  
       "\<lbrakk> I \<in> S; compl_assm vs ps I (map fst rm) \<rbrakk> \<Longrightarrow> prove vs honest_pr ps I r rm" and

    soundness:
       "\<lbrakk> I \<notin> S; sound_assm vs ps I xs \<rbrakk> \<Longrightarrow> 
          measure_pmf.prob 
            (pmf_of_set (tuples UNIV (length xs)))
            {rs. prove vs pr ps I r (zip xs rs)} \<le> sound_err I" 
begin


text \<open>Show that this locale satisfies the weaker assumptions of @{locale public_coin_proof_security}.\<close>

sublocale pc_props: 
  public_coin_proof_security ver0 ver1 S honest_pr "\<lambda>_. 0" sound_err compl_assm sound_assm
  by (unfold_locales)
     (fastforce simp add: prob_pmf_of_set_geq_1 tuples_Suc completeness, 
      clarsimp simp add: soundness)

end


end