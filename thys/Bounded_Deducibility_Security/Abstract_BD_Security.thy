(*<*)
theory Abstract_BD_Security
  imports Main
begin
(*>*)

section \<open>BD Security\<close>

subsection \<open>Abstract definition\<close>

no_notation relcomp (infixr "O" 75)

locale Abstract_BD_Security =
 fixes
  validSystemTrace :: "'traces \<Rightarrow> bool"
and \<comment> \<open>secret values:\<close>
  V :: "'traces \<Rightarrow> 'values"
and \<comment> \<open>observations:\<close>
  O :: "'traces \<Rightarrow> 'observations"
and \<comment> \<open>declassification bound:\<close>
  B :: "'values \<Rightarrow> 'values \<Rightarrow> bool"
and \<comment> \<open>declassification trigger:\<close>
  TT :: "'traces \<Rightarrow> bool"
begin

text \<open>A system is considered to be secure if, for all traces that satisfy a given condition
(later instantiated to be the absence of transitions satisfying a declassification trigger
condition, releasing the secret information), the secret value can be replaced by another
secret value within the declassification bound, without changing the observation.
Hence, an observer cannot distinguish secrets related by the declassification bound,
unless and until release of the secret information is allowed by the declassification trigger.\<close>

(* BD security: *)
definition secure :: bool where
"secure \<equiv>
 \<forall> tr vl vl1.
   validSystemTrace tr \<and> TT tr \<and> B vl vl1 \<and> V tr = vl \<longrightarrow>
   (\<exists> tr1. validSystemTrace tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1)"

lemma secureE:
assumes "secure" and "validSystemTrace tr" and "TT tr" and "B (V tr) vl1"
obtains tr1 where "validSystemTrace tr1" "O tr1 = O tr" "V tr1 = vl1"
using assms unfolding secure_def by auto

end (* context BD_Security *)

(*<*)
end
(*>*)
