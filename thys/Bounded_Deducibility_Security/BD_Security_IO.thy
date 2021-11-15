subsection \<open>Instantiation for IO automata\<close>

(*<*)
theory BD_Security_IO
imports Abstract_BD_Security BD_Security_TS IO_Automaton Filtermap
begin
(*>*)


no_notation relcomp (infixr "O" 75)

abbreviation never :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where "never U \<equiv> list_all (\<lambda> a. \<not> U a)"

locale BD_Security_IO = IO_Automaton istate step
 for istate :: 'state and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'out \<times> 'state"
+
fixes (* value filtering and production:  *)
   \<phi> :: "('state,'act,'out) trans \<Rightarrow> bool" and f :: "('state,'act,'out) trans \<Rightarrow> 'value"
 and (* observation filtering and production: *)
   \<gamma> :: "('state,'act,'out) trans \<Rightarrow> bool" and g :: "('state,'act,'out) trans \<Rightarrow> 'obs"
 and (* declassification trigger:  *)
   T :: "('state,'act,'out) trans \<Rightarrow> bool"
 and (* declassification bound: *)
   B :: "'value list \<Rightarrow> 'value list \<Rightarrow> bool"
begin

sublocale BD_Security_TS where validTrans = validTrans and srcOf = srcOf and tgtOf = tgtOf .

lemma reachNT_step_induct[consumes 1, case_names Istate Step]:
  assumes "reachNT s"
    and "P istate"
    and "\<And>s a ou s'. reachNT s \<Longrightarrow> step s a = (ou, s') \<Longrightarrow> \<not>T (Trans s a ou s') \<Longrightarrow> P s \<Longrightarrow> P s'"
  shows "P s"
  using assms
  by (induction rule: reachNT.induct) (auto elim: validTrans.elims)

lemma reachNT_PairI:
  assumes "reachNT s" and "step s a = (ou, s')" and "\<not> T (Trans s a ou s')"
  shows "reachNT s'"
  using assms reachNT.simps[of s']
  by auto

lemma reachNT_state_cases[cases set, consumes 1, case_names init step]:
  assumes "reachNT s"
  obtains "s = istate"
  | sh a ou where "reach sh" "step sh a = (ou,s)" "\<not>T (Trans sh a ou s)"
  using assms
  unfolding reachNT.simps[of s]
  by (fastforce intro: reachNT_reach elim: validTrans.elims)

(* This is assumed to be an invariant only modulo non T  *)
definition invarNT where
"invarNT Inv \<equiv> \<forall> s a ou s'. reachNT s \<and> Inv s \<and> \<not> T (Trans s a ou s') \<and> step s a = (ou,s') \<longrightarrow> Inv s'"

lemma invarNT_disj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<or> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma invarNT_conj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<and> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma holdsIstate_invarNT:
  assumes h: "holdsIstate Inv" and i: "invarNT Inv" and a: "reachNT s"
  shows "Inv s"
  using a using h i unfolding holdsIstate_def invarNT_def
  by (induction rule: reachNT_step_induct) auto

end (* context BD_Security_IO *)

(*<*)
end
(*>*)
