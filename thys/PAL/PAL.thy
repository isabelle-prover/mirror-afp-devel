section \<open>Public Announcement Logic (PAL) in HOL\<close>

text \<open>An earlier encoding and automation of the wise men puzzle, utilizing a shallow embedding of 
higher-order (multi-)modal logic in HOL, has been presented in \<^cite>\<open>"J41" and "J44"\<close>. However, this work did not 
convincingly address the interaction dynamics between the involved agents. Here we therefore extend and adapt 
the universal (meta-)logical reasoning approach of \<^cite>\<open>"J41"\<close> for public announcement logic (PAL) and 
we demonstrate how it can be utilized to achieve a convincing encoding and automation of the 
wise men puzzle in HOL, so that also the interaction dynamics as given in the scenario is adequately 
addressed. For further background information on the work presented here we refer to \<^cite>\<open>"R78" and "C90"\<close>.\<close>

theory PAL imports Main begin  (* Sebastian Reiche and Christoph Benzmüller, 2021 *)
nitpick_params[user_axioms,expect=genuine]

text \<open>Type i is associated with possible worlds\<close>
 typedecl i (* Type of possible worlds *)
 type_synonym \<sigma> = "i\<Rightarrow>bool" (*Type of world domains *)
 type_synonym \<tau> = "\<sigma>\<Rightarrow>i\<Rightarrow>bool" (* Type of world depended formulas (truth sets) *) 
 type_synonym \<alpha> = "i\<Rightarrow>i\<Rightarrow>bool" (* Type of accessibility relations between world *)
 type_synonym \<rho> = "\<alpha>\<Rightarrow>bool" (* Type of groups of agents *)

text \<open>Some useful relations (for constraining accessibility relations)\<close>
definition reflexive::"\<alpha>\<Rightarrow>bool" 
  where "reflexive R \<equiv> \<forall>x. R x x"
definition symmetric::"\<alpha>\<Rightarrow>bool" 
  where "symmetric R \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"
definition transitive::"\<alpha>\<Rightarrow>bool" 
  where "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
definition euclidean::"\<alpha>\<Rightarrow>bool" 
  where "euclidean R \<equiv> \<forall>x y z. R x y \<and> R x z \<longrightarrow> R y z"
definition intersection_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" 
  where "intersection_rel R Q \<equiv> \<lambda>u v. R u v \<and> Q u v"
definition union_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>" 
  where "union_rel R Q \<equiv> \<lambda>u v. R u v \<or> Q u v"
definition sub_rel::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" 
  where "sub_rel R Q \<equiv> \<forall>u v. R u v \<longrightarrow> Q u v"
definition inverse_rel::"\<alpha>\<Rightarrow>\<alpha>" 
  where "inverse_rel R \<equiv> \<lambda>u v. R v u"
definition big_union_rel::"\<rho>\<Rightarrow>\<alpha>" 
  where "big_union_rel X \<equiv> \<lambda>u v. \<exists>R. (X R) \<and> (R u v)"
definition big_intersection_rel::"\<rho>\<Rightarrow>\<alpha>"
  where "big_intersection_rel X \<equiv> \<lambda>u v. \<forall>R. (X R) \<longrightarrow> (R u v)"

text \<open>In HOL the transitive closure of a relation can be defined in a single line.\<close>
definition tc::"\<alpha>\<Rightarrow>\<alpha>" 
  where "tc R \<equiv> \<lambda>x y.\<forall>Q. transitive Q \<longrightarrow> (sub_rel R Q \<longrightarrow> Q x y)"

text \<open>Logical connectives for PAL\<close>
abbreviation patom::"\<sigma>\<Rightarrow>\<tau>" ("\<^sup>A_"[79]80) 
  where "\<^sup>Ap \<equiv> \<lambda>W w. W w \<and> p w"
abbreviation ptop::"\<tau>" ("\<^bold>\<top>") 
  where "\<^bold>\<top> \<equiv> \<lambda>W w. True" 
abbreviation pneg::"\<tau>\<Rightarrow>\<tau>" ("\<^bold>\<not>_"[52]53) 
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>W w. \<not>(\<phi> W w)" 
abbreviation pand::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<and>"51) 
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<and> (\<psi> W w)"   
abbreviation por::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<or>"50) 
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<or> (\<psi> W w)"   
abbreviation pimp::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longrightarrow> (\<psi> W w)"  
abbreviation pequ::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" (infixr"\<^bold>\<leftrightarrow>"48) 
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longleftrightarrow> (\<psi> W w)"
abbreviation pknow::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K_ _") 
  where "\<^bold>K r \<phi> \<equiv> \<lambda>W w.\<forall>v. (W v \<and> r w v) \<longrightarrow> (\<phi> W v)"
abbreviation ppal::"\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>[\<^bold>!_\<^bold>]_") 
  where "\<^bold>[\<^bold>!\<phi>\<^bold>]\<psi> \<equiv> \<lambda>W w. (\<phi> W w) \<longrightarrow> (\<psi> (\<lambda>z. W z \<and> \<phi> W z) w)"

text \<open>Glogal validity of PAL formulas\<close>
abbreviation pvalid::"\<tau> \<Rightarrow> bool" ("\<^bold>\<lfloor>_\<^bold>\<rfloor>"[7]8) 
  where "\<^bold>\<lfloor>\<phi>\<^bold>\<rfloor> \<equiv> \<forall>W.\<forall>w. W w \<longrightarrow> \<phi> W w"

text \<open>Introducing agent knowledge (K), mutual knowledge (E), distributed knowledge (D) and common knowledge (C).\<close>
abbreviation EVR::"\<rho>\<Rightarrow>\<alpha>"
  where "EVR G \<equiv> big_union_rel G"
abbreviation DIS::"\<rho>\<Rightarrow>\<alpha>" 
  where "DIS G \<equiv> big_intersection_rel G"
abbreviation agttknows::"\<alpha>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>K\<^sub>_ _") 
  where "\<^bold>K\<^sub>r \<phi> \<equiv>  \<^bold>K r \<phi>" 
abbreviation evrknows::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>E\<^sub>_ _") 
  where "\<^bold>E\<^sub>G \<phi> \<equiv>  \<^bold>K (EVR G) \<phi>"
abbreviation disknows :: "\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>D\<^sub>_ _") 
  where "\<^bold>D\<^sub>G \<phi> \<equiv> \<^bold>K (DIS G) \<phi>"
abbreviation prck::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_\<^bold>\<lparr>_\<^bold>|_\<^bold>\<rparr>")
  where "\<^bold>C\<^sub>G\<^bold>\<lparr>\<phi>\<^bold>|\<psi>\<^bold>\<rparr> \<equiv> \<lambda>W w. \<forall>v. (tc (intersection_rel (EVR G) (\<lambda>u v. W v \<and> \<phi> W v)) w v) \<longrightarrow> (\<psi> W v)"
abbreviation pcmn::"\<rho>\<Rightarrow>\<tau>\<Rightarrow>\<tau>" ("\<^bold>C\<^sub>_ _") 
  where "\<^bold>C\<^sub>G \<phi> \<equiv>  \<^bold>C\<^sub>G\<^bold>\<lparr>\<^bold>\<top>\<^bold>|\<phi>\<^bold>\<rparr>"

text \<open>Postulating S5 principles for the agent's accessibility relations.\<close>
abbreviation S5Agent::"\<alpha>\<Rightarrow>bool"
  where  "S5Agent i \<equiv> reflexive i \<and> transitive i \<and> euclidean i"
abbreviation S5Agents::"\<rho>\<Rightarrow>bool"
  where "S5Agents A \<equiv> \<forall>i. (A i \<longrightarrow> S5Agent i)"

text \<open>Introducing "Defs" as the set of the above definitions; useful for convenient unfolding.\<close>
named_theorems Defs
declare reflexive_def[Defs] symmetric_def[Defs] transitive_def[Defs] 
  euclidean_def[Defs] intersection_rel_def[Defs] union_rel_def[Defs] 
  sub_rel_def[Defs] inverse_rel_def[Defs] big_union_rel_def[Defs] 
  big_intersection_rel_def[Defs] tc_def[Defs]

text \<open>Consistency: nitpick reports a model.\<close>
 lemma True nitpick [satisfy] oops (* model found *)


section \<open>Automating the Wise Men Puzzle\<close>

text \<open>Agents are modeled as accessibility relations.\<close>
consts a::"\<alpha>" b::"\<alpha>" c::"\<alpha>" 
abbreviation  Agent::"\<alpha>\<Rightarrow>bool" ("\<A>") where "\<A> x \<equiv> x = a \<or> x = b \<or> x = c"
axiomatization where  group_S5: "S5Agents \<A>"

text \<open>Common knowledge: At least one of a, b and c has a white spot.\<close>
consts ws::"\<alpha>\<Rightarrow>\<sigma>" 
axiomatization where WM1: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^sup>Aws a \<^bold>\<or> \<^sup>Aws b \<^bold>\<or> \<^sup>Aws c)\<^bold>\<rfloor>" 

text \<open>Common knowledge: If x does not have a white spot then y knows this.\<close>
axiomatization where
  WM2ab: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
  WM2ac: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws a) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws a))))\<^bold>\<rfloor>" and
  WM2ba: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
  WM2bc: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws b) \<^bold>\<rightarrow> (\<^bold>K\<^sub>c (\<^bold>\<not>(\<^sup>Aws b))))\<^bold>\<rfloor>" and
  WM2ca: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>a (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" and
  WM2cb: "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> (\<^bold>\<not>(\<^sup>Aws c) \<^bold>\<rightarrow> (\<^bold>K\<^sub>b (\<^bold>\<not>(\<^sup>Aws c))))\<^bold>\<rfloor>" 

text \<open>Positive introspection principles are implied.\<close>
lemma WM2ab': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> \<^bold>K\<^sub>b (\<^sup>Aws a))\<^bold>\<rfloor>" 
  using WM2ab group_S5 unfolding Defs by metis
lemma WM2ac': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws a) \<^bold>\<rightarrow> \<^bold>K\<^sub>c (\<^sup>Aws a))\<^bold>\<rfloor>" 
  using WM2ac group_S5 unfolding Defs by metis
lemma WM2ba': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> \<^bold>K\<^sub>a (\<^sup>Aws b))\<^bold>\<rfloor>" 
  using WM2ba group_S5 unfolding Defs by metis
lemma WM2bc': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws b) \<^bold>\<rightarrow> \<^bold>K\<^sub>c (\<^sup>Aws b))\<^bold>\<rfloor>" 
  using WM2bc group_S5 unfolding Defs by metis
lemma WM2ca': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> \<^bold>K\<^sub>a (\<^sup>Aws c))\<^bold>\<rfloor>" 
  using WM2ca group_S5 unfolding Defs by metis
lemma WM2cb': "\<^bold>\<lfloor>\<^bold>C\<^sub>\<A> ((\<^sup>Aws c) \<^bold>\<rightarrow> \<^bold>K\<^sub>b (\<^sup>Aws c))\<^bold>\<rfloor>" 
  using WM2cb group_S5 unfolding Defs by metis

text \<open>Automated solutions of the Wise Men Puzzle.\<close>
theorem whitespot_c: "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>a(\<^sup>Aws a)\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>\<^bold>K\<^sub>b(\<^sup>Aws b)\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>" 
  using WM1 WM2ba WM2ca WM2cb unfolding Defs by (smt (verit))

text \<open>For the following, alternative formulation a proof is found by sledgehammer, while the
reconstruction of this proof using trusted methods (often) fails; this hints at further opportunities to
improve the reasoning tools in Isabelle/HOL.\<close>
theorem whitespot_c':
  "\<^bold>\<lfloor>\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>a (\<^sup>Aws a)) \<^bold>\<or> (\<^bold>K\<^sub>a (\<^bold>\<not>\<^sup>Aws a)))\<^bold>](\<^bold>[\<^bold>!\<^bold>\<not>((\<^bold>K\<^sub>b (\<^sup>Aws b)) \<^bold>\<or> (\<^bold>K\<^sub>b (\<^bold>\<not>\<^sup>Aws b)))\<^bold>](\<^bold>K\<^sub>c (\<^sup>Aws c)))\<^bold>\<rfloor>"
  using WM1 WM2ab WM2ac WM2ba WM2bc WM2ca WM2cb unfolding Defs 
   \<comment> \<open>sledgehammer by (smt (verit))\<close>
  oops
   
text \<open>Consistency: nitpick reports a model.\<close>
lemma True nitpick [satisfy] oops  
end





