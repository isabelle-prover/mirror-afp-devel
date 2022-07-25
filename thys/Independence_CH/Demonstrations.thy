section\<open>Some demonstrations\<close>

theory Demonstrations
  imports
    Definitions_Main
begin

text\<open>The following theory is only intended to explore some details of the
formalization and to show the appearance of relevant internalized formulas.
It is \<^bold>\<open>not\<close> intended as the entry point of the session. For that purpose,
consult \<^theory>\<open>Independence_CH.Definitions_Main\<close>\<close>

locale Demo = M_trivial + M_AC +
  fixes t\<^sub>1 t\<^sub>2
  assumes
    ts_in_nat[simp]: "t\<^sub>1\<in>\<omega>" "t\<^sub>2\<in>\<omega>"
    and
    power_infty: "power_ax(M)" "M(\<omega>)"
begin

text\<open>The next fake lemma is intended to explore the instances of the axiom
schemes that are needed to build our forcing models. They are categorized as
plain replacements (using \<^term>\<open>strong_replacement\<close>), “lambda-replacements”
using a higher order function, replacements  to perform
transfinite and general well-founded recursion (using \<^term>\<open>transrec_replacement\<close> and
\<^term>\<open>wfrec_replacement\<close> respectively) and for the construction of fixpoints
(using \<^term>\<open>iterates_replacement\<close>). Lastly, separations instances.\<close>

lemma
  assumes
    sorried_replacements:
    "\<And>P. strong_replacement(M,P)"
    "\<And>F. lam_replacement(M,F)"
    "\<And>Q S. iterates_replacement(M,Q,S)"
    "\<And>Q S. wfrec_replacement(M,Q,S)"
    "\<And>Q S. transrec_replacement(M,Q,S)"
    and
    sorried_separations: "\<And>Q. separation(M,Q)"
  shows
    "M_master(M)"
  apply unfold_locales
                      apply
    (simp_all add:
      sorried_replacements(1-2)
      sorried_separations
      power_infty)
  oops

\<comment> \<open>NOTE: Only for pretty-printing purposes, overrides previous
  fundamental notations\<close>
no_notation mem (infixl \<open>\<in>\<close> 50)
no_notation conj  (infixr \<open>\<and>\<close> 35)
no_notation disj (infixr \<open>\<or>\<close> 30)
no_notation iff (infixr \<open>\<longleftrightarrow>\<close> 25)
no_notation imp (infixr \<open>\<longrightarrow>\<close> 25)
no_notation not (\<open>\<not> _\<close> [40] 40)
no_notation All (\<open>'(\<forall>_')\<close>)
no_notation Ex (\<open>'(\<exists>_')\<close>)

no_notation Member (\<open>\<cdot>_ \<in>/ _\<cdot>\<close>)
no_notation Equal (\<open>\<cdot>_ =/ _\<cdot>\<close>)
no_notation Nand (\<open>\<cdot>\<not>'(_ \<and>/ _')\<cdot>\<close>)
no_notation And (\<open>\<cdot>_ \<and>/ _\<cdot>\<close>)
no_notation Or (\<open>\<cdot>_ \<or>/ _\<cdot>\<close>)
no_notation Iff (\<open>\<cdot>_ \<leftrightarrow>/ _\<cdot>\<close>)
no_notation Implies (\<open>\<cdot>_ \<rightarrow>/ _\<cdot>\<close>)
no_notation Neg (\<open>\<cdot>\<not>_\<cdot>\<close>)
no_notation Forall (\<open>'(\<cdot>\<forall>(/_)\<cdot>')\<close>)
no_notation Exists (\<open>'(\<cdot>\<exists>(/_)\<cdot>')\<close>)

notation Member (infixl \<open>\<in>\<close> 50)
notation Equal (infixl \<open>\<equiv>\<close> 50)
notation Nand (\<open>\<not>'(_ \<and>/ _')\<close>)
notation And  (infixr \<open>\<and>\<close> 35)
notation Or (infixr \<open>\<or>\<close> 30)
notation Iff (infixr \<open>\<longleftrightarrow>\<close> 25)
notation Implies (infixr \<open>\<longrightarrow>\<close> 25)
notation Neg (\<open>\<not> _\<close> [40] 40)
notation Forall (\<open>'(\<forall>_')\<close>)
notation Exists (\<open>'(\<exists>_')\<close>)

lemma "forces(t\<^sub>1\<in>t\<^sub>2) = (0 \<in> 1 \<and> forces_mem_fm(1, 2, 0, t\<^sub>1+\<^sub>\<omega>4, t\<^sub>2+\<^sub>\<omega>4))"
  unfolding forces_def by simp

(*
\<comment> \<open>Prefix abbreviated notation\<close>
notation Member (\<open>M\<close>)
notation Equal (\<open>Eq\<close>)
notation Nand (\<open>Na\<close>)
notation And  (\<open>A\<close>)
notation Or (\<open>O\<close>)
notation Iff (\<open>If\<close>)
notation Implies (\<open>Im\<close>)
notation Neg (\<open>Ne\<close>)
notation Forall (\<open>Fo\<close>)
notation Exists (\<open>Ex\<close>)
*)

(* forces_mem_fm(1, 2, 0, t\<^sub>1+\<^sub>\<omega>4, t\<^sub>1+\<^sub>\<omega>4)
   = forces_mem_fm(1, 2, 0, succ(succ(succ(succ(t\<^sub>1)))), succ(succ(succ(succ(t\<^sub>2)))))
   = \<dots> *)

definition forces_0_mem_1 where "forces_0_mem_1\<equiv>forces_mem_fm(1,2,0,t\<^sub>1+\<^sub>\<omega>4,t\<^sub>2+\<^sub>\<omega>4)"
thm forces_0_mem_1_def[
    unfolded frc_at_fm_def ftype_fm_def
    name1_fm_def name2_fm_def snd_snd_fm_def hcomp_fm_def
    ecloseN_fm_def eclose_n1_fm_def eclose_n2_fm_def
    is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
    is_If_fm_def least_fm_def Replace_fm_def Collect_fm_def
    fm_definitions,simplified]
  (* NOTE: in view of the above, @{thm fm_definitions} might be incomplete *)

named_theorems incr_bv_new_simps

schematic_goal incr_bv_Neg(* [incr_bv_new_simps] *):
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow> incr_bv(Neg(\<phi>))`n = ?x"
  unfolding Neg_def by simp

schematic_goal incr_bv_Exists [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow> incr_bv(Exists(\<phi>))`n = ?x"
  unfolding Exists_def by (simp add: incr_bv_Neg)
(*
schematic_goal incr_bv_And [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(And(\<phi>,\<psi>))`n = ?x"
  unfolding And_def by (simp add: incr_bv_Neg)

schematic_goal incr_bv_Or [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(Or(\<phi>,\<psi>))`n = ?x"
  unfolding Or_def by (simp add: incr_bv_Neg)

schematic_goal incr_bv_Implies [incr_bv_new_simps]:
  "mem(n,\<omega>) \<Longrightarrow> mem(\<phi>,formula) \<Longrightarrow>mem(\<psi>,formula)\<Longrightarrow> incr_bv(Implies(\<phi>,\<psi>))`n = ?x"
  unfolding Implies_def by (simp add: incr_bv_Neg)
*)

\<comment> \<open>The two renamings involved in the definition of \<^term>\<open>forces\<close> depend on
the recursive function \<^term>\<open>incr_bv\<close>. Here we have an apparently
exponential bottleneck, since all the propositional connectives (even \<^term>\<open>Neg\<close>)
duplicate the appearances of \<^term>\<open>incr_bv\<close>.

Not even the double negation of an atomic formula can be managed by the
system (in version 2021-1).\<close>
(* 

schematic_goal "forces(\<not>\<not>0\<in>1) = ?x"
  unfolding forces_def Neg_def
   by (simp add:ren_forces_nand_def ren_forces_forall_def 
      frc_at_fm_def ftype_fm_def
      name1_fm_def name2_fm_def snd_snd_fm_def hcomp_fm_def
      ecloseN_fm_def eclose_n1_fm_def eclose_n2_fm_def
      is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
      is_If_fm_def least_fm_def Collect_fm_def
      fm_definitions incr_bv_Neg incr_bv_Exists)
(* exception Size raised (line 183 of "./basis/LibrarySupport.sml") *)

*)

(*
declare is_ContHyp_fm_def[fm_definitions del]

thm is_ContHyp_fm_def[unfolded is_eclose_fm_def mem_eclose_fm_def eclose_n_fm_def
   is_If_fm_def least_fm_def Replace_fm_def Collect_fm_def
   fm_definitions, simplified] *)

end \<comment> \<open>\<^locale>\<open>Demo\<close>\<close>


end