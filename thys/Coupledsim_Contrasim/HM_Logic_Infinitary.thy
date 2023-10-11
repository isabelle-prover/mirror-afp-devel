section \<open>Infinitary Hennessy--Milner Logic\<close>

theory HM_Logic_Infinitary
  imports 
    Weak_Relations
begin

datatype ('a,'x)HML_formula =
  HML_true 
| HML_conj \<open>'x set\<close> \<open>'x \<Rightarrow> ('a,'x)HML_formula\<close>  (\<open>AND _ _\<close>)
| HML_neg \<open>('a,'x)HML_formula\<close>                  (\<open>~_\<close> [20] 60)
| HML_poss \<open>'a\<close> \<open>('a,'x)HML_formula\<close>            (\<open>\<langle>_\<rangle>_\<close> [60] 60)

\<comment>\<open>The HML formulation is derived from that by Max Pohlmann @{cite pohlmann2021reactivebisim}.\<close>

subsection \<open>Satisfaction Relation\<close>

context lts_tau
begin

function satisfies :: \<open>'s \<Rightarrow> ('a, 's) HML_formula \<Rightarrow> bool\<close> 
  (\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
    \<open>(p \<Turnstile> HML_true) = True\<close> 
  | \<open>(p \<Turnstile> HML_conj I F) = (\<forall> i \<in> I. p \<Turnstile> (F i))\<close> 
  | \<open>(p \<Turnstile> HML_neg \<phi>) = (\<not> p \<Turnstile> \<phi>)\<close>
  | \<open>(p \<Turnstile> HML_poss \<alpha> \<phi>) =
      (\<exists> p'. ((tau \<alpha> \<and> p \<longmapsto>* tau p') \<or> (\<not> tau \<alpha> \<and> p \<longmapsto>\<alpha> p')) \<and> p' \<Turnstile> \<phi>)\<close>
  using HML_formula.exhaust by (auto, blast)

inductive_set HML_wf_rel :: \<open>('s \<times> ('a, 's) HML_formula) rel\<close> 
  where
    \<open>\<phi> = F i \<and> i \<in> I \<Longrightarrow> ((p, \<phi>), (p, HML_conj I F)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p, HML_neg \<phi>)) \<in> HML_wf_rel\<close> 
  | \<open>((p, \<phi>), (p', HML_poss \<alpha> \<phi>)) \<in> HML_wf_rel\<close>

lemma HML_wf_rel_is_wf: \<open>wf HML_wf_rel\<close> 
  unfolding wf_def
proof (safe)
  fix P::\<open>'s \<times> ('a, 's) HML_formula \<Rightarrow> bool\<close> and t::\<open>'s \<times> ('a, 's) HML_formula\<close>
  obtain p \<phi> where \<open>t = (p, \<phi>)\<close> by force
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_wf_rel \<longrightarrow> P y) \<longrightarrow> P x\<close>
  hence \<open>P (p, \<phi>)\<close>
  proof (induct \<phi> arbitrary: p)
    case HML_true
    then show ?case
      by (metis HML_formula.distinct(1,3,5) HML_wf_rel.cases old.prod.exhaust)
  next
    case (HML_conj I F)
    thus ?case
      by (smt (verit) HML_formula.distinct(7,9) HML_formula.inject(1) HML_wf_rel.cases
         case_prodD case_prodE' lts_tau.HML_wf_rel_def mem_Collect_eq range_eqI)
  next
    case (HML_neg \<phi>)
    thus ?case
      by (metis HML_formula.distinct(11,7) HML_formula.inject(2) HML_wf_rel.cases surj_pair)
  next
    case (HML_poss a \<phi>)
    thus ?case
      by (smt (verit, del_insts) HML_formula.distinct(3,5,9,11)  HML_formula.inject(3)
        HML_wf_rel.cases case_prodD case_prodE' HML_wf_rel_def mem_Collect_eq)
  qed
  thus \<open>P t\<close> using \<open>t = (p, \<phi>)\<close> by simp
qed

termination satisfies using HML_wf_rel_is_wf 
  by (standard, (simp add: HML_wf_rel.intros)+)

inductive_set HML_direct_subformulas :: \<open>(('a, 's) HML_formula) rel\<close>
  where
    \<open>\<phi> = F i \<and> i \<in> I \<Longrightarrow> (\<phi>, HML_conj I F) \<in> HML_direct_subformulas\<close> 
  | \<open>(\<phi>, HML_neg \<phi>) \<in> HML_direct_subformulas\<close> 
  | \<open>(\<phi>, HML_poss \<alpha> \<phi>) \<in> HML_direct_subformulas\<close>

lemma HML_direct_subformulas_wf: \<open>wf HML_direct_subformulas\<close> 
  unfolding wf_def
proof (safe)
  fix P x
  assume \<open>\<forall>x. (\<forall>y. (y, x) \<in> HML_direct_subformulas \<longrightarrow> P y) \<longrightarrow> P x\<close>
  thus \<open>P x\<close>
  proof induct
    case HML_true
    then show ?case using HML_direct_subformulas.simps by blast
  next
    case (HML_conj I F)
    then show ?case
      by (metis HML_direct_subformulas.cases HML_formula.distinct(7,9)
          HML_formula.inject(1) range_eqI)
  next
    case (HML_neg \<phi>)
    then show ?case
      by (metis HML_direct_subformulas.simps HML_formula.distinct(11,7) HML_formula.inject(2))
  next
    case (HML_poss a \<phi>)
    then show ?case
      by (metis HML_direct_subformulas.simps HML_formula.distinct(11,9) HML_formula.inject(3))
  qed
qed

definition HML_subformulas where \<open>HML_subformulas \<equiv> (HML_direct_subformulas)\<^sup>+\<close>

lemma HML_subformulas_wf: \<open>wf HML_subformulas\<close>
  using HML_direct_subformulas_wf HML_subformulas_def wf_trancl
  by fastforce

lemma conj_only_depends_on_indexset:
  assumes \<open>\<forall>i\<in>I. f1 i = f2 i\<close>
  shows \<open>(p \<Turnstile> HML_conj I f1) = (p \<Turnstile> HML_conj I f2)\<close>
  using assms by auto

subsection \<open>Distinguishing Formulas\<close>

definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>HML_equivalent p q 
    \<equiv> (\<forall> \<phi>::('a, 's) HML_formula. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

fun distinguishes ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
   \<open>distinguishes \<phi> p q = (p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>)\<close>

fun distinguishes_from_set ::  \<open>('a,'s) HML_formula \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool\<close>
  where
   \<open>distinguishes_from_set \<phi> p Q = (p \<Turnstile> \<phi> \<and> (\<forall>q. q \<in> Q \<longrightarrow> \<not> q \<Turnstile> \<phi>))\<close>

lemma distinguishing_formula:
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists> \<phi>. p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>
  using assms  satisfies.simps(3) unfolding HML_equivalent_def 
  by blast

lemma HML_equivalent_symm:
  assumes \<open>HML_equivalent p q\<close>
  shows \<open>HML_equivalent q p\<close>
  using HML_equivalent_def assms by presburger

subsection \<open>Weak-NOR Hennessy--Milner Logic\<close>

definition HML_weaknor ::
  \<open>'x set \<Rightarrow> ('x \<Rightarrow> ('a,'x)HML_formula) \<Rightarrow> ('a,'x)HML_formula\<close>
  where \<open>HML_weaknor I F = HML_poss \<tau> (HML_conj I (\<lambda>f. HML_neg (F f)))\<close>

definition HML_weaknot ::
  \<open>('a,'x)HML_formula \<Rightarrow> ('a,'x)HML_formula\<close>
  where \<open>HML_weaknot \<phi> = HML_weaknor {undefined} (\<lambda>i. \<phi>)\<close>

inductive_set HML_weak_formulas :: \<open>('a,'x)HML_formula set\<close> where
  Base: \<open>HML_true \<in> HML_weak_formulas\<close> |
  Obs: \<open>\<phi> \<in> HML_weak_formulas \<Longrightarrow> (\<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) \<in> HML_weak_formulas\<close> |
  Conj: \<open>(\<And>i. i \<in> I \<Longrightarrow> F i \<in> HML_weak_formulas) \<Longrightarrow> HML_weaknor I F \<in> HML_weak_formulas\<close>

lemma weak_backwards_truth:
  assumes
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>p \<longmapsto>* tau  p'\<close>
    \<open>p' \<Turnstile> \<phi>\<close>
  shows
    \<open>p \<Turnstile> \<phi>\<close>
  using assms
proof cases
  case Base
  then show ?thesis by force
next
  case (Obs \<phi> a)
  then show ?thesis
    using assms(2,3) satisfies.simps(4) steps_concat tau_tau by blast
next
  case (Conj I F)
  then show ?thesis
    unfolding HML_weaknor_def tau_def
    using tau_tau assms steps_concat
    by force
qed

lemma tau_a_obs_implies_delay_step: 
  assumes \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
  shows \<open>\<exists>p'. p =\<rhd>a p' \<and> p' \<Turnstile> \<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p'' \<and> p'' \<Turnstile> \<langle>a\<rangle>\<phi>\<close> using assms by auto
  thus ?thesis using satisfies.simps(4) steps_concat tau_tau by blast
qed

lemma delay_step_implies_tau_a_obs: 
  assumes 
    \<open>p =\<rhd>a p'\<close>
    \<open>p' \<Turnstile> \<phi>\<close>
  shows \<open>p  \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close>
proof - 
  obtain p'' where \<open>p \<Rightarrow>^\<tau> p''\<close> and \<open>p'' \<Rightarrow>^a p'\<close>
    using assms steps.refl tau_tau by blast
  thus ?thesis
    by (metis assms(1,2) lts_tau.satisfies.simps(4) lts_tau.tau_tau)
qed

end
end