(* 

  A meta-modal logic for bisimulations
  Authors: Alfredo Burrieza, Fernando Soler-Toscano, Antonio Yuste-Ginel

*)

text \<open>This theory introduces a modal logic for reasoning about bisimulations (more details on 
  \<^cite>\<open>"burrieza2025metamodallogicbisimulations"\<close>). The proofs rely on various results concerning 
  maximally consistent sets, drawn from the APF entry \emph{Synthetic Completeness} by 
  Asta Halkjær From \<^cite>\<open>"HalkSyntComp"\<close>.\<close>

theory Bisimulation_Logic 
  imports "Synthetic_Completeness.Derivations" 
begin

section \<open>Syntax\<close>

text \<open>First, the language \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close> is introduced:\<close>

datatype 'p fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>'p fm\<close> \<open>'p fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Box \<open>'p fm\<close> (\<open>\<^bold>\<box> _\<close> [70] 70)
  | FrB \<open>'p fm\<close> (\<open>\<^bold>[b\<^bold>] _\<close> [70] 70)

text \<open>Defined connectives.\<close>

abbreviation Not (\<open>\<^bold>\<not> _\<close> [70] 70) where
  \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
abbreviation Tru (\<open>\<^bold>\<top>\<close>) where 
  \<open>\<^bold>\<top> \<equiv> \<^bold>\<not>\<^bold>\<bottom>\<close>
abbreviation Dis (infixr \<open>\<^bold>\<or>\<close> 60) where
  \<open>A \<^bold>\<or> B \<equiv> \<^bold>\<not>A \<^bold>\<longrightarrow> B\<close>
abbreviation Con (infixr \<open>\<^bold>\<and>\<close> 65) where
  \<open>A \<^bold>\<and> B \<equiv> \<^bold>\<not>(A \<^bold>\<longrightarrow> \<^bold>\<not>B)\<close>
abbreviation Iff (infixr \<open>\<^bold>\<longleftrightarrow>\<close> 55) where
  \<open>A \<^bold>\<longleftrightarrow> B \<equiv> (A \<^bold>\<longrightarrow> B) \<^bold>\<and> (B \<^bold>\<longrightarrow> A)\<close>
abbreviation Dia (\<open>\<^bold>\<diamond> _\<close> [70] 70) where 
  \<open>\<^bold>\<diamond>A \<equiv> \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>A\<close>
abbreviation FrD (\<open>\<^bold>\<langle>b\<^bold>\<rangle> _\<close> [70] 70) where 
  \<open>\<^bold>\<langle>b\<^bold>\<rangle>A \<equiv> \<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>A\<close>

text \<open>Iteration of modal operators \<open>\<^bold>\<box>\<close> and \<open>\<^bold>\<diamond>\<close>.\<close>

primrec chain_b :: \<open>nat \<Rightarrow> 'p fm \<Rightarrow> 'p fm\<close> (\<open>\<^bold>\<box>^_ _\<close> [70, 70] 70) where
  \<open>\<^bold>\<box>^0 f = f\<close>
| \<open>\<^bold>\<box>^(Suc n) f = \<^bold>\<box>(\<^bold>\<box>^n f)\<close>

primrec chain_d :: \<open>nat \<Rightarrow> 'p fm \<Rightarrow> 'p fm\<close> (\<open>\<^bold>\<diamond>^_ _\<close> [70, 70] 70) where
  \<open>\<^bold>\<diamond>^0 f = f\<close>
| \<open>\<^bold>\<diamond>^(Suc n) f = \<^bold>\<diamond>(\<^bold>\<diamond>^n f)\<close>

lemma chain_bd_sum:
  \<open>\<^bold>\<box>^n (\<^bold>\<box>^m F) = \<^bold>\<box>^(n+m) F\<close> and 
  \<open>\<^bold>\<diamond>^n (\<^bold>\<diamond>^m F) = \<^bold>\<diamond>^(n+m) F\<close>
  by (induct n) simp_all

section \<open>Semantics\<close>

text \<open>This is the type of both left and right models:\<close>

datatype ('p, 'w) model =
  Model (W: \<open>'w set\<close>) (R: \<open>('w \<times> 'w) set\<close>) (V: \<open>'w \<Rightarrow> 'p \<Rightarrow> bool\<close>)

text \<open>Given a model \<open>\<M>\<close> \<open>W \<M>\<close> denotes its set of worlds, \<open>R \<M>\<close> the accessibility relation and 
\<open>V \<M>\<close> the valuation function.\<close>

text \<open>This is the type of a model in \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>:\<close>

datatype ('p, 'w) modelLb =
  ModelLb (M1: \<open>('p, 'w) model\<close>) (M2: \<open>('p, 'w) model\<close>) (Z : \<open>('w \<times> 'w) set\<close>) 

text \<open>Given a model \<open>\<MM>\<close> of \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>, \<open>M1 \<MM>\<close> denotes the model on the left, \<open>M2 \<MM>\<close> the model on 
the right and \<open>Z \<MM>\<close> the bisimulation relation.\<close>

text \<open>Bi-models are a relevant class of \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>, as we will prove soundness and completeness of 
  the proof system \<open>\<turnstile>\<^sub>B\<close> for bi-models. First, the conditions for \<open>\<MM>\<close> to be a \<open>bi-model\<close> are 
introduced.\<close>

definition bi_model :: \<open>('p, 'w) modelLb \<Rightarrow> bool\<close> where
  \<open>bi_model \<MM>  \<equiv>
    \<comment> \<open>\<open>M1\<close> and \<open>M2\<close> have non-empty domains\<close>
    W (M1 \<MM>) \<noteq> {} \<and> W (M2 \<MM>) \<noteq> {} \<and> 
    \<comment> \<open>\<open>R1\<close> and \<open>R2\<close> are defined in the corresponding domains\<close>
    R (M1 \<MM>) \<subseteq> (W (M1 \<MM>)) \<times> (W (M1 \<MM>)) \<and>
    R (M2 \<MM>) \<subseteq> (W (M2 \<MM>)) \<times> (W (M2 \<MM>)) \<and>
    \<comment> \<open>\<open>Z\<close> is a non-empty relation from \<open>W (M1 \<MM>)\<close> to \<open>W (M2 \<MM>)\<close> \<close>
    Z \<MM> \<noteq> {} \<and> Z \<MM> \<subseteq> (W (M1 \<MM>)) \<times> (W (M2 \<MM>)) \<and>
    \<comment> \<open>Atomic harmony\<close>
    (\<forall> w w' . (w, w') \<in> Z \<MM> \<longrightarrow> ((V (M1 \<MM>)) w) = ((V (M2 \<MM>)) w')) \<and>
    \<comment> \<open>Forth\<close>
    (\<forall> w w' v . (w, w') \<in> Z \<MM> \<and> (w,v) \<in> R (M1 \<MM>) \<longrightarrow> 
        (\<exists> v' . (v,v') \<in> Z \<MM> \<and> (w', v') \<in> R (M2 \<MM>))) \<and>
    \<comment> \<open>Back\<close>
    (\<forall> w w' v' . (w, w') \<in> Z \<MM> \<and> (w',v') \<in> R (M2 \<MM>) \<longrightarrow> (\<exists> v . (v,v') \<in> Z \<MM> \<and> (w,v) \<in> R (M1 \<MM>)))\<close>

text \<open>In the semantics, formulas are evaluated differently depending on the pointed world is on the
  left (\<open>\<M>\<close>) or on the right (\<open>\<M>'\<close>). Datatype \<open>ep\<close> (evaluation point) indicates the side of a 
  model in which a given formula is evaluated.\<close>

datatype ep = \<m> | \<m>'

\<comment> \<open>Pointed model \<open>(\<M>,w)\<close>.\<close>
type_synonym ('p, 'w) Mctx  = \<open>('p, 'w) model  \<times> 'w\<close>

\<comment> \<open>Pointed \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>-modelLb \<open>(\<MM>,\<M>\<^sup>('\<^sup>),w)\<close>.\<close>
type_synonym ('p, 'w) MLbCtx = \<open>('p, 'w) modelLb \<times> ep \<times> 'w\<close>

text \<open>Definition of truth in a pointed \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>-modelLb.\<close>

fun semantics :: \<open>('p, 'w) MLbCtx \<Rightarrow> 'p fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>B\<close> 50) where
  \<open>_ \<Turnstile>\<^sub>B( \<^bold>\<bottom>::('p fm)) \<longleftrightarrow> False\<close>
| \<open>(\<MM>, \<m>, w)  \<Turnstile>\<^sub>B \<^bold>\<cdot>P \<longleftrightarrow> V (M1 \<MM>) w P\<close>
| \<open>(\<MM>, \<m>', w) \<Turnstile>\<^sub>B \<^bold>\<cdot>P \<longleftrightarrow> V (M2 \<MM>) w P\<close>
| \<open>(\<MM>, e, w) \<Turnstile>\<^sub>B A \<^bold>\<longrightarrow> B \<longleftrightarrow> (\<MM>, e, w) \<Turnstile>\<^sub>B A \<longrightarrow> (\<MM>, e, w) \<Turnstile>\<^sub>B B\<close>
| \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>\<box>A \<longleftrightarrow> (\<forall> v \<in> W (M1 \<MM>) . (w,v) \<in> R (M1 \<MM>) \<longrightarrow> (\<MM>, \<m>, v) \<Turnstile>\<^sub>B A)\<close>
| \<open>(\<MM>, \<m>', w) \<Turnstile>\<^sub>B \<^bold>\<box>A \<longleftrightarrow> (\<forall> v \<in> W (M2 \<MM>) . (w,v) \<in> R (M2 \<MM>) \<longrightarrow> (\<MM>, \<m>', v) \<Turnstile>\<^sub>B A)\<close>
| \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>[b\<^bold>]A \<longleftrightarrow> (\<forall> w' \<in> W (M2 \<MM>) . (w,w') \<in> (Z \<MM>) \<longrightarrow> (\<MM>, \<m>', w') \<Turnstile>\<^sub>B A)\<close>
| \<open>(\<MM>, \<m>', w) \<Turnstile>\<^sub>B \<^bold>[b\<^bold>]A \<longleftrightarrow> True\<close>

section \<open>Calculus\<close>

text \<open>Function \<open>eval\<close> and \<open>tautology\<close> define what is a propositional tautology.\<close>

primrec eval :: \<open>('p \<Rightarrow> bool) \<Rightarrow> ('p fm \<Rightarrow> bool) \<Rightarrow> 'p fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (\<^bold>\<cdot>P) = g P\<close>
| \<open>eval g h (A \<^bold>\<longrightarrow> B) = (eval g h A \<longrightarrow> eval g h B)\<close>
| \<open>eval _ h (\<^bold>\<box>A) = h (\<^bold>\<box>A)\<close>
| \<open>eval _ h (\<^bold>[b\<^bold>]A) = h (\<^bold>[b\<^bold>]A)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

\<comment> \<open>Example of propositional tautology\<close>
lemma \<open>tautology (\<^bold>[b\<^bold>]A \<^bold>\<or> \<^bold>\<not>\<^bold>[b\<^bold>]A)\<close> by simp

text \<open>Finally, the axiom system \<open>\<turnstile>\<^sub>B\<close> is presented.\<close>

inductive Calculus :: \<open>'p fm \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>B _\<close> [50] 50) where
  TAU:   \<open>tautology A \<Longrightarrow> \<turnstile>\<^sub>B A\<close>
| KSq:   \<open>\<turnstile>\<^sub>B \<^bold>\<box> (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>\<box>A \<^bold>\<longrightarrow> \<^bold>\<box>B)\<close>
| Kb:    \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>[b\<^bold>]A \<^bold>\<longrightarrow>\<^bold>[b\<^bold>]B)\<close>
| FORTH: \<open>\<turnstile>\<^sub>B (\<^bold>\<langle>b\<^bold>\<rangle>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]B) \<^bold>\<longrightarrow> \<^bold>\<langle>b\<^bold>\<rangle>(A \<^bold>\<and> \<^bold>\<diamond>B)\<close>    
| BACK:  \<open>\<turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<diamond>A \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>\<langle>b\<^bold>\<rangle>A\<close>                    
| HARM:  \<open>(l = \<^bold>\<cdot>p \<or> l = \<^bold>\<not>\<^bold>\<cdot>p) \<Longrightarrow> \<turnstile>\<^sub>B l \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]l\<close>
| NTS:   \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>[b\<^bold>]\<^bold>\<bottom>\<close>                            
| MP:    \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> B \<Longrightarrow> \<turnstile>\<^sub>B A \<Longrightarrow> \<turnstile>\<^sub>B B\<close>
| NSq:   \<open>\<turnstile>\<^sub>B A \<Longrightarrow> \<turnstile>\<^sub>B \<^bold>\<box>A\<close>
| Nb:    \<open>\<turnstile>\<^sub>B A \<Longrightarrow> \<turnstile>\<^sub>B \<^bold>[b\<^bold>]A\<close>

text \<open>Proofs use nested conditionals. Given a list \<open>A = [A\<^sub>1, ..., A\<^sub>n]\<close> of formulas, 
\<open>A \<^bold>\<leadsto> B\<close> represents \<open>A\<^sub>1 \<longrightarrow> (A\<^sub>2 \<longrightarrow> ... (A\<^sub>n \<longrightarrow> B))\<close>.\<close> 

primrec imply :: \<open>'p fm list \<Rightarrow> 'p fm \<Rightarrow> 'p fm\<close> (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> B) = B\<close>
| \<open>(A # \<Lambda> \<^bold>\<leadsto> B) = (A \<^bold>\<longrightarrow> \<Lambda> \<^bold>\<leadsto> B)\<close>

abbreviation Calculus_assms (infix \<open>\<turnstile>\<^sub>B\<close> 50) where
  \<open>\<Lambda> \<turnstile>\<^sub>B A \<equiv> \<turnstile>\<^sub>B \<Lambda> \<^bold>\<leadsto> A\<close>

section \<open>Soundness\<close>

text \<open>These lemmas will be used to prove soundness.\<close>

lemma atomic_harm:
  assumes \<open>bi_model \<MM>\<close>
  and "(w,w')\<in> Z \<MM>"
shows "((V (M1 \<MM>)) w p) = ((V (M2 \<MM>)) w' p)" using assms bi_model_def by metis

lemma eval_semantics: 
  assumes \<open>bi_model \<MM>\<close>
  shows \<open>eval (V (M1 \<MM>) w) (\<lambda>q. (\<MM>, \<m>, w) \<Turnstile>\<^sub>B q) p = ((\<MM>, \<m>, w) \<Turnstile>\<^sub>B p)\<close> and
        \<open>eval (V (M2 \<MM>) w) (\<lambda>q. (\<MM>, \<m>', w) \<Turnstile>\<^sub>B q) p = ((\<MM>, \<m>', w) \<Turnstile>\<^sub>B p)\<close>
  by (induct p) simp_all

text \<open>Tautologies are always true.\<close>

lemma tautology:
  assumes \<open>tautology A\<close> 
    and \<open>bi_model \<MM>\<close>
  shows \<open>(\<MM>, e, w) \<Turnstile>\<^sub>B A\<close> 
  by (metis (full_types) assms(1,2) ep.exhaust eval_semantics(1,2))

text \<open>Axiom FORTH is valid in all worlds in \<open>\<M>\<close> of bi-models.\<close>

lemma b_forth:
  assumes \<open>bi_model \<MM>\<close> and
  \<open>w \<in> W (M1 \<MM>)\<close>
  shows 
    \<open>(\<MM>, \<m>, w)  \<Turnstile>\<^sub>B (\<^bold>\<langle>b\<^bold>\<rangle>F \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]G) \<^bold>\<longrightarrow> \<^bold>\<langle>b\<^bold>\<rangle>(F \<^bold>\<and> \<^bold>\<diamond>G)\<close> 
proof -
  {assume A: \<open>(\<MM>, \<m>, w)  \<Turnstile>\<^sub>B (\<^bold>\<langle>b\<^bold>\<rangle>F \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]G)\<close>
    then obtain w' where w': 
     \<open>w' \<in> W (M2 \<MM>) \<and> (w,w') \<in> Z \<MM> \<and> ((\<MM>, \<m>', w')  \<Turnstile>\<^sub>B F)\<close>
      by fastforce
    obtain w2 where w2: \<open>w2 \<in> W (M1 \<MM>) \<and> (w, w2) \<in> R (M1 \<MM>) \<and> 
      (\<MM>, \<m>, w2)  \<Turnstile>\<^sub>B \<^bold>[b\<^bold>]G\<close> using A assms by auto
    then obtain w2' where w2': \<open>w2' \<in> W (M2 \<MM>) \<and> (w', w2') \<in> R (M2 \<MM>) \<and> 
      (w2, w2') \<in> Z \<MM>\<close> using bi_model_def assms w' 
      by (smt (verit, ccfv_SIG) SigmaD2 in_mono)  
    hence \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>(F \<^bold>\<and> \<^bold>\<diamond>G)\<close> using assms w' w2 by auto}
  thus ?thesis by auto
qed

text \<open>Axiom FORTH is valid in all worlds on \<open>\<M>'\<close> (bi-models).\<close>

lemma b_forth2:
  assumes \<open>bi_model \<MM>\<close> and
  \<open>w \<in> W (M2 \<MM>)\<close>
  shows 
    \<open>(\<MM>, \<m>', w)  \<Turnstile>\<^sub>B (\<^bold>\<langle>b\<^bold>\<rangle>F \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]G) \<^bold>\<longrightarrow> \<^bold>\<langle>b\<^bold>\<rangle>(F \<^bold>\<and> \<^bold>\<diamond>G)\<close> 
  by simp

text \<open>Axiom BACK is valid in all worlds on \<open>\<M>\<close> (bi-models).\<close>

lemma b_back:
  assumes \<open>bi_model \<MM>\<close> and
  \<open>w \<in> W (M1 \<MM>)\<close>
  shows 
    \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<diamond>F \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>\<langle>b\<^bold>\<rangle>F\<close> 
proof -
  {assume \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<diamond>F\<close>
    then obtain w' where w': \<open>w' \<in> W (M2 \<MM>) \<and> 
      (w,w') \<in> Z \<MM> \<and> (\<MM>, \<m>', w')  \<Turnstile>\<^sub>B \<^bold>\<diamond>F\<close> by auto
    then obtain w2' where w2': \<open>w' \<in> W (M2 \<MM>) \<and> 
      (w',w2') \<in> R (M2 \<MM>) \<and> (\<MM>, \<m>', w2')  \<Turnstile>\<^sub>B F\<close> by auto
    then obtain w2 where w2: \<open>w2 \<in> W (M1 \<MM>) \<and> (w,w2) \<in> R (M1 \<MM>) \<and> 
      (w2,w2') \<in> Z \<MM>\<close> using assms bi_model_def w' w2' 
      by (smt (verit, best) SigmaD2 bi_model_def in_mono)
    hence \<open>(\<MM>, \<m>, w2) \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>F\<close> using assms w2' w2 
      by (metis (no_types, lifting) SigmaD2 bi_model_def in_mono
          semantics.simps(1,4,7))
    hence \<open>(\<MM>, \<m>, w) \<Turnstile>\<^sub>B \<^bold>\<diamond>\<^bold>\<langle>b\<^bold>\<rangle>F\<close> using w2 assms by auto
  } 
  thus ?thesis by simp
qed

text \<open>Axiom BACK is valid in all worlds on \<open>\<M>'\<close> (bi-models).\<close>

lemma b_back2:
  assumes \<open>bi_model \<MM>\<close> and
  \<open>w \<in> W (M2 \<MM>)\<close>
  shows 
    \<open>(\<MM>, \<m>', w)  \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<diamond>F \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>\<langle>b\<^bold>\<rangle>F\<close> by simp

text \<open>Soundness theorem\<close>

theorem soundness: 
  \<open> \<turnstile>\<^sub>B A \<Longrightarrow> bi_model \<MM> \<Longrightarrow> 
    (w \<in> W (M1 \<MM>) \<longrightarrow> (\<MM>, \<m>, w) \<Turnstile>\<^sub>B A) \<and> 
    (w \<in> W (M2 \<MM>) \<longrightarrow> (\<MM>, \<m>', w) \<Turnstile>\<^sub>B A)\<close> 
proof (induct A arbitrary: w rule: Calculus.induct)
  case (TAU F)
  then show ?case 
    by (simp add: tautology)
next
  case (FORTH F G)
  then show ?case by (metis b_forth2 b_forth)
next
  case (BACK F)
  then show ?case by (metis b_back b_back2)
next
  case (HARM l)
  then show ?case using atomic_harm by fastforce
qed auto

section \<open>Admissible rules\<close>

text \<open>These lemmas are mostly from the AFP entry ``Synthetic Completeness'' by Asta Halkjær From.\<close>

lemma K_imply_head: \<open>p # A \<turnstile>\<^sub>B p\<close>
proof -
  have \<open>tautology (p # A \<^bold>\<leadsto> p)\<close>
    by (induct A) simp_all
  then show ?thesis using TAU by blast
qed

lemma K_imply_Cons:
  assumes \<open>A \<turnstile>\<^sub>B q\<close>
  shows \<open>p # A \<turnstile>\<^sub>B q\<close>
  using assms 
  by (metis K_imply_head MP imply.simps(1,2))

lemma K_right_mp:
  assumes \<open>A \<turnstile>\<^sub>B p\<close> \<open>A \<turnstile>\<^sub>B p \<^bold>\<longrightarrow> q\<close>
  shows \<open>A \<turnstile>\<^sub>B q\<close>
proof -
  have \<open>tautology (A \<^bold>\<leadsto> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> A \<^bold>\<leadsto> q)\<close>
    by (induct A) simp_all
  with TAU have \<open>\<turnstile>\<^sub>B A \<^bold>\<leadsto> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> A \<^bold>\<leadsto> q\<close> .
  then show ?thesis
    using assms MP by blast
qed

lemma deduct1: \<open>A \<turnstile>\<^sub>B p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile>\<^sub>B q\<close>
  by (meson K_right_mp K_imply_Cons K_imply_head)

lemma imply_append [iff]: \<open>(A @ B \<^bold>\<leadsto> r) = (A \<^bold>\<leadsto> B \<^bold>\<leadsto> r)\<close>
  by (induct A) simp_all

lemma imply_swap_append: \<open>A @ B \<turnstile>\<^sub>B r \<Longrightarrow> B @ A \<turnstile>\<^sub>B r\<close>
proof (induct B arbitrary: A)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma K_ImpI: \<open>p # A \<turnstile>\<^sub>B q \<Longrightarrow> A \<turnstile>\<^sub>B p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemma imply_mem [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>B p\<close>
  using K_imply_head K_imply_Cons by (induct A) fastforce+

lemma add_imply [simp]: \<open>\<turnstile>\<^sub>B q \<Longrightarrow> A \<turnstile>\<^sub>B q\<close>
  using K_imply_head MP by auto

lemma K_imply_weaken: \<open>A \<turnstile>\<^sub>B q \<Longrightarrow> set A \<subseteq> set A' \<Longrightarrow> A' \<turnstile>\<^sub>B q\<close>
  by (induct A arbitrary: q) (simp, metis K_right_mp K_ImpI 
      imply_mem insert_subset list.set(2))

lemma K_Boole:
  assumes \<open>(\<^bold>\<not> p) # A \<turnstile>\<^sub>B \<^bold>\<bottom>\<close>
  shows \<open>A \<turnstile>\<^sub>B p\<close>
proof -
  have T: \<open>tautology ((\<^bold>\<not> p \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow>  \<^bold>\<not>\<^bold>\<not>p)\<close> 
    by simp
  have \<open>A \<turnstile>\<^sub>B \<^bold>\<not> \<^bold>\<not> p\<close>
    using assms K_ImpI T 
    using TAU K_right_mp add_imply by blast 
  moreover have \<open>tautology (A \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> p)\<close>
    by (induct A) simp_all
  then have \<open>\<turnstile>\<^sub>B (A \<^bold>\<leadsto> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> A \<^bold>\<leadsto> p)\<close>
    using TAU by blast
  ultimately show ?thesis
    using MP by blast
qed

lemma MP_chain:
  assumes \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> B\<close>
  and \<open>\<turnstile>\<^sub>B B \<^bold>\<longrightarrow> C\<close>
shows \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> C\<close> 
proof -
  have \<open>\<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (( B \<^bold>\<longrightarrow> C) \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> C))\<close> using TAU by force
  thus ?thesis using assms MP by auto
qed

text \<open>This locale is use to prove common results of normal modal operators. As both \<open>\<^bold>\<box>\<close> and \<open>\<^bold>[b\<^bold>]\<close> 
  are normal, result involving \<open>\<^bold>K\<close> in \<open>Kop\<close> will be applied to them.\<close>

locale Kop =
  fixes K :: "'p fm \<Rightarrow> 'p fm"  (\<open>\<^bold>K _\<close> [70] 70)
  assumes Kax: "\<turnstile>\<^sub>B \<^bold>K (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>K A \<^bold>\<longrightarrow> \<^bold>K B)"
    and KN:  "\<turnstile>\<^sub>B A \<Longrightarrow> \<turnstile>\<^sub>B \<^bold>K A"

context Kop begin

abbreviation P (\<open>\<^bold>P _\<close> [70] 70) where \<open>\<^bold>P A \<equiv> \<^bold>\<not>\<^bold>K\<^bold>\<not>A\<close>

lemma K_distrib_K_imp:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>K (A \<^bold>\<leadsto> q)\<close>
  shows \<open>map (\<lambda> x . \<^bold>K x) A \<turnstile>\<^sub>B \<^bold>K q\<close>
proof -
  have \<open>\<turnstile>\<^sub>B \<^bold>K (A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map  (\<lambda> x . \<^bold>K x) A \<^bold>\<leadsto> \<^bold>K q\<close>
  proof (induct A)
    case Nil
    then show ?case
      by (simp add: TAU)
  next
    case (Cons a A)
    have \<open>\<turnstile>\<^sub>B \<^bold>K (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>K a \<^bold>\<longrightarrow> \<^bold>K (A \<^bold>\<leadsto> q)\<close>
      by (simp add: Kax)
    moreover have
      \<open>\<turnstile>\<^sub>B ((\<^bold>K (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>K a \<^bold>\<longrightarrow> \<^bold>K (A \<^bold>\<leadsto> q)) \<^bold>\<longrightarrow>
        (\<^bold>K (A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> map  (\<lambda> x . \<^bold>K x) A \<^bold>\<leadsto> \<^bold>K q) \<^bold>\<longrightarrow>
        (\<^bold>K (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>K a \<^bold>\<longrightarrow> map  (\<lambda> x . \<^bold>K x) A \<^bold>\<leadsto> \<^bold>K q))\<close>
      using TAU by force
    ultimately have \<open>\<turnstile>\<^sub>B \<^bold>K (a # A \<^bold>\<leadsto> q) \<^bold>\<longrightarrow> \<^bold>K a \<^bold>\<longrightarrow> map  (\<lambda> x . \<^bold>K x) A \<^bold>\<leadsto> \<^bold>K  q\<close>
      using Cons MP by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms MP by blast
qed

lemma Kpos:
  shows \<open>\<turnstile>\<^sub>B \<^bold>K(A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>PA \<^bold>\<longrightarrow> \<^bold>PB)\<close>
proof-
  have \<open>\<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>\<not>A)\<close> using TAU by force
  hence 1: \<open>\<turnstile>\<^sub>B \<^bold>K(A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>K\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>A)\<close> 
   by (meson KN Kax MP MP_chain)
  have \<open>\<turnstile>\<^sub>B  (\<^bold>K\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>A) \<^bold>\<longrightarrow> (\<^bold>PA \<^bold>\<longrightarrow> \<^bold>PB)\<close> using TAU by force
  thus ?thesis using 1 MP_chain by blast
qed

end

text \<open>Both \<open>\<^bold>\<box>\<close> and \<open>\<^bold>[b\<^bold>]\<close> are normal modal operators.\<close>

interpretation KBox: Kop "\<lambda> A . \<^bold>\<box> A" 
  by (simp add: KSq Kop_def NSq)

interpretation KFrB: Kop "\<lambda> A . \<^bold>[b\<^bold>] A"
  by (simp add: Kb Kop.intro Nb)

text \<open>Some other useful theorems of \<open>\<turnstile>\<^sub>B\<close> that are used in later proofs.\<close>

text \<open>First, the box-version of BACK axiom.\<close>

lemma BACK_rev:
  \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>[b\<^bold>]F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<box>F\<close>  
proof -
  have A: \<open> \<turnstile>\<^sub>B (\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F)\<close> using BACK .
  have \<open> \<turnstile>\<^sub>B (\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F) \<^bold>\<longrightarrow> ( \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F)\<close> 
    using TAU MP by force
  hence f1: \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F\<close> using A MP by auto
  have \<open>\<turnstile>\<^sub>B  \<^bold>\<box>(\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F)\<close> using TAU NSq by force
  hence f2: \<open>\<turnstile>\<^sub>B  \<^bold>\<box>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F\<close> using KSq MP by auto
  have \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>](F \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<not>F)\<close> using TAU Nb by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<box>(\<^bold>[b\<^bold>]F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F)\<close> using Kb NSq MP by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>[b\<^bold>]F \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>F\<close> using KSq MP by auto
  hence f3: \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>[b\<^bold>]F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F\<close> using f1 f2 MP_chain by blast
  have \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>](\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F)\<close> using TAU Nb by force
  hence f4: \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F\<close> using Kb MP by auto
  have \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>\<box>(\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> F)\<close> using  TAU Nb NSq by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>\<box>\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<box>F\<close> using KSq Kb MP Nb by metis
  thus ?thesis using f3 f4 MP_chain by blast
qed

\<comment> \<open>Generalization of axiom NTS.\<close>
lemma NTSgen:
  \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>] \<^bold>\<box>^n \<^bold>[b\<^bold>]\<^bold>\<bottom>\<close> 
proof (induct n)
  case 0
  then show ?case using NTS chain_b_def by simp
next
  case (Suc n)
  fix n
  assume \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>] \<^bold>\<box>^n \<^bold>[b\<^bold>] (\<^bold>\<bottom>::'p fm)\<close>
  hence \<open>\<turnstile>\<^sub>B  \<^bold>\<box> \<^bold>[b\<^bold>] \<^bold>\<box>^n \<^bold>[b\<^bold>] (\<^bold>\<bottom>::'p fm)\<close> using NSq by auto
  thus \<open>\<turnstile>\<^sub>B  \<^bold>[b\<^bold>] \<^bold>\<box>^(Suc n) \<^bold>[b\<^bold>] (\<^bold>\<bottom>::'p fm)\<close> using BACK_rev MP by auto
qed


section \<open>Maximal Consistent Sets\<close>

text \<open>These definitions and lemmas are mostly from the AFP entry ``Synthetic Completeness'' by 
  Asta Halkjær From.\<close>

\<comment> \<open>Definition of consistency and several useful lemmas\<close>
definition consistent :: \<open>'p fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<forall>A. set A \<subseteq> S \<longrightarrow> \<not> A \<turnstile>\<^sub>B \<^bold>\<bottom>\<close>

interpretation MCS_No_Witness_UNIV consistent
proof
  show \<open>infinite (UNIV :: 'p fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed (auto simp: consistent_def)

interpretation Derivations_Cut_MCS consistent Calculus_assms
proof
  fix A B and p :: \<open>'p fm\<close>
  assume \<open>\<turnstile>\<^sub>B A \<^bold>\<leadsto> p\<close> \<open>set A = set B\<close>
  then show \<open>\<turnstile>\<^sub>B B \<^bold>\<leadsto> p\<close>
    using K_imply_weaken by blast
next
  fix S :: \<open>'p fm set\<close>
  show \<open>consistent S = (\<forall>A. set A \<subseteq> S \<longrightarrow> (\<exists>q. \<not> A \<turnstile>\<^sub>B q))\<close>
    unfolding consistent_def using K_Boole K_imply_Cons by blast
next
  fix A B and p q :: \<open>'p fm\<close>
  assume \<open>A \<turnstile>\<^sub>B p\<close> \<open>p # B \<turnstile>\<^sub>B q\<close>
  then show \<open>A @ B \<turnstile>\<^sub>B q\<close>
    by (metis K_right_mp add_imply imply.simps(2) imply_append)
qed simp

interpretation Derivations_Bot consistent Calculus_assms \<open>\<^bold>\<bottom>\<close>
proof
  show \<open>\<And>A r. A \<turnstile>\<^sub>B \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>B r\<close>
    using K_Boole K_imply_Cons by blast
qed

interpretation Derivations_Imp consistent Calculus_assms \<open>\<lambda>p q. p \<^bold>\<longrightarrow> q\<close>
proof
  show \<open>\<And>A p q. p # A \<turnstile>\<^sub>B q \<Longrightarrow> A \<turnstile>\<^sub>B p \<^bold>\<longrightarrow> q\<close>
    using K_ImpI by blast
  show \<open>\<And>A p q. A \<turnstile>\<^sub>B p \<Longrightarrow> A \<turnstile>\<^sub>B p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>B q\<close>
    using K_right_mp by blast
qed

theorem deriv_in_maximal:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>\<turnstile>\<^sub>B p\<close>
  shows \<open>p \<in> S\<close>
  using assms MCS_derive by fastforce

lemma dia_not_box_bot:
  assumes \<open>consistent S\<close> \<open>maximal S\<close> \<open>\<^bold>\<langle>b\<^bold>\<rangle> F \<in> S\<close>
  shows \<open>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> S\<close> 
proof -
  have \<open>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>F \<in> S\<close> using assms(3) by simp
  have \<open>\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<not>F \<in> S\<close> by (simp add: MCS_impI assms(1,2))
  hence \<open>\<^bold>[b\<^bold>](\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<not>F) \<in> S\<close> using Calculus.Nb 
    by (metis K_imply_head assms(1,2) deriv_in_maximal imply.simps(1,2))
  hence \<open>\<^bold>[b\<^bold>]\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>F \<in> S\<close>
    by (meson Kb MCS_imp assms(1,2) deriv_in_maximal)
  thus \<open>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> S\<close> using \<open>\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>F \<in> S\<close>
    by (simp add: MCS_imp assms(1,2))
qed

text \<open>Some other useful lemmas that are repeatedly used in proofs.\<close>

lemma not_empty:
  assumes \<open>a \<in> A\<close>
  shows \<open>A \<noteq> {}\<close> 
  using assms by auto

lemma MPcons:
  assumes \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> (B \<^bold>\<longrightarrow> C)\<close>
  and \<open>\<turnstile>\<^sub>B B\<close>
shows \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> C\<close> 
  by (metis K_right_mp add_imply assms(1,2) imply.simps(1,2))

lemma multiple_MP_MCS:
  assumes \<open>MCS S\<close>
  and \<open>set A \<subseteq> S\<close>
  and \<open>A \<^bold>\<leadsto> f \<in> S\<close>
shows \<open>f \<in> S\<close> using assms by (induct A) auto

lemma not_imp_to_conj:
  assumes \<open>MCS A\<close>
  and \<open>\<^bold>\<not>(B \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> A\<close>
shows \<open>set B \<subseteq> A\<close> 
proof (rule ccontr)
  assume \<open>\<not> set B \<subseteq> A\<close>
  then obtain f where f: \<open>f \<in> set B \<and> f \<notin> A\<close> by auto
  hence \<open>(B \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> A\<close> 
    by (smt (verit, ccfv_SIG) MCS_derive MCS_explode assms(1) derive_assm 
        derive_cut imply_append imply_swap_append)
  thus False using assms(2) 
    using MCS_bot assms(1) by blast
qed

text \<open>Several lemmas of \<open>Kop\<close>, valid for normal modal operators.\<close>

context Kop begin

lemma not_pos_to_nec_not:
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>PF \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>F\<close> 
proof -
  have P1: \<open>\<turnstile>\<^sub>B ((\<^bold>PF \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>F) \<^bold>\<longrightarrow> (\<^bold>\<not>\<^bold>PF \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>F))\<close> using TAU by force
  have \<open>\<turnstile>\<^sub>B \<^bold>PF \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>F\<close> using TAU by force
  thus ?thesis using P1 MP by auto
qed

lemma not_pos_to_nec_not_deriv:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>\<not>F \<^bold>\<longrightarrow> G\<close>
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>PF \<^bold>\<longrightarrow> \<^bold>KG\<close>
  by (metis KN K_imply_Cons K_right_mp Kax assms 
      imply.simps(1,2) not_pos_to_nec_not)

lemma pos_not_to_not_nec:
  shows \<open>\<turnstile>\<^sub>B \<^bold>P\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>KF\<close>
proof -
  have P1: \<open>\<turnstile>\<^sub>B \<^bold>P\<^bold>\<not>F \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>\<^bold>\<not>F\<close> using TAU by force
  have \<open>\<turnstile>\<^sub>B \<^bold>K(F \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<not>F)\<close> using TAU KN by force
  hence P2: \<open>\<turnstile>\<^sub>B \<^bold>KF \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>\<^bold>\<not>F\<close> using Kax MP by auto
  have \<open>\<turnstile>\<^sub>B (\<^bold>P\<^bold>\<not>F \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>\<^bold>\<not>F) \<^bold>\<longrightarrow> (\<^bold>KF \<^bold>\<longrightarrow> \<^bold>K\<^bold>\<not>\<^bold>\<not>F) \<^bold>\<longrightarrow> (\<^bold>P\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>KF)\<close> 
    using TAU by force
  thus ?thesis using P1 P2 MP by auto
qed

lemma not_nec_to_pos_not:
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>KF \<^bold>\<longrightarrow> \<^bold>P\<^bold>\<not>F\<close>
proof -
  have P1: \<open>\<turnstile>\<^sub>B \<^bold>P\<^bold>\<not>F \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>\<^bold>\<not>F\<close> using TAU by force
  have \<open>\<turnstile>\<^sub>B \<^bold>K(\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> F)\<close> using TAU KN by force
  hence P2: \<open>\<turnstile>\<^sub>B \<^bold>K\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>KF\<close> using Kax MP by auto
  have \<open>\<turnstile>\<^sub>B (\<^bold>P\<^bold>\<not>F \<^bold>\<longleftrightarrow> \<^bold>\<not>\<^bold>K\<^bold>\<not>\<^bold>\<not>F) \<^bold>\<longrightarrow> (\<^bold>K\<^bold>\<not>\<^bold>\<not>F \<^bold>\<longrightarrow> \<^bold>KF) \<^bold>\<longrightarrow> (\<^bold>\<not>\<^bold>KF \<^bold>\<longrightarrow> \<^bold>P\<^bold>\<not>F)\<close> 
    using TAU by force
  thus ?thesis using P1 P2 MP by auto
qed

lemma pos_not_to_not_nec_MCS:
  assumes \<open>MCS A\<close>
    and \<open>\<^bold>P\<^bold>\<not>F \<in> A\<close> 
  shows \<open>\<^bold>\<not>\<^bold>KF \<in>  A\<close> using pos_not_to_not_nec 
    by (meson MCS_imp assms(1,2) deriv_in_maximal)

lemma pos_subset:
  assumes \<open>MCS A\<close> and \<open>MCS B\<close>
  shows \<open>{ F | F . \<^bold>K F \<in> A} \<subseteq> B \<longleftrightarrow> {\<^bold>PF | F . F \<in> B} \<subseteq> A\<close> 
proof
  assume As: \<open>{ F | F . \<^bold>K F \<in> A} \<subseteq> B\<close>
  show \<open>{\<^bold>PF | F . F \<in> B} \<subseteq> A\<close>
  proof
    fix F
    assume \<open>F \<in> {\<^bold>P F |F. F \<in> B}\<close>
    then obtain G where P: \<open>F = \<^bold>PG \<and> G\<in>B\<close> by auto
    show \<open>F \<in> A\<close>
    proof (rule ccontr)
      assume \<open>F \<notin> A\<close>
      hence \<open>\<^bold>K\<^bold>\<not>G \<in> A\<close> using assms(1) P \<open>F \<notin> A\<close> 
        by (metis (no_types, opaque_lifting) MCS_impI)
      thus False using As P assms(2) MCS_bot by blast
    qed
  qed
next
  assume As: \<open>{\<^bold>PF | F . F \<in> B} \<subseteq> A\<close>
  show \<open>{ F | F . \<^bold>K F \<in> A} \<subseteq> B\<close>
  proof
    fix F
    assume \<open>F \<in> { F | F . \<^bold>K F \<in> A}\<close>
    hence \<open>\<^bold>K F \<in> A\<close> by simp
    show \<open>F \<in> B\<close>
    proof (rule ccontr)
      assume \<open>F \<notin> B\<close>
      hence \<open>\<^bold>\<not>\<^bold>KF \<in>  A\<close> 
        using As assms pos_not_to_not_nec_MCS by auto
      thus False
        using \<open>\<^bold>K F \<in> A\<close> MCS_bot assms(1) by blast
    qed
  qed
qed

end

text \<open>Lemmas involving the negation of a chain of  \<open>\<^bold>\<box>\<close> or  \<open>\<^bold>\<diamond>\<close>.\<close>

lemma not_chain_d_to_chain_b_not:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>\<not>F \<^bold>\<longrightarrow> G\<close>
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<diamond>^n F) \<^bold>\<longrightarrow> (\<^bold>\<box>^n G)\<close>
proof (induct n)
  case 0
  then show ?case using assms by auto
next
  case (Suc n)
  assume \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<diamond>^n F) \<^bold>\<longrightarrow> (\<^bold>\<box>^n G)\<close>
  hence H: \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n F) \<^bold>\<longrightarrow> \<^bold>\<box>(\<^bold>\<box>^n G)\<close> using KSq MP NSq by blast
  have H2: \<open>\<And> A B C . \<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (B \<^bold>\<longrightarrow> C) \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> C)\<close> using TAU by force
  have \<open>\<turnstile>\<^sub>B \<^bold>\<not>(\<^bold>\<diamond>\<^bold>\<diamond>^n F) \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n F)\<close> 
    using KBox.not_pos_to_nec_not chain_d_def by auto 
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<not>(\<^bold>\<diamond>\<^bold>\<diamond>^n F) \<^bold>\<longrightarrow> \<^bold>\<box>(\<^bold>\<box>^n G)\<close> using H H2 MP by blast
  thus ?case using chain_b_def chain_d_def by simp
qed


lemma not_chain_b_to_chain_d_not:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>\<not>F \<^bold>\<longrightarrow> G\<close>
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<box>^n F) \<^bold>\<longrightarrow> (\<^bold>\<diamond>^n G)\<close>
proof (induct n)
  case 0
  then show ?case using assms by auto
next
  case (Suc n)
  assume P1: \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<box>^n F) \<^bold>\<longrightarrow> (\<^bold>\<diamond>^n G)\<close>
  have T: \<open>\<And> A B . \<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B)  \<^bold>\<longrightarrow> (\<^bold>\<not> B \<^bold>\<longrightarrow> \<^bold>\<not> A)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<diamond>^n G) \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<not> (\<^bold>\<box>^n F)\<close> using P1 MP by auto
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n G) \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>\<^bold>\<not>(\<^bold>\<box>^n F)\<close> using KSq MP NSq by blast
  hence P2: \<open>\<turnstile>\<^sub>B \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<box>^n F) \<^bold>\<longrightarrow> \<^bold>\<diamond>(\<^bold>\<diamond>^n G)\<close> using T MP by auto
  have P3: \<open>\<turnstile>\<^sub>B \<^bold>\<not> (\<^bold>\<box>^(n+1) F) \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<box>^n F)\<close>
    using KBox.not_nec_to_pos_not by auto
  have \<open>\<And> A B C . \<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (B \<^bold>\<longrightarrow> C) \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> C)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B (\<^bold>\<not>\<^bold>\<box>^(n+1) F) \<^bold>\<longrightarrow> \<^bold>\<diamond>(\<^bold>\<diamond>^n G)\<close> using P2 P3 MP by blast
  thus ?case using chain_b_def P2 MP chain_d_def by simp
qed

lemma not_chain_b_to_chain_d_not_rev:
  assumes \<open>\<turnstile>\<^sub>B F \<^bold>\<longrightarrow> \<^bold>\<not>G\<close>
  shows \<open>\<turnstile>\<^sub>B (\<^bold>\<diamond>^n G) \<^bold>\<longrightarrow>  \<^bold>\<not> (\<^bold>\<box>^n F)\<close>
proof (induct n)
  case 0
  have \<open>\<turnstile>\<^sub>B (F \<^bold>\<longrightarrow> \<^bold>\<not>G) \<^bold>\<longrightarrow> (G \<^bold>\<longrightarrow> \<^bold>\<not>F)\<close> using TAU by force
  then show ?case using assms chain_b_def chain_d_def MP by auto
next
  case (Suc n)
  assume P1: \<open>\<turnstile>\<^sub>B (\<^bold>\<diamond>^n G) \<^bold>\<longrightarrow>  \<^bold>\<not> (\<^bold>\<box>^n F)\<close>
  have T: \<open>\<And> A B . \<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> \<^bold>\<not>B)  \<^bold>\<longrightarrow> (B \<^bold>\<longrightarrow> \<^bold>\<not> A)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B (\<^bold>\<box>^n F) \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<diamond>^n G)\<close> using P1 MP by auto
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<box>(\<^bold>\<box>^n F) \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n G)\<close> using KSq MP NSq by blast
  hence P2: \<open>\<turnstile>\<^sub>B (\<^bold>\<box>^(n+1) F) \<^bold>\<longrightarrow> \<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n G)\<close> using T MP chain_b_def by simp
  have \<open>\<And> A B . \<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B)  \<^bold>\<longrightarrow> (\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>\<not> A)\<close> using TAU by force
  hence P3: \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>(\<^bold>\<diamond>^n G) \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<box>^(n+1) F)\<close> using P2 MP by blast 
  thus ?case using chain_d_def by simp
qed

section \<open>Elements for the Canonical model\<close>

text \<open>First, we introduce some relations that will by used to define the components of the 
  Canonical Model. The first one is the chain relation \<open>Chn\<close>:\<close>

abbreviation Chn :: \<open>('p fm set \<times> 'p fm set) set\<close> where
  \<open>Chn \<equiv> {(Sa,Sb) . MCS Sa \<and> MCS Sb \<and> {f . \<^bold>\<box>f \<in> Sa} \<subseteq> Sb}\<close>

text \<open>Now, the eelation \<open>Zmc\<close> linking MCS that will produce the bisimilarity relation:\<close>

abbreviation Zmc :: \<open>('p fm set \<times> 'p fm set) set\<close> where
  \<open>Zmc \<equiv> {(Sa,Sb) . MCS Sa \<and> MCS Sb \<and> {f. \<^bold>[b\<^bold>]f \<in> Sa} \<subseteq> Sb}\<close>

text \<open>Truth of propositional variables in MCS:\<close>

abbreviation Vmc :: \<open>'p fm set \<Rightarrow> 'p \<Rightarrow> bool\<close> where
  \<open>Vmc \<equiv> (\<lambda> S P. \<^bold>\<cdot>P \<in> S)\<close>

text \<open>Sets \<open>MC1\<close> and \<open>MC2\<close> will constitute the worlds on the left and on the right model of the 
  canonical model for \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>. All mc-sets are in \<open>MC1\<close>, while \<open>MC2\<close> contains only mc-sets containing
  \<open>\<^bold>\<box>^n\<^bold>[b\<^bold>]\<^bold>\<bottom>\<close> for all \<open>n\<close>.\<close>

abbreviation MC1 :: \<open>'p fm set set\<close> where
  \<open>MC1 \<equiv> {A . MCS A}\<close>

abbreviation MC2 :: \<open>'p fm set set\<close> where
  \<open>MC2 \<equiv> {A . MCS A \<and> (\<forall> n . \<^bold>\<box>^n \<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> A)}\<close>


text \<open>This lemma shows that \<open>Zmc\<close> goes from worlds not in \<open>MC2\<close> to worlds in \<open>MC2\<close>.\<close>

lemma Z_from_MC1_to_MC2:
  assumes \<open>(A,B) \<in> Zmc\<close>
  shows \<open>A \<notin> MC2 \<and> B \<in> MC2\<close>
proof - 
  have \<open>\<^bold>\<top> \<in> B\<close> using assms by auto
  hence \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<in> A\<close> using KFrB.pos_subset assms by force
  have \<open>A \<notin> MC2\<close> 
  proof
    assume \<open>A \<in> MC2\<close>
    hence \<open>\<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> A\<close> by (metis (no_types, lifting) mem_Collect_eq chain_b.simps(1))
    thus False using \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<in> A\<close> assms by fastforce 
  qed
  have \<open>\<forall> n . \<^bold>[b\<^bold>] \<^bold>\<box>^n \<^bold>[b\<^bold>] \<^bold>\<bottom> \<in> A\<close> using assms NTSgen deriv_in_maximal by auto
  hence \<open>\<forall> n .  \<^bold>\<box>^n \<^bold>[b\<^bold>] \<^bold>\<bottom> \<in> B\<close> using assms by auto
  hence \<open>B \<in> MC2\<close> using assms by blast
  thus ?thesis using \<open>A \<notin> MC2\<close> by simp
qed

text \<open>The following lemma is important for the proof of existence. It proves that if
  \<open>{f . \<^bold>\<box>f \<in> A} \<subseteq> B\<close> and \<open>A \<in> MC2\<close>, then \<open>B \<in> MC2\<close>.\<close>

lemma Chn_from_to_2:
  assumes \<open>(A,B) \<in> Chn\<close> and \<open>A \<in> MC2\<close> 
  shows \<open>B \<in> MC2\<close> 
proof -
  have Amc2: \<open>\<forall> n . \<^bold>\<box>^n \<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> A\<close> 
    using assms(2) by auto
  have \<open>\<forall> m . \<^bold>\<box>^(m+1) \<^bold>[b\<^bold>] \<^bold>\<bottom> \<in> A \<longrightarrow> \<^bold>\<box>^m \<^bold>[b\<^bold>] \<^bold>\<bottom> \<in> B\<close> using assms(1) by force
  hence \<open>\<forall> n . \<^bold>\<box>^n \<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> B\<close> using Amc2 by blast
  thus ?thesis using assms by blast
qed

text \<open>Lemmas used to prove existence.\<close>

lemma pos_r1_sub:
  assumes \<open>A \<in> MC1\<close> and \<open>B \<in> MC1\<close>
  shows \<open>(A,B) \<in> Chn \<longleftrightarrow> {\<^bold>\<diamond>F | F . F \<in> B} \<subseteq> A\<close> 
proof -
  have \<open>MCS A\<close> using assms(1) by simp
  have \<open>MCS B\<close> using assms(2) by simp
  have P: \<open>(A,B) \<in> Chn \<longleftrightarrow> {f . \<^bold>\<box>f \<in> A} \<subseteq> B\<close> using assms by simp
  have \<open>({F |F. \<^bold>\<box> F \<in> A} \<subseteq> B) \<longleftrightarrow> ({\<^bold>\<diamond> F |F. F \<in> B} \<subseteq> A)\<close> 
    using \<open>MCS A\<close> \<open>MCS B\<close> KBox.pos_subset by simp
  thus ?thesis using P by simp 
qed

lemma pos_r2_sub:
  assumes \<open>A \<in> MC2\<close> and \<open>B \<in> MC2\<close>
  shows \<open>(A,B) \<in> Chn \<longleftrightarrow> {\<^bold>\<diamond>F | F . F \<in> B} \<subseteq> A\<close> 
proof -
  have \<open>MCS A\<close> using assms(1) by simp
  have \<open>MCS B\<close> using assms(2) by simp
  have P: \<open>(A,B) \<in> Chn \<longleftrightarrow> {f . \<^bold>\<box>f \<in> A} \<subseteq> B\<close> using assms by simp
  have \<open>({F |F. \<^bold>\<box> F \<in> A} \<subseteq> B) \<longleftrightarrow> ({\<^bold>\<diamond> F |F. F \<in> B} \<subseteq> A)\<close> 
    using \<open>MCS A\<close> \<open>MCS B\<close> KBox.pos_subset by simp
  thus ?thesis using P by simp 
qed

lemma pos_b_r2_sub:
  assumes \<open>A \<in> MC1\<close> and \<open>B \<in> MC2\<close>
  shows \<open>(A,B) \<in> Zmc \<longleftrightarrow> {\<^bold>\<langle>b\<^bold>\<rangle>F | F . F \<in> B} \<subseteq> A\<close> 
proof -
  have \<open>MCS A\<close> using assms(1) by simp
  have \<open>MCS B\<close> using assms(2) by simp
  have P: \<open>(A,B) \<in> Zmc \<longleftrightarrow> {f . \<^bold>[b\<^bold>]f \<in> A} \<subseteq> B\<close> using assms by simp
  have \<open>({F |F. \<^bold>[b\<^bold>]F \<in> A} \<subseteq> B) \<longleftrightarrow> ({ \<^bold>\<langle>b\<^bold>\<rangle> F |F. F \<in> B} \<subseteq> A)\<close> 
    using \<open>MCS A\<close> \<open>MCS B\<close> KFrB.pos_subset by simp
  thus ?thesis using P by simp 
qed

text \<open>All mc-sets in \<open>MC2\<close> contain \<open>\<^bold>[b\<^bold>]F\<close> for every \<open>F\<close>.\<close>

lemma all_box_b_in_MC2:
  assumes \<open>S \<in> MC2\<close>
  shows \<open>\<^bold>[b\<^bold>]F \<in> S\<close>
proof -
  have \<open>\<turnstile>\<^sub>B \<^bold>\<bottom> \<^bold>\<longrightarrow> F\<close> using TAU by force
  have \<open>\<^bold>[b\<^bold>]\<^bold>\<bottom> \<in> S\<close> using assms chain_b.simps(1)
    by (metis (no_types, lifting) mem_Collect_eq)
  thus ?thesis using \<open>\<turnstile>\<^sub>B \<^bold>\<bottom> \<^bold>\<longrightarrow> F\<close> 
    by (smt (verit, best) KFrB.KN KFrB.Kax MCS_imp assms deriv_in_maximal
        mem_Collect_eq)
qed

section \<open>Existence\<close>

text \<open>First, we prove a general result for all normal modal operators.\<close>

context Kop begin

lemma Kop_existence:
  assumes \<open>MCS A\<close>
  and \<open>\<^bold>PF \<in> A\<close>
shows \<open>consistent ({F} \<union> {G . \<^bold>KG \<in> A})\<close>
proof (rule ccontr)
  assume \<open>\<not> consistent ({F} \<union> {G . \<^bold>KG \<in> A})\<close>
  then obtain S where S: \<open>set S \<subseteq> {G . \<^bold>KG \<in> A} \<and> F#S \<turnstile>\<^sub>B \<^bold>\<bottom>\<close> 
    by (metis (no_types, lifting) K_imply_Cons consistent_def 
        derive_split1 insert_is_Un subset_insert)  
  hence \<open>S \<turnstile>\<^sub>B \<^bold>\<not> F\<close> 
    using K_ImpI by blast
  hence \<open>\<turnstile>\<^sub>B S \<^bold>\<leadsto> \<^bold>\<not>F\<close> by simp
  hence D: \<open>\<turnstile>\<^sub>B map (\<lambda> f . \<^bold>Kf) S \<^bold>\<leadsto> \<^bold>K\<^bold>\<not>F\<close> 
    using KN K_distrib_K_imp by blast
  have \<open>set(map (\<lambda> f . \<^bold>Kf) S) \<subseteq> A\<close> using S by auto
  hence \<open>\<^bold>K\<^bold>\<not>F \<in> A\<close> using D 
    by (meson MCS_derive assms(1))
  hence \<open>\<^bold>\<not>\<^bold>K\<^bold>\<not>F \<notin> A\<close> 
    using MCS_bot assms(1) by blast
  thus False using assms(2) by auto
qed

end


lemma Chn_iff:
  assumes \<open>MCS A\<close>
  shows \<open>\<^bold>\<box>F \<in> A \<longleftrightarrow> (\<forall> B . (A,B) \<in> Chn \<longrightarrow> F\<in>B)\<close> 
proof 
  assume \<open>\<^bold>\<box>F \<in> A\<close>
  thus \<open>\<forall> B . (A,B) \<in> Chn \<longrightarrow> F \<in> B\<close> by auto
next
  assume A: \<open>\<forall> B . (A,B) \<in> Chn \<longrightarrow> F\<in>B\<close>
  show \<open>\<^bold>\<box>F \<in> A\<close>
  proof (rule ccontr)
    assume \<open>\<^bold>\<box>F \<notin> A\<close>
    hence \<open>\<^bold>\<diamond> \<^bold>\<not>F \<in> A\<close> 
      by (meson KBox.not_nec_to_pos_not MCS_imp assms deriv_in_maximal)
    hence \<open>consistent ({\<^bold>\<not>F} \<union> {G . \<^bold>\<box> G \<in> A})\<close> 
      using \<open>MCS A\<close> KBox.Kop_existence by auto  
    hence \<open>\<exists> S . (MCS S \<and> ({\<^bold>\<not>F} \<union> {G . \<^bold>\<box> G \<in> A}) \<subseteq> S)\<close> 
      using Extend_subset MCS_Extend' by metis
    then obtain S where S: \<open>(A,S) \<in> Chn \<and> \<^bold>\<not>F \<in> S \<and> F \<in> S\<close> using A assms by auto
    thus False using MCS_bot by blast
  qed
qed

text \<open>Existence for \<open>\<^bold>\<diamond>\<close> in \<open>MC1\<close>.\<close>

lemma existenceChn_1:
  assumes \<open>\<^bold>\<diamond>F \<in> A\<close> and \<open>A \<in> MC1\<close> 
  shows \<open>\<exists> B . B \<in> MC1 \<and> {F} \<union> {G . \<^bold>\<box>G \<in> A}\<subseteq>B\<close>  
proof -
  have \<open>consistent ({F} \<union> {G . \<^bold>\<box>G \<in> A})\<close> using assms KBox.Kop_existence by auto
  then obtain S where S: \<open>MCS S \<and> ({F} \<union> {G . \<^bold>\<box>G \<in> A}) \<subseteq> S\<close> 
    by (metis Extend_subset MCS_Extend')
  hence \<open>(A,S) \<in> Chn\<close> using assms by simp
  thus ?thesis using S by auto
qed

text \<open>Existence for \<open>\<^bold>\<diamond>\<close> in \<open>MC2\<close>.\<close>

lemma existenceChn_2:
  assumes \<open>\<^bold>\<diamond>F \<in> A\<close> and \<open>A \<in> MC2\<close> 
  shows \<open>\<exists> B . B \<in> MC2 \<and> {F} \<union> {G . \<^bold>\<box>G \<in> A}\<subseteq>B\<close>  
proof -
  have \<open>consistent ({F} \<union> {G . \<^bold>\<box>G \<in> A})\<close> using assms KBox.Kop_existence by auto
  then obtain S where S: \<open>MCS S \<and> ({F} \<union> {G . \<^bold>\<box>G \<in> A}) \<subseteq> S\<close> 
    by (metis Extend_subset MCS_Extend')
  hence \<open>(A,S) \<in> Chn\<close> using assms by simp
  thus ?thesis 
    by (metis (mono_tags, lifting) Chn_from_to_2 S assms(2))
qed

text \<open>Existence for \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<close> in \<open>MC1\<close>.\<close>

lemma existenceZmc:
  assumes \<open>\<^bold>\<langle>b\<^bold>\<rangle>F \<in> A\<close> and \<open>A \<in> MC1\<close> 
  shows \<open>\<exists> B . B \<in> MC2 \<and> {F} \<union> {G . \<^bold>[b\<^bold>]G \<in> A}\<subseteq>B\<close>  
proof -
  have \<open>consistent ({F} \<union> {G . \<^bold>[b\<^bold>]G \<in> A})\<close> using assms KFrB.Kop_existence by auto
  then obtain S where S: \<open>MCS S \<and> ({F} \<union> {G . \<^bold>[b\<^bold>]G \<in> A}) \<subseteq> S\<close> 
    by (metis Extend_subset MCS_Extend')
  hence \<open>(A,S) \<in> Zmc\<close> using assms by simp
  thus ?thesis 
    by (metis (mono_tags, lifting) S Z_from_MC1_to_MC2)
qed

section \<open>Atomic harmony of \<open>Zmc\<close>.\<close>

text \<open>MCS linked by \<open>Zmc\<close> contain the same propositional variables.\<close>

lemma Zmc_atomic_harmony:
  assumes \<open>(A,B) \<in> Zmc\<close>
  shows \<open>\<^bold>\<cdot>l \<in> A \<longleftrightarrow> \<^bold>\<cdot>l \<in> B\<close> 
proof
  assume \<open>\<^bold>\<cdot>l \<in> A\<close>
  hence \<open>\<^bold>[b\<^bold>]\<^bold>\<cdot>l \<in> A\<close> 
    by (metis (mono_tags, lifting) HARM assms deriv_in_maximal Derivations_Imp.MCS_impE 
        Derivations_Imp_axioms mem_Collect_eq old.prod.case)
  thus \<open>\<^bold>\<cdot>l \<in> B\<close> using assms by auto
next
  assume \<open>\<^bold>\<cdot>l \<in> B\<close>
  thus \<open>\<^bold>\<cdot>l \<in> A\<close> 
    by (smt (verit, del_insts) HARM MCS_bot MCS_imp assms deriv_in_maximal
        mem_Collect_eq prod.simps(2) subsetD)
qed

section \<open>Forth and Back\<close>

text \<open>First, an auxiliary lemma used in the proofs of forth and back properties of the Canonical
  Model.\<close>

lemma nec_As_to_nec_conj:
  assumes \<open>S \<in> MC1\<close>
  and \<open>{\<^bold>[b\<^bold>]f | f. f \<in> set A} \<subseteq> S\<close>
  shows \<open>\<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> S\<close> 
proof (rule ccontr)
  assume \<open>\<^bold>[b\<^bold>] \<^bold>\<not>(A \<^bold>\<leadsto> \<^bold>\<bottom>) \<notin> S\<close>
  hence \<open>\<^bold>\<not>\<^bold>[b\<^bold>] \<^bold>\<not> (A \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> S\<close> using assms(1) by blast
  hence \<open>\<^bold>\<langle>b\<^bold>\<rangle> (A \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> S\<close> by simp
  then obtain S2 where S2: \<open>(MCS S2) \<and> ({A \<^bold>\<leadsto> \<^bold>\<bottom>} \<union> {G . \<^bold>[b\<^bold>]G \<in> S}) \<subseteq> S2\<close> using assms(1)
    existenceZmc by (metis (mono_tags, lifting) mem_Collect_eq)
  hence \<open>({A \<^bold>\<leadsto> \<^bold>\<bottom>} \<union> set A) \<subseteq> S2\<close> using assms(2) mem_Collect_eq by auto
  hence \<open>\<^bold>\<bottom> \<in> S2\<close> using multiple_MP_MCS S2 by (metis insert_is_Un insert_subset)
  thus False using multiple_MP_MCS S2 insert_is_Un insert_subset by simp
qed

text \<open>Lemmas that will be used to prove that the Canonical Model satisfies forth and back
  properties.\<close>

lemma forth_cm:
  assumes \<open>(G1, G2) \<in> Zmc\<close>
  and \<open>(G1, G3) \<in> Chn\<close>
shows \<open>\<exists> G4 . (G3, G4) \<in> Zmc \<and> (G2, G4) \<in> Chn\<close>
proof -
  have GS: \<open>G1 \<in> MC1 \<and> G2 \<in> MC2 \<and> G3 \<in> MC1\<close> 
    using assms Z_from_MC1_to_MC2 by auto
  have \<open>consistent ({A . \<^bold>[b\<^bold>]A \<in> G3} \<union> {B | B. \<^bold>\<box>B \<in> G2})\<close> (is \<open>consistent (?L \<union> ?R)\<close>)
  proof (rule ccontr)
    assume \<open>\<not> consistent (?L \<union> ?R)\<close>
    then obtain AsBs where AB1: \<open>set AsBs \<subseteq> ?L \<union> ?R \<and> (AsBs \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> 
      using consistent_def by blast
    then obtain As Bs where AB: \<open>set As = (set AsBs \<inter> ?L) \<and> 
      set Bs = (set AsBs \<inter> ?R)\<close> 
      by (metis (lifting) inf_commute inter_set_filter) 
    hence \<open>set As \<union> set Bs = set AsBs\<close> using AB1 by auto
    hence \<open>(Bs@As \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> using AB 
      by (metis AB1 K_imply_weaken dual_order.refl set_append sup.commute)
    hence \<open>\<turnstile>\<^sub>B Bs \<^bold>\<leadsto> As \<^bold>\<leadsto> \<^bold>\<bottom>\<close> by simp
    hence D: \<open>\<turnstile>\<^sub>B (map (\<lambda> f. \<^bold>\<box> f) Bs) \<^bold>\<leadsto> \<^bold>\<box>(As \<^bold>\<leadsto> \<^bold>\<bottom>)\<close> 
      using KBox.KN KBox.K_distrib_K_imp by blast
    have \<open>finite (set As)\<close> using \<open>(Bs@As \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> by simp
    have \<open>set (map (\<lambda> f. \<^bold>\<box> f) Bs) \<subseteq> G2\<close> using AB by auto
    hence \<open>\<^bold>\<box>(As \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G2\<close> using D 
      by (metis (no_types, lifting) MCS_derive assms(1) case_prod_conv
          mem_Collect_eq)
    hence f1: \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<box>(As \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G1\<close> (is \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<box>?F1 \<in> G1\<close>) 
      by (metis (mono_tags, lifting) MCS_bot MCS_impE MCS_impI assms(1) 
          mem_Collect_eq prod.simps(2) subsetD)
    obtain NecAs where NecAs: \<open>NecAs = (map (\<lambda> f. \<^bold>[b\<^bold>]f) As)\<close> by simp
    hence sAs: \<open>set NecAs \<subseteq> G3 \<and> finite (set NecAs)\<close> 
      using AB assms by auto
    hence \<open>{\<^bold>[b\<^bold>] f |f. f \<in> set As} \<subseteq> G3\<close> using AB by blast
    hence \<open>\<^bold>[b\<^bold>]\<^bold>\<not>(As \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G3\<close> using GS nec_As_to_nec_conj[of "G3" "As"] by simp
    hence \<open>\<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not> (As \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G1\<close> (is \<open>\<^bold>\<diamond>\<^bold>[b\<^bold>]?F2 \<in> G1\<close>) using assms KBox.pos_subset by force
    hence \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<box>?F1 \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]?F2 \<in> G1\<close> 
      using f1 Derivations_Imp.MCS_imp Derivations_Imp_axioms assms(1) by fastforce 
    hence \<open>\<^bold>\<langle>b\<^bold>\<rangle>(\<^bold>\<box>?F1 \<^bold>\<and> \<^bold>\<diamond>?F2) \<in> G1\<close> (is \<open>\<^bold>\<langle>b\<^bold>\<rangle>?F12 \<in> G1\<close>) using FORTH MP 
      Derivations_Imp.MCS_imp Derivations_Imp_axioms GS deriv_in_maximal by fastforce
    then obtain A where A: \<open>(G1,A)\<in>Zmc \<and> A \<in> MC2 \<and> (\<^bold>\<box>?F1 \<^bold>\<and> \<^bold>\<diamond>?F2 \<in> A)\<close> 
      using assms(1) existenceZmc[of "?F12" "G1"] Z_from_MC1_to_MC2[of "G1"] 
      by auto
    hence \<open>{\<^bold>\<box>?F1, \<^bold>\<diamond>?F2} \<subseteq> A\<close> 
      by (metis (mono_tags, lifting) MCS_bot MCS_imp empty_subsetI insert_subset
          mem_Collect_eq) 
    then obtain B where B: \<open>B \<in> MC2 \<and> {?F1, ?F2} \<subseteq> B\<close> 
      using A existenceChn_2[of "?F2"] 
      by (metis (mono_tags, lifting) KBox.pos_not_to_not_nec_MCS MCS_bot MCS_imp mem_Collect_eq)
    hence \<open>\<^bold>\<bottom> \<in> B\<close> by blast
    thus False using B by auto
  qed
  then obtain G4 where G4: \<open>(?L \<union> ?R) \<subseteq> G4 \<and> MCS G4\<close> 
    using Extend_subset MCS_Extend' by fastforce
  hence \<open>{B | B. \<^bold>\<box>B \<in> G2} \<subseteq> G4\<close> by simp
  hence T1: \<open>(G2, G4) \<in> Chn\<close> using G4 GS by simp
  hence \<open>(G3, G4) \<in> Zmc\<close> using G4 GS Chn_from_to_2 by auto 
  thus ?thesis using T1 by auto
qed


lemma back_cm:
  assumes \<open>(G1, G2) \<in> Zmc\<close>
  and \<open>(G2, G3) \<in> Chn\<close>
shows \<open>\<exists> G4 . (G1, G4) \<in> Chn \<and> (G4, G3) \<in> Zmc\<close> 
proof -
  have GS: \<open>G1 \<in> MC1 \<and> G2 \<in> MC2 \<and> G3 \<in> MC2\<close> 
    using assms Chn_from_to_2 Z_from_MC1_to_MC2 
    by (metis (mono_tags, lifting) case_prodD mem_Collect_eq)
  have \<open>consistent ({\<^bold>\<langle>b\<^bold>\<rangle>A | A. A \<in> G3} \<union> {B | B. \<^bold>\<box>B \<in> G1})\<close> (is \<open>consistent (?L \<union> ?R)\<close>)
  proof (rule ccontr)
    assume \<open>\<not> consistent (?L \<union> ?R)\<close>
    then obtain PosAsBs where AB1: \<open>set PosAsBs \<subseteq> ?L \<union> ?R \<and> (PosAsBs \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> 
      using consistent_def by blast
    then obtain PosAs Bs where AB: \<open>set PosAs = (set PosAsBs \<inter> ?L) \<and> 
      set Bs = (set PosAsBs \<inter> ?R)\<close> 
      by (metis (lifting) inf_commute inter_set_filter) 
    hence \<open>set PosAs \<union> set Bs = set PosAsBs\<close> using AB1 by auto
    hence \<open>(Bs@PosAs \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> using AB 
      by (metis AB1 K_imply_weaken dual_order.refl set_append sup.commute)
    hence \<open>\<turnstile>\<^sub>B Bs \<^bold>\<leadsto> PosAs \<^bold>\<leadsto> \<^bold>\<bottom>\<close> by simp
    hence D: \<open>\<turnstile>\<^sub>B (map (\<lambda> f. \<^bold>\<box> f) Bs) \<^bold>\<leadsto> \<^bold>\<box>(PosAs \<^bold>\<leadsto> \<^bold>\<bottom>)\<close> 
      using KBox.KN KBox.K_distrib_K_imp by blast
    have \<open>finite (set PosAs)\<close> using \<open>(Bs@PosAs \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> by simp
    have \<open>set (map (\<lambda> f. \<^bold>\<box> f) Bs) \<subseteq> G1\<close> using AB by auto
    hence X1: \<open>\<^bold>\<box>(PosAs \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G1\<close> using D 
      by (metis (no_types, lifting) MCS_derive assms(1) case_prod_conv
          mem_Collect_eq)
    obtain As where As: \<open>As = (map (\<lambda> f. THE p . f = \<^bold>\<langle>b\<^bold>\<rangle>p) PosAs)\<close> by simp
    hence sAs: \<open>set As \<subseteq> G3 \<and> finite (set As)\<close> 
      using AB assms by auto
    have \<open>\<forall> f . f \<in> set PosAs \<longrightarrow> (\<exists> g . f = \<^bold>\<langle>b\<^bold>\<rangle>g)\<close> using AB by auto
    hence X: \<open>set PosAs = {\<^bold>\<langle>b\<^bold>\<rangle>g | g. g \<in> set As}\<close> using As by force
    have \<open>As \<^bold>\<leadsto> \<^bold>\<bottom> \<notin> G3\<close> using multiple_MP_MCS MCS_bot assms(2) sAs by auto
    hence \<open>\<^bold>\<not> (As \<^bold>\<leadsto> \<^bold>\<bottom>) \<in> G3\<close> (is \<open>?F2 \<in> G3\<close>) using assms(2) by blast
    hence \<open>\<^bold>\<diamond>?F2 \<in> G2\<close>  
      by (smt (verit, ccfv_threshold) assms KBox.pos_subset GS 
          mem_Collect_eq pos_r2_sub subsetD)
    hence \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<diamond>?F2 \<in> G1\<close> using assms KFrB.pos_subset by fastforce
    hence X2: \<open>\<^bold>\<diamond>\<^bold>\<langle>b\<^bold>\<rangle> ?F2 \<in> G1\<close> by (metis (mono_tags, lifting) BACK[of "?F2"] 
      deriv_in_maximal GS MCS_impE mem_Collect_eq)
    then obtain B where B: \<open>(G1,B)\<in>Chn \<and> B \<in> MC1 \<and> {\<^bold>\<langle>b\<^bold>\<rangle>?F2} \<union> {f . \<^bold>\<box> f \<in> G1}\<subseteq> B\<close> 
      using assms GS existenceChn_1[of "\<^bold>\<langle>b\<^bold>\<rangle>?F2" "G1"] by auto
    hence X3: \<open>{\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<not> (As \<^bold>\<leadsto> \<^bold>\<bottom>), PosAs \<^bold>\<leadsto> \<^bold>\<bottom>} \<subseteq> B\<close> using X1 by auto
    then obtain C where C: \<open>MCS C \<and> ({\<^bold>\<not> (As \<^bold>\<leadsto> \<^bold>\<bottom>)} \<union> {f .\<^bold>[b\<^bold>]f \<in> B}) \<subseteq> C\<close> 
      using existenceZmc[of "\<^bold>\<not> (As \<^bold>\<leadsto> \<^bold>\<bottom>)" "B"] B by auto 
    hence \<open>(B,C) \<in> Zmc\<close> using B C by simp
    hence BC: \<open>({\<^bold>\<langle>b\<^bold>\<rangle>f | f. f \<in> C}) \<subseteq> B\<close> 
      using pos_b_r2_sub[of "B" "C"] Z_from_MC1_to_MC2[of "B" "C"] by simp
    have \<open>set As \<subseteq> C\<close> using C not_imp_to_conj by auto
    hence \<open>{\<^bold>\<langle>b\<^bold>\<rangle>f | f. f \<in> set As} \<subseteq> B\<close> using BC by auto
    hence \<open>set PosAs \<subseteq> B\<close> using X by simp
    hence \<open>\<^bold>\<bottom> \<in> B\<close> using B X3
      by (simp add: multiple_MP_MCS)
    thus False using B by simp
  qed
  then obtain G4 where G4: \<open>(?L \<union> ?R) \<subseteq> G4 \<and> MCS G4\<close> 
    using Extend_subset MCS_Extend' by fastforce
  hence \<open>{B | B. \<^bold>\<box>B \<in> G1} \<subseteq> G4\<close> by simp
  hence T1: \<open>(G1, G4) \<in> Chn\<close> using G4 GS by simp
  hence \<open>G4 \<in> MC1\<close> using G4 by auto  
  hence \<open>(G4, G3) \<in> Zmc\<close> using G4 pos_b_r2_sub GS by auto 
  thus ?thesis using T1 by auto
qed

section \<open>Existence of elements in \<open>Zmc\<close>.\<close>

lemma Zmc_not_empty:
  \<open>Zmc \<noteq> {}\<close> 
proof -
  let ?V = \<open>\<lambda> w p . False\<close>
  let ?M1 = \<open>Model {0::nat} {} ?V\<close>
  let ?M2 = \<open>Model {0} {} ?V\<close>
  let ?M  =  \<open>ModelLb ?M1 ?M2 {(0,0)}\<close>
  have \<open>bi_model ?M\<close> using bi_model_def by force 
  have \<open>\<not> (?M, \<m>, 0) \<Turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close> by auto
  hence \<open>\<not> [\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top>] \<turnstile>\<^sub>B \<^bold>\<bottom>\<close> using soundness \<open>bi_model ?M\<close> by fastforce
  hence \<open>consistent {\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top>}\<close>
    by (metis K_imply_weaken consistent_def empty_set list.simps(15))
  hence \<open>\<exists> A . \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<in> A \<and> MCS A\<close>
    using MCS_Extend' Extend_subset insert_subset by metis
  hence \<open>\<exists> A . \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<in> A \<and> A \<in> MC1\<close> by auto
  hence \<open>\<exists> A B . \<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<top> \<in> A \<and> A \<in> MC1 \<and> MCS B \<and> {F . \<^bold>[b\<^bold>]F \<in> A} \<subseteq> B\<close> 
    using existenceZmc by force
  hence \<open>\<exists> A B . (A, B) \<in> Zmc\<close> by auto
  thus ?thesis by auto
qed

section \<open>Canonical Model\<close>

text \<open>The Canonical Model is defined in terms of \<open>MC1\<close>, \<open>MC2\<close>, \<open>Chn\<close> and \<open>Zmc\<close>.\<close>

text \<open>\<open>R1\<close> and \<open>R2\<close> are the modal acessibility relations of the models on the left and right of the
  Canonical Model for \<open>\<L>\<^sub>\<box>\<^sub>[\<^sub>b\<^sub>]\<close>. They are defined as restrictions of \<open>Chn\<close> for  \<open>MC1\<close> and  \<open>MC2\<close>, 
  respectively. The valuation function \<open>Vc\<close> is common for two models, it assigns True to a variable
  iff it belongs to the corresponding world. The bisimulation relation \<open>Zc\<close> is defined from \<open>Zmc\<close>.\<close>

abbreviation R1 :: \<open>('p fm set \<times> 'p fm set) set\<close> where
  \<open>R1 \<equiv> {(w1, w2) . w1 \<in> MC1 \<and> w2 \<in> MC1 \<and> (w1, w2) \<in> Chn}\<close>

abbreviation R2 :: \<open>('p fm set \<times> 'p fm set) set\<close> where
  \<open>R2 \<equiv> {(w1, w2) . w1 \<in> MC2 \<and> w2 \<in> MC2 \<and> (w1, w2) \<in> Chn}\<close>

abbreviation Vc :: \<open>'p fm set \<Rightarrow> 'p \<Rightarrow> bool\<close> where
  \<open>Vc w p \<equiv> \<^bold>\<cdot>p \<in> w\<close>

abbreviation Zc :: \<open>('p fm set \<times> 'p fm set) set\<close> where
  \<open>Zc \<equiv> {(w1, w2) . w1 \<in> MC1 \<and> w2 \<in> MC2 \<and> (w1, w2) \<in> Zmc}\<close>

text \<open>Now, models \<open>Mc1\<close> and \<open>Mc2\<close> are introduced. These are the models on the left and right, of
  the Canonical Model.\<close>

abbreviation Mc1 :: \<open>('p, 'p fm set) model\<close> where
  \<open>Mc1 \<equiv> Model MC1 R1 Vc\<close>

abbreviation Mc2 :: \<open>('p, 'p fm set) model\<close> where
  \<open>Mc2 \<equiv> Model MC2 R2 Vc\<close>

text \<open>Finally, the Canonical Model is introduced.\<close>

abbreviation CanMod :: \<open>('p, 'p fm set) modelLb\<close> where
  \<open>CanMod \<equiv> ModelLb Mc1 Mc2 Zc\<close>


lemma Chn_Rc2:
  \<open>((S,T) \<in> Chn \<and> S \<in> MC2 \<and> T \<in> MC2) \<longleftrightarrow> (S,T) \<in> R2\<close> (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume \<open>?L\<close>
  hence \<open>T \<in> MC2\<close> 
    by (metis (mono_tags, lifting)) 
  hence \<open>S \<in> MC2 \<and> T \<in> MC2\<close> using \<open>?L\<close> by simp
  thus \<open>?R\<close> using \<open>?L\<close> by simp
next
  assume \<open>?R\<close>
  thus \<open>?L\<close> by simp
qed

section \<open>Canonocity\<close>

text \<open>The Canonical Model is a bi-model.\<close>

lemma bi_model_CM:
  \<open>bi_model CanMod\<close> 
proof -
  \<comment> \<open>Properties of Z and W sets\<close>
  have \<open>Zmc \<noteq> {}\<close> using Zmc_not_empty by simp
  hence \<open>\<exists> A B . A \<in> MC1 \<and> B \<in> MC2 \<and> (A, B) \<in> Zmc\<close>  
    by (metis (mono_tags, lifting) Z_from_MC1_to_MC2 Collect_empty_eq 
     case_prodE mem_Collect_eq)
  hence \<open>MC1 \<noteq> {} \<and> MC2 \<noteq> {} \<and> Zc \<noteq> {}\<close> 
    by (smt (verit, ccfv_SIG) case_prodE not_empty mem_Collect_eq 
        prod.inject split_cong) 
  hence WZ: \<open>W (M1 CanMod) \<noteq> {} \<and> W (M2 CanMod) \<noteq> {} \<and> Z CanMod \<noteq> {} \<and> 
      Z CanMod \<subseteq> (W (M1 CanMod)) \<times> (W (M2 CanMod))\<close> by auto
  \<comment> \<open>Properties of R1 and R2\<close>
  have R1: \<open>R (M1 CanMod) \<subseteq> (W (M1 CanMod)) \<times> (W (M1 CanMod))\<close> by auto
  have R2: \<open>R (M2 CanMod) \<subseteq> (W (M2 CanMod)) \<times> (W (M2 CanMod))\<close> by auto
  \<comment> \<open>Atomic Harmony\<close>
  have \<open>\<forall> w w' l . (w, w') \<in> Z CanMod \<longrightarrow> 
    (\<^bold>\<cdot>l \<in> w \<longleftrightarrow> \<^bold>\<cdot>l \<in> w')\<close> by (metis (mono_tags, lifting) 
    Zmc_atomic_harmony mem_Collect_eq modelLb.sel(3) old.prod.case)
  hence AtHarm: \<open>\<forall> w w' . (w, w') \<in> Z CanMod \<longrightarrow> 
    ((V (M1 CanMod)) w) = ((V (M2 CanMod)) w')\<close> by auto
  \<comment> \<open>Forth\<close>
  have Forth: \<open>\<forall> w w' v . (w, w') \<in> Z CanMod \<and> (w,v) \<in> R (M1 CanMod) \<longrightarrow> 
        (\<exists> v' . (v,v') \<in> Z CanMod \<and> (w', v') \<in> R (M2 CanMod))\<close> 
    by (smt (z3) forth_cm Chn_from_to_2 mem_Collect_eq model.sel(2) modelLb.sel(1,2,3)
        old.prod.case)
  \<comment> \<open>Back\<close>
  have Back: \<open>\<forall> w w' v' . (w, w') \<in> Z CanMod \<and> (w',v') \<in> R (M2 CanMod) \<longrightarrow> 
      (\<exists> v . (v,v') \<in> Z CanMod \<and> (w,v) \<in> R (M1 CanMod))\<close>
    by (smt (z3) back_cm Chn_from_to_2 mem_Collect_eq model.sel(2) modelLb.sel(1,2,3)
        old.prod.case)
  show ?thesis unfolding bi_model_def using WZ R1 R2 AtHarm Forth Back
    by blast
qed

section \<open>Truth Lemma\<close>

text \<open>This is the key lemma for Completeness: a formula \<open>F\<close> is true in a given world \<open>w\<close> of the 
  Canonical Model iff \<open>F \<in> w\<close>.\<close>

lemma Truth_Lemma:
  \<open>\<forall> (S::'p fm set) . (MCS S \<longrightarrow> ((S \<in> MC1 \<longrightarrow> ((CanMod, \<m>, S)\<Turnstile>\<^sub>B F \<longleftrightarrow> F \<in> S)) \<and>
      (S \<in> MC2 \<longrightarrow> ((CanMod, \<m>', S)\<Turnstile>\<^sub>B F \<longleftrightarrow> F \<in> S))))\<close> (is \<open>?TL F\<close>)
proof (induct F)
  case Fls
  thus ?case by simp
next
  case (Pro x)
  thus ?case by simp
next
  case (Imp F1 F2)
  assume KSq: \<open>?TL F1\<close>
  assume Kb: \<open>?TL F2\<close>
  have \<open>\<forall> S . MCS S \<longrightarrow> (F1 \<^bold>\<longrightarrow> F2 \<in> S \<longleftrightarrow> (F1 \<in> S \<longrightarrow> F2 \<in> S))\<close> by auto
  thus ?case using KSq Kb by simp 
next
  case (Box F)
  assume A: \<open>?TL F\<close>
  have B: \<open>\<forall> S . MCS S \<and> S \<in> MC1 \<longrightarrow> 
      ((CanMod, \<m>, S) \<Turnstile>\<^sub>B \<^bold>\<box>F \<longleftrightarrow> 
          (\<forall> T . (S,T) \<in> R1 \<longrightarrow> (CanMod, \<m>, T) \<Turnstile>\<^sub>B F))\<close> 
    by (smt (z3) mem_Collect_eq model.sel(1,2) modelLb.sel(1) old.prod.case
        semantics.simps(5))
  have B': \<open>\<forall> S . MCS S \<and> S \<in> MC2 \<longrightarrow> 
      ((CanMod, \<m>', S) \<Turnstile>\<^sub>B \<^bold>\<box>F \<longleftrightarrow> 
          (\<forall> T . (S,T) \<in> R2 \<longrightarrow> (CanMod, \<m>', T) \<Turnstile>\<^sub>B F))\<close> 
    by (smt (z3) mem_Collect_eq model.sel(1,2) modelLb.sel(2) old.prod.case
        semantics.simps(6))
  have C: \<open>\<forall> S . MCS S \<and> S \<in> MC1 \<longrightarrow> 
      (\<^bold>\<box>F \<in> S \<longleftrightarrow> (\<forall> T . ((S,T) \<in> R1) \<longrightarrow> F \<in> T))\<close> 
    by (metis (mono_tags, lifting) Chn_iff mem_Collect_eq old.prod.case) 
  have C': \<open>\<forall> S . MCS S \<and> S \<in> MC2 \<longrightarrow> 
      (\<^bold>\<box>F \<in> S \<longleftrightarrow> (\<forall> T . ((S,T) \<in> R2) \<longrightarrow> F \<in> T))\<close> 
    by (metis (mono_tags, lifting) Chn_Rc2 Chn_iff Chn_from_to_2 ) 
  thus ?case using A B B' C by simp
next
  case (FrB F)
  assume A: \<open>?TL F\<close>
  have D1: \<open>\<forall> S . MCS S \<and> S \<in> MC1 \<longrightarrow> (\<^bold>[b\<^bold>]F \<in> S \<longleftrightarrow> 
          (\<forall> T . ((S,T) \<in> Zc) \<longrightarrow> F \<in> T))\<close> 
  proof (intro allI HOL.impI)
    fix S
    assume S: \<open>MCS (S::'p fm set) \<and> S \<in> MC1\<close>
    show \<open>\<^bold>[b\<^bold>]F \<in> S \<longleftrightarrow> (\<forall> T . ((S,T) \<in> Zc) \<longrightarrow> F \<in> T)\<close>
    proof 
      assume \<open>\<^bold>[b\<^bold>]F \<in> S\<close>
      thus \<open>\<forall> T . ((S,T) \<in> Zc) \<longrightarrow> F \<in> T\<close> by fastforce
    next
      assume T: \<open>\<forall> T . ((S,T) \<in> Zc) \<longrightarrow> F \<in> T\<close> 
      show \<open>\<^bold>[b\<^bold>]F \<in> S\<close> 
      proof (rule ccontr)
        assume \<open>\<^bold>[b\<^bold>]F \<notin> S\<close>
        hence \<open>\<^bold>\<langle>b\<^bold>\<rangle>\<^bold>\<not>F \<in> S\<close> 
          by (meson KFrB.not_nec_to_pos_not MCS_imp S deriv_in_maximal)
        hence \<open>\<exists> B . B \<in> MC2 \<and> {\<^bold>\<not>F} \<union> {G . \<^bold>[b\<^bold>]G \<in> S}\<subseteq>B\<close>
          using S existenceZmc[of "\<^bold>\<not>F" "S"] by fastforce
        then obtain B where \<open>(S,B) \<in> Zmc \<and> B \<in> MC2 \<and> \<^bold>\<not>F \<in> B\<close> 
          using S by auto
        hence B': \<open>(S,B) \<in> Zc \<and> F \<notin> B\<close> using S MCS_imp by auto
        hence \<open>F \<in> B\<close> using T by auto
        thus False using B' by simp
      qed
    qed
  qed
  have \<open>\<forall> S . MCS S \<and> S \<in> MC2 \<longrightarrow> \<^bold>[b\<^bold>]F \<in> S \<and> (CanMod, \<m>', S) \<Turnstile>\<^sub>B \<^bold>[b\<^bold>]F\<close> 
    using all_box_b_in_MC2 by auto
  thus ?case using A D1 by auto
qed

corollary truth_lemma_MC1:
  assumes \<open>S \<in> MC1\<close>
  shows \<open>\<forall> F . F \<in> S \<longleftrightarrow> (CanMod, \<m>, S) \<Turnstile>\<^sub>B F\<close> 
  using assms Truth_Lemma by auto

corollary truth_lemma_MC2:
  assumes \<open>S \<in> MC2\<close>
  shows \<open>\<forall> F . F \<in> S \<longleftrightarrow> (CanMod, \<m>', S) \<Turnstile>\<^sub>B F\<close> 
  using assms Truth_Lemma by auto 


section \<open>Completeness\<close>

text \<open>Proof of strong completeness.\<close>

theorem strong_completeness:
  assumes \<open>\<forall> (M :: ('p, 'p fm set) modelLb) ep w . 
      (bi_model M \<longrightarrow> (
          (w \<in> W (M1 M) \<longrightarrow> ((\<forall> \<gamma> \<in> set \<Gamma> . (M, \<m>, w) \<Turnstile>\<^sub>B \<gamma>) \<longrightarrow> (M, \<m>, w) \<Turnstile>\<^sub>B G)) \<and>
          (w \<in> W (M2 M) \<longrightarrow> ((\<forall> \<gamma> \<in> set \<Gamma> . (M, \<m>', w) \<Turnstile>\<^sub>B \<gamma>) \<longrightarrow> (M, \<m>', w) \<Turnstile>\<^sub>B G))))\<close>
  shows \<open>\<Gamma> \<turnstile>\<^sub>B G\<close> 
proof (rule ccontr)
  assume \<open>\<not> (\<Gamma> \<turnstile>\<^sub>B G)\<close>
  hence \<open>\<not> (\<^bold>\<not>G#\<Gamma> \<turnstile>\<^sub>B \<^bold>\<bottom>)\<close> using K_Boole by blast
  hence \<open>consistent (set (\<^bold>\<not>G#\<Gamma>))\<close> 
    using K_imply_weaken consistent_underivable by blast
  then obtain S where S: \<open>MCS S \<and> set (\<^bold>\<not>G#\<Gamma>) \<subseteq> S\<close> 
    using Extend_subset MCS_Extend' by blast
  have \<open>S \<in> MC1\<close> using S by auto
  hence N: \<open>(\<forall> F \<in> set \<Gamma> . (CanMod, \<m>, S) \<Turnstile>\<^sub>B F) \<and> ((CanMod, \<m>, S) \<Turnstile>\<^sub>B \<^bold>\<not>G)\<close> 
    using S \<open>S \<in> MC1\<close> Truth_Lemma 
    by (smt (z3) insert_subset list.simps(15) subsetD)
  hence \<open>(CanMod, \<m>, S) \<Turnstile>\<^sub>B G\<close> using bi_model_CM \<open>S \<in> MC1\<close> assms by auto
  thus False using N semantics.simps by auto
qed

text \<open>Definition of validity in bi-models:\<close>

abbreviation bi_model_valid :: \<open>'p fm \<Rightarrow> bool\<close> where
  \<open>bi_model_valid p \<equiv> \<forall> (M :: ('p, 'p fm set) modelLb) w. bi_model M \<longrightarrow> 
      ((w \<in> W (M1 M) \<longrightarrow> (M, \<m>, w)  \<Turnstile>\<^sub>B p) \<and>
       (w \<in> W (M2 M) \<longrightarrow> (M, \<m>', w) \<Turnstile>\<^sub>B p))\<close>

text \<open>Weak completeness and main result:\<close>

corollary completeness: \<open>bi_model_valid p \<Longrightarrow> \<turnstile>\<^sub>B p\<close> 
  by (metis imply.simps(1) strong_completeness) 

theorem main: \<open>(bi_model_valid p) \<longleftrightarrow> \<turnstile>\<^sub>B p\<close>
  using soundness completeness by metis


section \<open>Extension of atomic harmony to all formulas in \<open>\<L>\<^sub>\<box>\<close>\<close>

text \<open>Set of formulas in \<open>\<L>\<^sub>\<box>\<close>.\<close>

inductive_set Lbox :: \<open>'p fm set\<close> where
  Fls: \<open>\<^bold>\<bottom> \<in> Lbox\<close>
| Pro: \<open>\<^bold>\<cdot>l \<in> Lbox\<close> 
| Imp: \<open>A \<in> Lbox \<Longrightarrow> B \<in> Lbox \<Longrightarrow> A\<^bold>\<longrightarrow>B \<in> Lbox\<close>
| Box:   \<open>A \<in> Lbox \<Longrightarrow> \<^bold>\<box>A \<in> Lbox\<close>

text \<open>Auxiliary lemmas for the induction.\<close>

lemma BotPos:
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<bottom>\<close> using TAU by force

lemma BotNeg:
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<bottom>\<close>
  by (metis K_imply_Cons K_imply_head Nb imply.simps(1,2))

lemma impPos:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>A\<close>
    and \<open>\<turnstile>\<^sub>B B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]B\<close>
  shows \<open>\<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close>
proof -
  have \<open>\<turnstile>\<^sub>B \<^bold>\<not>A \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> B)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close> using Nb Kb MP by force
  hence 1: \<open>\<turnstile>\<^sub>B \<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close> using assms(1) MP_chain by auto
  have \<open>\<turnstile>\<^sub>B B \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> B)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close> using Nb Kb MP by force
  hence 2: \<open>\<turnstile>\<^sub>B B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close> using assms(2) MP_chain by auto
  have \<open>\<turnstile>\<^sub>B (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)) \<^bold>\<longrightarrow> 
      (B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>](A \<^bold>\<longrightarrow> B)\<close> using TAU by force
  thus ?thesis using 1 2 MPcons by blast  
qed  

lemma impNeg:
  assumes \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A\<close>
    and \<open>\<turnstile>\<^sub>B \<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>B\<close>
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>(A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<longrightarrow> B)\<close>
proof -
  have 1: \<open>\<turnstile>\<^sub>B \<^bold>\<not>(A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> A \<^bold>\<and> \<^bold>\<not>B\<close> using TAU by force
  have \<open>\<turnstile>\<^sub>B (A \<^bold>\<and> \<^bold>\<not>B) \<^bold>\<longrightarrow> (A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A) \<^bold>\<longrightarrow> (\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>B) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A \<^bold>\<and> \<^bold>[b\<^bold>]\<^bold>\<not>B\<close> 
    using TAU by force
  hence 2: \<open>\<turnstile>\<^sub>B \<^bold>\<not>(A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A \<^bold>\<and> \<^bold>[b\<^bold>]\<^bold>\<not>B\<close> using 1 MP_chain MPcons assms by blast
  have \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> \<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>\<not>(A \<^bold>\<longrightarrow> B)\<close> using TAU by force
  hence 3: \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<longrightarrow> B)\<close> by (metis MP_chain Nb MP Kb)
  have \<open>\<turnstile>\<^sub>B (\<^bold>[b\<^bold>]A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<longrightarrow> B)) \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A \<^bold>\<and> \<^bold>[b\<^bold>]\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<longrightarrow> B)\<close> 
    using TAU by force
  hence 4: \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]A \<^bold>\<and> \<^bold>[b\<^bold>]\<^bold>\<not>B \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>(A \<^bold>\<longrightarrow> B)\<close> using 3 MP by force
  thus ?thesis using 2 MP_chain by auto
qed  

lemma NSqPos:
  assumes \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A\<close>
  shows \<open>\<turnstile>\<^sub>B \<^bold>\<box>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<box>A\<close>
  using BACK_rev KSq MP MP_chain NSq assms by blast

lemma NSqNeg:
  assumes \<open>\<turnstile>\<^sub>B \<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>A\<close>
shows \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>\<box>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A\<close> 
proof -
  have 1: \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>\<box>A \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>\<not>A\<close>
    by (simp add: KBox.not_nec_to_pos_not)
  have 2: \<open>\<turnstile>\<^sub>B \<^bold>\<diamond>\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A\<close> using assms KBox.KN KBox.Kpos MP by blast
  have 3: \<open>\<turnstile>\<^sub>B (\<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> (\<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A)\<close> using TAU by force
  have 4: \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<langle>b\<^bold>\<rangle>(\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<not>A)\<close> using FORTH by force
  have 5: \<open>\<turnstile>\<^sub>B \<^bold>\<diamond>\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<box>A\<close> by (simp add: KBox.pos_not_to_not_nec) 
  have  \<open>\<turnstile>\<^sub>B (\<^bold>\<diamond>\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<not>\<^bold>\<box>A) \<^bold>\<longrightarrow> \<^bold>\<not>(\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<not>A)\<close> using TAU by force
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<not>(\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<not>A)\<close> using 5 MP by auto
  hence \<open>\<turnstile>\<^sub>B \<^bold>[b\<^bold>]\<^bold>\<not>(\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<not>A)\<close> using Nb by blast
  hence 6: \<open>\<turnstile>\<^sub>B \<^bold>\<langle>b\<^bold>\<rangle>(\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<not>A) \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close> 
    by (meson KFrB.not_nec_to_pos_not KFrB.not_pos_to_nec_not 
        KFrB.pos_not_to_not_nec MP MPcons) 
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<not>\<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A \<^bold>\<and> \<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close> using 4 MP_chain by blast
  hence \<open>\<turnstile>\<^sub>B \<^bold>\<diamond>\<^bold>[b\<^bold>]\<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>\<^bold>\<box>A\<close> using 3 MP by blast
  thus ?thesis using 1 2 MP_chain by blast
qed

text \<open>The following lemma extends atomic harmony (HARM) to all formulas in \<open>\<L>\<^sub>\<box>\<close>.\<close>

lemma Lbox_harm:
  assumes \<open>A \<in> Lbox\<close>
  shows\<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A\<close> 
proof -
  have \<open>\<turnstile>\<^sub>B A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]A \<and> \<turnstile>\<^sub>B \<^bold>\<not>A \<^bold>\<longrightarrow> \<^bold>[b\<^bold>]\<^bold>\<not>A\<close>
    using assms
  proof (induct A rule: Lbox.induct)
    case Fls
    thus ?case using BotPos BotNeg by simp
  next
    case (Pro l)
    thus ?case using HARM by fastforce
  next
    case (Imp A B)
    thus ?case using impPos impNeg by fastforce
  next
    case (Box A)
    thus ?case using NSqPos NSqNeg by fastforce
  qed
  thus ?thesis by simp
qed

end
