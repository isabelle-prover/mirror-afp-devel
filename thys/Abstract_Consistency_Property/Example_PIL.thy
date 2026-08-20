(*
  File: Example_PIL.thy
  Title: Example Completeness Proof for a Natural Deduction Calculus for Prior's Ideal Language
  Author: Asta Halkjær Boserup, 2025-2026.
  Reference:
    Blackburn, P. R., Braüner, T., & Kofod, J. L. Prior's Ideal Language.
    Mathematical Structures in Computer Science.
*)

chapter \<open>Example: Prior's Ideal Logic\<close>

theory Example_PIL imports
  Abstract_Consistency_Property
  "HOL-Number_Theory.Number_Theory"
begin

no_syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(\<open>indent=3 notation=\<open>binder \<Pi>\<in>\<close>\<close>\<Pi> _\<in>_./ _)\<close> 10)

section \<open>Syntax\<close>

datatype (symbols_tm: 'x) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Sym 'x (\<open>\<^bold>\<circle>\<close>)

datatype (symbols_fm: 'x) fm
  = TmI \<open>'x tm\<close> (\<open>\<^bold>\<bullet>\<close>)
  | TmP \<open>'x tm\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Neg \<open>'x fm\<close> (\<open>\<^bold>\<not> _\<close> [70] 70)
  | Con \<open>'x fm\<close> \<open>'x fm\<close> (infixr \<open>\<^bold>\<and>\<close> 35)
  | Box \<open>'x fm\<close> (\<open>\<^bold>\<box>\<close>)
  | Sat \<open>'x tm\<close> \<open>'x fm\<close> (\<open>\<^bold>@\<close>)
  | Glo \<open>'x fm\<close> (\<open>\<^bold>A\<close>)
  | Dwn \<open>'x fm\<close> (\<open>\<^bold>\<down>\<close>)
  | All \<open>'x fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Fls :: \<open>'x fm\<close> (\<open>\<^bold>\<bottom>\<close>) where
  \<open>\<^bold>\<bottom> \<equiv> undefined \<^bold>\<and> \<^bold>\<not> undefined\<close>

abbreviation Imp :: \<open>'x fm \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<^bold>\<not> (p \<^bold>\<and> \<^bold>\<not> q)\<close>

abbreviation Dia :: \<open>'x fm \<Rightarrow> 'x fm\<close> (\<open>\<^bold>\<diamond>\<close>) where
  \<open>\<^bold>\<diamond> p \<equiv> \<^bold>\<not> (\<^bold>\<box> (\<^bold>\<not> p))\<close>

type_synonym 'x lbd = \<open>'x tm \<times> 'x fm\<close>

section \<open>Semantics\<close>

record 'w frame =
  \<W> :: \<open>'w set\<close>
  \<R> :: \<open>'w \<Rightarrow> 'w set\<close>

record 'w gframe = \<open>'w frame\<close> +
  \<Pi> :: \<open>'w set set\<close>

record ('x, 'w) model = \<open>'w gframe\<close> +
  \<N> :: \<open>'x \<Rightarrow> 'w\<close>
  \<NN> :: \<open>nat \<Rightarrow> 'w\<close>
  \<V> :: \<open>'x \<Rightarrow> 'w set\<close>
  \<VV> :: \<open>nat \<Rightarrow> 'w set\<close>

abbreviation \<open>Model W R PI N e V f \<equiv> \<lparr>\<W> = W, \<R> = R, \<Pi> = PI, \<N> = N, \<NN> = e, \<V> = V, \<VV> = f\<rparr>\<close>

definition admissible :: \<open>'w frame \<Rightarrow> 'w set set \<Rightarrow> bool\<close> where
  \<open>admissible M PI \<equiv>
    (\<forall>X \<in> PI. \<W> M - X \<in> PI) \<and>
    (\<forall>X \<in> PI. \<forall>Y \<in> PI. X \<inter> Y \<in> PI) \<and>
    (\<forall>X \<in> PI. {w \<in> \<W> M. \<forall>v \<in> \<R> M w. v \<in> X} \<in> PI)\<close>

definition wf_frame :: \<open>'w frame \<Rightarrow> bool\<close> where
  \<open>wf_frame M \<equiv> \<W> M \<noteq> {} \<and> \<R> M ` \<W> M \<subseteq> Pow (\<W> M)\<close>

definition wf_gframe :: \<open>'w gframe \<Rightarrow> bool\<close> where
  \<open>wf_gframe M \<equiv> wf_frame (frame.truncate M) \<and> \<Pi> M \<noteq> {} \<and> \<Pi> M \<subseteq> Pow (\<W> M) \<and> admissible (frame.truncate M) (\<Pi> M)\<close>

definition wf_env :: \<open>('x, 'w) model \<Rightarrow> bool\<close> where
  \<open>wf_env M \<equiv> range (\<N> M) \<subseteq> \<W> M \<and> range (\<NN> M) \<subseteq> \<W> M \<and> range (\<V> M) \<subseteq> \<Pi> M \<and> range (\<VV> M) \<subseteq> \<Pi> M\<close>

definition wf_model :: \<open>('x, 'w) model \<Rightarrow> bool\<close> where
  \<open>wf_model M \<equiv> wf_gframe (gframe.truncate M) \<and> wf_env M\<close>

lemmas unfolds =
  model.defs gframe.defs frame.defs
  model.select_convs gframe.select_convs frame.select_convs

context
  fixes M :: \<open>('x, 'w) model\<close>
  assumes wf: \<open>wf_model M\<close>
begin

lemma wf_compl: \<open>X \<in> \<Pi> M \<Longrightarrow> \<W> M - X \<in> \<Pi> M\<close>
  using wf unfolding wf_model_def wf_gframe_def admissible_def unfolds by blast

lemma wf_inter: \<open>X \<in> \<Pi> M \<Longrightarrow> Y \<in> \<Pi> M \<Longrightarrow> X \<inter> Y \<in> \<Pi> M\<close>
  using wf unfolding wf_model_def wf_gframe_def admissible_def unfolds by blast

lemma wf_modal: \<open>X \<in> \<Pi> M \<Longrightarrow> {w \<in> \<W> M. \<forall>v \<in> \<R> M w. v \<in> X} \<in> \<Pi> M\<close>
  using wf unfolding wf_model_def wf_gframe_def admissible_def unfolds by blast

lemma wf_empty: \<open>{} \<in> \<Pi> M\<close>
  using wf wf_compl wf_inter unfolding wf_model_def wf_gframe_def unfolds by force

lemma wf_univ: \<open>\<W> M \<in> \<Pi> M\<close>  
  using wf wf_empty wf_compl by fastforce

lemma wf_\<Pi>: \<open>P \<in> \<Pi> M \<Longrightarrow> P \<subseteq> \<W> M\<close>
  using wf unfolding wf_gframe_def wf_model_def unfolds by fast

lemma wf_\<N>: \<open>\<N> M i \<in> \<W> M\<close>
  using wf unfolding wf_model_def wf_env_def by fast

lemma wf_\<NN>: \<open>\<NN> M n \<in> \<W> M\<close>
  using wf unfolding wf_model_def wf_env_def by blast

lemma wf_\<V>: \<open>\<V> M P \<in> \<Pi> M\<close>
  using wf unfolding wf_model_def wf_env_def by blast

lemma wf_\<V>': \<open>\<V> M n \<subseteq> \<W> M\<close>
  using wf wf_\<V> wf_\<Pi> by blast

lemma wf_\<VV>: \<open>\<VV> M n \<in> \<Pi> M\<close>
  using wf unfolding wf_model_def wf_env_def by blast

lemma wf_\<VV>': \<open>\<VV> M n \<subseteq> \<W> M\<close>
  using wf wf_\<VV> wf_\<Pi> by blast

end

type_synonym ('x, 'w) ctx = \<open>('x, 'w) model \<times> 'w\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infixr \<open>\<then>\<close> 0) where
  \<open>(t \<then> e) 0 = t\<close>
| \<open>(_ \<then> e) (Suc n) = e n\<close>

fun semantics :: \<open>('x, 'w) ctx \<Rightarrow> 'x fm \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) where
  \<open>((M, w) \<Turnstile> \<^bold>\<bullet>t) = (case_tm (\<NN> M) (\<N> M) t = w)\<close>
| \<open>((M, w) \<Turnstile> \<^bold>\<cdot>P) = (w \<in> case_tm (\<VV> M) (\<V> M) P)\<close>
| \<open>((M, w) \<Turnstile> (\<^bold>\<not> p)) = (\<not> (M, w) \<Turnstile> p)\<close>
| \<open>((M, w) \<Turnstile> (p \<^bold>\<and> q)) = ((M, w) \<Turnstile> p \<and> (M, w) \<Turnstile> q)\<close>
| \<open>((M, w) \<Turnstile> \<^bold>\<box> p) = (\<forall>v \<in> \<R> M w. (M, v) \<Turnstile> p)\<close>
| \<open>((M, _) \<Turnstile> \<^bold>@i p) = ((M, case_tm (\<NN> M) (\<N> M) i) \<Turnstile> p)\<close>
| \<open>((M, _) \<Turnstile> \<^bold>A p) = (\<forall>v \<in> \<W> M. (M, v) \<Turnstile> p)\<close>
| \<open>((M, w) \<Turnstile> \<^bold>\<down> p) = ((M\<lparr>\<NN> := (w \<then> \<NN> M)\<rparr>, w) \<Turnstile> p)\<close>
| \<open>((M, w) \<Turnstile> \<^bold>\<forall> p) = (\<forall>P \<in> \<Pi> M. (M\<lparr>\<VV> := (P \<then> \<VV> M)\<rparr>, w) \<Turnstile> p)\<close>

lemma \<open>(M, w) \<Turnstile> p \<^bold>\<longrightarrow> q \<longleftrightarrow> (M, w) \<Turnstile> p \<longrightarrow> (M, w) \<Turnstile> q\<close>
  by simp

lemma \<open>(M, w) \<Turnstile> \<^bold>\<down>(\<^bold>\<bullet>(\<^bold>#0))\<close>
  by (cases M) simp

lemma \<open>(M, w) \<Turnstile> \<^bold>\<forall>(\<^bold>@(\<^bold>\<circle>k) (\<^bold>\<cdot>(\<^bold>#0))) \<^bold>\<longrightarrow> \<^bold>@(\<^bold>\<circle>k) (\<^bold>\<forall>(\<^bold>\<cdot>(\<^bold>#0)))\<close>
  by (cases M) auto

lemma \<open>(M, w) \<Turnstile> \<^bold>@(\<^bold>\<circle>k) (\<^bold>\<forall>(\<^bold>\<cdot>(\<^bold>#0))) \<^bold>\<longrightarrow> \<^bold>\<forall>(\<^bold>@(\<^bold>\<circle>k) (\<^bold>\<cdot>(\<^bold>#0)))\<close>
  by (cases M) auto

lemma \<open>wf_model M \<Longrightarrow> (M, w) \<Turnstile> \<^bold>\<forall>(\<^bold>\<cdot>(\<^bold>#0)) \<^bold>\<longrightarrow> \<^bold>\<cdot>P\<close>
  unfolding wf_model_def wf_env_def by (fastforce split: tm.splits)

lemma \<open>wf_model M \<Longrightarrow> (M, w) \<Turnstile> \<^bold>\<forall>(\<^bold>@(\<^bold>\<circle>k) (\<^bold>\<cdot>(\<^bold>#0))) \<^bold>\<longrightarrow> \<^bold>\<down>(\<^bold>\<bullet>(\<^bold>\<circle>k) \<^bold>\<longrightarrow> \<^bold>@(\<^bold>#0) (\<^bold>\<cdot>P))\<close>
  unfolding wf_model_def wf_env_def by (fastforce split: tm.splits)

section \<open>Operations\<close>

abbreviation map_lbd :: \<open>('x \<Rightarrow> 'k) \<Rightarrow> 'x lbd \<Rightarrow> 'k lbd\<close> where
  \<open>map_lbd f \<equiv> map_prod (map_tm f) (map_fm f)\<close>

primrec symbols_lbd :: \<open>'x lbd \<Rightarrow> 'x set\<close> where
  \<open>symbols_lbd (i, p) = symbols_tm i \<union> symbols_fm p\<close>

abbreviation symbols :: \<open>'x lbd set \<Rightarrow> 'x set\<close> where
  \<open>symbols S \<equiv> \<Union>ip \<in> S. symbols_lbd ip\<close>

abbreviation lift_tm :: \<open>nat \<Rightarrow> 'x tm \<Rightarrow> 'x tm\<close> where
  \<open>lift_tm m \<equiv> case_tm (\<lambda>n. if n < m then \<^bold>#n else \<^bold>#(n + m + 1)) \<^bold>\<circle>\<close>

primrec vars_tm :: \<open>nat \<Rightarrow> 'x tm \<Rightarrow> nat set\<close> where
  \<open>vars_tm m (\<^bold>#n) = (if n \<le> m then {} else {n})\<close>
| \<open>vars_tm _ (\<^bold>\<circle>_) = {}\<close>

primrec vars_fm :: \<open>nat \<Rightarrow> 'x fm \<Rightarrow> nat set\<close> where
  \<open>vars_fm m (\<^bold>\<bullet>t) = vars_tm m t\<close>
| \<open>vars_fm m (\<^bold>\<cdot>P) = vars_tm m P\<close>
| \<open>vars_fm m (\<^bold>\<not> p) = vars_fm m p\<close>
| \<open>vars_fm m (p \<^bold>\<and> q) = vars_fm m p \<union> vars_fm m q\<close>
| \<open>vars_fm m (\<^bold>\<box> p) = vars_fm m p\<close>
| \<open>vars_fm m (\<^bold>@i p) = vars_tm m i \<union> vars_fm m p\<close>
| \<open>vars_fm m (\<^bold>A p) = vars_fm m p\<close>
| \<open>vars_fm m (\<^bold>\<down> p) = vars_fm (m + 1) p\<close>
| \<open>vars_fm m (\<^bold>\<forall> p) = vars_fm (m + 1) p\<close>

subsubsection \<open>Nominals\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'x tm) \<Rightarrow> 'x tm \<Rightarrow> 'x tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm _ (\<^bold>\<circle>k) = \<^bold>\<circle>k\<close>

primrec sub_nom :: \<open>(nat \<Rightarrow> 'x tm) \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> where
  \<open>sub_nom s (\<^bold>\<bullet>t) = \<^bold>\<bullet>(sub_tm s t)\<close>
| \<open>sub_nom _ (\<^bold>\<cdot>P) = \<^bold>\<cdot>P\<close>
| \<open>sub_nom s (\<^bold>\<not> p) = \<^bold>\<not> sub_nom s p\<close>
| \<open>sub_nom s (p \<^bold>\<and> q) = (sub_nom s p \<^bold>\<and> sub_nom s q)\<close>
| \<open>sub_nom s (\<^bold>\<box> p) = \<^bold>\<box>(sub_nom s p)\<close>
| \<open>sub_nom s (\<^bold>@i p) = \<^bold>@(sub_tm s i) (sub_nom s p)\<close>
| \<open>sub_nom s (\<^bold>A p) = \<^bold>A (sub_nom s p)\<close>
| \<open>sub_nom s (\<^bold>\<down> p) = \<^bold>\<down> (sub_nom (\<^bold>#0 \<then> \<lambda>n. lift_tm 0 (s n)) p)\<close>
| \<open>sub_nom s (\<^bold>\<forall> p) = \<^bold>\<forall> (sub_nom s p)\<close>

abbreviation inst_single_nom :: \<open>'x tm \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> (\<open>\<langle>_\<rangle>\<^sub>i\<close>) where
  \<open>\<langle>t\<rangle>\<^sub>i \<equiv> sub_nom (t \<then> \<^bold>#)\<close>

subsubsection \<open>Propositions\<close>

fun softqdf :: \<open>'x fm \<Rightarrow> bool\<close> where
  \<open>softqdf (\<^bold>\<bullet>_) = False\<close>
| \<open>softqdf (\<^bold>\<cdot>P) = True\<close>
| \<open>softqdf (\<^bold>\<not> p) = softqdf p\<close>
| \<open>softqdf (p \<^bold>\<and> q) = (softqdf p \<and> softqdf q)\<close>
| \<open>softqdf (\<^bold>\<box> p) = softqdf p\<close>
| \<open>softqdf (\<^bold>@i p) = softqdf p\<close>
| \<open>softqdf (\<^bold>A p) = softqdf p\<close>
| \<open>softqdf (\<^bold>\<down> p) = False\<close>
| \<open>softqdf (\<^bold>\<forall> p) = False\<close>

abbreviation softqdf_sub :: \<open>(nat \<Rightarrow> 'x fm) \<Rightarrow> bool\<close> where
  \<open>softqdf_sub s \<equiv> \<forall>n. softqdf (s n)\<close>

primrec lift_fm_nom :: \<open>nat \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> where
  \<open>lift_fm_nom m (\<^bold>\<bullet>t) = \<^bold>\<bullet>(lift_tm m t)\<close>
| \<open>lift_fm_nom _ (\<^bold>\<cdot>P) = \<^bold>\<cdot>P\<close>
| \<open>lift_fm_nom m (\<^bold>\<not> p) = \<^bold>\<not> lift_fm_nom m p\<close>
| \<open>lift_fm_nom m (p \<^bold>\<and> q) = (lift_fm_nom m p \<^bold>\<and> lift_fm_nom m q)\<close>
| \<open>lift_fm_nom m (\<^bold>\<box> p) = \<^bold>\<box>(lift_fm_nom m p)\<close>
| \<open>lift_fm_nom m (\<^bold>@i p) = \<^bold>@(lift_tm m i) (lift_fm_nom m p)\<close>
| \<open>lift_fm_nom m (\<^bold>A p) = \<^bold>A (lift_fm_nom m p)\<close>
| \<open>lift_fm_nom m (\<^bold>\<down> p) = \<^bold>\<down> (lift_fm_nom (m + 1) p)\<close>
| \<open>lift_fm_nom m (\<^bold>\<forall> p) = \<^bold>\<forall> (lift_fm_nom m p)\<close>

primrec lift_fm_pro :: \<open>nat \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> where
  \<open>lift_fm_pro _ (\<^bold>\<bullet>t) = \<^bold>\<bullet>t\<close>
| \<open>lift_fm_pro m (\<^bold>\<cdot>P) = \<^bold>\<cdot>(lift_tm m P)\<close>
| \<open>lift_fm_pro m (\<^bold>\<not> p) = \<^bold>\<not> lift_fm_pro m p\<close>
| \<open>lift_fm_pro m (p \<^bold>\<and> q) = (lift_fm_pro m p \<^bold>\<and> lift_fm_pro m q)\<close>
| \<open>lift_fm_pro m (\<^bold>\<box> p) = \<^bold>\<box>(lift_fm_pro m p)\<close>
| \<open>lift_fm_pro m (\<^bold>@i p) = \<^bold>@i (lift_fm_pro m p)\<close>
| \<open>lift_fm_pro m (\<^bold>A p) = \<^bold>A (lift_fm_pro m p)\<close>
| \<open>lift_fm_pro m (\<^bold>\<down> p) = \<^bold>\<down> (lift_fm_pro m p)\<close>
| \<open>lift_fm_pro m (\<^bold>\<forall> p) = \<^bold>\<forall> (lift_fm_pro (m + 1) p)\<close>

primrec sub_pro :: \<open>(nat \<Rightarrow> 'x fm) \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> where
  \<open>sub_pro _ (\<^bold>\<bullet>t) = \<^bold>\<bullet>t\<close>
| \<open>sub_pro s (\<^bold>\<cdot>P) = case_tm s (\<^bold>\<cdot> o \<^bold>\<circle>) P\<close>
| \<open>sub_pro s (\<^bold>\<not> p) = \<^bold>\<not> sub_pro s p\<close>
| \<open>sub_pro s (p \<^bold>\<and> q) = (sub_pro s p \<^bold>\<and> sub_pro s q)\<close>
| \<open>sub_pro s (\<^bold>\<box> p) = \<^bold>\<box>(sub_pro s p)\<close>
| \<open>sub_pro s (\<^bold>@i p) = \<^bold>@i (sub_pro s p)\<close>
| \<open>sub_pro s (\<^bold>A p) = \<^bold>A (sub_pro s p)\<close>
| \<open>sub_pro s (\<^bold>\<down> p) = \<^bold>\<down> (sub_pro (lift_fm_nom 0 o s) p)\<close>
| \<open>sub_pro s (\<^bold>\<forall> p) = \<^bold>\<forall> (sub_pro (\<^bold>\<cdot>(\<^bold>#0) \<then> \<lambda>n. lift_fm_pro 0 (s n)) p)\<close>

abbreviation inst_single_pro :: \<open>'x fm \<Rightarrow> 'x fm \<Rightarrow> 'x fm\<close> (\<open>\<langle>_\<rangle>\<^sub>p\<close>) where
  \<open>\<langle>q\<rangle>\<^sub>p \<equiv> sub_pro (q \<then> \<^bold>\<cdot> o \<^bold>#)\<close>

primrec sz_fm :: \<open>'x fm \<Rightarrow> nat\<close> where
  \<open>sz_fm (\<^bold>\<bullet>t) = 1\<close>
| \<open>sz_fm (\<^bold>\<cdot>P) = 1\<close>
| \<open>sz_fm (\<^bold>\<not> p) = sz_fm p + 1\<close>
| \<open>sz_fm (p \<^bold>\<and> q) = sz_fm p + sz_fm q + 1\<close>
| \<open>sz_fm (\<^bold>\<box> p) = sz_fm p + 1\<close>
| \<open>sz_fm (\<^bold>@i p) = sz_fm p + 1\<close>
| \<open>sz_fm (\<^bold>A p) = sz_fm p + 1\<close>
| \<open>sz_fm (\<^bold>\<down> p) = sz_fm p + 1\<close>
| \<open>sz_fm (\<^bold>\<forall> p) = sz_fm p + 1\<close>

primrec qs_fm :: \<open>'x fm \<Rightarrow> nat\<close> where
  \<open>qs_fm (\<^bold>\<bullet>t) = 0\<close>
| \<open>qs_fm (\<^bold>\<cdot>P) = 0\<close>
| \<open>qs_fm (\<^bold>\<not> p) = qs_fm p\<close>
| \<open>qs_fm (p \<^bold>\<and> q) = max (qs_fm p) (qs_fm q)\<close>
| \<open>qs_fm (\<^bold>\<box> p) = qs_fm p\<close>
| \<open>qs_fm (\<^bold>@i p) = qs_fm p\<close>
| \<open>qs_fm (\<^bold>A p) = qs_fm p\<close>
| \<open>qs_fm (\<^bold>\<down> p) = qs_fm p\<close>
| \<open>qs_fm (\<^bold>\<forall> p) = qs_fm p + 1\<close>

subsection \<open>Lemmas\<close>

subsubsection \<open>Finite\<close>

lemma finite_symbols_tm [simp]: \<open>finite (symbols_tm t)\<close>
  by (induct t) simp_all

lemma finite_symbols_fm [simp]: \<open>finite (symbols_fm p)\<close>
  by (induct p) simp_all

lemma finite_symbols_lbd: \<open>finite (symbols_lbd p)\<close>
  by (cases p) simp

subsubsection \<open>Terms\<close>

lemma env [simp]: \<open>P ((x \<then> E) n) = (P x \<then> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma [simp]: \<open>case_tm (x \<then> e) s (lift_tm 0 t) = case_tm e s t\<close>
  by (induct t) auto

lemma sub_tm_semantics [simp]: \<open>case_tm e g (sub_tm s t) = case_tm (\<lambda>n. case_tm e g (s n)) g t\<close>
  by (induct t) (auto split: tm.splits)

lemma semantics_tm_id [simp]: \<open>case_tm \<^bold># \<^bold>\<circle> t = t\<close>
  by (induct t) auto

lemma semantics_tm_id_map [simp]: \<open>map (case_tm \<^bold># \<^bold>\<circle>) ts = ts\<close>
  by (auto cong: map_cong)

lemma map_tm_sub_tm [simp]: \<open>map_tm f (sub_tm g t) = sub_tm (map_tm f o g) (map_tm f t)\<close>
  by (induct t) simp_all

lemma map_tm_lift_tm [simp]: \<open>map_tm f (lift_tm m t) = lift_tm m (map_tm f t)\<close>
  by (induct t) simp_all

lemma semantics_tm_fresh [simp]: \<open>x \<notin> symbols_tm t \<Longrightarrow> case_tm e (g(x := a)) t = case_tm e g t\<close>
  by (induct t) auto

lemma map_tm_inst_single: \<open>(map_tm f o (u \<then> \<^bold>#)) t = (map_tm f u \<then> \<^bold>#) t\<close>
  by (induct t) auto

subsubsection \<open>Nominals\<close>

lemma size_sub_nom [simp]: \<open>sz_fm (sub_nom s p) = sz_fm p\<close>
  by (induct p arbitrary: s) simp_all

lemma semantics_symbols_cong_nom:
  assumes \<open>\<forall>i \<in> symbols_fm p. N i = N' i\<close>
  shows \<open>(Model W R PI N e V f, w) \<Turnstile> p \<longleftrightarrow> (Model W R PI N' e V f, w) \<Turnstile> p\<close>
  using assms by (induct p arbitrary: e f w) (simp_all split: tm.splits)

corollary semantics_symbols_other_nom [simp]:
  assumes \<open>i \<notin> symbols_fm p\<close>
  shows \<open>(Model W R PI (N(i := x)) e V f, w) \<Turnstile> p \<longleftrightarrow> (Model W R PI N e V f, w) \<Turnstile> p\<close>
  using assms by (simp add: semantics_symbols_cong_nom)

lemma sub_nom_semantics [simp]:
  \<open>(Model W R PI N e V f, w) \<Turnstile> sub_nom s p \<longleftrightarrow> (Model W R PI N (\<lambda>n. case_tm e N (s n)) V f, w) \<Turnstile> p\<close>
  by (induct p arbitrary: e f s w) (simp_all split: tm.splits)

lemma map_fm_sub_nom: \<open>map_fm f (sub_nom s p) = sub_nom (map_tm f o s) (map_fm f p)\<close>
  by (induct p arbitrary: s) (simp_all add: comp_def)

lemma map_fm_inst_single_nom [simp]: \<open>map_fm f (\<langle>t\<rangle>\<^sub>i p) = \<langle>map_tm f t\<rangle>\<^sub>i (map_fm f p)\<close>
  unfolding map_fm_sub_nom map_tm_inst_single ..

subsubsection \<open>Propositions\<close>

lemma semantics_symbols_cong_pro:
  \<open>\<forall>P \<in> symbols_fm p. V P = V' P \<Longrightarrow>
  (Model W R PI N e V f, w) \<Turnstile> p \<longleftrightarrow> (Model W R PI N e V' f, w) \<Turnstile> p\<close>
  by (induct p arbitrary: e f w) (simp_all split: tm.splits)

corollary semantics_symbols_other_pro [simp]:
  assumes \<open>P \<notin> symbols_fm p\<close>
  shows \<open>(Model W R PI N e (V(P := x)) f, w) \<Turnstile> p \<longleftrightarrow> (Model W R PI N e V f, w) \<Turnstile> p\<close>
  using assms by (simp add: semantics_symbols_cong_pro)

lemma semantics_symbols_lbd_cong_pro:
  \<open>\<forall>P \<in> symbols_lbd (i, p). V P = V' P \<Longrightarrow>
  (Model W R PI N e V f, w) \<Turnstile> p \<longleftrightarrow> (Model W R PI N e V' f, w) \<Turnstile> p\<close>
  by (simp add: semantics_symbols_cong_pro)

lemma map_lift_fm_pro [simp]: \<open>map_fm f (lift_fm_pro m p) = lift_fm_pro m (map_fm f p)\<close>
  by (induct p arbitrary: m) simp_all

lemma map_lift_fm_nom [simp]: \<open>map_fm f (lift_fm_nom m p) = lift_fm_nom m (map_fm f p)\<close>
  by (induct p arbitrary: m) simp_all

lemma map_fm_sub_pro: \<open>map_fm f (sub_pro s p) = sub_pro (map_fm f o s) (map_fm f p)\<close>
  by (induct p arbitrary: s) (simp_all add: comp_def split: tm.splits)

lemma map_fm_inst_single: \<open>(map_fm f o (q \<then> \<^bold>\<cdot> o \<^bold>#)) p = (map_fm f q \<then> \<^bold>\<cdot> o \<^bold>#) p\<close>
  by (induct p) auto

lemma map_fm_inst_single_pro [simp]: \<open>map_fm f (\<langle>q\<rangle>\<^sub>p p) = \<langle>map_fm f q\<rangle>\<^sub>p (map_fm f p)\<close>
  unfolding map_fm_sub_pro map_fm_inst_single ..

subsection \<open>softqdf\<close>

lemma softqdf_map_fm [simp]: \<open>softqdf (map_fm f p) \<longleftrightarrow> softqdf p\<close>
  by (induct p) auto

lemma softqdf_lift_fm_nom [simp]: \<open>softqdf (lift_fm_nom m q) \<longleftrightarrow> softqdf q\<close>
  by (induct q arbitrary: m) auto

lemma softqdf_lift_fm_pro [simp]: \<open>softqdf (lift_fm_pro m q) \<longleftrightarrow> softqdf q\<close>
  by (induct q) auto

subsection \<open>Add env\<close>

lemma range_add_env:
  assumes \<open>range f \<subseteq> A\<close> \<open>a \<in> A\<close>
  shows \<open>range (a \<then> f) \<subseteq> A\<close>
proof safe
  fix x n
  show \<open>(a \<then> f) n \<in> A\<close>
    using assms by (induct n) auto
qed

lemma softqdf_add_env: \<open>softqdf q \<Longrightarrow> softqdf_sub (q \<then> \<^bold>\<cdot> o \<^bold>#)\<close>
  by (metis add_env.simps comp_apply not0_implies_Suc softqdf.simps(2))

lemma wf_env_add_nom: \<open>wf_env (Model W R PI N e V f) \<Longrightarrow> w \<in> W \<Longrightarrow>
    wf_env (\<lparr>\<W> = W, \<R> = R, \<Pi> = PI, \<N> = N, \<NN> = w \<then> e, \<V> = V, \<VV> = f\<rparr>)\<close>
  unfolding wf_env_def unfolds using range_add_env by meson
  
lemma wf_model_add_nom: \<open>wf_model (Model W R PI N e V f) \<Longrightarrow> w \<in> W \<Longrightarrow>
    wf_model (\<lparr>\<W> = W, \<R> = R, \<Pi> = PI, \<N> = N, \<NN> = w \<then> e, \<V> = V, \<VV> = f\<rparr>)\<close>
  using wf_env_add_nom unfolding wf_model_def wf_env_def wf_frame_def wf_gframe_def admissible_def unfolds by meson

lemma wf_env_add_pro: \<open>wf_env (Model W R PI N e V f) \<Longrightarrow> P \<in> PI \<Longrightarrow>
    wf_env (\<lparr>\<W> = W, \<R> = R, \<Pi> = PI, \<N> = N, \<NN> = e, \<V> = V, \<VV> = P \<then> f\<rparr>)\<close>
  unfolding wf_env_def unfolds using range_add_env by meson

lemma wf_model_add_pro:
  \<open>wf_model (Model W R PI N e V f) \<Longrightarrow> P \<in> PI \<Longrightarrow> wf_model (Model W R PI N e V (P \<then> f))\<close>
  using wf_env_add_pro unfolding wf_model_def wf_env_def wf_frame_def wf_gframe_def admissible_def unfolds by meson

lemma softqdf_lift_fm_nom_add_env [simp]:
  \<open>softqdf p \<Longrightarrow> (Model W R PI N (v \<then> e) V f, w) \<Turnstile> lift_fm_nom 0 p \<longleftrightarrow> (Model W R PI N e V f, w) \<Turnstile> p\<close>
  by (induct p arbitrary: e w) (simp_all split: tm.splits)

lemma softqdf_lift_fm_pro_add_env [simp]:
  \<open>softqdf p \<Longrightarrow> (Model W R PI N e V (P \<then> f), w) \<Turnstile> lift_fm_pro 0 p \<longleftrightarrow> (Model W R PI N e V f, w) \<Turnstile> p\<close>
  by (induct p arbitrary: e w) (simp_all split: tm.splits)

subsection \<open>Sizes\<close>

lemma qs_fm_sub_nom [simp]: \<open>qs_fm (sub_nom s p) = qs_fm p\<close>
  by (induct p arbitrary: s) auto

lemma softqdf_qs_fm [simp]: \<open>softqdf q \<Longrightarrow> qs_fm q = 0\<close>
  by (induct q) simp_all

lemma softqdf_sub_pro: \<open>softqdf_sub s \<Longrightarrow> softqdf_sub (\<^bold>\<cdot>(\<^bold>#0) \<then> \<lambda>n. lift_fm_pro 0 (s n))\<close>
  by (metis add_env.simps not0_implies_Suc softqdf.simps(2) softqdf_lift_fm_pro)

lemma qs_fm_sub_pro [simp]: \<open>softqdf_sub s \<Longrightarrow> qs_fm (sub_pro s p) = qs_fm p\<close>
proof (induct p arbitrary: s)
  case (All p)
  then show ?case
    using softqdf_sub_pro by force
qed (auto split: tm.splits)

section \<open>Propositional Quantification\<close>

definition worlds :: \<open>('x, 'w) model \<Rightarrow> 'x fm \<Rightarrow> 'w set\<close> where
  \<open>worlds M p \<equiv> { w \<in> \<W> M. (M, w) \<Turnstile> p }\<close>

lemma worlds_op [simp]:
  assumes \<open>wf_model M\<close>
  shows
    \<open>worlds M (\<^bold>\<not> p) = \<W> M - worlds M p\<close>
    \<open>worlds M (p \<^bold>\<and> q) = worlds M p \<inter> worlds M q\<close>
    \<open>worlds M (\<^bold>\<box> p) = {w \<in> \<W> M. \<forall>v \<in> \<R> M w. v \<in> worlds M p}\<close>
  using assms unfolding worlds_def wf_model_def wf_frame_def wf_gframe_def unfolds by auto

lemma softqdf_worlds:
  assumes \<open>wf_model M\<close> \<open>softqdf p\<close>
  shows \<open>worlds M p \<in> \<Pi> M\<close>
  using assms
proof (induct p)
  case (TmI x)
  then show ?case
    by simp
next
  case (TmP x)
  then have \<open>\<V> M P \<in> \<Pi> M\<close> \<open>\<VV> M n \<in> \<Pi> M\<close> for P n
    using wf_\<V> wf_\<VV> by fastforce+
  moreover have \<open>\<W> M \<in> \<Pi> M\<close>
    using TmP wf_univ by fastforce
  ultimately have \<open>\<V> M P \<inter> \<W> M \<in> \<Pi> M\<close> \<open>\<VV> M n \<inter> \<W> M \<in> \<Pi> M\<close> for P n
    using TmP wf_inter by fastforce+
  then have \<open>{w \<in> \<W> M. w \<in> \<V> M P} \<in> \<Pi> M\<close> \<open>{w \<in> \<W> M. w \<in> \<VV> M n} \<in> \<Pi> M\<close> for P n
    by (metis Int_def inf_commute)+
  then show ?case
    unfolding worlds_def
    by (auto split: tm.splits)
next
  case (Neg p)
  then show ?case
    by (simp add: wf_compl)
next
  case (Con p q)
  then show ?case
    by (simp add: wf_inter)
next
  case (Box p)
  then show ?case
    by (simp add: wf_modal)
next
  case (Sat k p)
  then have \<open>(\<forall>w. (M, w) \<Turnstile> \<^bold>@k p) \<or> (\<nexists>w. (M, w) \<Turnstile> \<^bold>@k p)\<close>
    by (auto split: tm.splits)
  then have \<open>worlds M (\<^bold>@k p) = {} \<or> worlds M (\<^bold>@k p) = \<W> M\<close>
    unfolding worlds_def by blast
  then show ?case
    using Sat(2) wf_univ wf_empty by fastforce
next
  case (Glo p)
  then have \<open>(\<forall>w. (M, w) \<Turnstile> \<^bold>A p) \<or> (\<nexists>w. (M, w) \<Turnstile> \<^bold>A p)\<close>
    by auto
  then have \<open>worlds M (\<^bold>A p) = {} \<or> worlds M (\<^bold>A p) = \<W> M\<close>
    unfolding worlds_def by blast
  then show ?case
    using Glo(2) wf_univ wf_empty by fastforce
next
  case (Dwn p)
  then show ?case
    by simp
next
  case (All p)
  then show ?case
    by simp
qed

definition sqdfs :: \<open>('x, 'w) model \<Rightarrow> 'w set set\<close> where
  \<open>sqdfs M \<equiv> { worlds M p |p. softqdf p }\<close>

lemma sqdfs:
  assumes \<open>wf_model M\<close>
  shows \<open>sqdfs M \<subseteq> \<Pi> M\<close>
  unfolding sqdfs_def using assms softqdf_worlds by blast

lemma sqdfs_admissible:
  assumes \<open>wf_model M\<close>
  shows \<open>admissible (frame.truncate M) (sqdfs M)\<close>
  unfolding admissible_def
proof safe
  fix X
  assume \<open>X \<in> sqdfs M\<close>
  then obtain p where \<open>X = worlds M p\<close> \<open>softqdf p\<close>
    unfolding sqdfs_def by fast
  moreover from this have \<open>worlds M (\<^bold>\<not> p) \<in> sqdfs M\<close>
    unfolding sqdfs_def by auto
  ultimately show \<open>\<W> (frame.truncate M) - X \<in> sqdfs M\<close>
    unfolding sqdfs_def unfolds using assms by simp
next
  fix X Y
  assume \<open>X \<in> sqdfs M\<close> \<open>Y \<in> sqdfs M\<close>
  then obtain p q where \<open>X = worlds M p\<close> \<open>softqdf p\<close> \<open>Y = worlds M q\<close> \<open>softqdf q\<close>
    unfolding sqdfs_def by fast
  moreover from this have \<open>worlds M (p \<^bold>\<and> q) \<in> sqdfs M\<close>
    unfolding sqdfs_def by auto
  ultimately show \<open>X \<inter> Y \<in> sqdfs M\<close>
    unfolding sqdfs_def using assms by simp
next
  fix X
  assume \<open>X \<in> sqdfs M\<close>
  then obtain p where \<open>X = worlds M p\<close> \<open>softqdf p\<close>
    unfolding sqdfs_def by fast
  moreover from this have \<open>worlds M (\<^bold>\<box> p) \<in> sqdfs M\<close>
    unfolding sqdfs_def by auto
  ultimately show \<open>{w \<in> \<W> (frame.truncate M). \<forall>v \<in> \<R> (frame.truncate M) w. v \<in> X} \<in> sqdfs M\<close>
    unfolding sqdfs_def unfolds using assms by simp
qed

definition with_worlds :: \<open>('x, 'w) model \<Rightarrow> (nat \<Rightarrow> 'x fm)  \<Rightarrow> ('x, 'w) model\<close> where
  \<open>with_worlds M s \<equiv> M\<lparr>\<VV> := worlds M o s\<rparr>\<close>

lemma sub_pro_with_worlds:
  assumes \<open>wf_model (Model W R PI N e V f)\<close> \<open>w \<in> W\<close> \<open>softqdf_sub s\<close>
  shows \<open>(Model W R PI N e V f, w) \<Turnstile> sub_pro s p \<longleftrightarrow> (with_worlds (Model W R PI N e V f) s, w) \<Turnstile> p\<close>
  using assms
proof (induct p arbitrary: s e f w)
  case (Box p)
  moreover from this have \<open>v \<in> R w \<Longrightarrow> v \<in> W\<close> for v
    unfolding wf_model_def wf_gframe_def wf_frame_def unfolds by auto
  ultimately show ?case
    unfolding with_worlds_def by simp
next
  case (Sat x p)
  moreover from this have \<open>case_tm e N x \<in> W\<close>
    unfolding wf_model_def wf_env_def
    by (auto split: tm.splits)
  ultimately show ?case
    unfolding with_worlds_def
    by (simp split: tm.splits)
next
  case (Dwn p)
  let ?s = \<open>lift_fm_nom 0 o s\<close>

  have \<open>wf_model (Model W R PI N (w \<then> e) V f)\<close>
    using Dwn by (simp add: wf_model_add_nom)
  moreover have \<open>softqdf_sub ?s\<close>
    using Dwn by simp
  ultimately have \<open>(Model W R PI N (w \<then> e) V f, w) \<Turnstile> sub_pro ?s p \<longleftrightarrow>
      (with_worlds (Model W R PI N (w \<then> e) V f) ?s, w) \<Turnstile> p\<close>
    using Dwn by fastforce
  moreover have \<open>worlds (Model W R PI N (w \<then> e) V f) o ?s = worlds (Model W R PI N e V f) o s\<close>
    unfolding worlds_def comp_def using Dwn(4) by simp
  ultimately have *: \<open>(Model W R PI N (w \<then> e) V f, w) \<Turnstile> sub_pro ?s p \<longleftrightarrow>
      (Model W R PI N (w \<then> e) V (worlds (Model W R PI N e V f) \<circ> s), w) \<Turnstile> p\<close>
    unfolding with_worlds_def by simp

  moreover have \<open>(with_worlds (Model W R PI N e V f) ?s, w) \<Turnstile> \<^bold>\<down> p \<longleftrightarrow>
      (Model W R PI N (w \<then> e) V (worlds (Model W R PI N e V f) o ?s), w) \<Turnstile> p\<close>
    unfolding with_worlds_def by simp
  then have ** :\<open>(with_worlds (Model W R PI N e V f) ?s, w) \<Turnstile> \<^bold>\<down> p \<longleftrightarrow>
      (Model W R PI N (w \<then> e) V (worlds (Model W R PI N e V f) o ?s), w) \<Turnstile> p\<close>
    by metis

  ultimately show ?case
    unfolding with_worlds_def by simp
next
  case (All p)
  let ?s = \<open>\<^bold>\<cdot>(\<^bold>#0) \<then> \<lambda>n. lift_fm_pro 0 (s n)\<close>

  have \<open>softqdf (?s n)\<close>  for n
    using All(4) by (induct n) auto
  then have \<open>softqdf_sub ?s\<close>
    by blast
  moreover have \<open>\<forall>P \<in> PI. wf_model (Model W R PI N e V (P \<then> f))\<close>
    using All(2) wf_model_add_pro by blast
  ultimately have \<open>(\<forall>P \<in> PI. (Model W R PI N e V (P \<then> f), w) \<Turnstile> sub_pro ?s p) \<longleftrightarrow>
    (\<forall>P \<in> PI. (with_worlds (Model W R PI N e V (P \<then> f)) ?s, w) \<Turnstile> p)\<close>
    using All by blast

  moreover have \<open>\<forall>P \<in> PI. P \<subseteq> W\<close>
    using All(2) unfolding wf_model_def wf_gframe_def unfolds by blast
  then have \<open>P \<in> PI \<Longrightarrow>
    (worlds (Model W R PI N e V (P \<then> f)) o ?s) n = (P \<then> worlds (Model W R PI N e V f) o s) n\<close> for P n
    unfolding worlds_def using All(4) by (induct n) auto
  then have \<open>P \<in> PI \<Longrightarrow>
      (worlds (Model W R PI N e V (P \<then> f)) o ?s) = (P \<then> worlds (Model W R PI N e V f) o s)\<close> for P
    by blast

  ultimately show ?case
    unfolding with_worlds_def by simp
qed (simp_all add: worlds_def with_worlds_def split: tm.splits)

lemma worlds_id_sub:
 assumes \<open>wf_model (Model W R PI N e V f)\<close>
 shows \<open>worlds (Model W R PI N e V f) (\<^bold>\<cdot> (\<^bold># n)) = f n\<close>
  using wf_\<VV>'[OF assms] unfolding worlds_def unfolds by auto

lemma worlds_inst_single_pro:
  assumes \<open>wf_model (Model W R PI N e V f)\<close>
  shows \<open>worlds (Model W R PI N e V f) o (q \<then> \<^bold>\<cdot> o \<^bold>#) = (worlds (Model W R PI N e V f) q \<then> f)\<close>
  unfolding comp_def env worlds_id_sub[OF assms] ..

corollary inst_single_worlds:
  assumes \<open>wf_model (Model W R PI N e V f)\<close> \<open>w \<in> W\<close> \<open>softqdf q\<close>
  shows
    \<open>(Model W R PI N e V f, w) \<Turnstile> \<langle>q\<rangle>\<^sub>p p \<longleftrightarrow>
     (Model W R PI N e V (worlds (Model W R PI N e V f) q \<then> f), w) \<Turnstile> p\<close>
proof -
  have
    \<open>(Model W R PI N e V f, w) \<Turnstile> \<langle>q\<rangle>\<^sub>p p \<longleftrightarrow>
     (Model W R PI N e V (worlds (Model W R PI N e V f) o (q \<then> \<^bold>\<cdot> o \<^bold>#)), w) \<Turnstile> p\<close>
    using sub_pro_with_worlds[OF assms(1-2)] assms(3) unfolding with_worlds_def
    by (metis model.update_convs(4) softqdf_add_env)
  then show ?thesis
    using assms worlds_inst_single_pro by metis
qed

section \<open>Model Existence\<close>

inductive confl_class :: \<open>'x lbd list \<Rightarrow> 'x lbd list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CNegP: \<open>[ (i, \<^bold>\<not> \<^bold>\<cdot>P) ] \<leadsto>\<^sub>\<crossmark> [(i, \<^bold>\<cdot>P)]\<close>
| CNegI: \<open>[ (i, \<^bold>\<not> \<^bold>\<bullet>k) ] \<leadsto>\<^sub>\<crossmark> [(i, \<^bold>\<bullet>k)]\<close>

inductive alpha_class :: \<open>'x lbd list \<Rightarrow> 'x lbd list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
  CSym: \<open>[ (i, \<^bold>\<bullet>k) ] \<leadsto>\<^sub>\<alpha> [(k, \<^bold>\<bullet>i)]\<close>
| CNom: \<open>[ (i, \<^bold>\<bullet>k), (i, p) ] \<leadsto>\<^sub>\<alpha> [(k, p)]\<close>
| CNegN: \<open>[ (i, \<^bold>\<not> \<^bold>\<not> p) ] \<leadsto>\<^sub>\<alpha> [(i, p)]\<close>
| CConP: \<open>[ (i, p \<^bold>\<and> q) ] \<leadsto>\<^sub>\<alpha> [(i, p), (i, q)]\<close>
| CSatP: \<open>[ (i, \<^bold>@k p) ] \<leadsto>\<^sub>\<alpha> [(k, p)]\<close>
| CSatN: \<open>[ (i, \<^bold>\<not> \<^bold>@k p) ] \<leadsto>\<^sub>\<alpha> [(k, \<^bold>\<not> p)]\<close>
| CBoxP: \<open>[ (i, \<^bold>\<box>p), (i, \<^bold>\<diamond>(\<^bold>\<bullet>k)) ] \<leadsto>\<^sub>\<alpha> [(k, p)]\<close>
| CDwnP: \<open>[ (i, \<^bold>\<down> p) ] \<leadsto>\<^sub>\<alpha> [ (i, \<langle>i\<rangle>\<^sub>i p) ]\<close>
| CDwnN: \<open>[ (i, \<^bold>\<not> \<^bold>\<down> p) ] \<leadsto>\<^sub>\<alpha> [ (i, \<^bold>\<not> \<langle>i\<rangle>\<^sub>i p) ]\<close>

inductive beta_class :: \<open>'x lbd list \<Rightarrow> 'x lbd list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>[ (i, \<^bold>\<not> (p \<^bold>\<and> q)) ] \<leadsto>\<^sub>\<beta> [(i, \<^bold>\<not> p), (i, \<^bold>\<not> q)]\<close>

inductive gamma_class_nom :: \<open>'x lbd list \<Rightarrow> ('x tm \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>i\<close> 50) where
  CRefl: \<open>[] \<leadsto>\<^sub>\<gamma>\<^sub>i (\<lambda>i. [ (i, \<^bold>\<bullet>i) ])\<close>
| CGloP: \<open>[ (i, \<^bold>A p) ] \<leadsto>\<^sub>\<gamma>\<^sub>i (\<lambda>k. [ (k, p) ])\<close>
  
inductive gamma_class_fm :: \<open>'x lbd list \<Rightarrow> ('x lbd set \<Rightarrow> 'x fm set) \<times> ('x fm \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>p\<close> 50) where
  CAllP: \<open>[ (i, \<^bold>\<forall> p) ] \<leadsto>\<^sub>\<gamma>\<^sub>p (\<lambda>_. {q. softqdf q}, \<lambda>q. [ (i, \<langle>q\<rangle>\<^sub>p p) ])\<close>

fun \<delta> :: \<open>'x lbd \<Rightarrow> 'x \<Rightarrow> 'x lbd list\<close> where
  CBoxN: \<open>\<delta> (i, \<^bold>\<not> \<^bold>\<box>p) k = [(\<^bold>\<circle>k, \<^bold>\<not> p), (i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle> k)))]\<close>
| CGloN: \<open>\<delta> (i, \<^bold>\<not> \<^bold>A p) k = [ (\<^bold>\<circle>k, \<^bold>\<not> p) ]\<close>
| CAllN: \<open>\<delta> (i, \<^bold>\<not> \<^bold>\<forall> p) P = [ (i, \<^bold>\<not> \<langle>\<^bold>\<cdot>(\<^bold>\<circle>P)\<rangle>\<^sub>p p) ]\<close>
| \<open>\<delta> _ _ = []\<close>

interpretation P: Params map_lbd symbols_lbd \<open>\<lambda>_. True\<close>
  by unfold_locales (auto simp: tm.map_id0 fm.map_id0 cong: tm.map_cong0 fm.map_cong0)

interpretation C: Confl map_lbd symbols_lbd \<open>\<lambda>_. True\<close> confl_class
  by unfold_locales (auto elim!: confl_class.cases intro: confl_class.intros)

interpretation A: Alpha map_lbd symbols_lbd \<open>\<lambda>_. True\<close> alpha_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: alpha_class.cases intro: alpha_class.intros)

interpretation B: Beta map_lbd symbols_lbd \<open>\<lambda>_. True\<close> beta_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: beta_class.cases intro: beta_class.intros)

interpretation GI: Gamma_UNIV map_tm map_lbd symbols_lbd \<open>\<lambda>_. True\<close> gamma_class_nom
  by unfold_locales (fastforce elim: gamma_class_nom.cases intro: gamma_class_nom.intros)+

interpretation GP: Gamma map_fm map_lbd symbols_lbd \<open>\<lambda>_. True\<close> gamma_class_fm
  by unfold_locales (fastforce elim: gamma_class_fm.cases intro: gamma_class_fm.intros)+

interpretation D: Delta map_lbd symbols_lbd \<open>\<lambda>_. True\<close> \<delta>
proof
  show \<open>\<And>f. \<delta> (map_lbd f p) (f x) = map (map_lbd f) (\<delta> p x)\<close> for p :: \<open>'x lbd\<close> and x
    by (induct p x rule: \<delta>.induct) simp_all
qed

abbreviation Kinds :: \<open>('x, 'x lbd) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, GI.kind, GP.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>P.sat\<^sub>E C.kind C\<close> \<open>P.sat\<^sub>E A.kind C\<close> \<open>P.sat\<^sub>E B.kind C\<close> \<open>P.sat\<^sub>E GI.kind C\<close> \<open>P.sat\<^sub>E GP.kind C\<close> \<open>P.sat\<^sub>E D.kind C\<close>
  shows \<open>P.prop\<^sub>E Kinds C\<close>
  unfolding P.prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_lbd symbols_lbd \<open>\<lambda>_. True\<close> Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    GI.Consistency_Kind_axioms GP.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_lbd symbols_lbd \<open>\<lambda>_. True\<close> Kinds
proof
 have \<open>infinite (UNIV :: 'x fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
  then show \<open>infinite (UNIV :: 'x lbd set)\<close>
    using finite_prod by blast
qed simp

context begin

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<cdot>P) \<notin> S \<or> (i, \<^bold>\<not> \<^bold>\<cdot>P) \<notin> S\<close>
  using sat\<^sub>E[of C.kind] by (force intro: CNegP)

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, p \<^bold>\<and> q) \<in> S \<Longrightarrow> {(i, p), (i, q)} \<union> S \<in> C\<close>
  using sat\<^sub>E[of A.kind] by (force intro: CConP)

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<not> (p \<^bold>\<and> q)) \<in> S \<Longrightarrow> {(i, \<^bold>\<not> p)} \<union> S \<in> C \<or> {(i, \<^bold>\<not> q)} \<union> S \<in> C\<close>
  using sat\<^sub>E[of B.kind] by (force intro: CConN)
  
lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<box> p) \<in> S \<Longrightarrow> (i, \<^bold>\<diamond>(\<^bold>\<bullet>k)) \<in> S \<Longrightarrow> {(k, p)} \<union> S \<in> C\<close>
  using sat\<^sub>E[of A.kind] by (force intro: CBoxP)

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<not> \<^bold>\<box>p) \<in> S \<Longrightarrow> \<exists>k. {(k, \<^bold>\<not> p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k))} \<union> S \<in> C\<close>
  using sat\<^sub>E[of D.kind] by fastforce
  
lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> { (i, \<^bold>\<bullet>i) } \<union> S \<in> C\<close>
  using sat\<^sub>E[of GI.kind] by (force intro: CRefl)

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>A p) \<in> S \<Longrightarrow> { (k, p) } \<union> S \<in> C\<close>
  using sat\<^sub>E[of GI.kind] by (force intro: CGloP)
 
lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<not> \<^bold>A p) \<in> S \<Longrightarrow> \<exists>k. { (k, \<^bold>\<not> p) } \<union> S \<in> C\<close>
  using sat\<^sub>E[of D.kind] by fastforce

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<forall> p) \<in> S \<Longrightarrow> softqdf q \<Longrightarrow> { (i, \<langle>q\<rangle>\<^sub>p p) } \<union> S \<in> C\<close>
  using sat\<^sub>E[of GP.kind] by (force intro: CAllP)

lemma \<open>P.prop\<^sub>E Kinds C \<Longrightarrow> S \<in> C \<Longrightarrow> (i, \<^bold>\<not> \<^bold>\<forall> p) \<in> S \<Longrightarrow> \<exists>P. { (i, \<^bold>\<not> \<langle>\<^bold>\<cdot>(\<^bold>\<circle>P)\<rangle>\<^sub>p p) } \<union> S \<in> C\<close>
  using sat\<^sub>E[of D.kind] by fastforce

end

definition equiv_nom :: \<open>'x lbd set \<Rightarrow> 'x tm \<Rightarrow> 'x tm \<Rightarrow> bool\<close> where
  \<open>equiv_nom S i k \<equiv> (i, \<^bold>\<bullet>k) \<in> S\<close>

definition assign :: \<open>'x tm \<Rightarrow> 'x lbd set \<Rightarrow> 'x tm\<close> (\<open>[_]\<^sub>_\<close> [0, 100] 100) where
  \<open>[i]\<^sub>S \<equiv> wo_rel.minim ( |UNIV| ) {k. equiv_nom S i k}\<close>

definition reach :: \<open>'x lbd set \<Rightarrow> 'x tm \<Rightarrow> 'x tm set\<close> where
  \<open>reach S i \<equiv> {[k]\<^sub>S |k. (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S}\<close>

definition val :: \<open>'x lbd set \<Rightarrow> 'x tm \<Rightarrow> 'x tm set\<close> where
  \<open>val S P \<equiv> {[i]\<^sub>S |i. (i, \<^bold>\<cdot>P) \<in> S}\<close>

lemma range_val_ne: \<open>range (val S) \<noteq> {}\<close>
  unfolding val_def by blast

lemma admissible_Pow: \<open>admissible F (Pow (\<W> F))\<close>
  unfolding admissible_def by blast

definition admits :: \<open>'w frame \<Rightarrow> 'w set set \<Rightarrow> 'w set set \<Rightarrow> bool\<close> where
  \<open>admits F B PI \<equiv> PI \<noteq> {} \<and> PI \<subseteq> Pow (\<W> F) \<and> B \<subseteq> PI \<and> admissible F PI\<close>

definition adm_\<delta> :: \<open>'w frame \<Rightarrow> 'w set set \<Rightarrow> 'w set set\<close> where
  \<open>adm_\<delta> M PI \<equiv>
    { \<W> M - X | X. X \<in> PI } \<union>
    { X \<inter> Y | X Y. X \<in> PI \<and> Y \<in> PI } \<union>
    { {w \<in> \<W> M. \<forall>v \<in> \<R> M w. v \<in> X} | X. X \<in> PI }\<close>

abbreviation \<open>grow F B \<equiv> \<lambda>PI. B \<union> PI \<union> adm_\<delta> F (B \<union> PI)\<close>

definition admit :: \<open>'w frame \<Rightarrow> 'w set set \<Rightarrow> 'w set set\<close> where
  \<open>admit F B \<equiv> lfp (grow F B)\<close>

lemma mono_grow: \<open>mono (grow F B)\<close>
  unfolding adm_\<delta>_def mono_def by (auto simp: subset_eq)

lemma admissible_\<delta>: \<open>admissible F B \<longleftrightarrow> adm_\<delta> F B \<subseteq> B\<close>
  unfolding admissible_def adm_\<delta>_def by auto

lemma admit_B: \<open>B \<subseteq> admit F B\<close>
  unfolding admit_def by (meson le_sup_iff lfp_greatest)

lemma admit_Pow: \<open>B \<subseteq> Pow (\<W> F) \<Longrightarrow> admit F B \<subseteq> Pow (\<W> F)\<close>
  unfolding admit_def using admissible_Pow admissible_\<delta> lfp_lowerbound 
  by (metis (no_types, lifting) order_class.order_eq_iff subset_Un_eq sup.absorb_iff1)

lemma admissible_grow: \<open>admissible F B \<longleftrightarrow> grow F B B = B\<close>
  using admissible_\<delta> by auto

lemma lfp_grow: \<open>grow F B (lfp (grow F B)) = lfp (grow F B)\<close>
  using lfp_unfold mono_grow by blast

lemma admit_admissible: \<open>admissible F (admit F B)\<close>
  unfolding admit_def
proof -
  have "B \<union> lfp (grow F B) = lfp (grow F B)"
    using lfp_grow by blast
  then show "admissible F (lfp (grow F B))"
    using lfp_grow[of B F] by (simp add: admissible_\<delta> sup.order_iff)
qed

lemma admits_admit: \<open>B \<noteq> {} \<Longrightarrow> B \<subseteq> Pow (\<W> F) \<Longrightarrow> admits F B (admit F B)\<close>
  by (metis admit_B admit_Pow admit_admissible admits_def subset_empty)

lemma admissible_admit:
  assumes \<open>B \<noteq> {}\<close> \<open>B \<subseteq> Pow (\<W> F)\<close>
  shows
    \<open>admit F B \<noteq> {}\<close>
    \<open>admit F B \<subseteq> Pow (\<W> F)\<close>
    \<open>admissible F (admit F B)\<close>
  using assms admits_admit unfolding admits_def by metis+

abbreviation canonical_frame :: \<open>'x lbd set \<Rightarrow> ('x tm) frame\<close> where
  \<open>canonical_frame S \<equiv> \<lparr> \<W> = {[k]\<^sub>S | k. True}, \<R> = reach S \<rparr>\<close>

abbreviation canonical_gframe :: \<open>'x lbd set \<Rightarrow> ('x tm) gframe\<close> where
  \<open>canonical_gframe S \<equiv> frame.extend (canonical_frame S)
    \<lparr> \<Pi> = admit (canonical_frame S) (range (val S)) \<rparr>\<close>

definition canonical :: \<open>'x lbd set \<Rightarrow> ('x, 'x tm) model\<close> where
  \<open>canonical S \<equiv>
    gframe.extend (canonical_gframe S)
     \<lparr> \<N> = \<lambda>i. [\<^bold>\<circle>i]\<^sub>S,
       \<NN> = \<lambda>i. [\<^bold>#i]\<^sub>S,
       \<V> = val S o \<^bold>\<circle>,
       \<VV> = val S o \<^bold>#
     \<rparr>\<close>

lemma wf_canonical_frame: \<open>wf_frame (canonical_frame S)\<close>
  unfolding wf_frame_def unfolds reach_def by auto

lemma val_Pow: \<open>range (val S) \<subseteq> Pow (\<W> (canonical_frame S))\<close>
  unfolding val_def by auto

lemma wf_cannonical_gframe: \<open>wf_gframe (canonical_gframe S)\<close>
  unfolding wf_gframe_def unfolds using wf_canonical_frame admissible_admit(2) admit_B admit_admissible
  by (metis (mono_tags, lifting) frame.select_convs(1) range_val_ne subset_empty val_Pow)

lemma admits_val: \<open>admits (canonical_frame S) (range (val S)) PI \<Longrightarrow> val S P \<in> PI\<close>
  unfolding admits_def by blast 

lemma admit_val: \<open>val S P \<in> admit (canonical_frame S) (range (val S))\<close>
  using admits_val admits_admit val_Pow by (simp add: admit_B range_subsetD)
 
lemma wf_canonical_env: \<open>wf_env (canonical S)\<close>
  unfolding wf_env_def canonical_def unfolds using admit_val by auto

lemma wf_gframe_canonical: \<open>wf_gframe (gframe.truncate (canonical S))\<close>
  using wf_cannonical_gframe unfolding canonical_def unfolds .
 
lemma wf_canonical: \<open>wf_model (canonical S)\<close>
  unfolding wf_model_def using wf_gframe_canonical wf_canonical_env by blast  

lemma admissible_sqdfs: \<open>admissible (canonical_frame S) (sqdfs (canonical S))\<close>
  using sqdfs_admissible[OF wf_canonical[of S]]
  unfolding canonical_def unfolds .

lemma sqdfs_Pow: \<open>sqdfs (canonical S) \<subseteq> Pow (\<W> (canonical_frame S))\<close>
  unfolding sqdfs_def canonical_def unfolds worlds_def by blast

lemma val_sqdfs: \<open>val S P \<in> sqdfs (canonical S)\<close>
  unfolding val_def sqdfs_def canonical_def unfolds worlds_def
  by (auto split: tm.splits intro!: exI[of _ \<open>\<^bold>\<cdot> P\<close>])

lemma admits_canonical_sqdfs: \<open>admits (canonical_frame S) (range (val S)) (sqdfs (canonical S))\<close>
  unfolding admits_def using admissible_sqdfs sqdfs_Pow val_sqdfs by blast

definition canonical_ctx :: \<open>'x lbd set \<Rightarrow> 'x tm \<Rightarrow> ('x, 'x tm) ctx\<close> (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>S, i\<rbrakk> \<equiv> (canonical S, [i]\<^sub>S)\<close>

lemma sqdfs_canonical: \<open>sqdfs (canonical S) = \<Pi> (canonical S)\<close>
proof
  show \<open>sqdfs (canonical S) \<subseteq> \<Pi> (canonical S)\<close>
    using sqdfs wf_canonical by blast
next
  have \<open>grow (canonical_frame S) (range (val S)) (sqdfs (canonical S)) \<subseteq> sqdfs (canonical S)\<close>
    using admissible_grow[of \<open>canonical_frame S\<close> \<open>sqdfs _\<close>] admits_canonical_sqdfs[of S] unfolding admits_def 
    by (metis (no_types, lifting) equalityE le_iff_sup)
  then have \<open>admit (canonical_frame S) (range (val S)) \<subseteq> sqdfs (canonical S)\<close>
    by (simp add: admit_def lfp_lowerbound)
  then show \<open>\<Pi> (canonical S) \<subseteq> sqdfs (canonical S)\<close>
    unfolding canonical_def unfolds .
qed

lemma canonical_tm_eta [simp]: \<open>case_tm (\<lambda>i. [\<^bold># i]\<^sub>S) (\<lambda>n. [\<^bold>\<circle> n]\<^sub>S) k = [k]\<^sub>S\<close>
  by (cases k) simp_all

corollary canonical_tm_eta' [simp]: \<open>case_tm (\<NN> (canonical S)) (\<N> (canonical S)) k = [k]\<^sub>S\<close>
  unfolding canonical_def unfolds by simp

locale MyHintikka = Hintikka map_lbd symbols_lbd \<open>\<lambda>_. True\<close> Kinds S
  for S :: \<open>'x lbd set\<close>
begin

lemmas
  confl = sat\<^sub>H[of C.kind] and
  alpha = sat\<^sub>H[of A.kind] and
  beta = sat\<^sub>H[of B.kind] and
  gammaI = sat\<^sub>H[of GI.kind] and
  gammaP = sat\<^sub>H[of GP.kind] and
  \<delta> = sat\<^sub>H[of D.kind]

lemma Nom_refl: \<open>(i, \<^bold>\<bullet>i) \<in> S\<close>
  using gammaI by (fastforce intro: CRefl)

lemma Nom_sym:
  assumes \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(k, \<^bold>\<bullet>i) \<in> S\<close>
  using assms alpha by (fastforce intro: CSym)

lemma Nom_trans:
  assumes \<open>(i, \<^bold>\<bullet>j) \<in> S\<close> \<open>(j, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
  using assms 
proof -
  have \<open>(j, \<^bold>\<bullet>i) \<in> S\<close>
    using assms Nom_sym by blast
  then show ?thesis
    using assms(2) alpha by (fastforce intro: CNom)
qed

lemma equiv_nom_ne: \<open>{k. equiv_nom S i k} \<noteq> {}\<close>
  unfolding equiv_nom_def using Nom_refl by blast

lemma equiv_nom_assign: \<open>equiv_nom S i ([i]\<^sub>S)\<close>
  unfolding assign_def using equiv_nom_ne 
  by (metis Field_card_of card_of_well_order_on mem_Collect_eq top.extremum wo_rel_def wo_rel.minim_in)

lemma equiv_nom_Nom:
  assumes \<open>equiv_nom S i k\<close> \<open>(i, p) \<in> S\<close>
  shows \<open>(k, p) \<in> S\<close>
proof -
  have \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
    using assms unfolding equiv_nom_def by blast
  then show ?thesis
    using assms alpha by (fastforce intro: CNom)
qed

lemma assign_in_W: \<open>[i]\<^sub>S \<in> \<W> (canonical S)\<close>
  unfolding canonical_def gframe.defs frame.defs unfolds by blast

theorem model: \<open>((i, p) \<in> S \<longrightarrow> \<lbrakk>S, i\<rbrakk> \<Turnstile> p) \<and> ((i, \<^bold>\<not> p) \<in> S \<longrightarrow> \<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> p)\<close>
proof (induct p arbitrary: i rule: wf_induct[where r=\<open>measures [qs_fm, sz_fm]\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case (TmI k)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<bullet>k\<close> \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
      moreover from this have \<open>(k, \<^bold>\<bullet>i) \<in> S\<close>
        using Nom_sym by fast
      ultimately have \<open>[i]\<^sub>S = [k]\<^sub>S\<close>
        using Nom_trans unfolding assign_def equiv_nom_def by metis
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<bullet>k\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by (simp split: tm.splits)
    next
      assume \<open>x = \<^bold>\<bullet>k\<close> \<open>(i, \<^bold>\<not> \<^bold>\<bullet>k) \<in> S\<close>
      then have \<open>(i, \<^bold>\<bullet>k) \<notin> S\<close>
        using confl by (fastforce intro: CNegI)
      then have \<open>\<not> equiv_nom S i k\<close>
        unfolding equiv_nom_def by blast
      moreover have \<open>(i, \<^bold>\<bullet>k) \<notin> S\<close>
        using \<open>(i, \<^bold>\<not> \<^bold>\<bullet>k) \<in> S\<close> using confl by (fastforce intro: CNegI)
      ultimately have \<open>[i]\<^sub>S \<noteq> [k]\<^sub>S\<close>
        using Nom_sym Nom_trans equiv_nom_assign unfolding equiv_nom_def by metis
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<bullet>k\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by (auto split: tm.splits)
    qed
  next
    case (TmP P)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<cdot>P\<close> \<open>(i, \<^bold>\<cdot>P) \<in> S\<close>
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<cdot>P\<close>
        unfolding canonical_ctx_def canonical_def val_def gframe.defs
        by (auto split: tm.splits)
    next
      assume \<open>x = \<^bold>\<cdot>P\<close> \<open>(i, \<^bold>\<not> \<^bold>\<cdot>P) \<in> S\<close>
      then have \<open>(i, \<^bold>\<cdot>P) \<notin> S\<close>
        using confl by (fastforce intro: CNegP)
      then have \<open>\<And>k. [k]\<^sub>S = [i]\<^sub>S \<Longrightarrow> (k, \<^bold>\<cdot>P) \<notin> S\<close>
        by (metis Nom_refl equiv_nom_Nom equiv_nom_assign equiv_nom_def)
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<cdot>P\<close>
        unfolding canonical_ctx_def canonical_def val_def gframe.defs
        by (auto split: tm.splits)
    qed
  next
    case (Neg p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<not> p\<close> \<open>(i, \<^bold>\<not> p) \<in> S\<close>
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<not> p\<close>
        using 2 unfolding canonical_ctx_def by simp
    next
      assume \<open>x = \<^bold>\<not> p\<close> \<open>(i, \<^bold>\<not> \<^bold>\<not> p) \<in> S\<close>
      then have \<open>(i, p) \<in> S\<close>
        using alpha by (fastforce intro: CNegN)
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<not> p\<close>
        using 2 Neg unfolding canonical_ctx_def by auto
    qed
  next
    case (Con p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = (p \<^bold>\<and> q)\<close> \<open>(i, p \<^bold>\<and> q) \<in> S\<close>
      then have \<open>(i, p) \<in> S \<and> (i, q) \<in> S\<close>
        using alpha by (fastforce intro: CConP)
      moreover have
        \<open>(p, x) \<in> measures [qs_fm, sz_fm]\<close>
        \<open>(q, x) \<in> measures [qs_fm, sz_fm]\<close>
        using Con by auto
      ultimately show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> (p \<^bold>\<and> q)\<close>
        using 2 unfolding canonical_ctx_def by auto
    next
      assume \<open>x = (p \<^bold>\<and> q)\<close> \<open>(i, \<^bold>\<not> (p \<^bold>\<and> q)) \<in> S\<close>
      then have \<open>(i, \<^bold>\<not> p) \<in> S \<or> (i, \<^bold>\<not> q) \<in> S\<close>
        using beta by (fastforce intro: CConN)
      moreover have
        \<open>(\<^bold>\<not> p, \<^bold>\<not> x) \<in> measures [qs_fm, sz_fm]\<close>
        \<open>(\<^bold>\<not> q, \<^bold>\<not> x) \<in> measures [qs_fm, sz_fm]\<close>
        using Con by auto
      ultimately show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> (p \<^bold>\<and> q)\<close>
        using 2 unfolding canonical_ctx_def by auto
    qed
  next
    case (Box p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<box> p\<close> \<open>(i, \<^bold>\<box> p) \<in> S\<close>
      {
        fix k
        assume \<open>[k]\<^sub>S \<in> reach S ([i]\<^sub>S)\<close>
        then obtain k' where \<open>([i]\<^sub>S, \<^bold>\<diamond> (\<^bold>\<bullet>k')) \<in> S\<close> \<open>[k']\<^sub>S = [k]\<^sub>S\<close>
          unfolding reach_def by auto
        then have \<open>(i, \<^bold>\<diamond> (\<^bold>\<bullet>k')) \<in> S\<close>
          using Nom_sym equiv_nom_Nom equiv_nom_assign equiv_nom_def by blast
        then have \<open>(k', p) \<in> S\<close>
          using \<open>(i, \<^bold>\<box> p) \<in> S\<close> alpha by (fastforce intro: CBoxP)
        then have \<open>\<lbrakk>S, k'\<rbrakk> \<Turnstile> p\<close>
          using 2 Box by simp
        then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close>
          unfolding canonical_ctx_def canonical_def using \<open>[k']\<^sub>S = [k]\<^sub>S\<close> by simp
      }
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<box> p\<close>
        unfolding canonical_ctx_def canonical_def reach_def gframe.defs frame.defs
        by auto
    next
      assume \<open>x = \<^bold>\<box> p\<close> \<open>(i, \<^bold>\<not> (\<^bold>\<box> p)) \<in> S\<close>
      then obtain k where k: \<open>(k, \<^bold>\<not> p) \<in> S\<close> \<open>(i, \<^bold>\<diamond> (\<^bold>\<bullet> k)) \<in> S\<close>
        using \<delta> by force
      then have \<open>\<not> \<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close>
        using 2 Box by simp
      moreover have \<open>([i]\<^sub>S, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S\<close>
        using k(2) equiv_nom_Nom equiv_nom_assign by fastforce
      then have \<open>[k]\<^sub>S \<in> reach S ([i]\<^sub>S)\<close>
        unfolding reach_def by blast
      ultimately show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<box> p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs frame.defs
        by auto
    qed
  next
    case (Sat k p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>@k p\<close> \<open>(i, \<^bold>@k p) \<in> S\<close>
      then have \<open>(k, p) \<in> S\<close>
        using alpha by (fastforce intro: CSatP)
      then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close>
        using 2 Sat by simp
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>@k p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by (auto split: tm.splits)
    next
      assume \<open>x = \<^bold>@k p\<close> \<open>(i, \<^bold>\<not> \<^bold>@k p) \<in> S\<close>
      then have \<open>(k, \<^bold>\<not> p) \<in> S\<close>
        using alpha by (fastforce intro: CSatN)
      then have \<open>\<not> \<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close>
        using 2 Sat by simp
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>@k p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by (auto split: tm.splits)
    qed
  next
    case (Glo p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>A p\<close> \<open>(i, \<^bold>A p) \<in> S\<close>
      then have \<open>(k, p) \<in> S\<close> for k
        using gammaI by (fastforce intro: CGloP)
      then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close> for k
        using 2 Glo by simp
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>A p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs frame.defs
        by auto
    next
      assume \<open>x = \<^bold>A p\<close> \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> S\<close>
      then have \<open>\<exists>k. (k, \<^bold>\<not> p) \<in> S\<close>
        using \<delta> by fastforce
      then have \<open>\<exists>k. \<not> \<lbrakk>S, k\<rbrakk> \<Turnstile> p\<close>
        using 2 Glo by auto
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>A p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs frame.defs
        by auto
    qed
  next
    case (Dwn p)
   then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<down> p\<close> \<open>(i, \<^bold>\<down> p) \<in> S\<close>
      then have \<open>(i, \<langle>i\<rangle>\<^sub>i p) \<in> S\<close>
        using alpha by (fastforce intro: CDwnP)
      moreover have \<open>(\<langle>i\<rangle>\<^sub>i p, x) \<in> measures [qs_fm, sz_fm]\<close>
        using Dwn by simp
      ultimately have \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<langle>i\<rangle>\<^sub>i p\<close>
        using 2 by (meson in_measure)
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<down> p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by simp
    next
      assume \<open>x = \<^bold>\<down> p\<close> \<open>(i, \<^bold>\<not> \<^bold>\<down> p) \<in> S\<close>
      then have \<open>(i, \<^bold>\<not> \<langle>i\<rangle>\<^sub>i p) \<in> S\<close>
        using alpha by (fastforce intro: CDwnN)
      moreover have \<open>(\<langle>i\<rangle>\<^sub>i p, x) \<in> measures [qs_fm, sz_fm]\<close>
        using Dwn by simp
      ultimately have \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<langle>i\<rangle>\<^sub>i p\<close>
        using 2 by (meson in_measure)
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<down> p\<close>
        unfolding canonical_ctx_def canonical_def gframe.defs
        by simp
    qed
  next
    case (All p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall> p\<close> \<open>(i, \<^bold>\<forall> p) \<in> S\<close>
      then have \<open>softqdf q \<Longrightarrow> (i, \<langle>q\<rangle>\<^sub>p p) \<in> S\<close> for q
        using gammaP by (fastforce intro: CAllP)
      moreover have \<open>softqdf q \<Longrightarrow> (\<langle>q\<rangle>\<^sub>p p, x) \<in> measures [qs_fm, sz_fm]\<close> for q
        using All by (metis less_add_one measures_less qs_fm.simps(9) qs_fm_sub_pro softqdf_add_env)
      ultimately have *: \<open>softqdf q \<Longrightarrow> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<langle>q\<rangle>\<^sub>p p\<close> for q
        using 2 by (meson in_measure)
      
      moreover note wf_canonical[of S] assign_in_W[of i]
      ultimately have \<open>softqdf q \<Longrightarrow>
        ((canonical S)\<lparr>\<VV> := (worlds (canonical S) q \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p\<close> for q
        using inst_single_worlds[where W=\<open>\<W> (canonical S)\<close> and q=q] unfolding canonical_ctx_def canonical_def unfolds by fastforce
      then have \<open>(\<forall>P \<in> sqdfs (canonical S). ((canonical S)\<lparr>\<VV> := (P \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p)\<close>
        unfolding sqdfs_def by blast
      then have \<open>(\<forall>P \<in> \<Pi> (canonical S). ((canonical S)\<lparr>\<VV> := (P \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p)\<close>
        using sqdfs_canonical by blast
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<forall> p\<close>
        unfolding canonical_ctx_def by simp
    next
      assume \<open>x = \<^bold>\<forall> p\<close> \<open>(i, \<^bold>\<not> \<^bold>\<forall> p) \<in> S\<close>
      then obtain P where \<open>(i, \<^bold>\<not> \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p) \<in> S\<close>
        using \<delta> by auto
      moreover have \<open>(\<^bold>\<not> \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p, x) \<in> measures [qs_fm, sz_fm]\<close>
        using All
        by (metis less_add_one measures_less qs_fm.simps(3) qs_fm.simps(9) qs_fm_sub_pro softqdf.simps(2) softqdf_add_env)
      ultimately have \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p\<close>
        using 2 unfolding canonical_ctx_def by auto
      moreover have \<open>softqdf (\<^bold>\<cdot> (\<^bold>\<circle> P))\<close>
        by simp
      moreover note wf_canonical[of S] assign_in_W[of i]
      ultimately have \<open>softqdf (\<^bold>\<cdot> (\<^bold>\<circle> P)) \<and>
        \<not> ((canonical S)\<lparr>\<VV> := (worlds (canonical S) (\<^bold>\<cdot> (\<^bold>\<circle> P)) \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p\<close>
        using inst_single_worlds[where W=\<open>\<W> (canonical S)\<close>] unfolding canonical_ctx_def canonical_def unfolds
        by fastforce
      then have \<open>(\<exists>P \<in> sqdfs (canonical S). \<not> ((canonical S)\<lparr>\<VV> := (P \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p)\<close>
        unfolding sqdfs_def by blast
      then have \<open>(\<exists>P \<in> \<Pi> (canonical S). \<not> ((canonical S)\<lparr>\<VV> := (P \<then> \<VV> (canonical S))\<rparr>, [i]\<^sub>S) \<Turnstile> p)\<close>
        using sqdfs_canonical by blast
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile> \<^bold>\<forall> p\<close>
        unfolding canonical_ctx_def by simp
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>'x lbd set\<close>
  assumes \<open>P.prop\<^sub>E Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>P.enough_new S\<close>
    and \<open>(i, p) \<in> S\<close>
  shows \<open>\<lbrakk>mk_mcs C S, i\<rbrakk> \<Turnstile> p\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>P.prop\<^sub>H Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  qed
  moreover have \<open>(i, p) \<in> mk_mcs C S\<close>
    using assms(4) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.model by blast
qed

section \<open>Natural Deduction\<close>

inductive Calculus_Set :: \<open>'x lbd set \<Rightarrow> 'x lbd \<Rightarrow> bool\<close> (\<open>_ \<tturnstile> _\<close> [50, 50] 50) where
  Assm [dest]: \<open>(i, p) \<in> A \<Longrightarrow> A \<tturnstile> (i, p)\<close>
| Ref [simp]: \<open>A \<tturnstile> (i, \<^bold>\<bullet>i)\<close>
| Nom [dest]: \<open>A \<tturnstile> (i, \<^bold>\<bullet>k) \<Longrightarrow> A \<tturnstile> (i, p) \<Longrightarrow> A \<tturnstile> (k, p)\<close>
| NotI [intro]: \<open>{(i, p)} \<union> A \<tturnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<tturnstile> (i, \<^bold>\<not> p)\<close>
| NotE [elim]: \<open>A \<tturnstile> (i, \<^bold>\<not> p) \<Longrightarrow> A \<tturnstile> (i, p) \<Longrightarrow> A \<tturnstile> (k, q)\<close>
| AndI [intro]: \<open>A \<tturnstile> (i, p) \<Longrightarrow> A \<tturnstile> (i, q) \<Longrightarrow> A \<tturnstile> (i, p \<^bold>\<and> q)\<close>
| AndD1 [dest]: \<open>A \<tturnstile> (i, p \<^bold>\<and> q) \<Longrightarrow> A \<tturnstile> (i, p)\<close>
| AndD2 [dest]: \<open>A \<tturnstile> (i, p \<^bold>\<and> q) \<Longrightarrow> A \<tturnstile> (i, q)\<close>
| SatI [intro]: \<open>A \<tturnstile> (i, p) \<Longrightarrow> A \<tturnstile> (k, \<^bold>@i p)\<close>
| SatE [dest]: \<open>A \<tturnstile> (i, \<^bold>@k p) \<Longrightarrow> A \<tturnstile> (k, p)\<close>
| BoxI [intro]: \<open>{(i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle>k)))} \<union> A \<tturnstile> (\<^bold>\<circle>k, p) \<Longrightarrow> k \<notin> symbols ({(i, p)} \<union> A) \<Longrightarrow> A \<tturnstile> (i, \<^bold>\<box> p)\<close>
| BoxE [elim]: \<open>A \<tturnstile> (i, \<^bold>\<box> p) \<Longrightarrow> A \<tturnstile> (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<Longrightarrow> A \<tturnstile> (k, p)\<close>
| GloI [intro]: \<open>A \<tturnstile> (\<^bold>\<circle>k, p) \<Longrightarrow> k \<notin> symbols ({(i, p)} \<union> A) \<Longrightarrow> A \<tturnstile> (i, \<^bold>A p)\<close>
| GloE [dest]: \<open>A \<tturnstile> (i, \<^bold>A p) \<Longrightarrow> A \<tturnstile> (k, p)\<close>
| DwnI [intro]: \<open>A \<tturnstile> (i, \<langle>i\<rangle>\<^sub>i p) \<Longrightarrow> A \<tturnstile> (i, \<^bold>\<down> p)\<close>
| DwnE [dest]: \<open>A \<tturnstile> (i, \<^bold>\<down> p) \<Longrightarrow> A \<tturnstile> (i, \<langle>i\<rangle>\<^sub>i p)\<close>
| AllI [intro]: \<open>A \<tturnstile> (i, \<langle>\<^bold>\<cdot>(\<^bold>\<circle>P)\<rangle>\<^sub>p p) \<Longrightarrow> P \<notin> symbols ({(i, p)} \<union> A) \<Longrightarrow> A \<tturnstile> (i, \<^bold>\<forall> p)\<close>
| AllE [dest]: \<open>A \<tturnstile> (i, \<^bold>\<forall> p) \<Longrightarrow> softqdf q \<Longrightarrow> A \<tturnstile> (i, \<langle>q\<rangle>\<^sub>p p)\<close>
| Clas: \<open>{(i, \<^bold>\<not> p)} \<union> A \<tturnstile> (i, p) \<Longrightarrow> A \<tturnstile> (i, p)\<close>

subsection \<open>Soundness\<close>

theorem soundness:
  assumes \<open>A \<tturnstile> (i, p)\<close> \<open>\<forall>(k, q) \<in> A. (Model W R PI N e V f, case_tm e N k) \<Turnstile> q\<close>
    \<open>wf_model (Model W R PI N e V f)\<close>
  shows \<open>(Model W R PI N e V f, case_tm e N i) \<Turnstile> p\<close>
  using assms
proof (induct A \<open>(i, p)\<close> arbitrary: i p N V pred: Calculus_Set)
  case (Ref A i)
  then show ?case
    by (auto split: tm.splits)
next
  case (Nom A i k p)
  then show ?case
    by (auto split: tm.splits)
next
  case (SatI A i p k)
  then show ?case
    by (auto split: tm.splits)
next
  case (SatE A i k p)
  then show ?case
    by (auto split: tm.splits)
next
  case (BoxI i k A p)
  {
    fix v
    assume v: \<open>v \<in> R (case_tm e N i)\<close>
    moreover have \<open>case_tm e N i \<in> W\<close>
      using BoxI(5) unfolding wf_env_def wf_model_def unfolds by (auto split: tm.splits)
    ultimately have \<open>v \<in> W\<close>
      using BoxI(5) unfolding wf_model_def wf_gframe_def wf_frame_def unfolds by blast
 
    let ?N = \<open>N(k := v)\<close>
    have \<open>\<forall>(i, p) \<in> A. (Model W R PI ?N e V f, case_tm e ?N i) \<Turnstile> p\<close>
      using BoxI by fastforce
    moreover have \<open>(Model W R PI ?N e V f, case_tm e ?N i) \<Turnstile> \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle> k))\<close>
      using v BoxI.hyps(3) by (simp split: tm.splits)
    moreover have \<open>wf_model (Model W R PI ?N e V f)\<close>
      using BoxI.prems(2) \<open>v \<in> W\<close> unfolding wf_env_def wf_model_def unfolds by auto
    ultimately have \<open>(Model W R PI ?N e V f, ?N k) \<Turnstile> p\<close>
      using BoxI.hyps(2) by fastforce
  }
  then have \<open>\<forall>v \<in> R (case_tm e N i). (Model W R PI (N(k := v)) e V f, v) \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>v \<in> R (case_tm e N i). (Model W R PI N e V f, v) \<Turnstile> p\<close>
    using BoxI.hyps(3) by simp
  then show ?case
    by simp
next
  case (BoxE A i p k)
  then show ?case
    by (auto split: tm.splits)
next
  case (GloI A k p i)
  {
    fix v
    assume \<open>v \<in> W\<close>
    let ?N = \<open>N(k := v)\<close>
    have \<open>\<forall>v. \<forall>(i, p) \<in> A. (Model W R PI ?N e V f, case_tm e ?N i) \<Turnstile> p\<close>
      using GloI.prems(1) GloI.hyps(3) by fastforce
    moreover have \<open>wf_model (Model W R PI ?N e V f)\<close>
      using GloI.prems(2)  \<open>v \<in> W\<close> unfolding wf_env_def wf_model_def unfolds by auto
    ultimately have \<open>(Model W R PI ?N e V f, ?N k) \<Turnstile> p\<close>
      using GloI.hyps(2) by fastforce
  }
  then have \<open>\<forall>v \<in> W. (Model W R PI (N(k := v)) e V f, v) \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>v \<in> W. (Model W R PI N e V f, v) \<Turnstile> p\<close>
    using GloI.hyps(3) by simp
  then show ?case
    by simp
next
  case (GloE A i p k)
  then show ?case
    using wf_\<NN> wf_\<N>
    by (cases k) fastforce+
next
  case (AllI A i P p)
  {
    fix X
    assume \<open>X \<in> PI\<close>
    let ?V = \<open>V(P := X)\<close>
    have \<open>\<forall>v. \<forall>(i, p) \<in> A. (Model W R PI N e ?V f, case_tm e N i) \<Turnstile> p\<close>
      using AllI.prems(1) AllI.hyps(3) by fastforce
    moreover have *: \<open>wf_model (Model W R PI N e ?V f)\<close>
      using AllI.prems(2) \<open>X \<in> PI\<close> unfolding wf_env_def wf_model_def unfolds by auto
    ultimately have \<open>(Model W R PI N e ?V f, case_tm e N i) \<Turnstile> \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p\<close>
      using AllI.hyps(2) by fast
    moreover have \<open>case_tm e N i \<in> W\<close>
      using AllI.prems(2) unfolding wf_model_def wf_env_def unfolds by (auto split: tm.splits) 
    ultimately have \<open>(Model W R PI N e ?V (worlds (Model W R PI N e ?V f) (\<^bold>\<cdot> (\<^bold>\<circle> P)) \<then> f), case_tm e N i) \<Turnstile> p\<close>
      using inst_single_worlds * by fastforce
    then have \<open>(Model W R PI N e ?V ({ w \<in> W. w \<in> X } \<then> f), case_tm e N i) \<Turnstile> p\<close>
      unfolding worlds_def by simp
    moreover have \<open>X \<in> Pow W\<close>
      using AllI.prems(2) \<open>X \<in> PI\<close> unfolding wf_model_def wf_gframe_def unfolds by auto
    then have \<open>{ w \<in> W. w \<in> X } = X\<close>
      by blast
    ultimately have \<open>(Model W R PI N e ?V (X \<then> f), case_tm e N i) \<Turnstile> p\<close>
      by simp
  }
  then have \<open>\<forall>X \<in> PI. (Model W R PI N e (V(P := X)) (X \<then> f), case_tm e N i) \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>X \<in> PI. (Model W R PI N e V (X \<then> f), case_tm e N i) \<Turnstile> p\<close>
    using AllI.hyps(3) by simp
  then show ?case
    by simp
next
  case (AllE A i p q)
  then show ?case
  proof (cases i)
    case (Var x1)
    then show ?thesis
      using AllE(2-) inst_single_worlds softqdf_worlds wf_\<NN> by fastforce
  next
    case (Sym x2)
    then show ?thesis
      using AllE(2-) inst_single_worlds softqdf_worlds wf_\<N> by fastforce
  qed
qed auto

corollary soundness':
  assumes \<open>{} \<tturnstile> (\<^bold>\<circle>i, p)\<close> \<open>i \<notin> symbols_fm p\<close>
    and \<open>wf_model M\<close> \<open>w \<in> \<W> M\<close>
  shows \<open>(M, w) \<Turnstile> p\<close>
proof (cases M)
  case (fields W R PI N e V f)
  let ?N = \<open>N(i := w)\<close>
  have \<open>wf_model (Model W R PI ?N e V f)\<close>
    using fields assms(3-4) unfolding wf_env_def wf_model_def unfolds by auto
  then have \<open>(Model W R PI ?N e V f, case_tm e ?N (\<^bold>\<circle>i)) \<Turnstile> p\<close>
    using assms(1) soundness by blast
  then have \<open>(Model W R PI ?N e V f, w) \<Turnstile> p\<close>
    by simp
  then show ?thesis
    using assms(2) fields by simp
qed

lemma no_bot: \<open>\<not> (M, w) \<Turnstile> \<^bold>\<bottom>\<close>
  by simp

corollary \<open>\<not> ({} \<tturnstile> (\<^bold>\<circle>i, \<^bold>\<bottom>))\<close>
  using soundness no_bot wf_canonical unfolding canonical_def unfolds
  by (metis (no_types, lifting) emptyE)

subsection \<open>Derived Rules\<close>

lemma Assm_head [simp]: \<open>{(p, i)} \<union> A \<tturnstile> (p, i)\<close>
  using Assm by blast

lemma Boole: \<open>{(i, \<^bold>\<not> p)} \<union> A \<tturnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<tturnstile> (i, p)\<close>
  using Clas AndD1 AndD2 NotE by meson

lemma FlsE [dest]: \<open>A \<tturnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<tturnstile> (k, p)\<close>
  by (meson Assm_head NotE NotI)

subsection \<open>Derivational Consistency\<close>

lemma calculus_confl:
  assumes \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close> 
  shows \<open>A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (CNegP i p)
  then show ?thesis
    using assms(2-)
    by (metis Assm NotE empty_set equals0D list.set_intros(1) set_ConsD subset_eq)
next
  case (CNegI i k)
  then show ?thesis
    using assms(2-) by fastforce
qed

lemma calculus_alpha:
  assumes \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>set qs \<union> A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (CSym i k)
  then show ?thesis
    using assms(2-)
    by (metis Assm_head Diff_partition Nom NotE NotI Ref list.set(1) list.simps(15))
next
  case (CNom i k p)
  then show ?thesis
    using assms(2-)
    by (metis AndD1 AndD2 Assm Nom NotE NotI empty_set insert_subset list.simps(15))
next
  case (CNegN i p)
  then show ?thesis
    using assms(2-)
    by (metis Assm_head Diff_partition NotE NotI empty_set list.simps(15))
next
  case (CConP k p q)
  then have \<open>A \<tturnstile> (k, p)\<close> \<open>A \<tturnstile> (k, q)\<close>
    using assms(2-) by (meson AndD1 AndD2 Assm list.set_intros(1) subset_eq)+
  moreover have \<open>{(k, p), (k, q)} \<union> A \<tturnstile> (k, \<^bold>\<bottom>)\<close>
    using CConP assms(2-) by auto
  then have \<open>{(k, q)} \<union> A \<tturnstile> (k, \<^bold>\<not> p)\<close>
    using NotI by auto
  ultimately have \<open>A \<tturnstile> (k, \<^bold>\<bottom>)\<close>
    using CConP(1) assms(2)
    by (metis AndD1 Assm NotE NotI list.set_intros(1) subset_code(1) sup.coboundedI2)
  then show ?thesis
    by blast
next
  case (CSatP i k p)
  then show ?thesis
    using assms(2-) SatE[of A i k p]
    by (metis Assm_head NotE NotI empty_set le_iff_sup list.simps(15))
next
  case (CSatN i k p)
  then show ?thesis
    using assms(2-) SatI[of A k p]
    by (metis Assm_head Boole FlsE NotE empty_set le_iff_sup list.simps(15))
next
  case (CBoxP i p k)
  then show ?thesis
    using assms(2-) BoxE[of A i p]
    by (metis AndD1 AndD2 Assm NotE NotI empty_set insert_subset list.simps(15))
next
  case (CDwnP i p)
  then show ?thesis
    using assms(2-) DwnE[of A i p]
    by (metis Assm_head Diff_partition NotE NotI empty_set list.simps(15))
next
  case (CDwnN i p)
  then show ?thesis
    using assms(2-) DwnI[of A i p]
    by (metis AndD1 AndD2 Assm_head Clas NotE empty_set le_iff_sup list.simps(15))
qed

lemma calculus_beta:
  assumes \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>\<forall>q \<in> set qs. {q} \<union> A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (CConN i p q)
  then show ?thesis
    using assms(2-) AndI[of A i p q]
    by (metis Assm Clas FlsE NotE UnI2 insert_is_Un list.set_intros(1) list.simps(15) subset_iff)
qed

lemma calculus_gammaI:
  assumes \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>i qs\<close> \<open>set ps \<subseteq> A\<close> \<open>set (qs k) \<union> A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case CRefl
  then show ?thesis
    using CRefl assms(2-) Ref[of A k] 
    by (metis (mono_tags, lifting) AndD1 AndD2 NotE NotI empty_set list.simps(15))
next
  case (CGloP i p)
  then show ?thesis
    using CGloP assms(2-) GloE[of A i p k]
    by (metis (no_types, lifting) Assm_head NotE NotI empty_set le_iff_sup list.simps(15))
qed

lemma calculus_gammaP:
  assumes \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>p (F, qs)\<close> \<open>set ps \<subseteq> A\<close> \<open>k \<in> F A\<close> \<open>set (qs k) \<union> A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (CAllP i p)
  then show ?thesis
    using assms(2-) AllE[of A i p]
    by (metis (no_types, lifting) Assm_head NotE NotI le_iff_sup list.set(1) list.simps(15) mem_Collect_eq)
qed

lemma calculus_\<delta>:
  assumes \<open>p \<in> A\<close> \<open>k \<notin> symbols A\<close> \<open>set (\<delta> p k) \<union> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  shows \<open>A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using assms
proof (induct p k rule: \<delta>.induct)
  case (1 i p k)
  then have \<open>{(\<^bold>\<circle>k, \<^bold>\<not> p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>(\<^bold>\<circle>k)))} \<union> A \<tturnstile> (a, \<^bold>\<bottom>)\<close> \<open>(i, \<^bold>\<not> \<^bold>\<box> p) \<in> A\<close>
    by simp_all
  then have \<open>{(i, \<^bold>\<diamond> (\<^bold>\<bullet>(\<^bold>\<circle>k)))} \<union> A \<tturnstile> (\<^bold>\<circle>k, p)\<close>
    using Boole by auto
  moreover have \<open>k \<notin> symbols ({(i, p)} \<union> A)\<close>
    using 1 by auto
  ultimately have \<open>A \<tturnstile> (i, \<^bold>\<box> p)\<close>
    using BoxI by blast
  then show ?thesis
    using \<open>(i, \<^bold>\<not> \<^bold>\<box> p) \<in> A\<close> by (meson Assm NotE)
next
  case (2 i p k)
  then have \<open>{(\<^bold>\<circle>k, \<^bold>\<not> p)} \<union> A \<tturnstile> (a, \<^bold>\<bottom>)\<close> \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> A\<close>
    by simp_all
  then have \<open>{(\<^bold>\<circle>k, \<^bold>\<not> p)} \<union> A \<tturnstile> (\<^bold>\<circle>k, \<^bold>\<bottom>)\<close>
    by fast
  then have \<open>A \<tturnstile> (\<^bold>\<circle>k, p)\<close>
    by (meson Boole)
  moreover have \<open>k \<notin> symbols ({(i, p)} \<union> A)\<close>
    using 2 CGloN by auto
  ultimately have \<open>A \<tturnstile> (i, \<^bold>A p)\<close>
    by blast
  then show ?thesis
    using \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> A\<close> Assm NotE by meson
next
  case (3 i p P)
  then have \<open>{(i, \<^bold>\<not> \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p)} \<union> A \<tturnstile> (a, \<^bold>\<bottom>)\<close> \<open>(i, \<^bold>\<not> \<^bold>\<forall> p) \<in> A\<close>
    by simp_all
  then have \<open>A \<tturnstile> (i, \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p)\<close>
    using Clas by blast
  moreover have \<open>P \<notin> symbols ({(i, p)} \<union> A)\<close>
    using 3 by auto
  ultimately have \<open>A \<tturnstile> (i, \<^bold>\<forall> p)\<close>
    by blast
  then show ?thesis
    using \<open>(i, \<^bold>\<not> \<^bold>\<forall> p) \<in> A\<close> Assm NotE by meson
qed simp_all

interpretation DC: Derivational_Confl map_lbd symbols_lbd \<open>\<lambda>_. True\<close> confl_class \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using calculus_confl by unfold_locales blast

interpretation DA: Derivational_Alpha map_lbd symbols_lbd \<open>\<lambda>_. True\<close> alpha_class \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using calculus_alpha by unfold_locales blast

interpretation DB: Derivational_Beta map_lbd symbols_lbd \<open>\<lambda>_. True\<close> beta_class \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using calculus_beta by unfold_locales blast

interpretation DGI: Derivational_Gamma map_tm map_lbd symbols_lbd \<open>\<lambda>_. True\<close> GI.classify_UNIV \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using calculus_gammaI by unfold_locales blast

interpretation DGP: Derivational_Gamma map_fm map_lbd symbols_lbd \<open>\<lambda>_. True\<close> gamma_class_fm \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using calculus_gammaP by unfold_locales blast

interpretation DD: Derivational_Delta map_lbd symbols_lbd \<open>\<lambda>_. True\<close> \<delta> \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  by unfold_locales (meson calculus_\<delta>)
  
interpretation Derivational_Consistency map_lbd symbols_lbd \<open>\<lambda>_. True\<close> Kinds \<open>\<lambda>A. \<not> A \<tturnstile> (a, \<^bold>\<bottom>)\<close>
  using prop\<^sub>E_Kinds[OF DC.kind DA.kind DB.kind DGI.kind DGP.kind DD.kind] by unfold_locales

subsection \<open>Strong Completeness\<close>

theorem strong_completeness:
  fixes p :: \<open>'x fm\<close>
  assumes mod: \<open>\<And>(M :: ('x, 'x tm) model) w. wf_model M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow>
      \<forall>(k, q) \<in> A. (M, case_tm (\<NN> M) (\<N> M) k) \<Turnstile> q \<Longrightarrow>
      (M, w) \<Turnstile> p\<close>
    and \<open>P.enough_new A\<close>
  shows \<open>A \<tturnstile> (i, p)\<close>
proof (rule ccontr)
  assume \<open>\<not> A \<tturnstile> (i, p)\<close>
  then have *: \<open>\<not> {(i, \<^bold>\<not> p)} \<union> A \<tturnstile> (i, \<^bold>\<bottom>)\<close>
    using Boole by blast

  let ?S = \<open>{(i, \<^bold>\<not> p)} \<union> A\<close>
  let ?C = \<open>{A. P.enough_new A \<and> \<not> A \<tturnstile> (undefined, \<^bold>\<bottom>)}\<close>
  let ?H = \<open>mk_mcs ?C ?S\<close>
  let ?M = \<open>canonical ?H\<close>

  have \<open>P.prop\<^sub>E Kinds ?C\<close>
    using Consistency by fast
  moreover have \<open>?S \<in> ?C\<close>
    using * FlsE params_left assms(2)
    by (metis (no_types, lifting) ext List.set_insert empty_set mem_Collect_eq )
  moreover from this have \<open>P.enough_new ?S\<close>
    by blast
  ultimately have **: \<open>\<forall>(k, q) \<in> ?S. \<lbrakk>?H, k\<rbrakk> \<Turnstile> q\<close>
    using model_existence[of ?C ?S] by blast
  then have \<open>\<forall>(k, q) \<in> ?S. (?M, case_tm (\<NN> ?M) (\<N> ?M) k) \<Turnstile> q\<close>
    unfolding canonical_tm_eta' canonical_ctx_def by blast

  moreover have \<open>wf_model ?M\<close>
    using wf_canonical by blast
  moreover have \<open>assign i ?H \<in> \<W> ?M\<close>
    unfolding canonical_def unfolds by auto

  ultimately have \<open>\<lbrakk>?H, i\<rbrakk> \<Turnstile> p\<close>
    using mod unfolding canonical_ctx_def by auto

  moreover have \<open>\<not> \<lbrakk>?H, i\<rbrakk> \<Turnstile> p\<close>
    using ** unfolding canonical_ctx_def by simp
  ultimately show False
    by simp
qed

section \<open>Natural Deduction with Lists\<close>

inductive Calculus :: \<open>'x lbd list \<Rightarrow> 'x lbd \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) where
  Assm [dest]: \<open>(i, p) \<in> set A \<Longrightarrow> A \<turnstile> (i, p)\<close>
| Ref [simp]: \<open>A \<turnstile> (i, \<^bold>\<bullet>i)\<close>
| Nom [dest]: \<open>A \<turnstile> (i, \<^bold>\<bullet>k) \<Longrightarrow> A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| NotI [intro]: \<open>(i, p) # A \<turnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<not> p)\<close>
| NotE [elim]: \<open>A \<turnstile> (i, \<^bold>\<not> p) \<Longrightarrow> A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (k, q)\<close>
| AndI [intro]: \<open>A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (i, q) \<Longrightarrow> A \<turnstile> (i, p \<^bold>\<and> q)\<close>
| AndD1 [dest]: \<open>A \<turnstile> (i, p \<^bold>\<and> q) \<Longrightarrow> A \<turnstile> (i, p)\<close>
| AndD2 [dest]: \<open>A \<turnstile> (i, p \<^bold>\<and> q) \<Longrightarrow> A \<turnstile> (i, q)\<close>
| SatI [intro]: \<open>A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (k, \<^bold>@i p)\<close>
| SatE [dest]: \<open>A \<turnstile> (i, \<^bold>@k p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| BoxI [intro]: \<open>(i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle>k))) # A \<turnstile> (\<^bold>\<circle>k, p) \<Longrightarrow> k \<notin> symbols ({(i, p)} \<union> set A) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<box> p)\<close>
| BoxE [elim]: \<open>A \<turnstile> (i, \<^bold>\<box> p) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| GloI [intro]: \<open>A \<turnstile> (\<^bold>\<circle>k, p) \<Longrightarrow> k \<notin> symbols ({(i, p)} \<union> set A) \<Longrightarrow> A \<turnstile> (i, \<^bold>A p)\<close>
| GloE [dest]: \<open>A \<turnstile> (i, \<^bold>A p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| DwnI [intro]: \<open>A \<turnstile> (i, \<langle>i\<rangle>\<^sub>i p) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<down> p)\<close>
| DwnE [dest]: \<open>A \<turnstile> (i, \<^bold>\<down> p) \<Longrightarrow> A \<turnstile> (i, \<langle>i\<rangle>\<^sub>i p)\<close>
| AllI [intro]: \<open>A \<turnstile> (i, \<langle>\<^bold>\<cdot>(\<^bold>\<circle>P)\<rangle>\<^sub>p p) \<Longrightarrow> P \<notin> symbols ({(i, p)} \<union> set A) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<forall> p)\<close>
| AllE [dest]: \<open>A \<turnstile> (i, \<^bold>\<forall> p) \<Longrightarrow> softqdf q \<Longrightarrow> A \<turnstile> (i, \<langle>q\<rangle>\<^sub>p p)\<close>
| Clas: \<open>(i, \<^bold>\<not> p) # A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (i, p)\<close>

definition bounded :: \<open>'a list \<Rightarrow> 'a set \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>bounded K A P \<equiv> set K \<subseteq> A \<and> (\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> P B)\<close>

lemma bounded_one [elim]:
  assumes \<open>bounded K A P\<close> \<open>\<And>A. P A \<Longrightarrow> Q A\<close>
  shows \<open>bounded K A Q\<close>
  using assms unfolding bounded_def by simp

lemma bounded_two [elim]:
  assumes \<open>bounded K A P\<close> \<open>bounded K' A Q\<close> \<open>\<And>A. P A \<Longrightarrow> Q A \<Longrightarrow> R A\<close>
  shows \<open>bounded (K @ K') A R\<close>
  using assms unfolding bounded_def by simp

lemma bounded_removeAll [dest]:
  assumes \<open>bounded K ({p} \<union> A) P\<close>
  shows \<open>bounded (removeAll p K) A (\<lambda>B. P (p # B))\<close>
  using assms unfolding bounded_def
  by (metis Diff_subset_conv insert_is_Un insert_mono list.simps(15) set_removeAll)

lemma bounded_params:
  assumes \<open>a \<notin> P.params ({p} \<union> A)\<close> \<open>bounded K A P\<close>
  shows \<open>bounded K A (\<lambda>B. a \<notin> P.params (set (p # B)))\<close>
  using assms unfolding bounded_def by auto

lemma finite_kernel: \<open>A \<tturnstile> (i, p) \<Longrightarrow> \<exists>K. bounded K A (\<lambda>B. B \<turnstile> (i, p))\<close>
proof (induct A \<open>(i, p)\<close> arbitrary: i p pred: Calculus_Set)
  case (Assm i p A)
  then show ?case
    unfolding bounded_def using Calculus.Assm
    by (metis empty_subsetI insert_subset set_replicate_Suc)
next
  case (Ref A i)
  then show ?case
    unfolding bounded_def using Calculus.Ref
    by (metis empty_set empty_subsetI)
next
  case (Nom A i k p)
  then show ?case
    by force
next
  case (NotI i p A)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. (i, p) # B \<turnstile> (i, \<^bold>\<bottom>))\<close>
    by blast
  then show ?case
    by fast
next
  case (BoxI i k A p)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. (i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle> k))) # B \<turnstile> (\<^bold>\<circle> k, p))\<close>
    by blast
  moreover from this have \<open>\<exists>K. bounded K A (\<lambda>B. k \<notin> P.params ({(i, p)} \<union> set B))\<close>
    using BoxI(2-3) bounded_params by fastforce
  ultimately show ?case
    by fastforce
next
  case (GloI A k p i)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. B \<turnstile> (\<^bold>\<circle> k, p))\<close>
    by blast
  moreover from this have \<open>\<exists>K. bounded K A (\<lambda>B. k \<notin> P.params ({(i, p)} \<union> set B))\<close>
    using GloI(3) bounded_params by fastforce
  ultimately show ?case
    by fastforce
next
  case (AllI A i P p)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. B \<turnstile> (i, \<langle>\<^bold>\<cdot> (\<^bold>\<circle> P)\<rangle>\<^sub>p p))\<close>
    by blast
  moreover from this have \<open>\<exists>K. bounded K A (\<lambda>B. P \<notin> P.params ({(i, p)} \<union> set B))\<close>
    using AllI(3) bounded_params by fastforce
  ultimately show ?case
    by fastforce
next
  case (Clas i p A)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. (i, \<^bold>\<not> p) # B \<turnstile> (i, p))\<close>
    by fast
  then show ?case
    using Calculus.Clas by force
qed fast+

corollary finite_assumptions: \<open>A \<tturnstile> (i, p) \<Longrightarrow> \<exists>B. set B \<subseteq> A \<and> B \<turnstile> (i, p)\<close>
  using finite_kernel unfolding bounded_def by blast

lemma calculus_set: \<open>A \<turnstile> (i, p) \<Longrightarrow> set A \<tturnstile> (i, p)\<close>
proof (induct A \<open>(i, p)\<close> arbitrary: i p pred: Calculus)
  case (Clas p q A)
  then show ?case
    using Calculus_Set.Clas by auto
qed auto

corollary soundness_list:
  assumes \<open>A \<turnstile> (i, p)\<close> \<open>\<forall>(k, q) \<in> set A. (M, case_tm (\<NN> M) (\<N> M) k) \<Turnstile> q\<close>
    and \<open>wf_model M\<close>
  shows \<open>(M, case_tm (\<NN> M) (\<N> M) i) \<Turnstile> p\<close>
  using assms soundness calculus_set
  by (metis (mono_tags, lifting) model.surjective unit.exhaust split_cong)

corollary soundness_nil:
  \<open>[] \<turnstile> (\<^bold>\<circle>i, p) \<Longrightarrow> i \<notin> symbols_fm p \<Longrightarrow> wf_model M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow> (M, w) \<Turnstile> p\<close>
  by (metis calculus_set empty_set soundness')
  
corollary \<open>\<not> ([] \<turnstile> (i, \<^bold>\<bottom>))\<close>
  by (metis equals0D no_bot set_empty2 soundness_list wf_canonical)

corollary strong_completeness_list:
  fixes p :: \<open>'x fm\<close>
  assumes \<open>\<And>(M :: ('x, 'x tm) model) w. wf_model M \<Longrightarrow> w \<in> \<W> M \<Longrightarrow>
      \<forall>(k, q) \<in> A. (M, case_tm (\<NN> M) (\<N> M) k) \<Turnstile> q \<Longrightarrow> (M, w) \<Turnstile> p\<close>
    and \<open>P.enough_new A\<close>
  shows \<open>\<exists>B. set B \<subseteq> A \<and> B \<turnstile> (i, p)\<close>
  using assms strong_completeness finite_assumptions by blast

theorem main:
  fixes p :: \<open>'x fm\<close>
  assumes \<open>i \<notin> symbols_fm p\<close> \<open>|UNIV :: 'x lbd set| \<le>o  |UNIV :: 'x set|\<close>
  shows \<open>[] \<turnstile> (\<^bold>\<circle>i, p) \<longleftrightarrow> (\<forall>(M :: ('x, 'x tm) model). \<forall>w \<in> \<W> M. wf_model M \<longrightarrow> (M, w) \<Turnstile> p)\<close>
  using assms strong_completeness_list[where A=\<open>{}\<close>] soundness_nil unfolding P.enough_new_def by fastforce

section \<open>The Need for SQDFs\<close>

subsection \<open>Finite Unions of Arithmetic Progressions\<close>

subsubsection \<open>From Manuel Eberl's Furstenberg-Topology AFP entry\<close>

definition arith_prog :: "int \<Rightarrow> nat \<Rightarrow> int set" where
  "arith_prog a b = {x. [x = a] (mod int b)}"

lemma arith_prog_0_right [simp]: "arith_prog a 0 = {a}"
  by (simp add: arith_prog_def)

lemma arith_prog_Suc_0_right [simp]: "arith_prog a (Suc 0) = UNIV"
  by (auto simp: arith_prog_def)

lemma in_arith_progI [intro]: "[x = a] (mod b) \<Longrightarrow> x \<in> arith_prog a b"
  by (auto simp: arith_prog_def)

lemma arith_prog_disjoint:
  assumes "[a \<noteq> a'] (mod int b)" and "b > 0"
  shows   "arith_prog a b \<inter> arith_prog a' b = {}"
  using assms by (auto simp: arith_prog_def cong_def)

lemma arith_prog_dvd_mono: "b dvd b' \<Longrightarrow> arith_prog a b' \<subseteq> arith_prog a b"
  by (auto simp: arith_prog_def cong_dvd_modulus)

lemma bij_betw_arith_prog:
  assumes "b > 0"
  shows   "bij_betw (\<lambda>n. a + int b * n) UNIV (arith_prog a b)"
proof (rule bij_betwI[of _ _ _ "\<lambda>x. (x - a) div int b"], goal_cases)
  case 1
  thus ?case 
    by (auto simp: arith_prog_def cong_add_lcancel_0 cong_mult_self_right mult_of_nat_commute)
next
  case 4
  thus ?case
    by (auto simp: arith_prog_def cong_iff_lin)
qed (use \<open>b > 0\<close> in \<open>auto simp: arith_prog_def\<close>)

lemma arith_prog_altdef: "arith_prog a b = range (\<lambda>n. a + int b * n)"
proof (cases "b = 0")
  case False
  thus ?thesis
    using bij_betw_arith_prog[of b] by (auto simp: bij_betw_def)
qed auto

lemma infinite_arith_prog: "b > 0 \<Longrightarrow> infinite (arith_prog a b)"
  using bij_betw_finite[OF bij_betw_arith_prog[of b]] by simp

(* from the lemma closed_arith_prog_fb *)
lemma arith_prog_complement:
  assumes \<open>b > 0\<close>
  shows "-arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)"
proof -
  have disjoint: "x \<notin> arith_prog a b" if "x \<in> arith_prog (a + int i) b" "i \<in> {1..<b}" for x i
  proof -
    have "[a \<noteq> a + int i] (mod int b)"
    proof
      assume "[a = a + int i] (mod int b)"
      hence "[a + 0 = a + int i] (mod int b)" by simp
      hence "[0 = int i] (mod int b)" by (subst (asm) cong_add_lcancel) auto
      with that show False by (auto simp: cong_def)
    qed
    thus ?thesis using arith_prog_disjoint[of a "a + int i" b] \<open>b > 0\<close> that by auto
  qed

  have covering: "x \<in> arith_prog a b \<or> x \<in> (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)" for x
  proof -
    define i where "i = nat ((x - a) mod (int b))"
    have "[a + int i = a + (x - a) mod int b] (mod int b)"
      unfolding i_def using \<open>b > 0\<close> by simp
    also have "[a + (x - a) mod int b = a + (x - a)] (mod int b)"
      by (intro cong_add) auto
    finally have "[x = a + int i] (mod int b)"
      by (simp add: cong_sym_eq)
    hence "x \<in> arith_prog (a + int i) b"
      using \<open>b > 0\<close> by (auto simp: arith_prog_def)
    moreover have "i < b" using \<open>b > 0\<close> 
      by (auto simp: i_def nat_less_iff)
    ultimately show ?thesis using \<open>b > 0\<close>
      by (cases "i = 0") auto
  qed

  from disjoint and covering show ?thesis
    by blast
qed

(* from instance t2_space *)
lemma arith_prog_distinguish:
  assumes "x \<noteq> y"
  shows "\<exists>a c b. b > 0 \<and> x \<in> arith_prog a b \<and> y \<in> arith_prog c b \<and> arith_prog a b \<inter> arith_prog c b = {}"
proof -
  define d where "d = nat \<bar>x - y\<bar> + 1"
  from \<open>x \<noteq> y\<close> have "d > 0"
    unfolding d_def by auto
  define U where "U = arith_prog x d"
  define V where "V = arith_prog y d"

  have "U \<inter> V = {}" unfolding U_def V_def d_def
  proof (use \<open>x \<noteq> y\<close> in transfer, rule arith_prog_disjoint)
    fix x y :: int
    assume "x \<noteq> y"
    show "[x \<noteq> y] (mod int (nat \<bar>x - y\<bar> + 1))"
    proof
      assume "[x = y] (mod int (nat \<bar>x - y\<bar> + 1))"
      hence "\<bar>x - y\<bar> + 1 dvd \<bar>x - y\<bar>"
        by (auto simp: cong_iff_dvd_diff algebra_simps)
      hence "\<bar>x - y\<bar> + 1 \<le> \<bar>x - y\<bar>"
        by (rule zdvd_imp_le) (use \<open>x \<noteq> y\<close> in auto)
      thus False by simp
    qed
  qed auto
  moreover have "x \<in> U" "y \<in> V"
    unfolding U_def V_def by (use \<open>d > 0\<close> in transfer, fastforce)+
  ultimately show ?thesis
    using U_def V_def \<open>0 < d\<close> by blast
qed

subsubsection \<open>Unions of Arithmetic Progressions\<close>

lemma arith_prog_offset_in: \<open>k \<in> arith_prog a b \<Longrightarrow> arith_prog k b = arith_prog a b\<close>
  unfolding arith_prog_def by (simp add: cong_def)

lemma arith_prog_mod: \<open>arith_prog (a mod int b) b = arith_prog a b\<close>
  unfolding arith_prog_def by auto                   

lemma mod_bounds: \<open>b > 0 \<Longrightarrow> a mod int b \<ge> 0 \<and> a mod int b < b\<close>
  by simp

lemma mod_range: \<open>{a mod int b |a. b > 0} \<subseteq> {0..<int b}\<close>
  using mod_bounds by auto

lemma finite_mod_range: \<open>finite {a mod int b |a. b > 0}\<close>
  using mod_range by (meson finite_atLeastLessThan_int finite_subset)

definition arith :: \<open>nat set \<Rightarrow> int set \<Rightarrow> bool\<close> where
  \<open>arith B U \<equiv> \<forall>a \<in> U. \<exists>b \<in> B. b > 0 \<and> arith_prog a b \<subseteq> U\<close>

lemma arith_mono: \<open>arith B U \<Longrightarrow> B \<subseteq> C \<Longrightarrow> arith C U\<close>
  unfolding arith_def by blast

lemma arith_empty_steps: \<open>arith B U \<Longrightarrow> B = {} \<Longrightarrow> U = {}\<close>
  unfolding arith_def by blast

lemma arith_ne_steps: \<open>arith B U \<Longrightarrow> U \<noteq> {} \<Longrightarrow> B \<noteq> {}\<close>
  using arith_empty_steps by blast

lemma arith_decomp:
  assumes \<open>arith B U\<close>
  obtains abs where
    \<open>finite B \<Longrightarrow> finite abs\<close>
    \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close>
    \<open>U = (\<Union>(a, b) \<in> abs. arith_prog a b)\<close>
proof -
  have \<open>\<forall>a\<in>U. \<exists>b \<in> B. b > 0 \<and> arith_prog (a mod int b) b \<subseteq> U\<close>
    using \<open>arith B U\<close> unfolding arith_def using arith_prog_mod by simp
  then obtain f where f: \<open>\<forall>a \<in> U. \<exists>b \<in> B. f a = b \<and> b > 0 \<and> arith_prog (a mod int b) b \<subseteq> U\<close>
    by metis

  let ?abs = \<open>{(a mod int (f a), f a) |a. a \<in> U}\<close>

  have abs: \<open>U = (\<Union>(a, b) \<in> ?abs. arith_prog a b)\<close>
    using f by fastforce

  have \<open>{a mod int (f a) |a. a \<in> U} \<subseteq> (\<Union>b \<in> B. {a mod int b |a. b > 0})\<close>
    using f by blast
  moreover have \<open>finite (\<Union>b \<in> B. {a mod int b |a. b > 0})\<close> if \<open>finite B\<close>
    using that finite_mod_range by fast
  ultimately have \<open>finite {a mod int (f a) |a. a \<in> U}\<close> if \<open>finite B\<close>
    using that by (meson finite_subset)

  moreover have \<open>?abs \<subseteq> {a mod int (f a) |a. a \<in> U} \<times> f ` U\<close>
    by blast
  moreover have fin_f: \<open>finite (f ` U)\<close> if \<open>finite B\<close>
    using that f by (meson finite_subset image_subsetI)
  ultimately have fin_abs: \<open>finite ?abs\<close> if \<open>finite B\<close>
    using that fin_f by (meson finite_SigmaI finite_subset)

  have pos: \<open>\<And>a b. (a, b) \<in> ?abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close>
    using f by blast

  show ?thesis
    using fin_abs pos abs that by meson
qed

lemma arith_UNIV: \<open>arith {1} UNIV\<close>
  unfolding arith_def by blast

lemma arith_empty: "arith B {}"
  unfolding arith_def by blast

lemma finite_case_prod_lcm: \<open>finite B \<Longrightarrow> finite C \<Longrightarrow> finite (case_prod lcm ` (B \<times> C))\<close>
  by blast

lemma arith_inter:
  assumes U: \<open>arith B U\<close> and V: \<open>arith C V\<close>
  shows \<open>arith (case_prod lcm ` (B \<times> C)) (U \<inter> V)\<close>
  unfolding arith_def
proof safe
  fix a
  assume a: \<open>a \<in> U\<close> \<open>a \<in> V\<close>
  
  from a U obtain b where b: \<open>b \<in> B\<close> \<open>b > 0\<close> \<open>arith_prog a b \<subseteq> U\<close>
    unfolding arith_def by auto
  from a V obtain c where c: \<open>c \<in> C\<close> \<open>c > 0\<close> \<open>arith_prog a c \<subseteq> V\<close>
    unfolding arith_def by auto

  with a b c U V have \<open>arith_prog a (lcm b c) \<subseteq> U \<inter> V\<close>
    using arith_prog_dvd_mono[of b \<open>lcm b c\<close> a] arith_prog_dvd_mono[of c \<open>lcm b c\<close> a] by blast
  moreover from b c have \<open>lcm b c > 0\<close>
    using lcm_pos_nat by blast
  ultimately show \<open>\<exists>b\<in>(\<lambda>(x, y). lcm x y) ` (B \<times> C). 0 < b \<and> arith_prog a b \<subseteq> U \<inter> V\<close>
    using b c by blast
qed

lemma arith_Inter:
  assumes \<open>finite X\<close> and X: \<open>\<forall>U \<in> X. arith B U\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>B'. (finite B \<longrightarrow> finite B') \<and> arith B' (\<Inter>X)\<close>
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert U X)
  then show ?case
    using arith_inter finite_case_prod_lcm
    by (metis Inf_insert cInf_singleton insertCI)
qed

lemma arith_union:
  assumes \<open>arith B U\<close> \<open>arith C V\<close>
  shows \<open>arith (B \<union> C) (U \<union> V)\<close>
  using assms unfolding arith_def by (metis Un_iff subset_trans sup_ge1 sup_ge2)

lemma arith_ne_infinite:
  assumes \<open>arith B U\<close> \<open>U \<noteq> {}\<close>
  shows \<open>infinite U\<close>
  using assms unfolding arith_def
  by (meson equals0I infinite_arith_prog rev_finite_subset)

lemma arith_prog_arith [intro]:
  assumes \<open>b > 0\<close>
  shows \<open>arith {b} (arith_prog a b)\<close>
  unfolding arith_def using assms arith_prog_offset_in by blast

lemma arith_prog_complement_arith [intro]:
  assumes \<open>b > 0\<close>
  shows \<open>arith {b} (- arith_prog a b)\<close>
proof -
  have "-arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)"
    using assms arith_prog_complement by blast
  also from assms have "arith {b} \<dots>"
    unfolding arith_def using arith_prog_offset_in by blast
  finally show ?thesis .
qed

lemma arith_complement_arith [intro]:
  assumes \<open>arith B U\<close> \<open>finite B\<close>
  shows \<open>\<exists>B'. finite B' \<and> arith B' (- U)\<close>
proof -
  obtain abs where
    abs: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close> \<open>finite abs\<close> and
    U: \<open>U = (\<Union>(a, b) \<in> abs. arith_prog a b)\<close>
    using assms arith_decomp by metis
  then have *: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> - arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using arith_prog_complement by simp

  have \<open>- U = (\<Inter>(a, b) \<in> abs. - arith_prog a b)\<close>
    using U by blast
  also have \<open>\<dots> = (\<Inter>(a, b) \<in> abs. (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b))\<close>
    using * by blast
  finally have **: \<open>- U = (\<Inter>(a, b) \<in> abs. (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b))\<close> .

  have \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> arith {b} (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using abs * by (metis arith_prog_complement_arith)
  then have ***: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> arith B (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using arith_mono abs by fast

  define X where X: \<open>X \<equiv> (\<lambda>(a, b). \<Union>i\<in>{1..<b}. arith_prog (a + int i) b) ` abs\<close>

  from X have \<open>finite X\<close>
    using abs(2) by simp
  moreover have \<open>\<forall>U\<in>X. arith B U\<close>
    using X *** by fast
  ultimately have \<open>\<exists>B'. finite B' \<and> arith B' (\<Inter> X)\<close>
    using arith_Inter[of X] \<open>finite B\<close> arith_UNIV by fastforce

  moreover from X have \<open>- U = \<Inter>X\<close>
    using ** by simp
  ultimately show ?thesis
    by simp
qed

lemma arith_distinguish:
  assumes \<open>x \<noteq> y\<close>
  shows \<open>\<exists>B U V. finite B \<and> arith B U \<and> arith B V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
proof -
  obtain a b c where
    b: \<open>0 < b\<close> and x: \<open>x \<in> arith_prog a b\<close> and y: \<open>y \<in> arith_prog c b\<close> and
    *: \<open>arith_prog a b \<inter> arith_prog c b = {}\<close>
    using assms arith_prog_distinguish by meson

  let ?B = \<open>{b}\<close>
  let ?U = \<open>arith_prog a b\<close>
  let ?V = \<open>arith_prog c b\<close>
  have \<open>finite ?B \<and> arith ?B ?U \<and> arith ?B ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}\<close>
    using b x y *
    by blast
  then show ?thesis
    by blast
qed

subsubsection \<open>Finite Unions of Arithmetic Progressions\<close>

definition fin_arith :: \<open>int set \<Rightarrow> bool\<close> where
  \<open>fin_arith U \<equiv> \<exists>B. finite B \<and> arith B U\<close>

lemma fin_arith_UNIV [intro]: \<open>fin_arith UNIV\<close>
  unfolding fin_arith_def using arith_UNIV by force

lemma fin_arith_empty [intro]: \<open>fin_arith {}\<close>
  unfolding fin_arith_def using arith_empty by blast

lemma fin_arith_inter [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith V \<Longrightarrow> fin_arith (U \<inter> V)\<close>
  unfolding fin_arith_def using arith_inter finite_case_prod_lcm by metis

lemma fin_arith_union [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith V \<Longrightarrow> fin_arith (U \<union> V)\<close>
  unfolding fin_arith_def using arith_union by blast

lemma fin_arith_compl [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith (- U)\<close>
  unfolding fin_arith_def by blast

lemma fin_arith_distinguish:
  assumes \<open>x \<noteq> y\<close>
  shows \<open>\<exists>U V. fin_arith U \<and> fin_arith V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
  using assms arith_distinguish unfolding fin_arith_def by meson

subsubsection \<open>Singletons\<close>

lemma arith_prog_singleton: \<open>\<Inter>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} = {x}\<close>
proof
  show \<open>\<Inter> {arith_prog a b |a b. 0 < b \<and> x \<in> arith_prog a b} \<subseteq> {x}\<close>
    using arith_prog_distinguish by fast
qed fast

lemma fin_arith_Inter_singleton: \<open>\<Inter>{U |U. fin_arith U \<and> x \<in> U} = {x}\<close>
proof -
  have \<open>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} \<subseteq> {U |U b. arith {b} U \<and> x \<in> U}\<close>
    using arith_prog_arith by blast
  also have \<open>\<dots> \<subseteq> {U |U B. finite B \<and> arith B U \<and> x \<in> U}\<close>
    by force
  finally have \<open>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} \<subseteq> {U |U. fin_arith U \<and> x \<in> U}\<close>
    unfolding fin_arith_def by auto
  then have \<open>\<Inter>{U |U. fin_arith U \<and> x \<in> U} \<subseteq> \<Inter>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b}\<close>
    by blast
  then show ?thesis
    using arith_prog_singleton by auto
qed

lemma singleton_not_finarith: \<open>\<not> fin_arith {x}\<close>
  unfolding fin_arith_def using arith_ne_infinite by blast

subsection \<open>Counterexample\<close>

definition Pss :: \<open>int set set\<close> where
  \<open>Pss \<equiv> {U. fin_arith U}\<close>

lemma Pss_empty: \<open>{} \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_UNIV: \<open>UNIV \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_union: \<open>X \<in> Pss \<Longrightarrow> Y \<in> Pss \<Longrightarrow> X \<union> Y \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_inter: \<open>X \<in> Pss \<Longrightarrow> Y \<in> Pss \<Longrightarrow> X \<inter> Y \<in> Pss\<close>
  unfolding Pss_def by blast
  
lemma Pss_compl: \<open>X \<in> Pss \<Longrightarrow> - X \<in> Pss\<close>
  unfolding Pss_def by blast

definition my_gframe :: \<open>int gframe\<close> where
  \<open>my_gframe \<equiv> \<lparr> \<W> = UNIV, \<R> = \<lambda>x. UNIV, \<Pi> = Pss \<rparr>\<close>

lemma wf_frame_mygframe: \<open>wf_frame (frame.truncate my_gframe)\<close>
  unfolding wf_frame_def unfolds my_gframe_def by blast  

lemma admissible_mygframe: \<open>admissible (frame.truncate my_gframe) (\<Pi> my_gframe)\<close>
  unfolding admissible_def unfolds my_gframe_def Pss_def
  by (auto simp: Compl_eq_Diff_UNIV[symmetric])

lemma wf_mygframe: \<open>wf_gframe my_gframe\<close>
  using wf_frame_mygframe admissible_mygframe
  unfolding wf_gframe_def unfolds my_gframe_def Pss_def by fast

definition my_model :: \<open>(int, int) model\<close> where
  \<open>my_model \<equiv> gframe.extend my_gframe \<lparr>\<N> = \<lambda>i. i, \<NN> = \<lambda>i. int i, \<V> = \<lambda>n. {}, \<VV> = \<lambda>n. {}\<rparr>\<close>

lemma wf_mymodel: \<open>wf_model my_model\<close>
  using wf_mygframe unfolding wf_model_def wf_env_def unfolds my_model_def my_gframe_def Pss_def
  by blast

abbreviation GloE :: \<open>'x fm \<Rightarrow> 'x fm\<close> (\<open>\<^bold>E\<close>) where
  \<open>\<^bold>E p \<equiv> \<^bold>\<not> (\<^bold>A (\<^bold>\<not> p))\<close>

text \<open>Nowhere-or-twice says that if formula p holds somewhere, then it holds in at least two distinct worlds.\<close>
text \<open>(We ignore de Bruijn complications and only instantiate with closed formulas.)\<close>

abbreviation \<open>nowhere_or_twice p \<equiv>
  (\<^bold>\<diamond> p) \<^bold>\<longrightarrow>
  (\<^bold>\<diamond> (\<^bold>\<down> (\<^bold>\<diamond> (\<^bold>\<down> (
    (\<^bold>@ (\<^bold>#1) p) \<^bold>\<and>
    (\<^bold>@ (\<^bold>#0) p) \<^bold>\<and>
    \<^bold>\<not> (\<^bold>@ (\<^bold>#0) (\<^bold>\<bullet>(\<^bold>#1))))))))\<close>

text \<open>Finite unions of arithmetic progressions are either empty or infinite.\<close>

lemma fin_arith_nowhere_or_twice:
  assumes \<open>fin_arith U\<close>
  shows \<open>U = {} \<or> (\<exists>x y. x \<in> U \<and> y \<in> U \<and> x \<noteq> y)\<close>
  using assms arith_ne_infinite unfolding fin_arith_def
  by (metis infinite_int_iff_unbounded less_le_not_le)

text \<open>So nowhere-or-twice holds for all admissible propositions.\<close>

lemma nowhere_or_twice_admissible: \<open>(my_model, x) \<Turnstile> \<^bold>\<forall> (nowhere_or_twice (\<^bold>\<cdot>(\<^bold>#0)))\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_nowhere_or_twice by simp

text \<open>However, propositional quantification lets us form a singleton.\<close>

abbreviation \<open>singleton x \<equiv> \<^bold>\<forall>( \<^bold>@(\<^bold>\<circle>x) (\<^bold>\<cdot>(\<^bold>#0)) \<^bold>\<longrightarrow> \<^bold>\<cdot>(\<^bold>#0) )\<close>

lemma singleton: \<open>((my_model, x) \<Turnstile> singleton y) \<longleftrightarrow> x = y\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_Inter_singleton by auto

lemma fin_arith_distinguish':
  \<open>\<forall>P. fin_arith P \<longrightarrow> y \<in> P \<longrightarrow> v \<in> P \<Longrightarrow> v \<noteq> w \<Longrightarrow> \<exists>P. y \<in> P \<and> fin_arith P \<and> w \<notin> P\<close>
  by (metis disjoint_iff fin_arith_distinguish)

text \<open>The singleton does not hold nowhere-or-twice.\<close>

lemma not_nowhere_or_twice_singleton: \<open>\<not> (my_model, x) \<Turnstile> nowhere_or_twice (singleton y)\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_distinguish' by auto

text \<open>So we cannot always eliminate a quantifier with a non-quantifier-free formula.\<close>
  
theorem counter:
  shows \<open>\<not> (my_model, x) \<Turnstile> \<^bold>\<forall> (nowhere_or_twice (\<^bold>\<cdot>(\<^bold>#0))) \<^bold>\<longrightarrow> nowhere_or_twice (singleton y)\<close>
  using nowhere_or_twice_admissible not_nowhere_or_twice_singleton
  by (meson semantics.simps(3,4))

end
