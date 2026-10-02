theory HOL_in_HOL_Deep_Infinity_ZFC
  imports HOL_Universe "ZFC_in_HOL.ZFC_Cardinals" "ZFC_in_HOL.Kirby"
begin

section \<open>The set-theoretic instantiation: \<open>V\<close> as a \<open>hol_universe\<close>\<close>

text \<open>This theory supplies the one ingredient the abstract half \<open>HOL_Universe\<close> leaves open: a
  type satisfying the \<open>hol_universe\<close> assumptions.  Over Paulson's \<^session>\<open>ZFC_in_HOL\<close> the
  individuals are interpreted as the finite ordinals \<^term>\<open>\<omega>\<close> and every function space is
  full, so the successor map witnesses Dedekind infinity and all assumptions of the locale are
  discharged.  The consistency of full classical \<open>HOL\<close> and of \<open>NK\<close> with \<open>DInf\<close> then fall out
  of the abstract theorems; \<open>V\<close> also validates the at most as strong Harrison-style
  interface \<open>harrison_universe\<close> outright --- and that most abstract interface carries the
  exported consistency theorem; a rank bound closes the development, showing every domain of
  the witnessing model lives inside the set \<open>Vset (\<omega> + \<omega>)\<close>.  Only this theory imports \<open>ZFC_in_HOL\<close>.\<close>

subsection \<open>Domains, application, abstraction\<close>

primrec D :: "ty \<Rightarrow> V" where
  "D \<iota> = \<omega>"
| "D \<o> = set {0, 1}"
| "D (\<sigma> \<^bold>\<Rightarrow> \<tau>) = VPi (D \<sigma>) (\<lambda>_. D \<tau>)"

definition VD :: "ty \<Rightarrow> V \<Rightarrow> bool" where "VD \<sigma> v \<equiv> v \<in> elts (D \<sigma>)"
definition VLm :: "ty \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" where "VLm \<sigma> h \<equiv> VLambda (D \<sigma>) h"

lemma VD_bool: "VD \<o> v \<longleftrightarrow> v = 0 \<or> v = 1" by (simp add: VD_def)

lemma VD_nonempty: "\<exists>v. VD \<sigma> v"
proof (induction \<sigma>)
  case (Fun \<sigma> \<tau>)
  then obtain w where w: "w \<in> elts (D \<tau>)" by (auto simp: VD_def)
  have "VLambda (D \<sigma>) (\<lambda>_. w) \<in> elts (D (\<sigma> \<^bold>\<Rightarrow> \<tau>))" by (simp add: VPi_I w)
  thus ?case by (auto simp: VD_def)
qed (auto simp: VD_def)

lemma D_nonempty_elts: "\<exists>v. v \<in> elts (D \<sigma>)"
  using VD_nonempty[of \<sigma>] by (simp add: VD_def)

lemma VLm_beta: "VD \<sigma> a \<Longrightarrow> app (VLm \<sigma> h) a = h a" by (simp add: VLm_def VD_def)
lemma VLm_dom: "(\<And>d. VD \<sigma> d \<Longrightarrow> VD \<tau> (h d)) \<Longrightarrow> VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) (VLm \<sigma> h)"
  by (simp add: VLm_def VD_def VPi_I)
lemma VAp_dom: "VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f \<Longrightarrow> VD \<sigma> a \<Longrightarrow> VD \<tau> (app f a)"
  by (metis D.simps(3) VD_def VPi_D)
lemma VAp_ext:
  "VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f \<Longrightarrow> VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) g \<Longrightarrow> (\<And>a. VD \<sigma> a \<Longrightarrow> app f a = app g a) \<Longrightarrow> f = g"
  by (metis D.simps(3) VD_def fun_ext)

definition VJv :: "'p \<Rightarrow> ty \<Rightarrow> V" where "VJv p \<sigma> = (SOME v. v \<in> elts (D \<sigma>))"

lemma VJv_dom: "VD \<sigma> (VJv p \<sigma>)"
  unfolding VJv_def VD_def using D_nonempty_elts[of \<sigma>] by (rule someI_ex)

lemma VJv_param_independent: "VJv p \<sigma> = VJv q \<sigma>"
  by (simp add: VJv_def)

text \<open>The \<open>V\<close>-frame discharges the Dedekind-infinity assumption \<open>ind_inf\<close> of \<open>hol_universe\<close>
  (verbatim the frame premise of @{thm [source] con_full_HOL_rel}): the successor on \<open>\<omega>\<close> is
  an injective, non-surjective self-map of the individuals.\<close>

lemma V_inf:
  "\<exists>d. VD (\<iota> \<^bold>\<Rightarrow> \<iota>) d
       \<and> (\<forall>a. VD \<iota> a \<longrightarrow> (\<forall>b. VD \<iota> b \<longrightarrow> (app d a = app d b \<longrightarrow> a = b)))
       \<and> (\<exists>c. VD \<iota> c \<and> (\<forall>z. VD \<iota> z \<longrightarrow> app d z \<noteq> c))"
proof -
  have beta: "app (VLm \<iota> succ) a = succ a" if "VD \<iota> a" for a by (rule VLm_beta[OF that])
  have dom: "VD (\<iota> \<^bold>\<Rightarrow> \<iota>) (VLm \<iota> succ)" by (rule VLm_dom) (simp add: VD_def)
  have injv: "\<forall>a. VD \<iota> a \<longrightarrow> (\<forall>b. VD \<iota> b \<longrightarrow> (app (VLm \<iota> succ) a = app (VLm \<iota> succ) b \<longrightarrow> a = b))"
    by (auto simp: beta)
  have nsv: "\<exists>c. VD \<iota> c \<and> (\<forall>z. VD \<iota> z \<longrightarrow> app (VLm \<iota> succ) z \<noteq> c)"
    by (rule exI[of _ 0]) (auto simp: beta VD_def)
  show ?thesis using dom injv nsv by blast
qed

text \<open>\<open>V\<close> is such a universe: the \<open>hol_universe\<close> assumptions are satisfiable (relative to
  \<open>ZF\<close>) --- yet they demand far less than full \<open>ZF\<close>.\<close>

theorem V_hol_universe:
  "hol_universe VD app VLm (1::V) 0 (VJv :: 'p \<Rightarrow> ty \<Rightarrow> V)"
proof unfold_locales
  show "\<And>\<sigma> \<tau> g k. VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) g \<Longrightarrow> VD (\<sigma> \<^bold>\<Rightarrow> \<tau>) k \<Longrightarrow>
         (\<And>a. VD \<sigma> a \<Longrightarrow> app g a = app k a) \<Longrightarrow> g = k" by (rule VAp_ext)
qed(auto intro!: V_inf VJv_dom VAp_dom VLm_dom VLm_beta simp: VD_bool)

subsection \<open>The standard model, by instantiation\<close>

text \<open>The constructed constants of the locale turn the \<open>V\<close>-frame into a standard model
  outright --- no hand-built logical constants over \<open>V\<close> are needed.  This natural model
  carries the Dedekind witness and the rank bound below; the consistency
  @{emph \<open>theorem\<close>} itself is exported once, from the Harrison-style interface
  in the next subsection.\<close>

lemmas V_standard_model =
  lambda_universe.is_standard_model[OF hol_universe.axioms(1)[OF V_hol_universe]]

subsection \<open>\<open>V\<close> validates the Harrison-style axiom, and consistency follows\<close>

text \<open>The at most as strong interface \<open>harrison_universe\<close> --- our rendering of Harrison's
  universe axiom --- is likewise validated by \<open>V\<close> directly: pairing is \<^term>\<open>vpair\<close>, a
  collection is small in the sense of the locale iff it is \<open>small\<close>, its code is Paulson's
  \<open>set\<close>, and the individuals are again the finite ordinals.  The coded-power closure is
  exactly \<open>VPow\<close> seen through the coding.  The locale rebuilds domains, application and
  abstraction from these four constants alone, so the headline consistency theorem rests
  on nothing beyond them --- one spine, through the most abstract interface.\<close>

lemma V_enc_inj:
  assumes "small {x. X x}" and "small {x. Y x}" and "set {x. X x} = set {x. Y x}"
  shows "X = Y"
proof -
  have "{x. X x} = {x. Y x}" using arg_cong[OF assms(3), of elts] assms(1,2) by simp
  thus ?thesis unfolding fun_eq_iff by (metis mem_Collect_eq)
qed

lemma V_small_sub: assumes "small {x. X x}" and "Y \<le> X" shows "small {x. Y x}"
proof (rule smaller_than_small[OF assms(1)])
  show "{x. Y x} \<subseteq> {x. X x}" using assms(2) by (auto simp: le_fun_def)
qed

lemma V_small_prod:
  assumes "small {x. X x}" and "small {x. Y x}"
  shows "small {z. \<exists>a b. X a \<and> Y b \<and> z = vpair a b}"
proof -
  have "{z. \<exists>a b. X a \<and> Y b \<and> z = vpair a b} = (\<lambda>(a, b). vpair a b) ` ({x. X x} \<times> {x. Y x})"
    by auto
  thus ?thesis using assms by simp
qed

lemma V_small_pow:
  assumes sX: "small {x. X x}"
  shows "small {z. \<exists>Y. Y \<le> X \<and> small {x. Y x} \<and> z = set {x. Y x}}"
proof (rule smaller_than_small[OF small_elts])
  show "{z. \<exists>Y. Y \<le> X \<and> small {x. Y x} \<and> z = set {x. Y x}} \<subseteq> elts (VPow (set {x. X x}))"
  proof
    fix z assume "z \<in> {z. \<exists>Y. Y \<le> X \<and> small {x. Y x} \<and> z = set {x. Y x}}"
    then obtain Y where Y: "Y \<le> X" and sY: "small {x. Y x}" and z: "z = set {x. Y x}"
      by blast
    have "elts z \<subseteq> elts (set {x. X x})" using Y sX sY by (auto simp: z le_fun_def)
    thus "z \<in> elts (VPow (set {x. X x}))" by (simp add: less_eq_V_def)
  qed
qed

lemma V_omega_inf:
  "\<exists>f c. (\<forall>a. a \<in> elts \<omega> \<longrightarrow> f a \<in> elts \<omega>)
       \<and> (\<forall>a b. a \<in> elts \<omega> \<longrightarrow> b \<in> elts \<omega> \<longrightarrow> f a = f b \<longrightarrow> a = b)
       \<and> c \<in> elts \<omega> \<and> (\<forall>a. a \<in> elts \<omega> \<longrightarrow> f a \<noteq> c)"
  by (intro exI[of _ succ] exI[of _ 0]) (auto simp: succ_neq_zero)

theorem V_harrison_universe:
  "harrison_universe vpair (\<lambda>X. set {x. X x}) (\<lambda>X. small {x. X x}) (\<lambda>x. x \<in> elts \<omega>)"
proof unfold_locales
  show "\<And>X Y. small {x. X x} \<Longrightarrow> small {x. Y x} \<Longrightarrow> set {x. X x} = set {x. Y x} \<Longrightarrow> X = Y"
    by (rule V_enc_inj)
  show "\<And>X Y. small {x. X x} \<Longrightarrow> Y \<le> X \<Longrightarrow> small {x. Y x}" by (rule V_small_sub)
qed(safe intro!: V_omega_inf V_small_pow V_small_prod | simp)+

theorem con_full_HOL:
  "con (insert (DInf :: 'p tm) (range (\<lambda>(\<sigma>,\<tau>). ACrel \<sigma> \<tau>)))"
  by (rule harrison_universe.con_full_HOL_harrison[OF V_harrison_universe])

subsection \<open>The Dedekind axiom of infinity and a countable Henkin witness\<close>

text \<open>The infinity-only consistency \<open>con {DInf}\<close> is the same \<open>V\<close>-model argument, now feeding the
  successor witness on \<open>\<omega>\<close> to the carrier-generic \<open>DInf_sat\<close>; it holds for \<^emph>\<open>every\<close> parameter
  type \<open>'p\<close>.  The \<^emph>\<open>countable\<close> model that witnesses it is the ZFC-free term model of
  @{thm [source] countable_henkin_sat}, so a set-theoretic universe enters \<^emph>\<open>only\<close> through the
  consistency premise --- the model itself has a countable total domain, carved out of the
  carrier \<^typ>\<open>'p tm set\<close>, and never mentions \<^typ>\<open>V\<close>.\<close>

theorem con_DInf: "con ({DInf} :: 'p tm set)"
proof -
  interpret U: hol_universe VD app VLm "1::V" "0::V" "VJv :: 'p \<Rightarrow> ty \<Rightarrow> V"
    by (rule V_hol_universe)
  interpret standard_model VD app VLm "1::V" "0::V"
    U.Ngv U.Dsv U.Iv U.Ev U.Piv "VJv :: 'p \<Rightarrow> ty \<Rightarrow> V"
    by (rule U.is_standard_model)
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> V" where "\<xi> = (\<lambda>n \<tau>. SOME v. VD \<tau> v)"
  have xi: "bkkA.asg \<xi>"
    unfolding bkkA.asg_def \<xi>_def using VD_nonempty by (metis someI_ex)
  \<comment> \<open>the successor on \<open>\<omega>\<close> is an injective, non-surjective self-map of the individuals\<close>
  define f0 :: V where "f0 = VLm \<iota> succ"
  have f0dom: "VD (\<iota> \<^bold>\<Rightarrow> \<iota>) f0" unfolding f0_def by (rule VLm_dom) (simp add: VD_def)
  have f0app: "app f0 a = succ a" if "VD \<iota> a" for a
    unfolding f0_def by (rule VLm_beta[OF that])
  have satD: "den (DInf :: 'p tm) \<xi> = 1"
  proof (rule DInf_sat[OF xi f0dom])
    show "\<forall>a. VD \<iota> a \<longrightarrow> (\<forall>b. VD \<iota> b \<longrightarrow> (app f0 a = app f0 b \<longrightarrow> a = b))"
      by (auto simp: f0app)
    show "\<exists>c. VD \<iota> c \<and> (\<forall>z. VD \<iota> z \<longrightarrow> app f0 z \<noteq> c)"
      by (rule exI[of _ 0]) (auto simp: f0app VD_def)
  qed
  show ?thesis by (rule model_con[OF xi]) (use wff_DInf satD in auto)
qed

theorem countable_henkin_model_DInf:
  obtains Dm Ap
      and Ee :: "(nat \<Rightarrow> ty \<Rightarrow> 'p::{countable,infinite} tm set) \<Rightarrow> 'p tm \<Rightarrow> 'p tm set"
      and vl \<xi>
  where "bkk_model Dm Ap Ee vl" "countable {x. \<exists>\<tau>. Dm \<tau> x}"
        "app_struct.asg Dm \<xi>" "vl (Ee \<xi> (DInf :: 'p tm))"
  by (rule countable_henkin_sat[OF cwff_DInf con_DInf])

text \<open>The converse half of the separation of axiom and scheme.  The main entry proves that
  the infinity @{emph \<open>scheme\<close>} does not yield the axiom (\<open>Diag_not_derives_DInf\<close>,
  \<open>henkin_scheme_refutes_DInf\<close> in its \<open>NK_Infinity\<close>).  The \<open>V\<close>-model settles the other
  direction: its parameter interpretation \<open>VJv\<close> is constant at each type
  (@{thm [source] VJv_param_independent}), so all diagram
  constants denote the same individual and every inequation \<open>dneq f i j\<close> is refuted, while
  \<open>DInf\<close> holds.  By soundness the axiom derives no diagram inequation --- as
  @{emph \<open>sentences\<close>}, axiom and scheme are incomparable.\<close>

theorem DInf_not_derives_dneq:
  fixes f :: "nat \<Rightarrow> 'p::infinite"
  shows "\<not> ({DInf} \<turnstile> dneq f i j)"
proof
  assume d: "{DInf} \<turnstile> dneq f i j"
  interpret U: hol_universe VD app VLm "1::V" "0::V" "VJv :: 'p \<Rightarrow> ty \<Rightarrow> V"
    by (rule V_hol_universe)
  interpret standard_model VD app VLm "1::V" "0::V"
    U.Ngv U.Dsv U.Iv U.Ev U.Piv "VJv :: 'p \<Rightarrow> ty \<Rightarrow> V"
    by (rule U.is_standard_model)
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> V" where "\<xi> = (\<lambda>n \<tau>. SOME v. VD \<tau> v)"
  have xi: "bkkA.asg \<xi>"
    unfolding bkkA.asg_def \<xi>_def using VD_nonempty by (metis someI_ex)
  \<comment> \<open>\<open>DInf\<close> holds, by the successor witness of \<open>con_DInf\<close>\<close>
  define f0 :: V where "f0 = VLm \<iota> succ"
  have f0dom: "VD (\<iota> \<^bold>\<Rightarrow> \<iota>) f0" unfolding f0_def by (rule VLm_dom) (simp add: VD_def)
  have f0app: "app f0 a = succ a" if "VD \<iota> a" for a
    unfolding f0_def by (rule VLm_beta[OF that])
  have satD: "den (DInf :: 'p tm) \<xi> = 1"
  proof (rule DInf_sat[OF xi f0dom])
    show "\<forall>a. VD \<iota> a \<longrightarrow> (\<forall>b. VD \<iota> b \<longrightarrow> (app f0 a = app f0 b \<longrightarrow> a = b))"
      by (auto simp: f0app)
    show "\<exists>c. VD \<iota> c \<and> (\<forall>z. VD \<iota> z \<longrightarrow> app f0 z \<noteq> c)"
      by (rule exI[of _ 0]) (auto simp: f0app VD_def)
  qed
  \<comment> \<open>the inequation fails: both parameters denote the same individual\<close>
  have peq: "den ((f i)\<^sup>p\<^bsub>\<iota>\<^esub> \<^bold>=\<^bsub>\<iota>\<^esub> (f j)\<^sup>p\<^bsub>\<iota>\<^esub>) \<xi> = 1"
    using sat_PEqB[OF wff_Par wff_Par xi] VJv_param_independent[of "f i" \<iota> "f j"] by simp
  have nsat: "den (dneq f i j) \<xi> \<noteq> 1"
    unfolding dneq_def
    using sat_NegB[OF wff_PEq[OF wff_Par wff_Par] xi] peq by simp
  have "den (dneq f i j) \<xi> = 1"
    by (rule soundness_bkk[OF d bkk_model_pred xi]) (use wff_DInf satD in auto)
  with nsat show False by simp
qed

subsection \<open>The universe has bounded rank: no replacement, no proper class\<close>

text \<open>The rank bound is now made precise: \<^emph>\<open>every\<close> domain \<open>D \<sigma>\<close> has rank below \<open>\<omega> + \<omega>\<close> (that is,
  \<open>\<omega> \<cdot> 2\<close>), so every domain is an element of the \<^emph>\<open>set\<close> \<open>Vset (\<omega> + \<omega>)\<close>.  The domain of individuals
  sits at rank \<open>\<omega>\<close>, and each function-space layer \<open>D (\<sigma> \<^bold>\<Rightarrow> \<tau>) = VPi (D \<sigma>) (\<lambda>_. D \<tau>)\<close> --- contained in
  \<open>VPow (VPow (VPow (D \<sigma> \<squnion> D \<tau>)))\<close> --- raises the rank by only three, which the limit ordinal
  \<open>\<omega> + \<omega>\<close> absorbs.\<close>

lemma rank_D_iota: "rank (D \<iota>) = \<omega>" by (simp add: rank_of_Ord)

lemma rank_VPow_le: "rank (VPow x) \<le> succ (rank x)"
proof -
  have small: "small ((\<lambda>y. succ (rank y)) ` elts (VPow x))" by simp
  have "rank (VPow x) = \<Squnion>((\<lambda>y. succ (rank y)) ` elts (VPow x))" by (rule rank_Sup)
  also have "\<dots> \<le> succ (rank x)"
    unfolding SUP_le_iff[OF small]
  proof
    fix y assume "y \<in> elts (VPow x)"
    hence "y \<le> x" by simp
    hence "rank y \<le> rank x" by (rule rank_mono)
    thus "succ (rank y) \<le> succ (rank x)" by (simp add: le_succ_iff)
  qed
  finally show ?thesis .
qed

lemma sup_Sup_pair: "(a::V) \<squnion> b = \<Squnion> {a, b}"
proof (rule order_antisym)
  have "a \<le> \<Squnion> {a, b}" by (intro Sup_upper) auto
  moreover have "b \<le> \<Squnion> {a, b}" by (intro Sup_upper) auto
  ultimately show "a \<squnion> b \<le> \<Squnion> {a, b}" by simp
  show "\<Squnion> {a, b} \<le> a \<squnion> b" by (rule Sup_least) auto
qed

lemma rank_sup_eq: "rank (a \<squnion> b) = rank a \<squnion> rank b"
  by (simp add: sup_Sup_pair rank_Union)

lemma VPi_le_VPow: "VPi A B \<le> VPow (VSigma A B)"
  by (auto simp: VPi_def less_eq_V_def)

lemma VSigma_const_le: "VSigma A (\<lambda>_. C) \<le> VPow (VPow (A \<squnion> C))"
proof (subst less_eq_V_def, rule subsetI)
  fix p assume "p \<in> elts (VSigma A (\<lambda>_. C))"
  then obtain a b where p: "p = \<langle>a, b\<rangle>" and a: "a \<in> elts A" and b: "b \<in> elts C" by auto
  have "\<langle>a, b\<rangle> \<le> VPow (A \<squnion> C)"
    unfolding vpair_def' using a b by (auto simp: less_eq_V_def)
  thus "p \<in> elts (VPow (VPow (A \<squnion> C)))" using p by auto
qed

lemma Limit_ww: "Limit (\<omega> + \<omega>)" by simp

lemma succ_lt_ww:
  assumes "Ord \<beta>" and "\<beta> < \<omega> + \<omega>" shows "succ \<beta> < \<omega> + \<omega>"
proof -
  have O: "Ord (\<omega> + \<omega>)" using Limit_ww Limit_is_Ord by blast
  from assms O have "\<beta> \<in> elts (\<omega> + \<omega>)" by (simp add: Ord_mem_iff_lt)
  with Limit_ww have "succ \<beta> \<in> elts (\<omega> + \<omega>)" by (simp add: Limit_def)
  with O show ?thesis by (blast intro: OrdmemD)
qed

lemma omega_lt_ww: "\<omega> < \<omega> + \<omega>"
proof -
  have "(0::V) < \<omega>" by (metis OrdmemD Ord_\<omega> zero_in_omega)
  hence "\<omega> + 0 < \<omega> + \<omega>" by simp
  thus ?thesis by simp
qed

lemma rank_VPi_const_lt:
  assumes "rank A < \<omega> + \<omega>" and "rank C < \<omega> + \<omega>"
  shows "rank (VPi A (\<lambda>_. C)) < \<omega> + \<omega>"
proof -
  have s1: "rank (VPi A (\<lambda>_. C)) \<le> succ (rank (VSigma A (\<lambda>_. C)))"
    by (rule order_trans[OF rank_mono[OF VPi_le_VPow] rank_VPow_le])
  have "rank (VSigma A (\<lambda>_. C)) \<le> succ (rank (VPow (A \<squnion> C)))"
    by (rule order_trans[OF rank_mono[OF VSigma_const_le] rank_VPow_le])
  also have "\<dots> \<le> succ (succ (rank (A \<squnion> C)))"
    by (simp add: le_succ_iff Ord_succ rank_VPow_le)
  finally have s2: "rank (VSigma A (\<lambda>_. C)) \<le> succ (succ (rank (A \<squnion> C)))" .
  have "succ (rank (VSigma A (\<lambda>_. C))) \<le> succ (succ (succ (rank (A \<squnion> C))))"
    using s2 by (simp add: le_succ_iff Ord_succ)
  with s1 have s3: "rank (VPi A (\<lambda>_. C)) \<le> succ (succ (succ (rank (A \<squnion> C))))"
    by (rule order_trans)
  have r: "rank (A \<squnion> C) < \<omega> + \<omega>"
    using assms by (simp add: rank_sup_eq)
  have "succ (rank (A \<squnion> C)) < \<omega> + \<omega>" using r by (simp add: succ_lt_ww)
  hence "succ (succ (rank (A \<squnion> C))) < \<omega> + \<omega>" by (simp add: succ_lt_ww Ord_succ)
  hence "succ (succ (succ (rank (A \<squnion> C)))) < \<omega> + \<omega>" by (simp add: succ_lt_ww Ord_succ)
  with s3 show ?thesis by (rule order_le_less_trans)
qed

theorem rank_D_lt: "rank (D \<sigma>) < \<omega> + \<omega>"
proof (induction \<sigma>)
  case Ind thus ?case by (simp add: rank_of_Ord omega_lt_ww)
next
  case Bool
  have "D \<o> \<le> \<omega>" by (auto simp: less_eq_V_def one_V_def)
  hence "rank (D \<o>) \<le> \<omega>" by (metis Ord_\<omega> rank_mono rank_of_Ord)
  thus ?case using omega_lt_ww by (rule order_le_less_trans)
next
  case (Fun \<sigma> \<tau>)
  have "rank (D (\<sigma> \<^bold>\<Rightarrow> \<tau>)) = rank (VPi (D \<sigma>) (\<lambda>_. D \<tau>))" by simp
  thus ?case using Fun.IH by (simp add: rank_VPi_const_lt)
qed

text \<open>Hence \<open>D \<sigma> \<in> elts (Vset (\<omega> + \<omega>))\<close> for every type: each domain of the witnessing
  model is an element of the \<^emph>\<open>set\<close> \<open>Vset (\<omega> + \<omega>)\<close>.\<close>

lemma D_in_Vset_ww: "D \<sigma> \<in> elts (Vset (\<omega> + \<omega>))"
  by (rule Ord_VsetI) (simp_all add: rank_D_lt)


end
