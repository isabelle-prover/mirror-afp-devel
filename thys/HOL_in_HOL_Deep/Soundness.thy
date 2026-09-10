theory Soundness
  imports Calculus
begin

section \<open>Soundness\<close>

text \<open>This section proves \<open>NK\<close> sound for the model class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close>
  (BKK Theorem 7.3, including BKK's evaluation-variant argument).\<close>

subsection \<open>The canonical construction respects \<open>\<beta>\<close>-conversion (BKK Remark 3.19)\<close>

text \<open>In a \<open>\<Sigma>\<close>-Henkin model, \<open>\<beta>\<close>-convertible terms denote the same object under any total
  assignment; the abstraction-congruence case uses functionality (property f).\<close>

context general_model
begin

lemma beq_den: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> (\<forall>n \<tau>. \<D>\<^bsub>\<tau>\<^esub> (\<xi> n \<tau>)) \<Longrightarrow> \<lparr>s\<rparr>\<^bsub>\<xi>\<^esub> = \<lparr>t\<rparr>\<^bsub>\<xi>\<^esub>"
proof (induction arbitrary: \<xi> rule: beq.induct)
  case beta thus ?case using den_App_Abs resp_def by auto
next
  case (abs L b \<sigma> \<tau> b')
  define x where "x = fresh (L \<union> fvs b \<union> fvs b')"
  have xL: "x \<notin> L" and xb: "x \<notin> fvs b" and xb': "x \<notin> fvs b'"           
    using fresh_notin[of "L \<union> fvs b \<union> fvs b'"] abs unfolding x_def by auto
  have wb: "wff\<^bsub>\<tau>\<^esub>(b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)" and wb': "wff\<^bsub>\<tau>\<^esub>(b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    using beq_wffL beq_wffR abs xL by blast+
  {
    fix a
    assume a: "\<D>\<^bsub>\<sigma>\<^esub> a"
    hence tot: "\<forall>n \<gamma>. \<D>\<^bsub>\<gamma>\<^esub> (\<xi>(x\<^bsub>\<sigma>\<^esub> := a) n \<gamma>)"
      using abs.prems by (auto simp: upd_def)
    have "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>b\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
        by (rule gm_beta[OF wb xb abs.prems a])
    also have "\<dots> = \<lparr>b'\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>\<rparr>\<^bsub>\<xi>(x\<^bsub>\<sigma>\<^esub> := a)\<^esub>"
      using abs.IH[OF xL, of "\<xi>(x\<^bsub>\<sigma>\<^esub> := a)"] tot by blast
    also have "\<dots> = \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b'\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a"
      using gm_beta wb' xb' abs.prems a by simp
    finally have "\<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a = \<lparr>\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b'\<rparr>\<^bsub>\<xi>\<^esub> \<^bold>@ a".
  }
  thus ?case
    using gm_funct gm_lamTy wff_Abs_open_rev wb xb abs.prems wb' xb' by blast
qed(auto simp: den.simps(8))

end

subsection \<open>Abstract soundness (BKK Theorem 7.3)\<close>

text \<open>Soundness over the abstract \<open>\<Sigma>\<close>-models of Section 2, following BKK's
  proof of Theorem 7.3 case by case.  The \<open>NK(\<Pi>I)\<close> case uses BKK's device verbatim:
  ``from the evaluation function \<open>E\<close>, one can define another evaluation function \<open>E'\<close>
  such that \<open>E'(w) \<equiv> a\<close> and \<open>E'\<^bsub>\<phi>\<^esub>(A) \<equiv> E\<^bsub>\<phi>\<^esub>(A)\<close> if \<open>w\<close> does not occur in \<open>A\<close>'' ---
  realised below by reading the parameter as a fresh variable after an injective shift
  of all free variables.  The extensionality cases \<open>NK(f)\<close> and \<open>NK(b)\<close> rest on BKK's
  Lemma 4.2 on Leibniz equality, proven here abstractly (BKK themselves route them
  through Theorem 4.3(3) and Lemma 3.48/Theorem 4.3(4), which rest on Lemma 4.2).\<close>

subsubsection \<open>The variable shift\<close>

text \<open>\<open>vshift\<close> renames every free variable \<open>n\<close> to \<open>n + 1\<close>, freeing the name \<open>0\<close> at every
  type; \<open>\<beta>\<close>-equality and typing are stable under it and under the parameter-to-variable
  rename \<open>pvar\<close>.\<close>

definition vshift :: "'p tm \<Rightarrow> 'p tm" where "vshift = msub (\<lambda>n \<tau>. (Suc n)\<^sup>f\<^bsub>\<tau>\<^esub>)"
lemma occ_vshift: "occ (vshift t) = (\<lambda>(n, \<tau>). (Suc n, \<tau>)) ` occ t"
  unfolding vshift_def by (induction t) (auto simp: image_Un)
lemma pars_vshift: "pars (vshift t) = pars t"
  unfolding vshift_def by (induction t) auto
lemma wff_vshift: "wff\<^bsub>\<tau>\<^esub>(t) \<Longrightarrow> wff\<^bsub>\<tau>\<^esub>(vshift t)"
  by (auto elim: wff_msub intro: wff_Fre simp: vshift_def)
lemma vshift_opn: "vshift (t\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) = (vshift t)\<^bold>\<langle>(Suc x)\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>"
  unfolding vshift_def by (subst msub_opn) auto
lemma beq_vshift: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> vshift s \<approx>\<^bsub>\<rho>\<^esub> vshift t"
proof (induction rule: beq.induct)
  case (beta \<sigma> \<rho> b a)
  moreover have "vshift ((\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b) \<^bold>\<cdot> a) = (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b)) \<^bold>\<cdot> (vshift a)"
    by (simp add: vshift_def)
  moreover have "vshift (b\<^bold>\<langle>a\<^bold>\<rangle>) = (vshift b)\<^bold>\<langle>vshift a\<^bold>\<rangle>"
    unfolding vshift_def by (subst msub_opn) auto
  moreover have "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<rho>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b))"
    using wff_vshift beta unfolding vshift_def by force
  ultimately show ?case using beq.beta wff_vshift by metis
next case appL thus ?case by (metis beq.appL msub.simps(9) vshift_def wff_vshift)
next case appR thus ?case by (metis beq.appR msub.simps(9) vshift_def wff_vshift)
next case (abs L b \<sigma> \<tau> b')
  have "\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b) \<approx>\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub> \<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b')" 
  proof (rule beq.abs[of "{0} \<union> Suc ` L"])
    show "finite ({0} \<union> Suc ` L)" using abs.hyps(1) by simp
    fix y assume y: "y \<notin> {0} \<union> Suc ` L"
    then obtain x where x: "y = Suc x" "x \<notin> L" by (cases y) auto
    show "(vshift b)\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle> \<approx>\<^bsub>\<tau>\<^esub> (vshift b')\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>" using abs.IH[OF x(2)]
      by (simp add: x(1) vshift_opn[symmetric])
  qed
  thus ?case by (simp add: vshift_def)
qed(auto simp: wff_vshift intro: beq.intros)

lemma beq_pvar: "s \<approx>\<^bsub>\<rho>\<^esub> t \<Longrightarrow> pvar w \<sigma>w x s \<approx>\<^bsub>\<rho>\<^esub> pvar w \<sigma>w x t"
proof (induction rule: beq.induct)
  case beta thus ?case by (smt (verit, best) beq.simps pvar.simps(10,9) pvar_opn wff_pvar)
qed(auto simp: wff_pvar beq.abs pvar_opn intro: beq.intros)

lemma occ_pvar: "occ (pvar w \<sigma>w x t) \<subseteq> occ t \<union> {(x, \<sigma>w)}"
  by (induction t) auto

subsubsection \<open>Satisfaction of Leibniz equality (BKK Lemma 4.2)\<close>

text \<open>Leibniz equality \<open>\<beta>\<close>-reduces to its \<open>\<forall>\<close>-form (the syntactic prelude to Lemma 4.2).\<close>

lemma Leib_beq: assumes wA: "wff\<^bsub>\<alpha>\<^esub>(A)" and wB: "wff\<^bsub>\<alpha>\<^esub>(B)"
  shows "(A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B))"
proof -
  have lcA: "lc A" and lcB: "lc B" using wA wB by (auto intro: wff_lc)
  let ?inner = "\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> (\<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> Bnd 1)))"
  have "(Leib \<alpha> \<^bold>\<cdot> A) \<approx>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ?inner"
    using beq.beta[OF wff_Leib[unfolded Leib_def] wA]
    unfolding Leib_def by (simp add: opn_lc[OF lcA])
  moreover {
    have "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(?inner)" using beq_wffR calculation by blast
    with beq.beta[OF this wB]
    have "(?inner \<^bold>\<cdot> B) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<Pi>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ((Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B))"
      using opn_lc[OF lcA] opn_lc[OF lcB] by simp
  }
  ultimately show ?thesis using beq.trans beq.appL wB by blast
qed

context sigma_model
begin

lemma sat_Leib: assumes wA: "wff\<^bsub>\<alpha>\<^esub>(A)" and wB: "wff\<^bsub>\<alpha>\<^esub>(B)" and xi: "asg \<xi>"
  shows "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)) \<longleftrightarrow> Ee \<xi> A = Ee \<xi> B"
proof -
  have lcA: "lc A" and lcB: "lc B" using wA wB by (auto intro: wff_lc)
  define p where "p = fresh (fvs A \<union> fvs B)"
  have p: "p \<notin> fvs A" "p \<notin> fvs B"
    unfolding p_def using fresh_notin[of "fvs A \<union> fvs B"] by auto
  let ?b = "(Bnd 0 \<^bold>\<cdot> A) \<^bold>\<supset> (Bnd 0 \<^bold>\<cdot> B)"
  have wI: "wff\<^bsub>(\<alpha>\<^bold>\<Rightarrow>\<o>)\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub> ?b)"
    by (smt (verit, del_insts) ImpB_def lcA lcB opn.simps(1,4,5,9) opn_lc wA wB
        wff_AbsI wff_App wff_Fre wff_ImpB)
  have pf: "p \<notin> fvs ?b" using p by (auto simp: ImpB_def)
  have unf: "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B)) \<longleftrightarrow> (\<forall>r. Dm (\<alpha> \<^bold>\<Rightarrow> \<o>) r
      \<longrightarrow> (vl (Ap r (Ee \<xi> A)) \<longrightarrow> vl (Ap r (Ee \<xi> B))))"
  proof -
    have inner: "vl (Ee (\<xi>(p\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> := r)) (?b\<^bold>\<langle>p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>\<^bold>\<rangle>))
        \<longleftrightarrow> (vl (Ap r (Ee \<xi> A)) \<longrightarrow> vl (Ap r (Ee \<xi> B)))"
      if r: "Dm (\<alpha> \<^bold>\<Rightarrow> \<o>) r" for r 
    proof -
      let ?\<xi> = "\<xi>(p\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> := r)"
      have ob: "?b\<^bold>\<langle>p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>\<^bold>\<rangle> = (p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> A) \<^bold>\<supset> (p\<^sup>f\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> B)"
        by (simp add: opn_lc[OF lcA] opn_lc[OF lcB])
      have cA: "Ee ?\<xi> A = Ee \<xi> A"
        using p ev_coin[OF wA asg_upd[OF xi r] xi]
        unfolding upd_def fvs_eq_fst_occ image_iff by force
      have cB: "Ee ?\<xi> B = Ee \<xi> B"
        using p ev_coin[OF wB asg_upd[OF xi r] xi]
        unfolding upd_def fvs_eq_fst_occ image_iff by force
      show ?thesis unfolding ob
        by (smt (verit, del_insts) asg_upd cA cB ev_app ev_var sat_ImpB that upd_same wA wB
            wff_App wff_AppE wff_App_FreFre wff_FreE xi)
    qed
    show ?thesis
      unfolding ev_beta[OF Leib_beq[OF wA wB] xi] sat_Forall[OF wI pf xi]
      using inner by blast
  qed
  show ?thesis 
  proof
    assume L: "vl (Ee \<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> B))"
    let ?r = "Ap (Ee \<xi> (Eq \<alpha>)) (Ee \<xi> A)"
    have rA: "vl (Ap ?r (Ee \<xi> A))"
      using vl_eq[OF xi ev_type[OF wA xi] ev_type[OF wA xi]] by simp
    have "vl (Ap ?r (Ee \<xi> B))"
      using unf L as_appTy[OF ev_type[OF wff_Eq xi] ev_type[OF wA xi]] rA by blast
    thus "Ee \<xi> A = Ee \<xi> B"
      using vl_eq[OF xi ev_type[OF wA xi] ev_type[OF wB xi]] by simp
  qed(simp add: unf)
qed

end

subsubsection \<open>The evaluation variant at a parameter\<close>

context bkk_model
begin

text \<open>Agreement under the variable shift: shifting all free variables and the
  assignment in step leaves denotations unchanged (property f resolves the
  abstraction case applicatively).\<close>

lemma Ee_vshift:
  assumes \<open>wff\<^bsub>\<tau>\<^esub>(A)\<close> \<open>asg \<xi>\<close> \<open>asg \<xi>'\<close> \<open>\<And>n \<tau>'. (n, \<tau>') \<in> occ A \<Longrightarrow> \<xi>' (Suc n) \<tau>' = \<xi> n \<tau>'\<close>
  shows \<open>Ee \<xi>' (vshift A) = Ee \<xi> A\<close>
using assms proof (induction A arbitrary: \<tau> \<xi> \<xi>' rule: size_induct)
  case (App s u)
  then obtain \<sigma> where ws: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>\<^esub>(s)" and wu: "wff\<^bsub>\<sigma>\<^esub>(u)"
      using App by auto
  have IHs: "Ee \<xi>' (vshift s) = Ee \<xi> s"
    using App wf by auto
  have IHu: "Ee \<xi>' (vshift u) = Ee \<xi> u"
    using App by auto
  have "Ee \<xi>' (vshift (s \<^bold>\<cdot> u)) = Ee \<xi>' (vshift s \<^bold>\<cdot> vshift u)"
    by (simp add: vshift_def)
  also have "\<dots> = Ap (Ee \<xi>' (vshift s)) (Ee \<xi>' (vshift u))"
    by (meson ev_app App.prems(3) wff_vshift ws wu) 
  also have "\<dots> = Ap (Ee \<xi> s) (Ee \<xi> u)" by (simp add: IHs IHu)
  also have "\<dots> = Ee \<xi> (s \<^bold>\<cdot> u)"
    by (simp add: ev_app[OF ws wu App.prems(2)])
  finally show ?case using App by simp
next
  case (Abs \<sigma> b)
  then obtain \<tau>' where t: "\<tau> = \<sigma> \<^bold>\<Rightarrow> \<tau>'" and wA: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>'\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
    by (metis wff_AbsE)
  have wS: "wff\<^bsub>\<sigma>\<^bold>\<Rightarrow>\<tau>'\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b))"
    using wff_vshift[OF wA] by (simp add: vshift_def)
  define y where "y = fresh (fvs b)"
  have y: "y \<notin> fvs b" unfolding y_def by (simp add: fresh_notin)
  have y': "Suc y \<notin> fvs (vshift b)"
    using y by (force simp: occ_vshift fvs_eq_fst_occ)
  {
    fix d
    assume d: "Dm \<sigma> d"
    have IH: "Ee (\<xi>'(Suc y\<^bsub>\<sigma>\<^esub> := d)) (vshift (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)) = Ee (\<xi>(y\<^bsub>\<sigma>\<^esub> := d)) (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    proof (rule Abs.IH)
      show "size (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>) \<le> size b" using Abs by simp
    next
      fix n \<tau>''
      assume o: "(n, \<tau>'') \<in> occ (b\<^bold>\<langle>y\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
      hence "(n, \<tau>'') \<in> occ b \<or> (n, \<tau>'') = (y, \<sigma>)"
          using occ_opn[of 0 "y\<^sup>f\<^bsub>\<sigma>\<^esub>" b] by auto
      thus "(\<xi>'(Suc y\<^bsub>\<sigma>\<^esub> := d)) (Suc n) \<tau>'' = (\<xi>(y\<^bsub>\<sigma>\<^esub> := d)) n \<tau>''"
        using Abs by (auto simp: upd_def)
    qed(auto intro: wff_Abs_open[OF wA y] asg_upd[OF Abs.prems(2) d] asg_upd[OF Abs.prems(3) d])
    hence "Ap (Ee \<xi>' (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b))) d = Ap (Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)) d"
      using ev_abs_app[OF wS Abs.prems(3) y', OF d] ev_abs_app[OF wA Abs.prems(2) y, OF d]
      by (simp add: vshift_opn)
  }
  hence "Ee \<xi>' (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (vshift b)) = Ee \<xi> (\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)"
      using prop_f ev_type[OF wS Abs.prems(3)] ev_type[OF wA
      Abs.prems(2)] unfolding functional_def by blast
  thus ?case using Abs by (simp add: vshift_def)
qed(auto simp: Ee_closed vshift_def ev_var)

text \<open>BKK's \<open>E'\<close> (the \<open>NK(\<Pi>I)\<close> case of Theorem 7.3): the parameter \<open>w\<close> is read as the
  freshly freed variable \<open>0\<close>, assigned \<open>a\<close>.\<close>

definition upshift :: "(nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> ty \<Rightarrow> 'u \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> 'u" where
  "upshift \<xi> \<sigma> a = (\<lambda>n \<tau>. case n of 0 \<Rightarrow> (if \<tau> = \<sigma> then a else \<xi> 0 \<tau>) | Suc m \<Rightarrow> \<xi> m \<tau>)"
definition Evar :: "'p \<Rightarrow> ty \<Rightarrow> 'u \<Rightarrow> (nat \<Rightarrow> ty \<Rightarrow> 'u) \<Rightarrow> 'p tm \<Rightarrow> 'u" where
  "Evar w \<sigma> a \<xi> A = Ee (upshift \<xi> \<sigma> a) (pvar w \<sigma> 0 (vshift A))"
lemma asg_upshift: "asg \<xi> \<Longrightarrow> Dm \<sigma> a \<Longrightarrow> asg (upshift \<xi> \<sigma> a)"
  by (auto simp: asg_def upshift_def split: nat.splits)
lemma Evar_par: "asg \<xi> \<Longrightarrow> Dm \<sigma> a \<Longrightarrow> Evar w \<sigma> a \<xi> (w\<^sup>p\<^bsub>\<sigma>\<^esub>) = a"
  by (smt (verit, del_insts) Evar_def asg_upshift bkk_model.upshift_def
      bkk_model_axioms ev_var msub.simps(3) old.nat.simps(4) pvar.simps(3) vshift_def)
lemma Evar_agree: "wff\<^bsub>\<tau>\<^esub>(A) \<Longrightarrow> asg \<xi> \<Longrightarrow> Dm \<sigma> a \<Longrightarrow> w \<notin> pars A \<Longrightarrow> Evar w \<sigma> a \<xi> A = Ee \<xi> A" 
  using Evar_def asg_upshift bkk_model.Ee_vshift bkk_model_axioms
        pars_vshift upshift_def by fastforce
lemma Evar_bkk: assumes a: "Dm \<sigma> a" shows "bkk_model Dm Ap (Evar w \<sigma> a) vl"
proof (unfold_locales, goal_cases)
  case 1 thus ?case
    by (simp add: Evar_def asg_upshift assms ev_type wff_pvar wff_vshift)
next
  case 2 thus ?case
    by (metis Evar_agree assms emptyE ev_var tm.simps(230) wff_Fre)
next
  case 3 thus ?case
    by (simp add: Evar_def vshift_def)
       (metis asg_upshift assms ev_app vshift_def wff_pvar wff_vshift)
next
  case (4 \<tau> A \<xi> \<xi>')
  have ag: "upshift \<xi> \<sigma> a n \<tau>' = upshift \<xi>' \<sigma> a n \<tau>'"
    if o: "(n, \<tau>') \<in> occ (pvar w \<sigma> 0 (vshift A))" for n \<tau>'
  proof -
    from o have "(n, \<tau>') \<in> occ (vshift A) \<union> {(0, \<sigma>)}"
        using occ_pvar[of w \<sigma> 0 "vshift A"] by blast
    then consider (sh) m where "n = Suc m" "(m, \<tau>') \<in> occ A" |
        (zero) "n = 0" "\<tau>' = \<sigma>" by (auto simp: occ_vshift)
    thus ?thesis using "4"(4) upshift_def by fastforce
  qed
  show ?case unfolding Evar_def 
    by (rule ev_coin[OF wff_pvar[OF wff_vshift[OF 4(1)]]
        asg_upshift[OF 4(2) a] asg_upshift[OF 4(3) a] ag])
next
  case 5 thus ?case
    by (metis (full_types) Evar_def asg_upshift assms beq_pvar beq_vshift ev_beta)
qed(auto simp: Evar_def asg_upshift assms vl_eq vl_pi vl_dis vl_neg vl_iota
               vshift_def prop_b prop_f)

end

subsubsection \<open>Soundness\<close>

text \<open>BKK Theorem 7.3, for the class \<open>\<M>\<^bsub>\<beta>fb\<^esub>\<close> (with primitive equality and description):
  each case mirrors BKK's proof text.\<close>

theorem soundness_bkk:
  assumes "\<Phi> \<turnstile> C" "bkk_model Dm Ap Ee vl" "app_struct.asg Dm \<xi>"
          "\<forall>A \<in> \<Phi>. wff\<^bsub>\<o>\<^esub>(A)" "\<forall>A \<in> \<Phi>. vl (Ee \<xi> A)"
    shows "vl (Ee \<xi> C)"
using assms proof (induction arbitrary: Dm Ap Ee vl \<xi> rule: bprov.induct)
  case Hyp thus ?case by blast
next
  case Beta thus ?case
    by (metis bkk_model_def sigma_eval.ev_beta sigma_model.axioms(1))
next 
  case NegI thus ?case
    by (metis UnE bkk_model_def sigma_model.sat_Neg sigma_model.vl_TF singleton_iff)
next
  case NegE thus ?case
    using bkk_model.axioms(1) bprov_wff sigma_model.sat_Neg by fastforce
next
  case DisIL thus ?case
    by (metis Hyp bprov_wff bkk_model.axioms(1) sigma_model.sat_Dis)
next
  case DisIR thus ?case
    by (metis bprov_wff sigma_model.sat_Dis bkk_model.axioms(1))
next
  case DisE thus ?case
    by (metis UnE bkk_model.axioms(1) sigma_model.sat_Dis singleton_iff)
next
  case (PiI \<Phi> G w \<alpha>)
  interpret M: bkk_model Dm Ap Ee vl by (rule PiI.prems(1))
  have wGw: "wff\<^bsub>\<o>\<^esub>(G \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>))"
    using bprov_wff[OF PiI.hyps(1)] PiI.prems(3) by blast
  have "vl (Ap (Ee \<xi> G) a)" if a: "Dm \<alpha> a" for a 
  proof -
    let ?E = "M.Evar w \<alpha> a"
    interpret V: bkk_model Dm Ap ?E vl by (rule M.Evar_bkk[OF a])
    have sat: "\<forall>A \<in> \<Phi>. vl (?E \<xi> A)" using PiI.prems(3,4) PiI.hyps(4)
        by (auto simp: M.Evar_agree[OF _ PiI.prems(2) a])
    have "vl (?E \<xi> (G \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>)))" by (rule PiI.IH[OF M.Evar_bkk[OF a]
        PiI.prems(2) PiI.prems(3) sat])
    moreover have "?E \<xi> (G \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>)) = Ap (Ee \<xi> G) a"
        by (simp add: V.ev_app[OF PiI.hyps(2) wff_Par PiI.prems(2)]
          M.Evar_agree[OF PiI.hyps(2) PiI.prems(2) a PiI.hyps(3)]
              M.Evar_par[OF PiI.prems(2) a])
    ultimately show ?thesis by simp
  qed
  thus ?case by (simp add: M.sat_Pi[OF PiI.hyps(2) PiI.prems(2)])
next
  case (PiE \<Phi> \<alpha> G A)
  interpret M: bkk_model Dm Ap Ee vl by (rule PiE.prems(1))
  have wPiG: "wff\<^bsub>\<o>\<^esub>(Pi \<alpha> \<^bold>\<cdot> G)" using bprov_wff[OF PiE.hyps(1)]
      PiE.prems(3) by blast
  have wG: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(G)" using wPiG by (auto dest: wff_unique)
  have "vl (Ap (Ee \<xi> G) (Ee \<xi> A))" using PiE.IH[OF PiE.prems]
      M.sat_Pi[OF wG PiE.prems(2)]
      M.ev_type[OF PiE.hyps(2) PiE.prems(2)] by simp
  thus ?case by (simp add: M.ev_app[OF wG PiE.hyps(2) PiE.prems(2)])
next
  case Contr thus ?case
    using bkk_model.axioms(1) sigma_model.sat_Neg sigma_model.vl_TF by fastforce
next
  case (FuncE \<Phi> \<alpha> G \<beta> H)
  interpret M: bkk_model Dm Ap Ee vl by (rule FuncE.prems(1))
  have lcG: "lc G" and lcH: "lc H" using FuncE.hyps(2,3)
    by (auto intro: wff_lc)
  define y where "y = fresh (fvs G \<union> fvs H)"
  have y: "y \<notin> fvs G" "y \<notin> fvs H" unfolding y_def
    using fresh_notin[of "fvs G \<union> fvs H"] by auto
  let ?b = "G \<^bold>\<cdot> Bnd 0 \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> H \<^bold>\<cdot> Bnd 0"
  have wI: "wff\<^bsub>\<alpha>\<^bold>\<Rightarrow>\<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> ?b)"
    by (auto intro!: wff_AbsI wff_App[OF FuncE.hyps(2) wff_Fre] wff_App[OF FuncE.hyps(3) wff_Fre]
             simp: opn_lc[OF lcG] opn_lc[OF lcH])
  have yb: "y \<notin> fvs ?b" using y by (auto simp: Leib_def Forall_def ImpB_def)
  have pointwise: "Ap (Ee \<xi> G) d = Ap (Ee \<xi> H) d" if d: "Dm \<alpha> d" for d
  proof -
    let ?\<xi> = "\<xi>(y\<^bsub>\<alpha>\<^esub> := d)"
    have "vl (Ee \<xi> (\<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> ?b))" using FuncE.IH[OF FuncE.prems] .
    hence "vl (Ee ?\<xi> (?b\<^bold>\<langle>y\<^sup>f\<^bsub>\<alpha>\<^esub>\<^bold>\<rangle>))"
      using FuncE.prems(2) M.sat_Forall that wI yb by blast
    hence "vl (Ee ?\<xi> (G \<^bold>\<cdot> (y\<^sup>f\<^bsub>\<alpha>\<^esub>) \<^bold>\<doteq>\<^bsub>\<beta>\<^esub> H \<^bold>\<cdot> (y\<^sup>f\<^bsub>\<alpha>\<^esub>)))"
        by (simp add: opn_lc[OF lcG] opn_lc[OF lcH])
    hence "Ee ?\<xi> (G \<^bold>\<cdot> (y\<^sup>f\<^bsub>\<alpha>\<^esub>)) = Ee ?\<xi> (H \<^bold>\<cdot> (y\<^sup>f\<^bsub>\<alpha>\<^esub>))"
      by (meson FuncE.hyps(2,3) FuncE.prems(2) M.sat_Leib M.sigma_model_axioms app_struct.asg_upd
                sigma_eval_def sigma_model_def that wff_App wff_Fre)
    moreover have "Ee ?\<xi> G = Ee \<xi> G"
      by (metis (mono_tags, lifting) FuncE.hyps(2) FuncE.prems(2) M.asg_upd M.ev_coin fst_conv
                fvs_eq_fst_occ image_eqI that upd_def y(1))
    moreover have "Ee ?\<xi> H = Ee \<xi> H"
      by (metis (mono_tags, lifting) FuncE.hyps(3) FuncE.prems(2) M.asg_upd M.ev_coin fst_conv
                fvs_eq_fst_occ image_eqI that upd_def y(2))
    ultimately show ?thesis
      by (metis FuncE.hyps(2,3) FuncE.prems(2) M.asg_upd M.ev_app M.ev_var that upd_same wff_Fre)
  qed
  have "Ee \<xi> G = Ee \<xi> H"
    using FuncE.hyps(2,3) FuncE.prems(2) M.ev_type M.functional_def M.prop_f pointwise by blast
  thus ?case by (simp add: M.sat_Leib[OF FuncE.hyps(2,3) FuncE.prems(2)])
next
  case (BoolE \<Phi> A B)
  interpret M: bkk_model Dm Ap Ee vl by (rule BoolE.prems(1))
  have "vl (Ee \<xi> A) \<longleftrightarrow> vl (Ee \<xi> B)"
    using BoolE by fast
  hence "Ee \<xi> A = Ee \<xi> B"
    by (simp add: BoolE.hyps(3,4) BoolE.prems(2) M.ev_type M.prop_b)
  thus ?case
    by (simp add: M.sat_Leib[OF BoolE.hyps(3,4) BoolE.prems(2)])
next case (Desc \<alpha> A \<Phi>)
  interpret M: bkk_model Dm Ap Ee vl by (rule Desc.prems(1))
  define y where "y = fresh (fvs A)"
  have y: "y \<notin> fvs A" unfolding y_def by (simp add: fresh_notin)
  let ?f = "Ee \<xi> (Leib \<alpha> \<^bold>\<cdot> A)"
  have sing: "vl (Ap ?f b) \<longleftrightarrow> b = Ee \<xi> A" if b: "Dm \<alpha> b" for b 
  proof -
    let ?\<xi> = "\<xi>(y\<^bsub>\<alpha>\<^esub> := b)"
    have c: "Ee ?\<xi> (Leib \<alpha> \<^bold>\<cdot> A) = ?f"
      using y
      by (safe intro!: M.ev_coin[OF wff_App[OF wff_Leib Desc.hyps]
                                    M.asg_upd[OF Desc.prems(2) b] Desc.prems(2)])
         (auto simp add: Forall_def ImpB_def Leib_def upd_def fvs_eq_fst_occ image_iff)
    have cA: "Ee ?\<xi> A = Ee \<xi> A"
      by (metis (mono_tags, lifting) Desc.hyps Desc.prems(2) M.asg_upd M.ev_coin fst_conv
                fvs_eq_fst_occ image_eqI that upd_def y)
    have "Ap ?f b = Ee ?\<xi> (A \<^bold>\<doteq>\<^bsub>\<alpha>\<^esub> (y\<^sup>f\<^bsub>\<alpha>\<^esub>))"
      by (simp add: M.ev_app[OF wff_App[OF wff_Leib Desc.hyps]
            wff_Fre M.asg_upd[OF Desc.prems(2) b]]
            M.ev_var[OF M.asg_upd[OF Desc.prems(2) b]] c)
    thus ?thesis
      by (metis Desc.hyps that cA Desc.prems(2) wff_Fre M.sat_Leib M.ev_var app_struct.asg_upd
                upd_same M.app_struct_axioms)
  qed
  have "Ee \<xi> (Iota \<alpha> \<^bold>\<cdot> (Leib \<alpha> \<^bold>\<cdot> A)) = Ee \<xi> A"
    using M.vl_iota[OF Desc.prems(2) M.ev_type[OF wff_App[OF wff_Leib Desc.hyps] Desc.prems(2)]
                    M.ev_type[OF Desc.hyps Desc.prems(2)]] sing 
    by (simp add: M.ev_app[OF wff_Iota wff_App[OF wff_Leib Desc.hyps]
        Desc.prems(2)])
  thus ?case 
    by (simp add: M.sat_Leib[OF wff_App[OF wff_Iota wff_App[OF wff_Leib Desc.hyps]]
                  Desc.hyps Desc.prems(2)])
next
  case (EqR \<alpha> A \<Phi>)
  interpret M: bkk_model Dm Ap Ee vl by (rule EqR.prems(1))
  show ?case
    by (simp add: M.ev_app[OF wff_App[OF wff_Eq EqR.hyps] EqR.hyps EqR.prems(2)]
        M.ev_app[OF wff_Eq EqR.hyps EqR.prems(2)]
        M.vl_eq[OF EqR.prems(2) M.ev_type[OF EqR.hyps EqR.prems(2)]
                    M.ev_type[OF EqR.hyps EqR.prems(2)]])
next case (EqL \<Phi> C \<alpha> D)
  interpret M: bkk_model Dm Ap Ee vl by (rule EqL.prems(1))
  have wCD: "wff\<^bsub>\<o>\<^esub>(C \<^bold>=\<^bsub>\<alpha>\<^esub> D)" using bprov_wff[OF EqL.hyps(1)] EqL.prems(3)
    by blast
  have wC: "wff\<^bsub>\<alpha>\<^esub>(C)" and wD: "wff\<^bsub>\<alpha>\<^esub>(D)" using wCD
    by (auto dest: wff_unique)
  have "vl (Ee \<xi> (C \<^bold>=\<^bsub>\<alpha>\<^esub> D))" using EqL.IH[OF EqL.prems] .
  hence "Ee \<xi> C = Ee \<xi> D"
    by (simp add: M.ev_app[OF wff_App[OF wff_Eq wC] wD EqL.prems(2)]
        M.ev_app[OF wff_Eq wC EqL.prems(2)]
        M.vl_eq[OF EqL.prems(2) M.ev_type[OF wC EqL.prems(2)] M.ev_type[OF wD EqL.prems(2)]])
  thus ?case by (simp add: M.sat_Leib[OF wC wD EqL.prems(2)])
qed


subsubsection \<open>The canonical construction is a BKK model\<close>

text \<open>Every \<open>\<Sigma>\<close>-Henkin general model in the sense of Section 2 --- the
  frame-based canonical construction --- is a BKK model: take \<open>E := den\<close> and
  \<open>\<upsilon> := (\<lambda>a. a = Tv)\<close>.  The four evaluation conditions are the denotation lemmas,
  and the \<open>L\<close>-properties are the \<open>gm\<close>-conditions.\<close>

sublocale general_model \<subseteq> bkkA: app_struct Dm Ap
  by unfold_locales (use gm_nonempty gm_appTy in blast)+

sublocale general_model \<subseteq> bkk: bkk_model Dm Ap "\<lambda>\<xi> A. \<lparr>A\<rparr>\<^bsub>\<xi>\<^esub>" "\<lambda>a. a = Tv"
  by (unfold_locales;
      auto simp: bkkA.functional_def general_model_axioms[unfolded general_model_def]
                 bkkA.asg_def frame_sig.den.simps(8) resp_def
         intro: beq_den den_coincidence den_dom)


subsubsection \<open>Derived rules for the defined quantifiers\<close>

text \<open>\<open>NK(\<Pi>E)\<close> and \<open>NK(\<Pi>I)\<close> for the folded quantifier \<open>\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub>\<close>.\<close>

lemma PiE_Forall: "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<^bold>\<cdot> A"
  unfolding Forall_def by (rule bprov.PiE)
lemma PiI_Forall: "\<Phi> \<turnstile> (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<alpha>\<^esub>) \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<Longrightarrow> w \<notin> pars (\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b)
                   \<Longrightarrow> (\<forall>D \<in> \<Phi>. w \<notin> pars D)  \<Longrightarrow> \<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b"
  unfolding Forall_def by (rule bprov.PiI)

text \<open>Existential elimination at a fresh eigen-parameter, for the defined quantifier
  \<open>\<^bold>\<exists> = \<^bold>\<not>\<^bold>\<Pi>\<^bold>\<not>\<close>: the derived counterpart of the paper-style step ``obtain a witness''.\<close>

lemma ExE: assumes ex: "\<Phi> \<turnstile> \<^bold>\<exists>\<^bsub>\<sigma>\<^esub> b" and step: "\<Phi> \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> C"
    and wb: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> b)" 
  and wC: "wff\<^bsub>\<o>\<^esub>(C)" and wpb: "w \<notin> pars b" and wpC: "w \<notin> pars C"
      and wp\<Phi>: "\<forall>D \<in> \<Phi>. w \<notin> pars D" and fp: "freep \<Phi>" 
  shows "\<Phi> \<turnstile> C"
proof -
  have wNb: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))"
    by (auto intro!: wff_opn[OF wb] wff_Fre wff_AbsI)
  have fp1: "freep (\<Phi> \<union> {\<^bold>\<not> C})" using freep_add[OF fp] by simp
  have fp2: "freep (\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>})"
      using freep_add[OF freep_add[OF fp]] by simp
  have s1: "\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> C"
    by (rule bprov_weaken[OF step _ fp2]) auto
  have s2: "\<Phi> \<union> {\<^bold>\<not> C} \<union> {b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>} \<turnstile> \<^bold>\<not> C" by (auto intro: bprov.Hyp)
  have bq: "(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b)) \<^bold>\<cdot> (w\<^sup>p\<^bsub>\<sigma>\<^esub>) \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<not> (b\<^bold>\<langle>w\<^sup>p\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
      using beq.beta[OF wNb wff_Par] by simp
    have s5: "\<Phi> \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b)"
      using wpb wpC wp\<Phi>
      by (safe intro!:
          PiI_Forall[OF bprov.Beta[OF beq.sym[OF bq] bprov.NegI[OF
                bprov.NegE[OF s2 s1 wff_FalseB] wff_opn[OF wb wff_Par]]] wNb]) auto
  have s6: "\<Phi> \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<not> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> b))" by (rule bprov_weaken[OF ex _ fp1]) auto
  show ?thesis by (rule bprov.Contr[OF bprov.NegE[OF s6 s5 wff_FalseB] wC])
qed

text \<open>Universal instantiation directly at the \<open>\<beta>\<close>-reduced instance.\<close>

lemma PiE_open: "\<Phi> \<turnstile> \<^bold>\<Pi>\<^bsub>\<alpha>\<^esub> b \<Longrightarrow> wff\<^bsub>\<alpha> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<alpha>\<^esub> b) \<Longrightarrow> wff\<^bsub>\<alpha>\<^esub>(A) \<Longrightarrow> \<Phi> \<turnstile> b\<^bold>\<langle>A\<^bold>\<rangle>" 
  by (metis PiE_Forall beq.beta bprov.Beta)

text \<open>Soundness, repackaged in the validity and satisfaction notation: the two
  forms used by the closing summary.\<close>

theorem soundness_sat:
  "\<Phi> \<turnstile> C \<Longrightarrow> \<Phi> \<Turnstile>('u) C"
  by (simp add: bkk_consequence_def rel_truth_def soundness_bkk)

theorem soundness_valid: "\<turnstile> A \<Longrightarrow> \<Turnstile>('u) A"
  unfolding bkk_valid_def rel_truth_def
  by (auto intro: soundness_bkk[of "{}" A])

end
