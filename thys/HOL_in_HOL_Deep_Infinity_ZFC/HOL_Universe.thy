theory HOL_Universe
  imports "HOL_in_HOL_Deep.Completeness" "HOL_in_HOL_Deep.NK_Infinity"
begin

section \<open>Full classical HOL, abstractly: the choice scheme, the axioms' satisfaction, and \<open>hol_universe\<close>\<close>

text \<open>This theory is the @{emph \<open>set-theory-free\<close>} half of the companion development: it
  imports only the main entry @{session HOL_in_HOL_Deep} and never mentions a set-theoretic
  universe.  The Dedekind axiom of infinity \<open>DInf\<close>, its satisfaction conditions and its
  separation from the infinity scheme are inherited from the main entry (theory
  \<open>NK_Infinity\<close>); here the relational choice scheme
  \<open>ACrel\<close> is added as an object formula with its satisfaction condition in an
  @{emph \<open>arbitrary\<close>}
  \<open>\<Sigma>\<close>-standard model, the abstract relative-consistency theorem is derived --- full
  classical
  \<open>HOL\<close> is consistent as soon as @{emph \<open>some\<close>} standard model has Dedekind-infinite
  individuals --- and the universe interfaces are isolated from which the required standard
  model is @{emph \<open>constructed\<close>}: the locale \<open>hol_universe\<close>, and beneath it an at most as
  strong Harrison-style locale \<open>harrison_universe\<close>.
  Completeness for the extension by \<open>DInf\<close> is likewise established here, in plain HOL.
  That the assumptions of these locales are satisfiable is a separate question --- no
  @{emph \<open>plain-HOL\<close>} type answers it: Cantor's tower outgrows every type plain HOL can
  construct, and G\"odel's second theorem bars every other plain-HOL route (see the document
  introduction) --- and is deferred to this entry's final theory, \<open>HOL_in_HOL_Deep_Infinity_ZFC\<close>,
  which instantiates both locales with Paulson's axiomatic set-theoretic universe \<^emph>\<open>V\<close>.  The split makes the
  dependency structure machine-visible: nothing in this theory rests on \<open>ZFC_in_HOL\<close>.\<close>

section \<open>Consistency of full classical HOL: infinity and choice\<close>

text \<open>\<open>NK\<close> already carries extensionality (property f) and typed description.  Adding the
  Dedekind axiom of infinity \<open>DInf\<close> and the axiom of \<^emph>\<open>choice\<close> makes the object logic full
  classical higher-order logic in the sense of Church.  The consistency of the whole package
  is reduced, in one carrier-generic argument, to the existence of a standard frame with
  Dedekind-infinite individuals.\<close>

subsection \<open>The axiom of choice as a relational scheme\<close>

text \<open>Choice is stated, without any new primitive, as the relational scheme
  \<open>AC\<^bsub>\<sigma>,\<tau>\<^esub> = \<^bold>\<Pi>R. (\<^bold>\<Pi>X. \<^bold>\<exists>Y. R\<cdot>X\<cdot>Y) \<^bold>\<supset> (\<^bold>\<exists>F. \<^bold>\<Pi>X. R\<cdot>X\<cdot>(F\<cdot>X))\<close> at every pair of types.\<close>

definition rR where "rR = (5::nat)"
definition rX where "rX = (6::nat)"
definition rY where "rY = (7::nat)"
definition rF where "rF = (8::nat)"

definition ACatom1 :: "ty \<Rightarrow> ty \<Rightarrow> 'p tm" where
  "ACatom1 \<sigma> \<tau> = (((rR\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>)) \<^bold>\<cdot> (rY\<^sup>f\<^bsub>\<tau>\<^esub>))"
definition ACatom2 :: "ty \<Rightarrow> ty \<Rightarrow> 'p tm" where
  "ACatom2 \<sigma> \<tau> = (((rR\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>)) \<^bold>\<cdot> ((rF\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>)))"
definition ACprem :: "ty \<Rightarrow> ty \<Rightarrow> 'p tm" where
  "ACprem \<sigma> \<tau> = \<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. \<^bold>\<exists>rY\<^bsub>\<tau>\<^esub>. ACatom1 \<sigma> \<tau>"
definition ACconcl :: "ty \<Rightarrow> ty \<Rightarrow> 'p tm" where
  "ACconcl \<sigma> \<tau> = \<^bold>\<exists>rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub>. \<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. ACatom2 \<sigma> \<tau>"
definition ACrel :: "ty \<Rightarrow> ty \<Rightarrow> 'p tm" where
  "ACrel \<sigma> \<tau> = \<^bold>\<Pi>rR\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>. (ACprem \<sigma> \<tau> \<^bold>\<supset> ACconcl \<sigma> \<tau>)"

(*<*)
lemma wff_ACatom1 [intro]: "wff\<^bsub>\<o>\<^esub>(ACatom1 \<sigma> \<tau> :: 'p tm)"
  unfolding ACatom1_def by (rule wff_App[OF wff_App[OF wff_Fre wff_Fre] wff_Fre])
lemma wff_ACatom2 [intro]: "wff\<^bsub>\<o>\<^esub>(ACatom2 \<sigma> \<tau> :: 'p tm)"
  unfolding ACatom2_def
  by (rule wff_App[OF wff_App[OF wff_Fre wff_Fre] wff_App[OF wff_Fre wff_Fre]])
lemma wff_ACprem: "wff\<^bsub>\<o>\<^esub>(ACprem \<sigma> \<tau> :: 'p tm)"
  unfolding ACprem_def by (rule wff_AllN[OF wff_ExN[OF wff_ACatom1]])
lemma wff_ACconcl: "wff\<^bsub>\<o>\<^esub>(ACconcl \<sigma> \<tau> :: 'p tm)"
  unfolding ACconcl_def by (rule wff_ExN[OF wff_AllN[OF wff_ACatom2]])
lemma wff_ACrel: "wff\<^bsub>\<o>\<^esub>(ACrel \<sigma> \<tau> :: 'p tm)"
  unfolding ACrel_def by (rule wff_AllN[OF wff_ImpB[OF wff_ACprem wff_ACconcl]])

lemmas rdefs = rR_def rX_def rY_def rF_def

lemma fvs_ACrel: "fvs (ACrel \<sigma> \<tau> :: 'p tm) = {}"
  by (simp add: ACrel_def ACprem_def ACconcl_def ACatom1_def ACatom2_def
      ExN_def AllN_def Forall_def ImpB_def rdefs)

lemma cwff_ACrel: "cwff \<o> (ACrel \<sigma> \<tau> :: 'p tm)"
  by (rule cwffI[OF wff_ACrel fvs_ACrel])
(*>*)

text \<open>The scheme in full, as for \<open>DInf\<close>: assembled by definitional unfolding, and in its
  locally-nameless normal form:\<close>

lemma ACrel_unfolded:
  "(ACrel \<sigma> \<tau> :: 'p tm)
   = (\<^bold>\<Pi>rR\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>.
       ((\<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. \<^bold>\<exists>rY\<^bsub>\<tau>\<^esub>. (((rR\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>)) \<^bold>\<cdot> (rY\<^sup>f\<^bsub>\<tau>\<^esub>)))
        \<^bold>\<supset> (\<^bold>\<exists>rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub>. \<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>.
             (((rR\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>)) \<^bold>\<cdot> ((rF\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub>) \<^bold>\<cdot> (rX\<^sup>f\<^bsub>\<sigma>\<^esub>))))))"
  by (simp only: ACrel_def ACprem_def ACconcl_def ACatom1_def ACatom2_def)

lemma ACrel_norm:
  "(ACrel \<sigma> \<tau> :: 'p tm)
   = \<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub>
       ((\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> (\<^bold>\<exists>\<^bsub>\<tau>\<^esub> ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>\<cdot> Bnd 0)))
        \<^bold>\<supset> (\<^bold>\<exists>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma>\<^esub> ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0) \<^bold>\<cdot> (Bnd (Suc 0) \<^bold>\<cdot> Bnd 0)))))"
  by (simp add: ACrel_def ACprem_def ACconcl_def ACatom1_def ACatom2_def
      ExN_def AllN_def Forall_def ImpB_def rdefs)

subsection \<open>Satisfaction of the choice scheme in an arbitrary standard model\<close>

text \<open>Every instance of the scheme holds in \<^emph>\<open>any\<close> \<open>\<Sigma>\<close>-standard model: the full function
  space supplies the choice function as the \<open>\<lambda>\<close>-abstraction of a meta-level Hilbert
  choice.  (The corresponding satisfaction analysis for \<open>DInf\<close> --- \<open>DInf_sat\<close> and its
  relatives --- lives in the main entry's \<open>NK_Infinity\<close> and is used below unchanged.)\<close>

context standard_model
begin

lemma ACrel_sat:
  assumes xi: "bkkA.asg \<xi>"
  shows "den (ACrel \<sigma> \<tau>) \<xi> = Tv"
proof -
  have body: "den (ACprem \<sigma> \<tau> \<^bold>\<supset> ACconcl \<sigma> \<tau>) (\<xi>(rR\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub> := d)) = Tv"
    if d: "Dm (\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>) d" for d
  proof -
    define \<eta> where "\<eta> = \<xi>(rR\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub> := d)"
    have ea: "bkkA.asg \<eta>" unfolding \<eta>_def using xi d by (rule bkkA.asg_upd)
    \<comment> \<open>meaning of the premise\<close>
    have prem: "(den (ACprem \<sigma> \<tau>) \<eta> = Tv)
        = (\<forall>a. Dm \<sigma> a \<longrightarrow> (\<exists>b. Dm \<tau> b \<and> (d \<^bold>@ a) \<^bold>@ b = Tv))"
    proof -
      have inner: "(den (ACatom1 \<sigma> \<tau>) ((\<eta>(rX\<^bsub>\<sigma>\<^esub> := a))(rY\<^bsub>\<tau>\<^esub> := b)) = Tv) = ((d \<^bold>@ a) \<^bold>@ b = Tv)"
        if a: "Dm \<sigma> a" and b: "Dm \<tau> b" for a b
      proof -
        define \<rho> where "\<rho> = (\<eta>(rX\<^bsub>\<sigma>\<^esub> := a))(rY\<^bsub>\<tau>\<^esub> := b)"
        have "den (ACatom1 \<sigma> \<tau>) \<rho> = (d \<^bold>@ a) \<^bold>@ b"
          unfolding ACatom1_def by (simp add: den.simps(8) \<rho>_def \<eta>_def upd_def rdefs)
        thus ?thesis by (simp add: \<rho>_def)
      qed
      have step: "(den (\<^bold>\<exists>rY\<^bsub>\<tau>\<^esub>. ACatom1 \<sigma> \<tau>) (\<eta>(rX\<^bsub>\<sigma>\<^esub> := a)) = Tv)
          = (\<exists>b. Dm \<tau> b \<and> (d \<^bold>@ a) \<^bold>@ b = Tv)" if a: "Dm \<sigma> a" for a
      proof -
        have "(den (\<^bold>\<exists>rY\<^bsub>\<tau>\<^esub>. ACatom1 \<sigma> \<tau>) (\<eta>(rX\<^bsub>\<sigma>\<^esub> := a)) = Tv)
            = (\<exists>b. Dm \<tau> b \<and> den (ACatom1 \<sigma> \<tau>) ((\<eta>(rX\<^bsub>\<sigma>\<^esub> := a))(rY\<^bsub>\<tau>\<^esub> := b)) = Tv)"
          by (rule sat_ExN[OF wff_ACatom1 bkkA.asg_upd[OF ea a]])
        thus ?thesis using inner[OF a] by (simp cong: conj_cong)
      qed
      have "(den (ACprem \<sigma> \<tau>) \<eta> = Tv)
          = (\<forall>a. Dm \<sigma> a \<longrightarrow> den (\<^bold>\<exists>rY\<^bsub>\<tau>\<^esub>. ACatom1 \<sigma> \<tau>) (\<eta>(rX\<^bsub>\<sigma>\<^esub> := a)) = Tv)"
        unfolding ACprem_def by (rule sat_AllN[OF wff_ExN[OF wff_ACatom1] ea])
      thus ?thesis using step by simp
    qed
    \<comment> \<open>the conclusion, with the choice function \<open>Lm \<sigma> (\<lambda>x. SOME y. \<dots>)\<close> as witness; it lands
       in the full function space by @{thm Lm_dom}\<close>
    have concl: "den (ACconcl \<sigma> \<tau>) \<eta> = Tv"
      if P: "\<forall>a. Dm \<sigma> a \<longrightarrow> (\<exists>b. Dm \<tau> b \<and> (d \<^bold>@ a) \<^bold>@ b = Tv)"
    proof -
      define g where "g = Lm \<sigma> (\<lambda>x. SOME y. Dm \<tau> y \<and> (d \<^bold>@ x) \<^bold>@ y = Tv)"
      have resp: "Dm \<tau> (SOME y. Dm \<tau> y \<and> (d \<^bold>@ x) \<^bold>@ y = Tv)" if x: "Dm \<sigma> x" for x
      proof -
        from P x have "\<exists>y. Dm \<tau> y \<and> (d \<^bold>@ x) \<^bold>@ y = Tv" by blast
        from someI_ex[OF this] show ?thesis by simp
      qed
      have gdom: "Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) g"
        unfolding g_def by (rule Lm_dom) (rule resp)
      have gapp: "(d \<^bold>@ a) \<^bold>@ (g \<^bold>@ a) = Tv" if a: "Dm \<sigma> a" for a
      proof -
        have e: "g \<^bold>@ a = (SOME y. Dm \<tau> y \<and> (d \<^bold>@ a) \<^bold>@ y = Tv)"
          unfolding g_def by (rule beta_Lm[OF resp a])
        from P a have ex: "\<exists>y. Dm \<tau> y \<and> (d \<^bold>@ a) \<^bold>@ y = Tv" by blast
        from someI_ex[OF ex] show ?thesis by (simp add: e)
      qed
      have inner2: "(den (ACatom2 \<sigma> \<tau>) ((\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := g))(rX\<^bsub>\<sigma>\<^esub> := a)) = Tv)
          = ((d \<^bold>@ a) \<^bold>@ (g \<^bold>@ a) = Tv)" if a: "Dm \<sigma> a" for a
      proof -
        define \<rho> where "\<rho> = (\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := g))(rX\<^bsub>\<sigma>\<^esub> := a)"
        have "den (ACatom2 \<sigma> \<tau>) \<rho> = (d \<^bold>@ a) \<^bold>@ (g \<^bold>@ a)"
          unfolding ACatom2_def by (simp add: den.simps(8) \<rho>_def \<eta>_def upd_def rdefs)
        thus ?thesis by (simp add: \<rho>_def)
      qed
      have step2: "(den (\<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. ACatom2 \<sigma> \<tau>) (\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := g)) = Tv)
          = (\<forall>a. Dm \<sigma> a \<longrightarrow> (d \<^bold>@ a) \<^bold>@ (g \<^bold>@ a) = Tv)"
      proof -
        have "(den (\<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. ACatom2 \<sigma> \<tau>) (\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := g)) = Tv)
            = (\<forall>a. Dm \<sigma> a \<longrightarrow> den (ACatom2 \<sigma> \<tau>) ((\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := g))(rX\<^bsub>\<sigma>\<^esub> := a)) = Tv)"
          by (rule sat_AllN[OF wff_ACatom2 bkkA.asg_upd[OF ea gdom]])
        thus ?thesis using inner2 by simp
      qed
      have "(den (ACconcl \<sigma> \<tau>) \<eta> = Tv)
          = (\<exists>k. Dm (\<sigma> \<^bold>\<Rightarrow> \<tau>) k \<and> den (\<^bold>\<Pi>rX\<^bsub>\<sigma>\<^esub>. ACatom2 \<sigma> \<tau>) (\<eta>(rF\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau>\<^esub> := k)) = Tv)"
        unfolding ACconcl_def by (rule sat_ExN[OF wff_AllN[OF wff_ACatom2] ea])
      thus ?thesis using gdom step2 gapp by auto
    qed
    have imp: "(den (ACprem \<sigma> \<tau> \<^bold>\<supset> ACconcl \<sigma> \<tau>) \<eta> = Tv)
        = ((den (ACprem \<sigma> \<tau>) \<eta> = Tv) \<longrightarrow> (den (ACconcl \<sigma> \<tau>) \<eta> = Tv))"
      by (rule sat_ImpBB[OF wff_ACprem wff_ACconcl ea])
    have "den (ACprem \<sigma> \<tau> \<^bold>\<supset> ACconcl \<sigma> \<tau>) \<eta> = Tv"
      unfolding imp using prem concl by blast
    thus ?thesis by (simp add: \<eta>_def)
  qed
  have "(den (ACrel \<sigma> \<tau>) \<xi> = Tv)
      = (\<forall>d. Dm (\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>) d
             \<longrightarrow> den (ACprem \<sigma> \<tau> \<^bold>\<supset> ACconcl \<sigma> \<tau>) (\<xi>(rR\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<tau> \<^bold>\<Rightarrow> \<o>\<^esub> := d)) = Tv)"
    unfolding ACrel_def by (rule sat_AllN[OF wff_ImpB[OF wff_ACprem wff_ACconcl] xi])
  thus "den (ACrel \<sigma> \<tau>) \<xi> = Tv" using body by simp
qed
end

text \<open>\<^bold>\<open>The relative-consistency theorem, abstractly.\<close>  Suppose \<^emph>\<open>some\<close> \<^emph>\<open>standard\<close>
  \<open>\<Sigma>\<close>-model has an injective but not surjective self-map of its individuals --- that is,
  Dedekind-infinitely many individuals.  Then full classical \<open>HOL\<close> is consistent.
  Consistency is the predicate \<open>con\<close> of the main entry, defined by
  \<open>con \<Phi> \<longleftrightarrow> \<not> (\<Phi> \<turnstile> \<^bold>\<bottom>)\<close>: the conclusion below states that \<open>NK\<close> cannot derive falsity
  from \<open>DInf\<close> together with all instances of \<open>ACrel\<close>.  The eigen-parameter starvation that
  makes \<open>con\<close> a weak reading for impure infinite contexts (main entry, \<open>NK_Infinity\<close>)
  cannot arise here: the axioms use no parameters at all, so the context is pure, and over
  an infinite signature \<open>con \<Phi>\<close> and \<open>\<not> (\<Phi> \<tturnstile> \<^bold>\<bottom>)\<close> provably coincide
  (@{thm [source] fprov_eq_bprov}).  The proof
  works for an \<^emph>\<open>arbitrary\<close> such model, whatever type its elements come from, and uses no
  set theory.  The one thing plain HOL cannot supply is the premise --- a model with
  infinitely many individuals; producing one is the central task of the set-theoretic theory
  that concludes this entry.\<^footnote>\<open>Why not?  Plain HOL has infinite @{emph \<open>types\<close>}, and every
  single level \<open>nat\<close>, \<open>nat \<Rightarrow> bool\<close>, \<open>\<dots>\<close> of the full tower exists as a type.  What it lacks
  is @{emph \<open>one carrier\<close>} for the whole tower at once.  In BKK's sense ``standard'' means
  only that the function domains are @{emph \<open>full\<close>}; but a model formalised inside plain HOL
  necessarily has one further feature: the object types are values of the datatype \<open>ty\<close>, so
  any formalised model --- the locale @{locale standard_model} included --- interprets all
  domains inside a single carrier type \<open>'u\<close> (simple types cannot assign each object type its
  own meta-type).  Over infinite individuals with full function spaces that one carrier must
  outgrow every level of the tower.  No plain-HOL type reaches that far: every type plain HOL can construct is bounded
  in cardinality by some finite tower of function spaces over its one primitive infinite
  type \<open>ind\<close> (of which \<open>nat\<close> is the familiar copy).  One might hope to escape with a @{emph \<open>Henkin\<close>} model, whose function domains
  need not be full and which therefore fits into a small carrier.  But a sparse function
  domain need not provide what the axiom asks for.  \<open>DInf\<close> says: @{emph \<open>there exists\<close>} an injective,
  non-surjective self-map of the individuals.  In a Henkin model that map has to be an
  element of the (now sparse) function domain \<open>D\<^bsub>\<iota> \<^bold>\<Rightarrow> \<iota>\<^esub>\<close> --- and it may simply not be
  there, even when the individuals are infinite.  This is not a hypothetical: the main
  entry's \<open>henkin_scheme_refutes_DInf\<close> constructs a Henkin model with infinitely many
  individuals in which \<open>DInf\<close> is nevertheless @{emph \<open>false\<close>}.  And the canonical way to build
  a Henkin model that does contain the witness --- the term-model construction --- takes the
  consistency of \<open>DInf\<close> as its @{emph \<open>premise\<close>}, and so cannot be the way to prove it
  (that @{emph \<open>every\<close>} other route fails as well is G\"odel's second theorem, see the
  introduction).\<close>\<close>

theorem con_full_HOL_rel:
  fixes Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and Lm :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u" and Tv Fv Ngv Dsv :: 'u
    and Iv Ev Piv :: "ty \<Rightarrow> 'u" and Jv :: "'p \<Rightarrow> ty \<Rightarrow> 'u"
  assumes M: "standard_model Dm Ap Lm Tv Fv Ngv Dsv Iv Ev Piv Jv"
    and inf: "\<exists>d. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d
                  \<and> (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (Ap d a = Ap d b \<longrightarrow> a = b)))
                  \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> Ap d z \<noteq> c))"
  shows "con (insert (DInf :: 'p tm) (range (\<lambda>(\<sigma>,\<tau>). ACrel \<sigma> \<tau>)))"
proof -
  interpret standard_model Dm Ap Lm Tv Fv Ngv Dsv Iv Ev Piv Jv by (rule M)
  \<comment> \<open>the constants inhabit their domains, so a domain-respecting assignment exists\<close>
  define \<xi> :: "nat \<Rightarrow> ty \<Rightarrow> 'u" where "\<xi> = (\<lambda>n \<rho>. Jv undefined \<rho>)"
  have xi: "bkkA.asg \<xi>" by (simp add: \<xi>_def bkkA.asg_def Jv_dom)
  from inf obtain d where d: "Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d"
    and dinj: "\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (Ap d a = Ap d b \<longrightarrow> a = b))"
    and dns: "\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> Ap d z \<noteq> c)" by blast
  have satD: "den (DInf :: 'p tm) \<xi> = Tv" by (rule DInf_sat[OF xi d dinj dns])
  have satAC: "den (ACrel \<sigma> \<tau> :: 'p tm) \<xi> = Tv" for \<sigma> \<tau> by (rule ACrel_sat[OF xi])
  show ?thesis
    by (rule model_con[OF xi]) (use wff_DInf wff_ACrel satD satAC in auto)
qed

text \<open>Completeness carries over to the axiomatic extension, in its strongest form: \<open>{DInf}\<close> is
  a finite context, so @{thm [source] completeness_hyps_open_finite} applies ---
  free variables are allowed in the conclusion, the carrier and the signature are any infinite
  types, and purity is automatic.  Any formula true in every infinite-carrier model of \<open>DInf\<close>
  is thus already derivable from \<open>DInf\<close> in \<open>NK\<close>, and with soundness the two coincide ---
  established by the plain-HOL completeness of the main entry, with no set universe.\<close>

theorem NK_completeness_DInf:
  fixes A :: "'p::infinite tm"
  assumes "wff\<^bsub>\<o>\<^esub>(A)" and "{DInf} \<Turnstile>('u::infinite) A"
  shows "{DInf} \<turnstile> A"
proof (rule completeness_hyps_open_finite[OF _ _ assms(1) assms(2)])
  show "finite {DInf :: 'p tm}" by simp
next
  fix B :: "'p tm" assume "B \<in> {DInf}"
  thus "wff\<^bsub>\<o>\<^esub>(B)" by (simp add: wff_DInf)
qed

theorem sound_and_complete_DInf:
  fixes A :: "'p::infinite tm"
  assumes "wff\<^bsub>\<o>\<^esub>(A)"
  shows "{DInf} \<turnstile> A \<longleftrightarrow> {DInf} \<Turnstile>('u::infinite) A"
  using assms NK_completeness_DInf soundness_sat by blast


section \<open>Minimising the meta-theory: a weaker universe suffices\<close>

text \<open>We weaken the premise of @{thm [source] con_full_HOL_rel} once more.  Instead of
  \<^emph>\<open>assuming\<close> the logical constants (as \<open>standard_model\<close> does), the locale \<open>hol_universe\<close>
  adds Dedekind-infinite individuals to the constants-construction interface
  @{locale lambda_universe} of the main entry: a universe with full function spaces,
  booleans, extensionality and a domain-respecting parameter interpretation, over which
  the constants are @{emph \<open>constructed\<close>}.  Any model of these weaker assumptions ---
  the final theory provides one over \<open>V\<close> --- thus yields the relative consistency of full \<open>HOL\<close>.\<close>

locale hol_universe = lambda_universe Dm Ap Lm Tv Fv Jv
  for Dm :: "ty \<Rightarrow> 'u \<Rightarrow> bool" and Ap :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and Lm :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u" and Tv Fv :: 'u and Jv :: "'p \<Rightarrow> ty \<Rightarrow> 'u" +
  assumes ind_inf: "\<exists>d. Dm (\<iota> \<^bold>\<Rightarrow> \<iota>) d
                     \<and> (\<forall>a. Dm \<iota> a \<longrightarrow> (\<forall>b. Dm \<iota> b \<longrightarrow> (Ap d a = Ap d b \<longrightarrow> a = b)))
                     \<and> (\<exists>c. Dm \<iota> c \<and> (\<forall>z. Dm \<iota> z \<longrightarrow> Ap d z \<noteq> c))"
begin

theorem con_full_HOL_universe:
  "con (insert (DInf :: 'p tm) (range (\<lambda>(\<sigma>,\<tau>). ACrel \<sigma> \<tau>)))"
  by (rule con_full_HOL_rel[OF is_standard_model ind_inf])

end

section \<open>Minimising further: a Harrison-style universe axiom\<close>

text \<open>Harrison's self-verification of HOL Light \<^cite>\<open>Harrison06\<close> proves the soundness of
  HOL-with-infinity in a meta-logic strengthened by a single \<^emph>\<open>universe axiom\<close>: an infinite
  type closed under the set-forming operations that full function spaces require.  The
  locale \<open>harrison_universe\<close> is our rendering of that axiom, one level below
  \<open>hol_universe\<close>: it mentions neither types, domains, application nor abstraction.  Fixed
  are an injective pairing \<open>pr\<close>, an injective coding \<open>enc\<close> of the \<^emph>\<open>small\<close> collections
  \<open>Sm\<close>, and a small Dedekind-infinite collection \<open>D0\<close> of individuals; smallness is closed
  downwards, under products and --- the strong-limit core of Harrison's axiom --- under
  \<^emph>\<open>coded power collections\<close> (\<open>Sm_pow\<close>).\<^footnote>\<open>In effect this axiom postulates a fresh base
  type \<open>v\<close> that gathers the domains of the whole type hierarchy over \<open>\<iota>\<close> and \<open>\<o>\<close>, so that
  every finite-type domain embeds into it.  The subtlety is that \<open>v\<close> is closed only under the
  operations those finite types require --- pairing and \<^emph>\<open>small\<close> (coded) power collections ---
  and \<^emph>\<open>not\<close> under its own full function space \<open>v \<^bold>\<Rightarrow> \<o>\<close>, which by Cantor would be strictly
  larger.  This restricted closure, rather than a full powerset, is exactly what keeps the
  axiom consistent and of merely strong-limit strength.\<close>  From these data alone the whole
  \<open>hol_universe\<close> structure is @{emph \<open>constructed\<close>}: domains as collections of coded functional
  graphs, abstraction by coding, application by decoding.\<close>

locale harrison_universe =
  fixes pr :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" and enc :: "('u \<Rightarrow> bool) \<Rightarrow> 'u"
    and Sm :: "('u \<Rightarrow> bool) \<Rightarrow> bool" and D0 :: "'u \<Rightarrow> bool"
  assumes pr_inj: "pr a b = pr c d \<Longrightarrow> a = c \<and> b = d"
    and enc_inj: "\<lbrakk>Sm X; Sm Y; enc X = enc Y\<rbrakk> \<Longrightarrow> X = Y"
    and Sm_sub: "\<lbrakk>Sm X; Y \<le> X\<rbrakk> \<Longrightarrow> Sm Y"
    and Sm_prod: "\<lbrakk>Sm X; Sm Y\<rbrakk> \<Longrightarrow> Sm (\<lambda>z. \<exists>a b. X a \<and> Y b \<and> z = pr a b)"
    and Sm_pow: "Sm X \<Longrightarrow> Sm (\<lambda>z. \<exists>Y. Y \<le> X \<and> Sm Y \<and> z = enc Y)"
    and Sm_D0: "Sm D0"
    and D0_inf: "\<exists>f c. (\<forall>a. D0 a \<longrightarrow> D0 (f a))
                     \<and> (\<forall>a b. D0 a \<longrightarrow> D0 b \<longrightarrow> f a = f b \<longrightarrow> a = b)
                     \<and> D0 c \<and> (\<forall>a. D0 a \<longrightarrow> f a \<noteq> c)"
begin

text \<open>Smallness of the empty collection need not be assumed: it is a sub-collection of the
  small \<open>D0\<close>.\<close>

lemma Sm_empty: "Sm (\<lambda>_. False)"
  by (rule Sm_sub[OF Sm_D0]) (simp add: le_fun_def)

subsection \<open>Truth values, domains, abstraction, application\<close>

text \<open>The truth values are the first stages of the cumulative hierarchy in miniature: \<open>HTv\<close>
  codes the empty collection, \<open>HFv\<close> its singleton.  Both collections are small --- the empty
  one by \<open>Sm_empty\<close>, its singleton as the coded power collection of the empty one
  (\<open>Sm_pow\<close>) --- and \<open>enc_inj\<close> keeps the two codes apart.  A function domain consists of the codes of the
  functional graphs over the argument domain; application decodes, abstraction codes.\<close>

definition HTv :: 'u where "HTv = enc (\<lambda>_. False)"
definition HFv :: 'u where "HFv = enc (\<lambda>z. z = HTv)"

primrec HD :: "ty \<Rightarrow> 'u \<Rightarrow> bool" where
  "HD \<iota> = D0"
| "HD \<o> = (\<lambda>x. x = HTv \<or> x = HFv)"
| "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) = (\<lambda>x. \<exists>g. (\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a))
                        \<and> x = enc (\<lambda>z. \<exists>a. HD \<sigma> a \<and> z = pr a (g a)))"

definition Hgr :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u \<Rightarrow> bool" where
  "Hgr \<sigma> g = (\<lambda>z. \<exists>a. HD \<sigma> a \<and> z = pr a (g a))"
definition HLm :: "ty \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u" where "HLm \<sigma> g = enc (Hgr \<sigma> g)"
text \<open>The \<open>THE\<close> below is Isabelle's @{emph \<open>definite description\<close>} at the meta-level ---
  unique choice, not a choice principle; decoding is well-defined by \<open>enc_inj\<close>.  (The
  \<open>SOME\<close> in \<open>HJv\<close> is meta-level Hilbert choice of Isabelle/HOL.  Neither adds an axiom to
  the embedded object logic.)\<close>

definition Hdec :: "'u \<Rightarrow> 'u \<Rightarrow> bool" where "Hdec x = (THE X. Sm X \<and> enc X = x)"
definition HAp :: "'u \<Rightarrow> 'u \<Rightarrow> 'u" where "HAp f a = (THE b. Hdec f (pr a b))"
definition HJv :: "'p \<Rightarrow> ty \<Rightarrow> 'u" where "HJv p \<sigma> = (SOME d. HD \<sigma> d)"

lemma HD_Fun: "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) x \<longleftrightarrow> (\<exists>g. (\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)) \<and> x = HLm \<sigma> g)"
  by (simp add: HLm_def Hgr_def)

subsection \<open>Every domain is small and inhabited\<close>

lemma Sm_singleton_HTv: "Sm (\<lambda>z. z = HTv)"
proof -
  have "(\<lambda>z. \<exists>Y. Y \<le> (\<lambda>_. False) \<and> Sm Y \<and> z = enc Y) = (\<lambda>z. z = HTv)"
  proof (rule ext)
    fix z show "(\<exists>Y. Y \<le> (\<lambda>_. False) \<and> Sm Y \<and> z = enc Y) = (z = HTv)"
    proof
      assume "\<exists>Y. Y \<le> (\<lambda>_. False) \<and> Sm Y \<and> z = enc Y"
      then obtain Y where "Y \<le> (\<lambda>_. False)" and z: "z = enc Y" by blast
      from this(1) have "Y = (\<lambda>_. False)" by (auto simp: le_fun_def fun_eq_iff)
      with z show "z = HTv" by (simp add: HTv_def)
    next
      assume "z = HTv"
      hence "(\<lambda>_. False) \<le> (\<lambda>_. False) \<and> Sm (\<lambda>_. False) \<and> z = enc (\<lambda>_. False)"
        using Sm_empty by (simp add: HTv_def)
      thus "\<exists>Y. Y \<le> (\<lambda>_. False) \<and> Sm Y \<and> z = enc Y" by blast
    qed
  qed
  with Sm_pow[OF Sm_empty] show ?thesis by simp
qed

lemma HTv_neq_HFv: "HTv \<noteq> HFv"
proof
  assume "HTv = HFv"
  hence "(\<lambda>_. False) = (\<lambda>z. z = HTv)"
    using enc_inj[OF Sm_empty Sm_singleton_HTv] HTv_def HFv_def by metis
  from fun_cong[OF this, of HTv] show False by simp
qed

lemma Sm_bool: "Sm (HD \<o>)"
proof -
  have sub: "Y = (\<lambda>_. False) \<or> Y = (\<lambda>z. z = HTv)" if le: "Y \<le> (\<lambda>z. z = HTv)" for Y
  proof -
    have imp: "Y w \<Longrightarrow> w = HTv" for w using le_funD[OF le, of w] by simp
    show ?thesis
    proof (cases "Y HTv")
      case True
      have "Y = (\<lambda>z. z = HTv)" by (rule ext) (use imp True in blast)
      thus ?thesis ..
    next
      case False
      have "Y = (\<lambda>_. False)" by (rule ext) (use imp False in blast)
      thus ?thesis ..
    qed
  qed
  have "(\<lambda>z. \<exists>Y. Y \<le> (\<lambda>z. z = HTv) \<and> Sm Y \<and> z = enc Y) = HD \<o>"
  proof (rule ext)
    fix z show "(\<exists>Y. Y \<le> (\<lambda>z. z = HTv) \<and> Sm Y \<and> z = enc Y) = HD \<o> z"
    proof
      assume "\<exists>Y. Y \<le> (\<lambda>z. z = HTv) \<and> Sm Y \<and> z = enc Y"
      then obtain Y where "Y \<le> (\<lambda>z. z = HTv)" and z: "z = enc Y" by blast
      from sub[OF this(1)] z show "HD \<o> z" by (auto simp: HTv_def HFv_def)
    next
      assume "HD \<o> z"
      then consider "z = HTv" | "z = HFv" by auto
      thus "\<exists>Y. Y \<le> (\<lambda>z. z = HTv) \<and> Sm Y \<and> z = enc Y"
      proof cases
        case 1
        hence "(\<lambda>_. False) \<le> (\<lambda>z. z = HTv) \<and> Sm (\<lambda>_. False) \<and> z = enc (\<lambda>_. False)"
          using Sm_empty by (simp add: le_fun_def HTv_def)
        thus ?thesis by blast
      next
        case 2
        hence "(\<lambda>z. z = HTv) \<le> (\<lambda>z. z = HTv) \<and> Sm (\<lambda>z. z = HTv) \<and> z = enc (\<lambda>z. z = HTv)"
          using Sm_singleton_HTv by (simp add: HFv_def)
        thus ?thesis by blast
      qed
    qed
  qed
  with Sm_pow[OF Sm_singleton_HTv] show ?thesis by simp
qed

text \<open>The function-space case is the Harrison core: every coded graph is a small
  subcollection of the product of the two domains, so the domain of codes sits inside the
  coded power collection of that product.\<close>

lemma Sm_HD: "Sm (HD \<sigma>)"
proof (induction \<sigma>)
  case Ind show ?case by (simp add: Sm_D0)
next
  case Bool show ?case by (rule Sm_bool)
next
  case (Fun \<sigma> \<tau>)
  let ?P = "\<lambda>z. \<exists>a b. HD \<sigma> a \<and> HD \<tau> b \<and> z = pr a b"
  have "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) \<le> (\<lambda>z. \<exists>Y. Y \<le> ?P \<and> Sm Y \<and> z = enc Y)"
  proof (intro le_funI le_boolI)
    fix x assume "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) x"
    hence "\<exists>g. (\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)) \<and> x = HLm \<sigma> g"
      by (simp add: HLm_def Hgr_def)
    then obtain g where g: "\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)" and x: "x = HLm \<sigma> g" by blast
    have le: "Hgr \<sigma> g \<le> ?P" using g by (auto simp: Hgr_def le_fun_def)
    have "Sm (Hgr \<sigma> g)" by (rule Sm_sub[OF Sm_prod[OF Fun.IH] le])
    with le x show "\<exists>Y. Y \<le> ?P \<and> Sm Y \<and> x = enc Y" by (auto simp: HLm_def)
  qed
  from Sm_sub[OF Sm_pow[OF Sm_prod[OF Fun.IH]] this] show ?case .
qed

lemma HLm_dom: assumes "\<And>d. HD \<sigma> d \<Longrightarrow> HD \<tau> (h d)" shows "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) (HLm \<sigma> h)"
  unfolding HD_Fun using assms by blast

lemma HD_ne: "\<exists>x. HD \<sigma> x"
proof (induction \<sigma>)
  case Ind show ?case using D0_inf by auto
next
  case Bool show ?case by auto
next
  case (Fun \<sigma> \<tau>)
  from Fun.IH(2) obtain w where w: "HD \<tau> w" by blast
  have "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) (HLm \<sigma> (\<lambda>_. w))" by (rule HLm_dom) (rule w)
  thus ?case by blast
qed

subsection \<open>Decoding is inverse to coding, and the frame conditions follow\<close>

lemma Hdec_enc: assumes "Sm X" shows "Hdec (enc X) = X"
  unfolding Hdec_def by (rule the_equality) (use assms enc_inj in \<open>blast+\<close>)

lemma Hgr_pr: assumes "HD \<sigma> a" shows "Hgr \<sigma> h (pr a b) \<longleftrightarrow> b = h a"
  using assms by (auto simp: Hgr_def dest: pr_inj)

lemma Sm_Hgr: assumes "\<And>d. HD \<sigma> d \<Longrightarrow> HD \<tau> (h d)" shows "Sm (Hgr \<sigma> h)"
proof (rule Sm_sub[OF Sm_prod[OF Sm_HD Sm_HD]])
  show "Hgr \<sigma> h \<le> (\<lambda>z. \<exists>a b. HD \<sigma> a \<and> HD \<tau> b \<and> z = pr a b)"
    using assms by (auto simp: Hgr_def le_fun_def)
qed

lemma HAp_HLm: assumes sm: "Sm (Hgr \<sigma> h)" and a: "HD \<sigma> a" shows "HAp (HLm \<sigma> h) a = h a"
  unfolding HAp_def HLm_def Hdec_enc[OF sm]
  by (rule the_equality) (simp_all add: Hgr_pr[OF a])

lemma HD_FunE:
  assumes f: "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f"
  shows "\<exists>g. (\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)) \<and> f = HLm \<sigma> g \<and> (\<forall>a. HD \<sigma> a \<longrightarrow> HAp f a = g a)"
proof -
  from f have "\<exists>g. (\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)) \<and> f = HLm \<sigma> g"
    by (simp add: HLm_def Hgr_def)
  then obtain g where g: "\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)" and fe: "f = HLm \<sigma> g" by blast
  have sm: "Sm (Hgr \<sigma> g)" by (rule Sm_Hgr) (use g in blast)
  have "\<forall>a. HD \<sigma> a \<longrightarrow> HAp f a = g a" unfolding fe using HAp_HLm[OF sm] by blast
  with g fe show ?thesis by blast
qed

lemma HAp_dom: assumes f: "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) f" and a: "HD \<sigma> a" shows "HD \<tau> (HAp f a)"
proof -
  from HD_FunE[OF f] obtain g where g: "\<forall>a. HD \<sigma> a \<longrightarrow> HD \<tau> (g a)"
    and app: "\<forall>a. HD \<sigma> a \<longrightarrow> HAp f a = g a" by blast
  from g app a show ?thesis by auto
qed

lemma HAp_ext:
  assumes g: "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) g" and k: "HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) k"
    and e: "\<And>a. HD \<sigma> a \<Longrightarrow> HAp g a = HAp k a"
  shows "g = k"
proof -
  from HD_FunE[OF g] obtain g0 where g0: "g = HLm \<sigma> g0"
    and appg: "\<forall>a. HD \<sigma> a \<longrightarrow> HAp g a = g0 a" by blast
  from HD_FunE[OF k] obtain k0 where k0: "k = HLm \<sigma> k0"
    and appk: "\<forall>a. HD \<sigma> a \<longrightarrow> HAp k a = k0 a" by blast
  have gk: "g0 a = k0 a" if "HD \<sigma> a" for a
    using appg appk e[OF that] that by simp
  have "Hgr \<sigma> g0 = Hgr \<sigma> k0" by (rule ext) (auto simp: Hgr_def gk)
  thus ?thesis by (simp add: g0 k0 HLm_def)
qed

lemma HJv_dom: "HD \<sigma> (HJv p \<sigma>)"
  unfolding HJv_def by (rule someI_ex[OF HD_ne])

text \<open>Dedekind infinity transfers from the meta-level self-map \<open>f\<close> of \<open>D0\<close> to the object
  level: the witness in \<open>HD (\<iota> \<^bold>\<Rightarrow> \<iota>)\<close> is its coded graph \<open>HLm \<iota> f\<close>.\<close>

lemma HD_inf:
  "\<exists>d. HD (\<iota> \<^bold>\<Rightarrow> \<iota>) d
     \<and> (\<forall>a. HD \<iota> a \<longrightarrow> (\<forall>b. HD \<iota> b \<longrightarrow> (HAp d a = HAp d b \<longrightarrow> a = b)))
     \<and> (\<exists>c. HD \<iota> c \<and> (\<forall>z. HD \<iota> z \<longrightarrow> HAp d z \<noteq> c))"
proof -
  from D0_inf obtain f c where f: "\<forall>a. D0 a \<longrightarrow> D0 (f a)"
    and inj: "\<forall>a b. D0 a \<longrightarrow> D0 b \<longrightarrow> f a = f b \<longrightarrow> a = b"
    and c: "D0 c" and ns: "\<forall>a. D0 a \<longrightarrow> f a \<noteq> c" by blast
  have sm: "Sm (Hgr \<iota> f)" by (rule Sm_Hgr[where \<tau> = \<iota>]) (use f in simp)
  have dty: "HD (\<iota> \<^bold>\<Rightarrow> \<iota>) (HLm \<iota> f)" by (rule HLm_dom) (use f in simp)
  have dapp: "\<And>a. HD \<iota> a \<Longrightarrow> HAp (HLm \<iota> f) a = f a" by (rule HAp_HLm[OF sm])
  have "\<forall>a. HD \<iota> a \<longrightarrow> (\<forall>b. HD \<iota> b \<longrightarrow> (HAp (HLm \<iota> f) a = HAp (HLm \<iota> f) b \<longrightarrow> a = b))"
    using inj by (simp add: dapp)
  moreover have "\<exists>c'. HD \<iota> c' \<and> (\<forall>z. HD \<iota> z \<longrightarrow> HAp (HLm \<iota> f) z \<noteq> c')"
    using c ns by (auto simp: dapp intro!: exI[of _ c])
  ultimately show ?thesis using dty by blast
qed

subsection \<open>Every Harrison universe is a \<open>hol_universe\<close>\<close>

theorem harrison_hol_universe: "hol_universe HD HAp HLm HTv HFv (HJv :: 'p \<Rightarrow> ty \<Rightarrow> 'u)"
proof unfold_locales
  show "\<And>\<sigma> \<tau> g k. HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) g \<Longrightarrow> HD (\<sigma> \<^bold>\<Rightarrow> \<tau>) k \<Longrightarrow>
         (\<And>a. HD \<sigma> a \<Longrightarrow> HAp g a = HAp k a) \<Longrightarrow> g = k" by (rule HAp_ext)
  show "\<And>a. HD \<o> a \<longleftrightarrow> a = HTv \<or> a = HFv" by simp
qed(safe intro!: HD_inf HJv_dom HTv_neq_HFv HAp_dom HLm_dom HAp_HLm[OF Sm_Hgr])

lemmas harrison_standard_model =
  lambda_universe.is_standard_model[OF hol_universe.axioms(1)[OF harrison_hol_universe]]

theorem con_full_HOL_harrison:
  "con (insert (DInf :: 'p tm) (range (\<lambda>(\<sigma>,\<tau>). ACrel \<sigma> \<tau>)))"
  by (rule hol_universe.con_full_HOL_universe[OF harrison_hol_universe])

end

end
