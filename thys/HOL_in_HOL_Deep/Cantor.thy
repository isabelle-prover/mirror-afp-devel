theory Cantor
  imports Consistency
begin


section \<open>Example: Cantor's theorem\<close>

text \<open>The surjective and the injective Cantor theorem, at every type \<open>\<sigma>\<close>: there is no
  surjection from \<open>\<sigma>\<close> onto \<open>\<sigma> \<^bold>\<Rightarrow> \<o>\<close>, and no injection from \<open>\<sigma> \<^bold>\<Rightarrow> \<o>\<close> into \<open>\<sigma>\<close>.  Both are
  derived @{emph \<open>inside the calculus\<close>}: genuine \<open>NK\<close>-derivations via the diagonal
  predicate (for the injective version via the description operator \<open>NK(\<iota>)\<close>, following
  Andrews 1972).  The Cantor sentences are stated as in the @{emph \<open>Stanford
  Encyclopedia of Philosophy\<close>} entry on Church's type theory (Benzm\"uller and
  Andrews 2024), generalised from \<open>\<iota>\<close> to every type \<open>\<sigma>\<close>.\<close>

subsection \<open>The defined existential quantifier, and the Cantor sentences\<close>

text \<open>The Cantor sentences are stated literally, as in the cited encyclopedia entry: no surjection
  \<open>\<G> : \<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<close> onto \<open>\<sigma> \<^bold>\<Rightarrow> \<o>\<close>, and no injection \<open>\<I> : (\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<close>.  The
  following lemmas record their locally-nameless normal forms (by computation) and
  the closedness facts used by the derivations.  The right-hand sides deliberately
  show the machine-level de Bruijn normal form (indices \<open>Bnd 0\<close>, \<open>Bnd (Suc 0)\<close>
  and so on); the named-binder left-hand sides are the human-facing statements.\<close>

lemma surj_norm:
  "(\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>. ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
   = \<^bold>\<exists>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<exists>\<^bsub>\<sigma>\<^esub>
      ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd (Suc 0))))"
  by (simp add: ExN_def AllN_def \<G>_def \<F>_def \<X>_def)

lemma inj_norm:
  "(\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
      (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
       \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)))
   = \<^bold>\<exists>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>
      (((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>=\<^bsub>\<sigma>\<^esub> (Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd
          0))
       \<^bold>\<supset> (Bnd (Suc 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0))))"
  by (simp add: ExN_def AllN_def \<I>_def \<F>_def \<H>_def)

lemma wff_surj:
  "wff\<^bsub>\<o>\<^esub>(\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>.
      ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))"
  unfolding surj_norm
  by (intro wff_Not wff_Forall)
     (auto del: wff_Not wff_PEq wff_Forall
           intro!: wff_Not wff_Forall wff_PEq wff_Eq wff_App wff_Fre)

lemma wff_inj:
  "wff\<^bsub>\<o>\<^esub>(\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
      (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
       \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)))"
  unfolding inj_norm
  by (intro wff_Not wff_Forall)
     (auto del: wff_Not wff_Forall wff_ImpB wff_PEq
           intro!: wff_Not wff_Forall wff_ImpB wff_PEq wff_Eq wff_App wff_Fre)

lemma fvs_surj [simp]:
  "fvs (\<^bold>\<not> (\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>.
      ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))) = {}"
  by (simp add: surj_norm)

lemma fvs_inj [simp]:
  "fvs (\<^bold>\<not> (\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
      (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
       \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)))) = {}"
  by (simp add: inj_norm)

lemma pars_surj [simp]:
  "pars (\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>.
      ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)) = {}"
  by (simp add: surj_norm Forall_def)

lemma pars_inj [simp]:
  "pars (\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
      (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
       \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))) = {}"
  by (simp add: inj_norm)

text \<open>Typing of the terms occurring in the derivations, once and for all.\<close>

lemma wff_surj_body:
  "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<exists>\<^bsub>\<sigma>\<^esub>
     ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd (Suc 0)))))"
  by (rule wff_AbsI)
     (auto del: wff_Not wff_Forall wff_PEq
           intro!: wff_Not wff_Forall wff_PEq wff_Eq wff_App wff_Fre)

lemma wff_inst_body:
  "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<exists>\<^bsub>\<sigma>\<^esub>
     ((Par g (\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd (Suc 0))))"
  by (rule wff_AbsI)
     (auto del: wff_Not wff_Forall wff_PEq
           intro!: wff_Not wff_Forall wff_PEq wff_Eq wff_App wff_Par wff_Fre)

lemma wff_diag:
  "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> ((Par g (\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<cdot> Bnd 0) \<^bold>\<cdot> Bnd 0)))"
  by (rule wff_AbsI) (auto del: wff_Not intro!: wff_Not wff_App wff_Par wff_Fre)

lemma wff_wit_body:
  assumes "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(D)" and "lc D"
  shows "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> ((Par g (\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> D))"
  using assms
  by (intro wff_AbsI) (auto del: wff_PEq intro!: wff_PEq wff_Eq wff_App wff_Par wff_Fre)

subsection \<open>The surjective Cantor theorem in \<open>NK\<close>\<close>

theorem nk_surjective_cantor: fixes \<sigma> :: ty shows
  "\<turnstile> (\<^bold>\<not> (\<^bold>\<exists>\<G>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<exists>\<X>\<^bsub>\<sigma>\<^esub>.
     ((\<G>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>\<cdot> \<X>\<^sup>f\<^bsub>\<sigma>\<^esub>) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>)) :: 'p::infinite tm)"
    (is "\<turnstile> \<^bold>\<not> ?S")
proof -
  \<comment> \<open>two distinct parameters: the assumed surjection \<open>g\<close>, the inner witness \<open>a\<close>\<close>
  obtain g a :: 'p where ag: "a \<noteq> g"
    by (metis (full_types) ex_new_if_finite finite.emptyI
        finite.insertI infinite_UNIV insert_iff)
  let ?gP = "g\<^sup>p\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> :: 'p tm" and ?aP = "a\<^sup>p\<^bsub>\<sigma>\<^esub> :: 'p tm"
  \<comment> \<open>the diagonal \<open>?F = \<^bold>\<Lambda>\<X>. \<^bold>\<not> (g \<^bold>\<cdot> \<X> \<^bold>\<cdot> \<X>)\<close>; the two \<open>\<^bold>\<exists>\<close>-assumptions;
    the diagonal instance \<open>?\<phi> = g \<^bold>\<cdot> a \<^bold>\<cdot> a\<close>\<close>
  let ?F = "\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> ((?gP \<^bold>\<cdot> Bnd 0) \<^bold>\<cdot> Bnd 0))"
  let ?Sg = "\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<exists>\<^bsub>\<sigma>\<^esub> ((?gP \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd (Suc 0)))"
  let ?E = "(?gP \<^bold>\<cdot> ?aP) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?F"
  let ?\<phi> = "(?gP \<^bold>\<cdot> ?aP) \<^bold>\<cdot> ?aP"
  \<comment> \<open>bookkeeping, once and for all: typing and parameter-freshness\<close>
  have wF: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(?F)" by (rule wff_diag)
  have lcF: "lc ?F" by (rule wff_lc[OF wF])
  have fp1: "freep {?S, ?Sg}" and fp2: "freep {?S, ?Sg, ?E}"
    by (intro freep_finite, simp)+
  \<comment> \<open>the derivation, innermost context first\<close>
  have 1: "{?S, ?Sg, ?E} \<turnstile> ?E"  \<comment> \<open>\<open>NK(Hyp)\<close>\<close>
    by (auto intro: bprov.Hyp)
  have 2: "{?S, ?Sg, ?E} \<turnstile> ?\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (?F \<^bold>\<cdot> ?aP)"
    \<comment> \<open>apply both sides of (1) to \<open>a\<close> --- \<open>NK(=\<^sub>l)\<close>, Leibniz \<open>NK(\<Pi>E)\<close>\<close>
    by (rule peq_app[OF 1 fp2]) (auto intro!: wff_App wff_Par wF)
  have 3: "?F \<^bold>\<cdot> ?aP \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<not> ?\<phi>"  \<comment> \<open>\<open>\<beta>\<close>-reduce the diagonal\<close>
    using beq.beta[OF wF wff_Par] by simp
  have 4: "{?S, ?Sg, ?E} \<turnstile> ?\<phi> \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (\<^bold>\<not> ?\<phi>)"  \<comment> \<open>\<open>NK(\<beta>)\<close> on (2) by (3)\<close>
    by (rule leib_reduce_right[OF 2 3]) (auto intro!: wff_App wff_Par)
  have 5: "{?S, ?Sg, ?E} \<turnstile> \<^bold>\<bottom>"
    \<comment> \<open>\<open>?\<phi> \<^bold>\<doteq> \<^bold>\<not> ?\<phi>\<close> is contradictory --- \<open>NK(\<Pi>E)\<close>, \<open>NK(\<not>E)\<close>, tertium non datur\<close>
    by (rule leib_neg_contra[OF 4 fp2]) (auto intro!: wff_App wff_Par)
  have 6: "{?S, ?Sg} \<turnstile> ?Sg"  \<comment> \<open>\<open>NK(Hyp)\<close>\<close>
    by (auto intro: bprov.Hyp)
  have 7: "{?S, ?Sg} \<turnstile> \<^bold>\<exists>\<^bsub>\<sigma>\<^esub> ((?gP \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?F)"
    \<comment> \<open>\<open>NK(\<Pi>E)\<close>: instantiate the surjectivity of \<open>g\<close> at the diagonal \<open>?F\<close>\<close>
    using PiE_open[OF 6 wff_inst_body wF]
    by (simp add: opn_lc[OF lcF])
  have 8: "{?S, ?Sg} \<turnstile> \<^bold>\<bottom>"  \<comment> \<open>\<open>NK(\<exists>E)\<close>, discharging the witness \<open>a\<close>\<close>
    by (rule ExE[where w = a, OF 7 _
          wff_wit_body[OF wF lcF] wff_FalseB])
      (use 5 ag in \<open>auto simp: opn_lc[OF lcF] insert_commute
        intro!: freep_finite\<close>)
  have 9: "{?S} \<turnstile> \<^bold>\<exists>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<exists>\<^bsub>\<sigma>\<^esub>
      ((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd (Suc 0))))"
    \<comment> \<open>\<open>NK(Hyp)\<close>, in locally-nameless normal form\<close>
    by (subst surj_norm[symmetric]) (auto intro: bprov.Hyp)
  have 10: "{?S} \<turnstile> \<^bold>\<bottom>"  \<comment> \<open>\<open>NK(\<exists>E)\<close>, discharging the witness \<open>g\<close>\<close>
    by (rule ExE[where w = g, OF 9 _ wff_surj_body wff_FalseB])
      (use 8 in \<open>auto simp: insert_commute intro!: freep_finite\<close>)
  show ?thesis  \<comment> \<open>\<open>NK(\<not>I)\<close> discharges the assumed surjection\<close>
    by (rule bprov.NegI[OF _ wff_surj]) (use 10 in simp)
qed

subsection \<open>The injective Cantor theorem in \<open>NK\<close>\<close>

  text \<open>Typing of the description-based diagonal predicate.\<close>

lemma wff_desc_diag: 
  "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> (((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (((Par i ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>)) \<^bold>\<cdot>
      Bnd 0) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> Bnd (Suc 0)))) \<^bold>\<cdot> Bnd 0)))"
proof (rule wff_AbsI)
  fix x
  have inner: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (((Par i ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>)) \<^bold>\<cdot> Bnd 0)
      \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> x\<^sup>f\<^bsub>\<sigma>\<^esub>))"
    by (rule wff_AbsI)
       (auto del: wff_PEq wff_LeibE wff_Leib
             intro!: wff_LeibE wff_Leib wff_PEq wff_Eq wff_App wff_Par wff_Fre)
  show "wff\<^bsub>\<o>\<^esub>((\<^bold>\<not> (((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot>
     (\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (((Par i ((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>)) \<^bold>\<cdot> Bnd 0) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> Bnd (Suc 0)))) \<^bold>\<cdot> Bnd
         0))\<^bold>\<langle>x\<^sup>f\<^bsub>\<sigma>\<^esub>\<^bold>\<rangle>)"
    using inner by (auto del: wff_Not intro!: wff_Not wff_App wff_Iota wff_Fre)
qed


theorem nk_injective_cantor: fixes \<sigma> :: ty shows 
  "\<turnstile> (\<^bold>\<not> (\<^bold>\<exists>\<I>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub>. \<^bold>\<Pi>\<F>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>. \<^bold>\<Pi>\<H>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>.
     (((\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>) \<^bold>=\<^bsub>\<sigma>\<^esub> (\<I>\<^sup>f\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> \<^bold>\<cdot> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))
      \<^bold>\<supset> (\<F>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> \<H>\<^sup>f\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>))) :: 'p::infinite tm)"
  (is "\<turnstile> \<^bold>\<not> ?S")
proof -
  \<comment> \<open>The same narrative as for the surjective theorem, with the diagonal
    formed through the description operator: steps (1)-(2) instantiate the
    assumed injectivity; step (3) shows that, by injectivity, the singleton
    predicate \<open>\<^bold>\<Lambda>H. i \<^bold>\<cdot> H \<^bold>\<doteq> a\<close> of the image point \<open>a = i \<^bold>\<cdot> ?G\<close> is the
    Leibniz singleton of the diagonal \<open>?G = \<^bold>\<Lambda>x. \<^bold>\<not> (\<^bold>\<iota>(\<^bold>\<Lambda>H. i \<^bold>\<cdot> H \<^bold>\<doteq> x) \<^bold>\<cdot> x)\<close>,
    so \<open>NK(\<iota>)\<close> describes it to \<open>?G\<close> itself (step (4)) --- description inverts
    \<open>i\<close>; steps (5)-(6) derive the diagonal contradiction \<open>?\<psi> \<^bold>\<doteq> \<^bold>\<not> ?\<psi>\<close>;
    steps (7)-(8) and \<open>NK(\<not>I)\<close> discharge the assumption.\<close>
  obtain i h :: 'p where hi: "h \<noteq> i"
    by (metis (full_types) ex_new_if_finite finite.emptyI
        finite.insertI infinite_UNIV insert_iff)
  let ?\<tau> = "(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>"
  let ?iP = "i\<^sup>p\<^bsub>?\<tau>\<^esub> :: 'p tm" and ?hP = "h\<^sup>p\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> :: 'p tm"
  let ?G = "\<^bold>\<Lambda>\<^bsub>\<sigma>\<^esub> (\<^bold>\<not> (((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> (\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ((?iP \<^bold>\<cdot> Bnd 0) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> Bnd (Suc 0)))) \<^bold>\<cdot> Bnd 0))"
  let ?a = "?iP \<^bold>\<cdot> ?G"
  let ?PX = "\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ((?iP \<^bold>\<cdot> Bnd 0) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> ?a)"
  let ?LG = "(Leib (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> ?G"
  let ?\<psi> = "((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> ?PX) \<^bold>\<cdot> ?a"
  let ?IBb = "\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>
    (((Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>=\<^bsub>\<sigma>\<^esub> (Bnd (Suc (Suc 0)) \<^bold>\<cdot> Bnd
        0))
     \<^bold>\<supset> (Bnd (Suc 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0)))"
  let ?IB = "\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>
    (((?iP \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> Bnd 0))
     \<^bold>\<supset> (Bnd (Suc 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0)))"
  let ?\<Gamma> = "{?S, ?IB}"
  have wG: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(?G)"
    using wff_desc_diag[where \<sigma> = \<sigma> and i = i] by simp
  \<comment> \<open>bookkeeping, once and for all: typing, local closure, freshness\<close>
  have lcG: "lc ?G" by (rule wff_lc[OF wG])
  have wa: "wff\<^bsub>\<sigma>\<^esub>(?a)" by (auto intro!: wff_App wff_Par wG)
  have lca: "lc ?a" by (rule wff_lc[OF wa])
  have wPX: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(?PX)"
    by (rule wff_AbsI)
       (auto del: wff_LeibE simp: opn_lc[OF lca]
             intro!: wff_LeibE wff_App wff_Par wff_Fre wa wG)
  have wLG: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(?LG)"
    by (auto del: wff_Leib intro!: wff_App wff_Leib wG)
  have wIo: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> ?PX)"
    by (auto intro!: wff_App wff_Iota wPX)
  have w\<psi>: "wff\<^bsub>\<o>\<^esub>(?\<psi>)" by (rule wff_App[OF wIo wa])
  have wIBb: "wff\<^bsub>((\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> ?IBb :: 'p tm)"
    by (rule wff_AbsI)
       (auto del: wff_Forall wff_ImpB wff_LeibE wff_Leib wff_PEq
             intro!: wff_Forall wff_ImpB wff_LeibE wff_Leib wff_PEq wff_Eq wff_App wff_Fre)
  have fp\<Gamma>: "freep ?\<Gamma>" by (intro freep_finite) simp
  \<comment> \<open>the derivation\<close>
  have 1: "?\<Gamma> \<turnstile> ?IB"  \<comment> \<open>\<open>NK(Hyp)\<close>\<close>
    by (auto intro: bprov.Hyp)
  have 2: "?\<Gamma> \<turnstile> ((?iP \<^bold>\<cdot> F) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> H)) \<^bold>\<supset> (F \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> H)"
    if wF: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(F)" and wH: "wff\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>(H)"
      and lcF: "lc F" and lcH: "lc H" for F H
    \<comment> \<open>instantiate (1) at closed \<open>F\<close>, \<open>H\<close>: twice \<open>NK(\<Pi>E)\<close>, each followed by \<open>NK(\<beta>)\<close>\<close>
  proof -
    let ?B1 = "\<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (((?iP \<^bold>\<cdot> Bnd (Suc 0)) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> Bnd 0))
        \<^bold>\<supset> (Bnd (Suc 0) \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0))"
    have wB1: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?B1)"
      by (rule wff_AbsI)
         (auto del: wff_ImpB intro!: wff_ImpB wff_Eq wff_App wff_Par wff_Fre)
    have bq1: "(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?B1) \<^bold>\<cdot> F \<approx>\<^bsub>\<o>\<^esub>
          \<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> (((?iP \<^bold>\<cdot> F) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> Bnd 0)) \<^bold>\<supset> (F \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0))"
      using beq.beta[OF wB1 wF] by (simp add: opn_lc[OF lcF])
    have wB2: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>
        (((?iP \<^bold>\<cdot> F) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> Bnd 0)) \<^bold>\<supset> (F \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0)))"
      by (rule wff_AbsI)
         (auto simp: opn_lc[OF lcF] del: wff_ImpB
               intro!: wff_ImpB wff_Eq wff_App wff_Par wff_Fre wF)
    have bq2: "(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub>
        (((?iP \<^bold>\<cdot> F) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> Bnd 0)) \<^bold>\<supset> (F \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> Bnd 0))) \<^bold>\<cdot> H \<approx>\<^bsub>\<o>\<^esub>
        ((?iP \<^bold>\<cdot> F) \<^bold>=\<^bsub>\<sigma>\<^esub> (?iP \<^bold>\<cdot> H)) \<^bold>\<supset> (F \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> H)"
      using beq.beta[OF wB2 wH] by (simp add: opn_lc[OF lcF]
          opn_lc[OF lcH])
    show ?thesis by (rule bprov.Beta[OF bq2 PiE_Forall[OF
        bprov.Beta[OF bq1 PiE_Forall[OF 1 wF]] wH]])
  qed
  have 3: "?\<Gamma> \<turnstile> ?PX \<^bold>\<doteq>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub> ?LG"
    \<comment> \<open>by injectivity, the singleton predicate of \<open>?a\<close> is the Leibniz
      singleton of \<open>?G\<close>: pointwise by \<open>NK(b)\<close>, closed by \<open>NK(\<Pi>I)\<close>
      and \<open>NK(f)\<close>\<close>
  proof -
    let ?body = "(?PX \<^bold>\<cdot> Bnd 0) \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (?LG \<^bold>\<cdot> Bnd 0)"
    have wbody: "wff\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<o>\<^esub>(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?body)"
      by (rule wff_AbsI) (auto simp: opn_lc[OF wff_lc[OF wPX]]
          opn_lc[OF wff_lc[OF wLG]]
          intro!: wff_Eq wff_App wff_Fre
              wPX wLG wG)
    have A_beta: "?PX \<^bold>\<cdot> ?hP \<approx>\<^bsub>\<o>\<^esub> ((?iP \<^bold>\<cdot> ?hP) \<^bold>\<doteq>\<^bsub>\<sigma>\<^esub> ?a)"  \<comment> \<open>\<open>NK(\<beta>)\<close>\<close>
      using beq.beta[OF wPX wff_Par] by (simp add: opn_lc[OF lca])
    have wA: "wff\<^bsub>\<o>\<^esub>(?PX \<^bold>\<cdot> ?hP)" by (auto intro!: wff_App wPX wff_Par)
    have wB: "wff\<^bsub>\<o>\<^esub>(?LG \<^bold>\<cdot> ?hP)"
      by (auto intro!: wff_App wLG wff_Par wG)
    have wih: "wff\<^bsub>\<sigma>\<^esub>(?iP \<^bold>\<cdot> ?hP)" by (auto intro!: wff_App wff_Par)
    have dir1: "?\<Gamma> \<union> {?PX \<^bold>\<cdot> ?hP} \<turnstile> ?LG \<^bold>\<cdot> ?hP"
      \<comment> \<open>if \<open>h\<close> is in the singleton then \<open>i \<^bold>\<cdot> h \<^bold>= i \<^bold>\<cdot> ?G\<close>, so \<open>h \<^bold>= ?G\<close>
        by the injectivity instance (2) and \<open>NK(\<supset>E)\<close>\<close>
    proof -
      let ?\<Delta> = "?\<Gamma> \<union> {?PX \<^bold>\<cdot> ?hP}"
      have fp\<Delta>: "freep ?\<Delta>" by (intro freep_finite) simp
      have d1: "?\<Delta> \<turnstile> ?PX \<^bold>\<cdot> ?hP" by (auto intro: bprov.Hyp)
      have imp: "?\<Delta> \<turnstile> ((?iP \<^bold>\<cdot> ?hP) \<^bold>=\<^bsub>\<sigma>\<^esub> ?a) \<^bold>\<supset> (?hP \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?G)"
        by (rule bprov_weaken[OF 2[OF wff_Par wG wff_lc[OF wff_Par]
            lcG] _ fp\<Delta>]) auto
      have "?\<Delta> \<turnstile> ?hP \<^bold>=\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?G"
        by (rule bprov_ImpE[OF imp leib_to_peq[OF bprov.Beta[OF
            A_beta d1] fp\<Delta> wih wa] fp\<Delta>])
           (auto intro!: wih wa wff_Par wG)
      hence "?\<Delta> \<turnstile> ?hP \<^bold>\<doteq>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?G" by (rule bprov.EqL)
      hence "?\<Delta> \<turnstile> ?G \<^bold>\<doteq>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?hP"
        by (rule leib_sym[OF _ fp\<Delta> wff_Par wG])
      thus ?thesis by simp
    qed
    have dir2: "?\<Gamma> \<union> {?LG \<^bold>\<cdot> ?hP} \<turnstile> ?PX \<^bold>\<cdot> ?hP"
      \<comment> \<open>conversely, Leibniz-equals of \<open>?G\<close> lie in the singleton --- by
        congruence and \<open>NK(\<beta>)\<close>\<close>
    proof -
      let ?\<Delta> = "?\<Gamma> \<union> {?LG \<^bold>\<cdot> ?hP}"
      have fp\<Delta>: "freep ?\<Delta>" by (intro freep_finite) simp
      have d1: "?\<Delta> \<turnstile> ?G \<^bold>\<doteq>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?hP" by (auto intro: bprov.Hyp)
      show ?thesis by (rule bprov.Beta[OF beq.sym[OF A_beta]
          leib_cong2[OF leib_sym[OF d1 fp\<Delta> wG wff_Par] fp\<Delta> wff_Par
              wG wff_Par]])
    qed
    have bqh: "(\<^bold>\<Lambda>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?body) \<^bold>\<cdot> ?hP \<approx>\<^bsub>\<o>\<^esub> (?PX \<^bold>\<cdot> ?hP) \<^bold>\<doteq>\<^bsub>\<o>\<^esub> (?LG \<^bold>\<cdot> ?hP)"
      using beq.beta[OF wbody wff_Par]
      by (simp add: opn_lc[OF wff_lc[OF wPX]] opn_lc[OF wff_lc[OF
          wLG]])
    have allh: "?\<Gamma> \<turnstile> \<^bold>\<Pi>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?body"
      \<comment> \<open>\<open>NK(b)\<close>, then \<open>NK(\<Pi>I)\<close> at the fresh \<open>h\<close>\<close>
      by (rule PiI_Forall[OF bprov.Beta[OF beq.sym[OF bqh]
          bprov.BoolE[OF dir1 dir2 wA wB]] wbody])
        (use hi in \<open>auto simp: Leib_def\<close>)
    show ?thesis  \<comment> \<open>\<open>NK(f)\<close>: functional extensionality\<close>
      by (rule bprov.FuncE[OF allh wPX wLG])
  qed
  have 4: "?\<Gamma> \<turnstile> ((Iota (\<sigma> \<^bold>\<Rightarrow> \<o>)) \<^bold>\<cdot> ?PX) \<^bold>\<doteq>\<^bsub>\<sigma> \<^bold>\<Rightarrow> \<o>\<^esub> ?G"
    \<comment> \<open>\<open>NK(\<iota>)\<close>: description maps the Leibniz singleton --- and by (3)
      the singleton predicate of \<open>?a\<close> --- to \<open>?G\<close> itself\<close>
    by (rule leib_trans[OF leib_cong2[OF 3 fp\<Gamma> wPX wLG wff_Iota]
          bprov.Desc[OF wG] fp\<Gamma>])
      (auto intro!: wff_App wff_Iota wPX wLG wG)
  have 5: "?G \<^bold>\<cdot> ?a \<approx>\<^bsub>\<o>\<^esub> \<^bold>\<not> ?\<psi>"  \<comment> \<open>\<open>\<beta>\<close>-reduce the diagonal at \<open>?a\<close>\<close>
    using beq.beta[OF wG wa] by (simp add: opn_lc[OF lca])
  have 6: "?\<Gamma> \<turnstile> \<^bold>\<bottom>"
    \<comment> \<open>apply (4) at \<open>?a\<close>, \<open>\<beta>\<close>-reduce by (5): \<open>?\<psi> \<^bold>\<doteq> \<^bold>\<not> ?\<psi>\<close>, contradictory
      --- \<open>NK(\<Pi>E)\<close>, \<open>NK(\<not>E)\<close>, tertium non datur\<close>
    by (rule leib_neg_contra[OF bprov.Beta[OF beq.appR[OF 5
          wff_App[OF wff_Leib w\<psi>]]
          leib_cong1[OF 4 fp\<Gamma> wIo wG wa]] fp\<Gamma> w\<psi>])
  have 7: "{?S} \<turnstile> \<^bold>\<exists>\<^bsub>(\<sigma> \<^bold>\<Rightarrow> \<o>) \<^bold>\<Rightarrow> \<sigma>\<^esub> ?IBb"
    \<comment> \<open>\<open>NK(Hyp)\<close>, in locally-nameless normal form\<close>
    by (subst inj_norm[symmetric]) (auto intro: bprov.Hyp)
  have 8: "{?S} \<turnstile> \<^bold>\<bottom>"  \<comment> \<open>\<open>NK(\<exists>E)\<close>, discharging the witness \<open>i\<close>\<close>
  proof (rule ExE[where w = i, OF 7 _ wIBb wff_FalseB], goal_cases)
    case 1 show ?case using 6 by (simp add: insert_commute)
    next case 2 show ?case
      by (simp add: Leib_def ImpB_def Forall_def)
    next case 3 show ?case by (simp add: FalseB_def Forall_def)
    next case 4 show ?case by auto
    next case 5 show ?case by (intro freep_finite) simp
  qed
  show ?thesis  \<comment> \<open>\<open>NK(\<not>I)\<close> discharges the assumed injection\<close>
    by (rule bprov.NegI[OF _ wff_inj]) (use 8 in simp)
qed

end
