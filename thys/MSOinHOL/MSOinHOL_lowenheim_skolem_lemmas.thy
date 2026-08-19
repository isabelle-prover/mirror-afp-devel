theory MSOinHOL_lowenheim_skolem_lemmas
  imports
    MSOinHOL_faithfulness_locale
    MSOinHOL_comprehension
    "HOL-Library.Countable_Set"
begin

text \<open>Supporting lemmas for the downward Loewenheim--Skolem construction
  in \<open>MSOinHOL_lowenheim_skolem\<close>.  This file holds the technical
  machinery (Skolem-witness operators \<open>wF\<close> / \<open>wS\<close>, the omega-stage
  iteration \<open>stage\<close>, monotonicity / countability / common-stage
  lemmas).  The main theorems live in the parent file.\<close>

text \<open>Lemma \<open>coincidence\<close> (generalises \<open>L12\<close> / \<open>N12\<close>): truth depends only on
  the free variables of \<open>\<phi>\<close>.  Compact structured induction; the binder
  cases use IH after extending the agreement through the bound-variable
  update via \<open>EnvMod_def\<close> / \<open>SetMod_def\<close>.\<close>

lemma coincidence:
  assumes "\<And>x. x free_in \<phi> \<Longrightarrow> g x = g' x"
    and "\<And>X. X free2_in \<phi> \<Longrightarrow> G X = G' X"
  shows "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)"
  using assms
proof (induct \<phi> arbitrary: g g' G G')
  case (AtmD r u v) thus ?case by simp
next
  case (PrdD X z) thus ?case by simp
next
  case (NegD \<phi>)
  have "(\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)"
    using NegD.hyps NegD.prems(1,2)
          is_free.simps(3) is_free2.simps(3)
    by presburger
  thus ?case by simp
next
  case (AndD \<phi> \<psi>)
  from AndD.hyps[of g g' G G'] AndD.prems show ?case by simp
next
  case (ExD y \<phi>)
  have "(\<langle>I,D,E\<rangle>,g[y\<leftarrow>d],G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g'[y\<leftarrow>d],G' \<Turnstile>\<^sup>d \<phi>)"
    for d
    using EnvMod_def ExD.hyps ExD.prems(1,2)
          is_free.simps(5) is_free2.simps(5)
    by presburger
  thus ?case by simp
next
  case (ExD2 Y \<phi>)
  have "(\<langle>I,D,E\<rangle>,g,G\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g',G'\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<phi>)" for S
    by (rule ExD2.hyps) (use ExD2.prems in \<open>auto simp: SetMod_def\<close>)
  thus ?case by simp
qed

text \<open>The formula type \<open>\<F>\<close> is countable (datatype over countable atoms).\<close>

instance \<F> :: countable by countable_datatype

text \<open>Pad a finite parameter list to a total assignment (default outside
  its range).\<close>

definition padA :: "D \<Rightarrow> D list \<Rightarrow> (V \<Rightarrow> D)"
  where "padA d0 xs = (\<lambda>i. if i < length xs then xs ! i else d0)"

definition padB :: "(D \<Rightarrow> bool) \<Rightarrow> (D \<Rightarrow> bool) list \<Rightarrow> (V2 \<Rightarrow> (D \<Rightarrow> bool))"
  where "padB S0 Ss = (\<lambda>i. if i < length Ss then Ss ! i else S0)"

text \<open>First-order (FO) and second-order (SO) Skolem witness functions
  \<open>wF\<close> and \<open>wS\<close> for a single existential demand of the form
  \<open>\<exists>y. \<psi>\<close> or \<open>\<exists>\<^sub>2Y. \<psi>\<close>.  A partial assignment is supplied as a list of
  free-variable values padded out by defaults \<open>d\<^sub>0\<close> and \<open>S\<^sub>0\<close>
  (via \<open>padA\<close> / \<open>padB\<close>).  The function then asks whether the existential
  demand is satisfiable in the big model \<open>(I,D,E)\<close>; if so it picks a
  satisfying witness via the \<open>SOME\<close> operator, and otherwise
  falls back to the default.  These witnesses are the per-step building
  blocks of the Tarski--Vaught stage construction below, which feeds
  every existential demand of the formula with a witness whose value
  comes from the big model but whose name lives in the (countable)
  hull.\<close>

definition wF ::
  "\<I> \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> ((D \<Rightarrow> bool) \<Rightarrow> bool)
    \<Rightarrow> D \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> \<F> \<Rightarrow> V \<Rightarrow> D list
    \<Rightarrow> (D \<Rightarrow> bool) list \<Rightarrow> D"
  where
    "wF I D E d0 S0 \<psi> y xs Ss =
       (if (\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,(padA d0 xs)[y\<leftarrow>d],(padB S0 Ss) \<Turnstile>\<^sup>d \<psi>)
        then (SOME d. D d \<and>
                \<langle>I,D,E\<rangle>,(padA d0 xs)[y\<leftarrow>d],(padB S0 Ss) \<Turnstile>\<^sup>d \<psi>)
        else d0)"

definition wS ::
  "\<I> \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> ((D \<Rightarrow> bool) \<Rightarrow> bool)
    \<Rightarrow> D \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> \<F> \<Rightarrow> V2 \<Rightarrow> D list
    \<Rightarrow> (D \<Rightarrow> bool) list \<Rightarrow> (D \<Rightarrow> bool)"
  where
    "wS I D E d0 S0 \<psi> Y xs Ss =
       (if (\<exists>S. E S \<and>
              \<langle>I,D,E\<rangle>,(padA d0 xs),(padB S0 Ss)\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)
        then (SOME S. E S \<and>
                \<langle>I,D,E\<rangle>,(padA d0 xs),(padB S0 Ss)\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)
        else S0)"

lemma wF_mem: "D d0 \<Longrightarrow> D (wF I D E d0 S0 \<psi> y xs Ss)"
  unfolding wF_def
  by (cases "\<exists>d. D d \<and>
               \<langle>I,D,E\<rangle>,(padA d0 xs)[y\<leftarrow>d],(padB S0 Ss) \<Turnstile>\<^sup>d \<psi>";
      simp, metis (mono_tags, lifting) someI_ex)

lemma wS_mem: "E S0 \<Longrightarrow> E (wS I D E d0 S0 \<psi> Y xs Ss)"
  unfolding wS_def
  by (cases "\<exists>S. E S \<and>
               \<langle>I,D,E\<rangle>,(padA d0 xs),(padB S0 Ss)\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>";
      simp, metis (mono_tags, lifting) someI_ex)

text \<open>Witness-membership specialised to seeds @{text "g 0"} /
  @{text "G 0"}: no extra \<open>D (g 0)\<close> premise.\<close>

lemma wF_mem_seed:
  "g into D \<Longrightarrow> D (wF I D E (g 0) S\<^sub>0 \<psi> y xs Ss)"
  by (blast intro: wF_mem)

lemma wS_mem_seed:
  "G into E \<Longrightarrow> E (wS I D E d\<^sub>0 (G 0) \<psi> Y xs Ss)"
  by (blast intro: wS_mem)

text \<open>The omega-stage (FO carrier, SO carrier): step \<open>n+1\<close> adds every
  \<open>wF\<close> / \<open>wS\<close> witness over parameter lists drawn from the carriers at
  stage \<open>n\<close>.\<close>

primrec stage ::
    "\<I> \<Rightarrow> (D \<Rightarrow> bool) \<Rightarrow> ((D \<Rightarrow> bool) \<Rightarrow> bool)
      \<Rightarrow> (V \<Rightarrow> D) \<Rightarrow> (V2 \<Rightarrow> (D \<Rightarrow> bool)) \<Rightarrow> nat
      \<Rightarrow> ((D \<Rightarrow> bool) \<times> ((D \<Rightarrow> bool) \<Rightarrow> bool))"
  where
    "stage I D E g G 0 = (Range g, Range G)"
  | "stage I D E g G (Suc n) =
       ((\<lambda>d. fst (stage I D E g G n) d
              \<or> (\<exists>\<psi> y xs Ss.
                   (\<forall>x\<in>set xs. fst (stage I D E g G n) x)
                 \<and> (\<forall>S\<in>set Ss. snd (stage I D E g G n) S)
                 \<and> d = wF I D E (g 0) (G 0) \<psi> y xs Ss)),
        (\<lambda>S. snd (stage I D E g G n) S
              \<or> (\<exists>\<psi> Y xs Ss.
                   (\<forall>x\<in>set xs. fst (stage I D E g G n) x)
                 \<and> (\<forall>S'\<in>set Ss. snd (stage I D E g G n) S')
                 \<and> S = wS I D E (g 0) (G 0) \<psi> Y xs Ss)))"

text \<open>Helper: countability of a binary product (from
  \<open>countable_SIGMA\<close>).\<close>

lemma countable_Times2:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> countable (A \<times> B)"
  using countable_SIGMA[of A "\<lambda>_. B"] by (simp add: Sigma_def)

text \<open>An explicit Skolem witness produced from parameters drawn from
  stage \<open>n\<close> sits in stage \<open>Suc n\<close> (FO / SO).  Direct from the second
  clause of \<open>stage\<close>.\<close>

lemma fst_stage_Suc_intro:
  "\<forall>x\<in>set xs. fst (stage I D E g G N) x \<Longrightarrow>
   \<forall>S\<in>set Ss. snd (stage I D E g G N) S \<Longrightarrow>
   fst (stage I D E g G (Suc N)) (wF I D E (g 0) (G 0) \<psi> y xs Ss)"
  by (simp, blast)

lemma snd_stage_Suc_intro:
  "\<forall>x\<in>set xs. fst (stage I D E g G N) x \<Longrightarrow>
   \<forall>S\<in>set Ss. snd (stage I D E g G N) S \<Longrightarrow>
   snd (stage I D E g G (Suc N)) (wS I D E (g 0) (G 0) \<psi> Y xs Ss)"
  by (simp, blast)

text \<open>The next two lemmas are instances of the coincidence lemma in
  which the assignments \<open>a\<close>, \<open>b\<close> are first restricted to the
  free-variable prefix of \<open>\<psi>\<close> (the indices \<open>[0..<fresh \<psi>]\<close> and
  \<open>[0..<fresh2 \<psi>]\<close>) and then re-extended to total assignments via
  \<open>padA\<close> / \<open>padB\<close> with defaults \<open>d\<^sub>0\<close>, \<open>S\<^sub>0\<close>.  Because \<open>\<psi>\<close> can only
  look at the variables it actually uses, the value of \<open>\<psi>\<close> under the
  padded assignment coincides with its value under the original one.
  This is precisely the rewrite needed for the Tarski--Vaught step:
  the truth of an existential demand on the partial (padded) assignment
  is the truth of the same demand on the original assignment, so a
  witness chosen for the padded form automatically refutes / verifies
  the original form, and the truth transfer through one stage of the
  hull construction goes through by @{method simp} alone.\<close>

lemma pad_truth_eq_FO:
  "(\<langle>I,D,E\<rangle>, (padA d\<^sub>0 (map a [0..<fresh \<psi>]))[y\<leftarrow>d], (padB S\<^sub>0 (map b [0..<fresh2 \<psi>])) \<Turnstile>\<^sup>d \<psi>) = (\<langle>I,D,E\<rangle>, a[y\<leftarrow>d], b \<Turnstile>\<^sup>d \<psi>)"
  by (rule coincidence)
     (auto dest!: L6 N6 simp: EnvMod_def padA_def padB_def)

lemma pad_truth_eq_SO:
  "(\<langle>I,D,E\<rangle>, padA d\<^sub>0 (map a [0..<fresh \<psi>]), (padB S\<^sub>0 (map b [0..<fresh2 \<psi>]))\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>) = (\<langle>I,D,E\<rangle>, a, b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)"
  by (rule coincidence)
     (auto dest!: L6 N6 simp: SetMod_def padA_def padB_def)

text \<open>The Skolem witness \<open>wF\<close> / \<open>wS\<close> realizes its demand whenever one
  exists in \<open>(D,E)\<close>: membership in \<open>D\<close> / \<open>E\<close> plus the truth on the
  padded assignment.  Direct from \<open>someI_ex\<close>.\<close>

lemma wF_realizes:
  assumes "\<exists>d. D d \<and>
            \<langle>I,D,E\<rangle>,(padA d0 xs)[y\<leftarrow>d],(padB S0 Ss) \<Turnstile>\<^sup>d \<psi>"
  shows "D (wF I D E d0 S0 \<psi> y xs Ss)
           \<and> (\<langle>I,D,E\<rangle>,(padA d0 xs)[y\<leftarrow>wF I D E d0 S0 \<psi> y xs Ss],
                     (padB S0 Ss) \<Turnstile>\<^sup>d \<psi>)"
  using someI_ex[OF assms] assms unfolding wF_def by simp

lemma wS_realizes:
  assumes "\<exists>S. E S \<and>
            \<langle>I,D,E\<rangle>,(padA d0 xs),(padB S0 Ss)\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>"
  shows "E (wS I D E d0 S0 \<psi> Y xs Ss)
           \<and> (\<langle>I,D,E\<rangle>,(padA d0 xs),
                     (padB S0 Ss)\<langle>Y\<leftarrow>wS I D E d0 S0 \<psi> Y xs Ss\<rangle>
                       \<Turnstile>\<^sup>d \<psi>)"
  using someI_ex[OF assms] assms unfolding wS_def by simp

text \<open>Full Tarski--Vaught step (FO / SO): from an existential over
  \<open>(D,E)\<close> reachable through \<open>a\<close>, \<open>b\<close>, the \<open>wF\<close> / \<open>wS\<close> witness lives
  in \<open>D\<close> / \<open>E\<close> and satisfies the formula relative to \<open>a\<close>, \<open>b\<close>.  Core
  lemma for the \<open>TVfo\<close> / \<open>TVso\<close> of \<open>skolem_hull\<close>.\<close>

lemma skolem_step_FO:
  assumes "\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>"
  shows "D (wF I D E d\<^sub>0 S\<^sub>0 \<psi> y
              (map a [0..<fresh \<psi>]) (map b [0..<fresh2 \<psi>]))
         \<and> (\<langle>I,D,E\<rangle>, a[y\<leftarrow>wF I D E d\<^sub>0 S\<^sub>0 \<psi> y
                          (map a [0..<fresh \<psi>])
                          (map b [0..<fresh2 \<psi>])],
                     b \<Turnstile>\<^sup>d \<psi>)"
proof -
  let ?xs = "map a [0..<fresh \<psi>]"
  and ?Ss = "map b [0..<fresh2 \<psi>]"
  have "\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,(padA d\<^sub>0 ?xs)[y\<leftarrow>d],(padB S\<^sub>0 ?Ss) \<Turnstile>\<^sup>d \<psi>"
    using assms by (simp add: pad_truth_eq_FO)
  from wF_realizes[OF this] show ?thesis
    by (simp add: pad_truth_eq_FO)
qed

lemma skolem_step_SO:
  assumes "\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>"
  shows "E (wS I D E d\<^sub>0 S\<^sub>0 \<psi> Y
              (map a [0..<fresh \<psi>]) (map b [0..<fresh2 \<psi>]))
         \<and> (\<langle>I,D,E\<rangle>, a,
              b\<langle>Y\<leftarrow>wS I D E d\<^sub>0 S\<^sub>0 \<psi> Y
                   (map a [0..<fresh \<psi>])
                   (map b [0..<fresh2 \<psi>])\<rangle>
                \<Turnstile>\<^sup>d \<psi>)"
proof -
  let ?xs = "map a [0..<fresh \<psi>]"
  and ?Ss = "map b [0..<fresh2 \<psi>]"
  have "\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,(padA d\<^sub>0 ?xs),(padB S\<^sub>0 ?Ss)\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>"
    using assms by (simp add: pad_truth_eq_SO)
  from wS_realizes[OF this] show ?thesis
    by (simp add: pad_truth_eq_SO)
qed

text \<open>The \<open>(Suc n)\<close>-stage is contained in the \<open>n\<close>-stage plus the image
  of \<open>wF\<close> / \<open>wS\<close> over the four-fold product \<open>\<F> \<times> V \<times> Lists\<^sub>\<D>(n) \<times>
  Lists\<^sub>\<P>(n)\<close>, where the first two factors range over all formulas and
  all binder variables, and the last two over lists of FO domain elements
  resp.\ SO predicates that already live in the \<open>n\<close>-th stage.  Used to
  derive countability of each stage by induction.\<close>

lemma fst_stage_Suc_subset:
  "{d. fst (stage I D E g G (Suc n)) d}
     \<subseteq> {d. fst (stage I D E g G n) d}
       \<union> (\<lambda>(\<psi>, y, xs, Ss). wF I D E (g 0) (G 0) \<psi> y xs Ss) `
         (UNIV \<times> UNIV
            \<times> {xs. set xs \<subseteq> {d. fst (stage I D E g G n) d}}
            \<times> {Ss. set Ss \<subseteq> {S. snd (stage I D E g G n) S}})"
  (is "_ \<subseteq> ?R")
proof (rule subsetI, simp only: mem_Collect_eq)
  fix d assume "fst (stage I D E g G (Suc n)) d"
  then consider
      "fst (stage I D E g G n) d"
    | \<psi> y xs Ss
        where "\<forall>x\<in>set xs. fst (stage I D E g G n) x"
              "\<forall>S\<in>set Ss. snd (stage I D E g G n) S"
              "d = wF I D E (g 0) (G 0) \<psi> y xs Ss"
    by auto
  thus "d \<in> ?R"
    by cases (auto intro!: rev_image_eqI[where x="(_, _, _, _)"])
qed

lemma snd_stage_Suc_subset:
  "{S. snd (stage I D E g G (Suc n)) S}
     \<subseteq> {S. snd (stage I D E g G n) S}
       \<union> (\<lambda>(\<psi>, Y, xs, Ss). wS I D E (g 0) (G 0) \<psi> Y xs Ss) `
         (UNIV \<times> UNIV
            \<times> {xs. set xs \<subseteq> {d. fst (stage I D E g G n) d}}
            \<times> {Ss. set Ss \<subseteq> {S. snd (stage I D E g G n) S}})"
  (is "_ \<subseteq> ?R")
proof (rule subsetI, simp only: mem_Collect_eq)
  fix S assume "snd (stage I D E g G (Suc n)) S"
  then consider
      "snd (stage I D E g G n) S"
    | \<psi> Y xs Ss
        where "\<forall>x\<in>set xs. fst (stage I D E g G n) x"
              "\<forall>S'\<in>set Ss. snd (stage I D E g G n) S'"
              "S = wS I D E (g 0) (G 0) \<psi> Y xs Ss"
    by auto
  thus "S \<in> ?R"
    by cases (auto intro!: rev_image_eqI[where x="(_, _, _, _)"])
qed

text \<open>Monotonicity of the \<open>stage\<close> chain: a single-step extension lifts
  to arbitrary suffixes.\<close>

lemma fst_stage_mono:
  "m \<le> n \<Longrightarrow> fst (stage I D E g G m) d \<Longrightarrow> fst (stage I D E g G n) d"
  by (induct n) (auto simp del: stage.simps simp: stage.simps(2) le_Suc_eq)

lemma snd_stage_mono:
  "m \<le> n \<Longrightarrow> snd (stage I D E g G m) S \<Longrightarrow> snd (stage I D E g G n) S"
  by (induct n) (auto simp del: stage.simps simp: stage.simps(2) le_Suc_eq)

text \<open>Finitely many parameters in the omega-union all share a common
  stage.\<close>

lemma common_stage_lifted:
  assumes hx: "\<forall>x\<in>set xs. \<exists>n. fst (stage I D E g G n) x"
    and hS: "\<forall>S\<in>set Ss. \<exists>n. snd (stage I D E g G n) S"
  shows "\<exists>N. (\<forall>x\<in>set xs. fst (stage I D E g G N) x)
               \<and> (\<forall>S\<in>set Ss. snd (stage I D E g G N) S)"
proof -
  obtain fX where fX: "\<forall>x\<in>set xs. fst (stage I D E g G (fX x)) x"
    using hx by metis
  obtain fS where fS: "\<forall>S\<in>set Ss. snd (stage I D E g G (fS S)) S"
    using hS by metis
  let ?N = "Max (insert 0 (fX ` set xs \<union> fS ` set Ss))"
  have bX: "fX x \<le> ?N" if "x \<in> set xs" for x
    using that by (simp add: Max_ge)
  have bS: "fS S \<le> ?N" if "S \<in> set Ss" for S
    using that by (simp add: Max_ge)
  from bX fX fst_stage_mono
    have "\<forall>x\<in>set xs. fst (stage I D E g G ?N) x" by blast
  moreover from bS fS snd_stage_mono
    have "\<forall>S\<in>set Ss. snd (stage I D E g G ?N) S" by blast
  ultimately show ?thesis by blast
qed

text \<open>A \<open>wF\<close> / \<open>wS\<close> witness built from hull-valued parameters is itself
  in the hull.  Combines \<open>common_stage_lifted\<close> with the single-Suc-step
  intros.\<close>

lemma wF_in_omega_union:
  assumes "\<forall>x\<in>set xs. \<exists>n. fst (stage I D E g G n) x"
    and "\<forall>S\<in>set Ss. \<exists>n. snd (stage I D E g G n) S"
  shows "\<exists>n. fst (stage I D E g G n)
                  (wF I D E (g 0) (G 0) \<psi> y xs Ss)"
  using common_stage_lifted[OF assms]
  by (meson fst_stage_Suc_intro)

lemma wS_in_omega_union:
  assumes "\<forall>x\<in>set xs. \<exists>n. fst (stage I D E g G n) x"
    and "\<forall>S\<in>set Ss. \<exists>n. snd (stage I D E g G n) S"
  shows "\<exists>n. snd (stage I D E g G n)
                  (wS I D E (g 0) (G 0) \<psi> Y xs Ss)"
  using common_stage_lifted[OF assms]
  by (meson snd_stage_Suc_intro)

text \<open>Tarski--Vaught closure of the omega-union: combines
  \<open>skolem_step_FO\<close> / \<open>skolem_step_SO\<close> with
  \<open>wF_in_omega_union\<close> / \<open>wS_in_omega_union\<close>.\<close>

lemma stage_TV_FO:
  assumes "a into (\<lambda>d. \<exists>n. fst (stage I D E g G n) d)"
    and "b into (\<lambda>S. \<exists>n. snd (stage I D E g G n) S)"
    and "\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>"
  shows "\<exists>d. (\<exists>n. fst (stage I D E g G n) d)
              \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>"
  using skolem_step_FO[OF assms(3), of "g 0" "G 0"]
        wF_in_omega_union[of "map a [0..<fresh \<psi>]" I D E g G
                              "map b [0..<fresh2 \<psi>]" \<psi> y]
        assms(1,2)
  by auto

lemma stage_TV_SO:
  assumes "a into (\<lambda>d. \<exists>n. fst (stage I D E g G n) d)"
    and "b into (\<lambda>S. \<exists>n. snd (stage I D E g G n) S)"
    and "\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>"
  shows "\<exists>S. (\<exists>n. snd (stage I D E g G n) S)
              \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>"
  using skolem_step_SO[OF assms(3), of "g 0" "G 0"]
        wS_in_omega_union[of "map a [0..<fresh \<psi>]" I D E g G
                              "map b [0..<fresh2 \<psi>]" \<psi> Y]
        assms(1,2)
  by auto

text \<open>Inductive step for stage countability: each \<open>Suc\<close>-stage is
  countable provided both \<open>n\<close>-stages are.\<close>

lemma cntDE_step:
  assumes cD: "countable {d. fst (stage I D E g G n) d}"
    and cE: "countable {S. snd (stage I D E g G n) S}"
  shows "countable {d. fst (stage I D E g G (Suc n)) d}"
    and "countable {S. snd (stage I D E g G (Suc n)) S}"
proof -
  let ?A = "{xs. set xs \<subseteq> {d. fst (stage I D E g G n) d}}"
  let ?B = "{Ss. set Ss \<subseteq> {S. snd (stage I D E g G n) S}}"
  have lDE: "countable ?A" "countable ?B"
    apply (metis cD countable_lists lists_eq_set)
    by (metis cE countable_lists lists_eq_set)
  hence cT:
      "countable ((UNIV::\<F> set) \<times> (UNIV::V set) \<times> ?A \<times> ?B)"
      "countable ((UNIV::\<F> set) \<times> (UNIV::V2 set) \<times> ?A \<times> ?B)"
    by (auto intro!: countable_Times2)
  hence prods:
      "countable ((\<lambda>(\<psi>,y,xs,Ss). wF I D E (g 0) (G 0) \<psi> y xs Ss) `
         ((UNIV::\<F> set) \<times> (UNIV::V set) \<times> ?A \<times> ?B))"
      "countable ((\<lambda>(\<psi>,Y,xs,Ss). wS I D E (g 0) (G 0) \<psi> Y xs Ss) `
         ((UNIV::\<F> set) \<times> (UNIV::V2 set) \<times> ?A \<times> ?B))"
    by (auto intro: countable_image)
  from prods(1) cD fst_stage_Suc_subset[of I D E g G n]
    show "countable {d. fst (stage I D E g G (Suc n)) d}"
    by (meson countable_Un countable_subset)
  from prods(2) cE snd_stage_Suc_subset[of I D E g G n]
    show "countable {S. snd (stage I D E g G (Suc n)) S}"
    by (meson countable_Un countable_subset)
qed

text \<open>Stage carriers stay inside \<open>D\<close> / \<open>E\<close> (by induction on the stage;
  \<open>wF_mem_seed\<close> / \<open>wS_mem_seed\<close> handle the witness case).\<close>

lemma fst_stage_subD:
  "g into D \<Longrightarrow> fst (stage I D E g G n) d \<Longrightarrow> D d"
  by (induct n arbitrary: d) (auto simp: wF_mem_seed)

lemma snd_stage_subE:
  "G into E \<Longrightarrow> snd (stage I D E g G n) S \<Longrightarrow> E S"
  by (induct n arbitrary: S) (auto simp: wS_mem_seed)

text \<open>Every stage is countable; hence so is the omega-union of stages.
  Pure consequence of \<open>cntDE_step\<close>.\<close>

lemma stage_countable:
  "countable {d. fst (stage I D E g G n) d}
     \<and> countable {S. snd (stage I D E g G n) S}"
proof (induct n)
  case 0
  have "{d. fst (stage I D E g G 0) d} = range g"
       "{S. snd (stage I D E g G 0) S} = range G"
    by auto
  thus ?case by simp
next
  case (Suc n) thus ?case
    using cntDE_step[of I D E g G n] by simp
qed

lemma stage_omega_countable:
  "countable {d. \<exists>n. fst (stage I D E g G n) d}"
  "countable {S. \<exists>n. snd (stage I D E g G n) S}"
proof -
  have eqs:
      "{d. \<exists>n. fst (stage I D E g G n) d}
         = (\<Union>n. {d. fst (stage I D E g G n) d})"
      "{S. \<exists>n. snd (stage I D E g G n) S}
         = (\<Union>n. {S. snd (stage I D E g G n) S})"
    by auto
  show "countable {d. \<exists>n. fst (stage I D E g G n) d}"
       "countable {S. \<exists>n. snd (stage I D E g G n) S}"
    unfolding eqs using stage_countable by (auto intro: countable_UN)
qed

text \<open>Reindex one sort onto a countable nonempty sub-domain, keeping the
  values on a finite ``guarded'' prefix specified by a predicate
  \<open>free\<close> bounded by \<open>fr\<close>.\<close>

lemma reindex_one:
  fixes free :: "nat \<Rightarrow> bool" and fr :: nat
    and D\<^sub>0 :: "'a \<Rightarrow> bool" and g :: "nat \<Rightarrow> 'a"
  assumes "countable {x. D\<^sub>0 x}" and "D\<^sub>0 d\<^sub>0"
    and "Range g \<^bold>\<subseteq> D\<^sub>0"
    and bound: "\<And>x. free x \<Longrightarrow> x < fr"
  obtains g' where "Range g' = D\<^sub>0"
    and "\<And>x. free x \<Longrightarrow> g' x = g x"
proof -
  let ?D = "{x. D\<^sub>0 x}"
  have hD: "?D \<noteq> {}"
    and re: "range (from_nat_into ?D) = ?D"
    and mem: "D\<^sub>0 (from_nat_into ?D k)" for k
    using assms(2) range_from_nat_into[OF _ assms(1)]
          from_nat_into
    by auto
  define g' where
    "g' n = (if free n then g n else from_nat_into ?D (n - fr))"
    for n
  have "Range g' = D\<^sub>0"
  proof (rule ext, rule iffI)
    fix d assume "Range g' d"
    thus "D\<^sub>0 d"
      using assms(3) mem
      by (auto simp: g'_def split: if_split_asm)
  next
    fix d assume "D\<^sub>0 d"
    hence "d \<in> range (from_nat_into ?D)" using re by simp
    then obtain k where "from_nat_into ?D k = d" by auto
    moreover have "\<not> free (fr + k)" using bound by force
    ultimately have "g' (fr + k) = d" by (simp add: g'_def)
    thus "Range g' d" by auto
  qed
  moreover have "\<And>x. free x \<Longrightarrow> g' x = g x"
    by (simp add: g'_def)
  ultimately show ?thesis using that by blast
qed

text \<open>Reindex (both sorts): reindex the (countably many) variables to
  surject onto the countable @{text "D0, E0"}, while agreeing with the
  originals on the finitely many free variables of \<open>\<phi>\<close>.  Two
  applications of \<open>reindex_one\<close>.\<close>

lemma reindex:
  assumes "countable {d. D\<^sub>0 d}" and "D\<^sub>0 d\<^sub>0"
    and "countable {S. E\<^sub>0 S}" and "E\<^sub>0 S\<^sub>0"
    and "Range g \<^bold>\<subseteq> D\<^sub>0" and "Range G \<^bold>\<subseteq> E\<^sub>0"
  obtains g' G'
    where "Range g' = D\<^sub>0" and "Range G' = E\<^sub>0"
      and "\<And>x. x free_in \<phi> \<Longrightarrow> g' x = g x"
      and "\<And>X. X free2_in \<phi> \<Longrightarrow> G' X = G X"
proof -
  obtain g' where g':
      "Range g' = D\<^sub>0"
      "\<And>x. x free_in \<phi> \<Longrightarrow> g' x = g x"
    using reindex_one[OF assms(1,2,5),
            of "\<lambda>x. x free_in \<phi>" "fresh \<phi>"]
          L6
    by blast
  obtain G' where G':
      "Range G' = E\<^sub>0"
      "\<And>X. X free2_in \<phi> \<Longrightarrow> G' X = G X"
    using reindex_one[OF assms(3,4,6),
            of "\<lambda>X. X free2_in \<phi>" "fresh2 \<phi>"]
          N6
    by blast
  show ?thesis using that g' G' by blast
qed

text \<open>Reindex + coincidence in one step: obtain @{text "g'/G'"}
  surjecting onto the countable @{text "D0/E0"} whose induced truth on
  \<open>\<phi>\<close> coincides with the original.\<close>

lemma reindex_coincide:
  assumes "countable {d. D\<^sub>0 d}" and "countable {S. E\<^sub>0 S}"
    and "Range g \<^bold>\<subseteq> D\<^sub>0" and "Range G \<^bold>\<subseteq> E\<^sub>0"
  obtains g' G'
    where "Range g' = D\<^sub>0" and "Range G' = E\<^sub>0"
      and "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)
             = (\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)"
proof -
  have nD: "D\<^sub>0 (g 0)" and nE: "E\<^sub>0 (G 0)"
    using assms(3,4) by auto
  obtain g' G' where rg: "Range g' = D\<^sub>0" and rG: "Range G' = E\<^sub>0"
    and ag: "\<And>x. x free_in \<phi> \<Longrightarrow> g' x = g x"
    and aG: "\<And>X. X free2_in \<phi> \<Longrightarrow> G' X = G X"
    using reindex[OF assms(1) nD assms(2) nE assms(3,4)] by blast
  have "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)"
    by (rule coincidence) (simp_all add: ag aG)
  thus thesis using that rg rG by blast
qed

end
