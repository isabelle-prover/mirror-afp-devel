theory MSOinHOL_lowenheim_skolem
  imports MSOinHOL_lowenheim_skolem_lemmas
begin

text \<open>Two-sorted elementary substructure (Tarski--Vaught form).\<close>

definition ElementarySubstructure
    ("\<langle>_,_,_\<rangle> \<subseteq>\<^sub>E \<langle>_,_,_\<rangle>")
  where
    "\<langle>I',D',E'\<rangle> \<subseteq>\<^sub>E \<langle>I,D,E\<rangle> \<equiv>
       D' \<^bold>\<subseteq> D \<and> E' \<^bold>\<subseteq> E
       \<and> (\<forall>g G \<phi>. G into E' \<longrightarrow> g into D'
            \<longrightarrow> ((\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I',D',E'\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)))"

text \<open>Minimal interpretation whose range model is elementary in a larger
  model.\<close>

locale MinS_ES = MinS +
  fixes DD :: \<D> and EE :: \<P>
  assumes ES: "\<langle>II,Range gg, Range GG\<rangle> \<subseteq>\<^sub>E \<langle>II,DD,EE\<rangle>"
begin

lemma \<N>_valid_ES:
  "\<langle>II,DD,EE\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi> = \<langle>II,Range gg, Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>"
  using ES ElementarySubstructure_def by (smt (verit))

end

text \<open>Specialisation to the standard model
  @{text "\<langle>II,Univ,Univ\<rangle>"}.\<close>

locale MinS_ES_Univ = MinS_ES II gg GG Univ Univ for II gg GG
begin

lemma \<N>_valid_ES_Univ:
  "\<langle>II,Univ,Univ\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi> = \<langle>II,Range gg,Range GG\<rangle>,gg,GG \<Turnstile>\<^sup>d \<phi>"
  using \<N>_valid_ES .

end

text \<open>Range-relative validity: the right-hand side of
  \<open>FaithfulMS_all\<close>.\<close>

definition RangeValid ("\<Turnstile>\<^sup>r _" 9)
  where "\<Turnstile>\<^sup>r \<phi> \<equiv> \<forall>I g G. \<langle>I, Range g, Range G\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>"

lemma into_Range: "f into Range f"
  by auto

text \<open>Easy direction.\<close>

lemma ValD_imp_RangeValid: "\<Turnstile>\<^sup>d \<phi> \<Longrightarrow> \<Turnstile>\<^sup>r \<phi>"
  unfolding RangeValid_def ValD_def using into_Range by smt

text \<open>Truth preservation across a Tarski--Vaught-closed sub-pair
  @{text "(D0,E0)"}.\<close>

lemma truth_pres:
  assumes subD: "D\<^sub>0 \<^bold>\<subseteq> D" and subE: "E\<^sub>0 \<^bold>\<subseteq> E"
    and TVfo:
      "\<And>y \<psi> a b.
         a into D\<^sub>0 \<Longrightarrow> b into E\<^sub>0 \<Longrightarrow>
         (\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
         (\<exists>d. D\<^sub>0 d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>)"
    and TVso:
      "\<And>Y \<psi> a b.
         a into D\<^sub>0 \<Longrightarrow> b into E\<^sub>0 \<Longrightarrow>
         (\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
         (\<exists>S. E\<^sub>0 S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)"
    and aD: "a into D\<^sub>0" and bE: "b into E\<^sub>0"
  shows "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,a,b \<Turnstile>\<^sup>d \<psi>) = (\<langle>I,D,E\<rangle>,a,b \<Turnstile>\<^sup>d \<psi>)"
  using aD bE
proof (induct \<psi> arbitrary: a b)
  case (ExD y \<psi>)
  thus ?case
    using ExD.hyps[of "a[y\<leftarrow>_]" b] TVfo[of a b y \<psi>] subD
    by (force simp: EnvMod_def)
next
  case (ExD2 Y \<psi>)
  thus ?case
    using ExD2.hyps[of a "b\<langle>Y\<leftarrow>_\<rangle>"] TVso[of a b Y \<psi>] subE
    by (force simp: SetMod_def)
qed simp_all

text \<open>Countable seed-form Tarski--Vaught hull: extends any countable
  nonempty @{text "(D0,E0) \<subseteq> (D,E)"} to a countable TV-closed pair
  @{text "(N,M)"} between them.\<close>

lemma skolem_hull:
  assumes "D\<^sub>0 \<^bold>\<subseteq> D" and "E\<^sub>0 \<^bold>\<subseteq> E"
    and "\<exists>x. D\<^sub>0 x" and "\<exists>S. E\<^sub>0 S"
    and "countable {d. D\<^sub>0 d}" and "countable {d. E\<^sub>0 d}"
  obtains N M
    where "N \<^bold>\<subseteq> D" and "M \<^bold>\<subseteq> E"
      and "D\<^sub>0 \<^bold>\<subseteq> N" and "E\<^sub>0 \<^bold>\<subseteq> M"
      and "countable {d. N d}" and "countable {S. M S}"
      and "\<And>y \<psi> a b.
             a into N \<Longrightarrow> b into M \<Longrightarrow>
             (\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
             (\<exists>d. N d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>)"
      and "\<And>Y \<psi> a b.
             a into N \<Longrightarrow> b into M \<Longrightarrow>
             (\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
             (\<exists>S. M S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)"
proof -
  obtain g :: "\<E>" where g: "Range g = D\<^sub>0"
    by (metis (mono_tags, lifting) Collect_inj
        assms(3,5) empty_Collect_eq full_SetCompr_eq
        range_from_nat_into)
  obtain G :: "\<G>" where G: "Range G = E\<^sub>0"
    by (metis (mono_tags, lifting) Collect_inj
        assms(4,6) empty_Collect_eq full_SetCompr_eq
        range_from_nat_into)
  define Dh where Dh: "Dh = (\<lambda>d. \<exists>n. fst (stage I D E g G n) d)"
  define Eh where Eh: "Eh = (\<lambda>S. \<exists>n. snd (stage I D E g G n) S)"
  have base:
      "Range g d \<Longrightarrow> fst (stage I D E g G 0) d"
      "Range G S \<Longrightarrow> snd (stage I D E g G 0) S"
    for d S
    by simp_all
  have RgDh: "Range g \<^bold>\<subseteq> Dh"
    and RGEh: "Range G \<^bold>\<subseteq> Eh"
    using base unfolding Dh Eh by blast+
  have DhsubD: "Dh \<^bold>\<subseteq> D"
    using fst_stage_subD assms(1)
    unfolding Dh by (metis (full_types) g)
  have EhsubE: "Eh \<^bold>\<subseteq> E"
    using snd_stage_subE assms(2)
    unfolding Eh by (metis (mono_tags, lifting) G)
  have cDh: "countable {d. Dh d}"
    and cEh: "countable {S. Eh S}"
    unfolding Dh Eh by (rule stage_omega_countable)+
  have TVfo:
      "a into Dh \<Longrightarrow> b into Eh \<Longrightarrow>
       (\<exists>d. D d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
       (\<exists>d. Dh d \<and> \<langle>I,D,E\<rangle>,a[y\<leftarrow>d],b \<Turnstile>\<^sup>d \<psi>)"
    for y \<psi> a b
    unfolding Dh Eh by (rule stage_TV_FO)
  have TVso:
      "a into Dh \<Longrightarrow> b into Eh \<Longrightarrow>
       (\<exists>S. E S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>) \<Longrightarrow>
       (\<exists>S. Eh S \<and> \<langle>I,D,E\<rangle>,a,b\<langle>Y\<leftarrow>S\<rangle> \<Turnstile>\<^sup>d \<psi>)"
    for Y \<psi> a b
    unfolding Dh Eh by (rule stage_TV_SO)
  show ?thesis
    using DhsubD EhsubE G RGEh RgDh TVfo TVso cDh cEh g that
    by force
qed

text \<open>Downward L\"owenheim--Skolem: TV-closure is upgraded to genuine
  elementarity via @{text truth_pres}.\<close>

theorem DownwardLowenheimSkolem:
  assumes "D\<^sub>0 \<^bold>\<subseteq> D" and "E\<^sub>0 \<^bold>\<subseteq> E"
    and "\<exists>x. D\<^sub>0 x" and "\<exists>x. E\<^sub>0 x"
    and "countable {d. D\<^sub>0 d}" and "countable {S. E\<^sub>0 S}"
  shows "\<exists>N M.
           D\<^sub>0 \<^bold>\<subseteq> N \<and> countable {d. N d}
           \<and> E\<^sub>0 \<^bold>\<subseteq> M \<and> countable {S. M S}
           \<and> \<langle>I,N,M\<rangle> \<subseteq>\<^sub>E \<langle>I,D,E\<rangle>"
proof -
  obtain N M
    where "N \<^bold>\<subseteq> D" "M \<^bold>\<subseteq> E"
      "D\<^sub>0 \<^bold>\<subseteq> N" "E\<^sub>0 \<^bold>\<subseteq> M"
      "countable {d. N d}" "countable {S. M S}"
      "\<And>y \<psi> a b.
         a into N \<Longrightarrow> b into M \<Longrightarrow>
         \<exists>d:D. \<langle>I,D,E\<rangle>,a[y \<leftarrow> d],b \<Turnstile>\<^sup>d \<psi> \<Longrightarrow>
         \<exists>d:N. \<langle>I,D,E\<rangle>,a[y \<leftarrow> d],b \<Turnstile>\<^sup>d \<psi>"
      "\<And>Y \<psi> a b.
         a into N \<Longrightarrow> b into M \<Longrightarrow>
         \<exists>S:E. \<langle>I,D,E\<rangle>,a,b\<langle>Y \<leftarrow> S\<rangle> \<Turnstile>\<^sup>d \<psi> \<Longrightarrow>
         \<exists>S:M. \<langle>I,D,E\<rangle>,a,b\<langle>Y \<leftarrow> S\<rangle> \<Turnstile>\<^sup>d \<psi>"
    using skolem_hull[of D\<^sub>0 D E\<^sub>0 E, OF assms] by blast
  hence "D\<^sub>0 \<^bold>\<subseteq> N \<and> countable {d. N d}
         \<and> E\<^sub>0 \<^bold>\<subseteq> M \<and> countable {S. M S}
         \<and> \<langle>I,N,M\<rangle> \<subseteq>\<^sub>E \<langle>I,D,E\<rangle>"
    using ElementarySubstructure_def truth_pres
          skolem_hull[of D\<^sub>0 D E\<^sub>0 E, OF assms]
    by auto
  thus ?thesis by blast
qed

text \<open>Strongest faithfulness: standard validity = minimal validity over
  elementary interpretations.\<close>

theorem Deep'_to_MinS:
  "(\<Turnstile>\<^sup>d' \<phi>) = (\<forall>II gg GG. MinS_ES_Univ II gg GG \<longrightarrow> MinS.ValM (MinS.DpToShM II gg GG \<phi>))"
proof
  assume "\<Turnstile>\<^sup>d' \<phi>"
  thus "\<forall>II gg. MinS_ES_Univ II gg \<^bold>\<subseteq> (\<lambda>GG. MinS.ValM (MinS.DpToShM II gg GG \<phi>))"
    using MinS.FaithfulMD MinS_ES.\<N>_valid_ES
          MinS_ES_Univ_def ValD'_def
    by blast
next
  assume A: "\<forall>II gg GG.
               MinS_ES_Univ II gg GG
                 \<longrightarrow> MinS.ValM (MinS.DpToShM II gg GG \<phi>)"
  show "\<Turnstile>\<^sup>d' \<phi>"
    unfolding ValD'_def
  proof (safe)
    fix I :: \<I> and g :: \<E> and G :: \<G>
    have "Range g \<^bold>\<subseteq> Univ" "Range G \<^bold>\<subseteq> Univ"
         "\<exists>x. Range g x" "\<exists>x. Range G x"
         "countable {d. MSOinHOL_preliminaries.Range g d}"
         "countable {S. MSOinHOL_preliminaries.Range G S}"
      by (auto simp add: full_SetCompr_eq)
    then obtain N M
      where 7: "Range g \<^bold>\<subseteq> N" "countable {d. N d}"
               "Range G \<^bold>\<subseteq> M" "countable {S. M S}"
        and ES: "\<langle>I,N,M\<rangle> \<subseteq>\<^sub>E \<langle>I,Univ,Univ\<rangle>"
      using DownwardLowenheimSkolem
              [where D\<^sub>0="Range g" and E\<^sub>0="Range G"
                 and D=Univ and E=Univ]
      by metis
    then obtain g' G'
      where g': "Range g' = N" and G': "Range G' = M"
        and g'G':
          "(\<langle>I,Range g',Range G'\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)
             = (\<langle>I,N,M\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
      using reindex by (smt (verit, best) reindex_coincide)
    hence "\<langle>I,Range g',Range G'\<rangle> \<subseteq>\<^sub>E \<langle>I,Univ,Univ\<rangle>"
      using ES by presburger
    then interpret MinS_ES_Univ I g' G'
      by (simp add: MinS_ES.intro MinS_ES_Univ_def)
    have "MinS.ValM (MinS.DpToShM I g' G' \<phi>)"
      using A MinS_ES_Univ_axioms by blast
    hence "\<langle>I,N,M\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>"
      using FaithfulMDlem ValM_def g' G' g'G' by blast
    thus "\<langle>I,Univ,Univ\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>"
      using ES
      unfolding ElementarySubstructure_def
      by (smt (verit, best) "7"(1,3) G' g')
  qed
qed

text \<open>Faithfulness to the standard reading (companion of
  @{text Faithful_to_Henkin}).\<close>

corollary Faithful_to_Standard:
  "(\<Turnstile>\<^sup>d' \<phi>) = (\<forall>II gg GG. MinS_ES_Univ II gg GG \<longrightarrow> MinS.ValM (MinS.DpToShM II gg GG \<phi>))"
  using Deep'_to_MinS .

text \<open>Earlier Range-seeded route to the general-reading converse: the
  hull packaged with its truth-preservation payoff, derived in one step
  from @{text DownwardLowenheimSkolem}.\<close>

lemma ls_hull:
  assumes gD: "g into D" and GE: "G into E"
  obtains D\<^sub>0 E\<^sub>0
    where "D\<^sub>0 \<^bold>\<subseteq> D" and "E\<^sub>0 \<^bold>\<subseteq> E"
      and "Range g \<^bold>\<subseteq> D\<^sub>0" and "Range G \<^bold>\<subseteq> E\<^sub>0"
      and "countable {d. D\<^sub>0 d}" and "countable {S. E\<^sub>0 S}"
      and "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
proof -
  have *:
      "Range g \<^bold>\<subseteq> D" "Range G \<^bold>\<subseteq> E"
      "\<exists>x. Range g x" "\<exists>x. Range G x"
      "countable {d. Range g d}" "countable {S. Range G S}"
    using assms by (auto simp: full_SetCompr_eq)
  obtain N M
    where N: "Range g \<^bold>\<subseteq> N" "countable {d. N d}"
              "Range G \<^bold>\<subseteq> M" "countable {S. M S}"
      and ES: "\<langle>I,N,M\<rangle> \<subseteq>\<^sub>E \<langle>I,D,E\<rangle>"
    using DownwardLowenheimSkolem
            [where D\<^sub>0="Range g" and E\<^sub>0="Range G",
             OF *(1,2,3,4,5,6), of I]
    by metis
  have sub: "N \<^bold>\<subseteq> D" "M \<^bold>\<subseteq> E"
    and ES':
      "\<And>g G \<phi>. G into M \<Longrightarrow> g into N \<Longrightarrow>
        (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,N,M\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
    using ES unfolding ElementarySubstructure_def by auto
  have gn: "g into N" "G into M"
    using into_Range N(1,3) by (metis (mono_tags, lifting))+
  show thesis
    using that[OF sub N(1,3,2,4) ES'[OF gn(2) gn(1), symmetric]] .
qed

text \<open>Range reduction: countermodels reduce to range-only
  countermodels.\<close>

lemma Range_reduction:
  assumes "g into D" and "G into E"
  obtains g' G'
    where "(\<langle>I,Range g',Range G'\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)
             = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
proof -
  obtain D\<^sub>0 E\<^sub>0
    where *:
        "Range g \<^bold>\<subseteq> D\<^sub>0" "Range G \<^bold>\<subseteq> E\<^sub>0"
        "countable {d. D\<^sub>0 d}" "countable {S. E\<^sub>0 S}"
      and eq:
        "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>) = (\<langle>I,D,E\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)"
    using assms by (rule ls_hull)
  obtain g' G'
    where rg: "Range g' = D\<^sub>0" and rG: "Range G' = E\<^sub>0"
      and coin:
        "(\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g,G \<Turnstile>\<^sup>d \<phi>)
           = (\<langle>I,D\<^sub>0,E\<^sub>0\<rangle>,g',G' \<Turnstile>\<^sup>d \<phi>)"
    using reindex_coincide[OF *(3,4,1,2)] by blast
  show thesis using that[of g' G'] rg rG eq coin by simp
qed

text \<open>Range-relative = general (Henkin) deep validity.\<close>

theorem RangeValid_imp_ValD: "\<Turnstile>\<^sup>r \<phi> \<Longrightarrow> \<Turnstile>\<^sup>d \<phi>"
  unfolding RangeValid_def ValD_def
  using Range_reduction by metis

corollary RangeValid_iff_ValD: "(\<Turnstile>\<^sup>r \<phi>) = (\<Turnstile>\<^sup>d \<phi>)"
  using RangeValid_imp_ValD ValD_imp_RangeValid by blast

text \<open>Faithfulness to the general (Henkin) reading.  Together with
  @{text Faithful_to_Standard} it yields the two faithfulness results;
  the limitative @{text Standard_strictly_stronger} below separates them.\<close>

corollary Faithful_to_Henkin: "(\<Turnstile>\<^sup>r \<phi>) = (\<Turnstile>\<^sup>d \<phi>)"
  using RangeValid_iff_ValD .

text \<open>The standard reading is strictly stronger; comprehension witnesses
  the gap.\<close>

lemma Standard_strictly_stronger:
  "(\<forall>(\<phi>::\<F>). (\<Turnstile>\<^sup>d \<phi>) \<longrightarrow> (\<Turnstile>\<^sup>d' \<phi>)) \<and> (\<exists>(\<phi>::\<F>). (\<Turnstile>\<^sup>d' \<phi>) \<and> \<not> (\<Turnstile>\<^sup>d \<phi>))"
proof
  show "\<forall>(\<phi>::\<F>). (\<Turnstile>\<^sup>d \<phi>) \<longrightarrow> (\<Turnstile>\<^sup>d' \<phi>)"
    using Val by blast
next
  let ?\<phi> = "\<exists>\<^sup>d\<^sub>2(0::V2). \<forall>\<^sup>d(0::V).
              (((0::V2)\<^sup>d((0::V)))
                 \<longleftrightarrow>\<^sup>d ((0::R)\<^sup>d((0::V),(0::V))))"
  have "\<Turnstile>\<^sup>d' ?\<phi>" by (rule comprehension_atom)
  moreover have "\<not> (\<Turnstile>\<^sup>d ?\<phi>)"
    unfolding DefD
    apply (rule notI,
           drule spec[where x="\<lambda>r (a::D) b. a = b"],
           drule spec[where x="Univ::D\<Rightarrow>bool"],
           drule spec[where x="\<lambda>S::D\<Rightarrow>bool. \<exists>d::D. \<not>S d"],
           drule spec[where x="\<lambda>x::V. undefined::D"],
           drule spec[where x="\<lambda>X::V2. \<lambda>d::D. False"])
    by (auto simp: SetMod_def EnvMod_def)
  ultimately show "\<exists>(\<phi>::\<F>). (\<Turnstile>\<^sup>d' \<phi>) \<and> \<not> (\<Turnstile>\<^sup>d \<phi>)"
    by blast
qed

end
