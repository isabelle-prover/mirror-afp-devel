section \<open>Mapping Arbitrary Isabelle/HOL Sets into ZFC; their Cardinalities\<close>

theory General_Cardinals
  imports ZFC_Typeclasses "HOL-Analysis.Continuum_Not_Denumerable"

begin

subsection \<open>Making the embedding from the type class explicit\<close>

definition V_of :: "'a::embeddable \<Rightarrow> V"
  where "V_of \<equiv> SOME f. inj f"

lemma inj_V_of: "inj V_of"
  unfolding V_of_def by (metis embeddable_class.ex_inj some_eq_imp)

declare inv_f_f [OF inj_V_of, simp]

lemma inv_V_of_image_eq [simp]: "inv V_of ` (V_of ` X) = X"
  by (auto simp: image_comp)

lemma infinite_V_of: "infinite (UNIV::'a set) \<Longrightarrow> infinite (range (V_of::'a::embeddable\<Rightarrow>V))"
  using finite_imageD inj_V_of by blast

lemma countable_V_of: "countable (range (V_of::'a::countable\<Rightarrow>V))"
  by blast

lemma elts_set_V_of: "small X \<Longrightarrow> elts (ZFC_in_HOL.set (V_of ` X)) \<approx> X"
  by (metis inj_V_of inj_eq inj_on_def inj_on_image_eqpoll_self replacement set_of_elts small_iff)

lemma V_of_image_times: "V_of ` (X \<times> Y) \<approx> (V_of ` X) \<times> (V_of ` Y)"
proof -
  have "V_of ` (X \<times> Y) \<approx> X \<times> Y"
    by (meson inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self)
  also have "\<dots> \<approx> (V_of ` X) \<times> (V_of ` Y)"
    by (metis eqpoll_sym inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self times_eqpoll_cong)
  finally show ?thesis .
qed

subsection \<open>The cardinality of the continuum\<close>

definition "Real_set \<equiv> ZFC_in_HOL.set (range (V_of::real\<Rightarrow>V))"
definition "Complex_set \<equiv> ZFC_in_HOL.set (range (V_of::complex\<Rightarrow>V))"
definition "C_continuum \<equiv> vcard Real_set"

lemma V_of_Real_set: "bij_betw V_of (UNIV::real set) (elts Real_set)"
  by (simp add: Real_set_def bij_betw_def inj_V_of)

lemma uncountable_Real_set: "uncountable (elts Real_set)"
  using V_of_Real_set countable_iff_bij uncountable_UNIV_real by blast

lemma "Card C_continuum"
  by (simp add: C_continuum_def Card_def)

lemma C_continuum_ge: "C_continuum \<ge> \<aleph>1"
proof -
  have "\<not> C_continuum < \<aleph>1"
  proof -
    have "\<not> vcard Real_set \<le> \<aleph>0"
      using countable_iff_le_Aleph0 uncountable_Real_set by presburger
    then show ?thesis
      by (simp add: C_continuum_def lt_csucc_iff one_V_def)
  qed
  then show ?thesis
    by (simp add: C_continuum_def Ord_not_less)
qed


lemma V_of_Complex_set: "bij_betw V_of (UNIV::complex set) (elts Complex_set)"
  by (simp add: Complex_set_def bij_betw_def inj_V_of)

lemma uncountable_Complex_set: "uncountable (elts Complex_set)"
  using V_of_Complex_set countableI_bij2 uncountable_UNIV_complex by blast

lemma Complex_vcard: "vcard Complex_set = C_continuum"
proof -
  define emb1 where "emb1 \<equiv> V_of o complex_of_real o inv V_of"
  have "elts Real_set \<approx> elts Complex_set"
  proof (rule lepoll_antisym)
    show "elts Real_set \<lesssim> elts Complex_set"
      unfolding lepoll_def
    proof (intro conjI exI)
      show "inj_on emb1 (elts Real_set)"
        unfolding emb1_def Real_set_def
        by (simp add: inj_V_of inj_compose inj_of_real inj_on_imageI)
      show "emb1 ` elts Real_set \<subseteq> elts Complex_set"
        by (simp add: emb1_def Real_set_def Complex_set_def image_subset_iff)
    qed
    define emb2 where "emb2 \<equiv> (\<lambda>z. (V_of (Re z), V_of (Im z))) o inv V_of"
    have "elts Complex_set \<lesssim> elts Real_set \<times> elts Real_set"
      unfolding lepoll_def
    proof (intro conjI exI)
      show "inj_on emb2 (elts Complex_set)"
        unfolding emb2_def Complex_set_def inj_on_def
        by (simp add: complex.expand inj_V_of inj_eq)
      show "emb2 ` elts Complex_set \<subseteq> elts Real_set \<times> elts Real_set"
        by (simp add: emb2_def Real_set_def Complex_set_def image_subset_iff)
    qed
    also have "\<dots>  \<approx> elts Real_set"
      by (simp add: infinite_times_eqpoll_self uncountable_Real_set uncountable_infinite)
    finally show "elts Complex_set \<lesssim> elts Real_set" .
  qed
  then show ?thesis
    by (simp add: C_continuum_def cardinal_cong)
qed

subsection \<open>Cardinality of an arbitrary HOL set\<close>

definition gcard :: "'a::embeddable set \<Rightarrow> V" 
  where "gcard X \<equiv> vcard (ZFC_in_HOL.set (V_of ` X))"

lemma gcard_big_0: "\<not> small X \<Longrightarrow> gcard X = 0"
  by (metis elts_eq_empty_iff elts_of_set gcard_def inv_V_of_image_eq replacement vcard_0)

lemma gcard_empty_0 [simp]: "gcard {} = 0"
  by (metis gcard_def image_is_empty vcard_0 zero_V_def)

lemma gcard_single_1 [simp]: "gcard {x} = 1"
  by (simp add: gcard_def)

lemma gcard_finite_set: "\<lbrakk>finite X; a \<notin> X\<rbrakk> \<Longrightarrow> gcard (insert a X) = succ (gcard X)" 
  by (simp add: gcard_def inj_V_of inj_image_mem_iff finite_csucc vcard_finite_set)

lemma gcard_eq_card: "finite X \<Longrightarrow> gcard X = ord_of_nat (card X)"
  by (induction X rule: finite_induct) (auto simp add: gcard_finite_set)

lemma Card_gcard [iff]: "Card (gcard X)"
  by (simp add: Card_def gcard_def)

lemma gcard_eq_vcard [simp]: "gcard (elts x) = vcard x"
  by (metis cardinal_cong elts_set_V_of gcard_def small_elts)

lemma gcard_eqpoll: "small X \<Longrightarrow> elts (gcard X) \<approx> X"
  by (metis cardinal_eqpoll elts_set_V_of eqpoll_trans gcard_def)

lemma gcard_image_le: 
  assumes "small A"
  shows "gcard (f ` A) \<le> gcard A"
proof -
  have "(V_of ` f ` A) \<lesssim> (V_of ` A)"
    by (metis image_lepoll inv_V_of_image_eq lepoll_trans)
  then show ?thesis
    by (simp add: assms gcard_def lepoll_imp_Card_le)
qed

lemma gcard_image: "inj_on f A \<Longrightarrow> gcard (f ` A) = gcard A"
  by (metis dual_order.antisym gcard_big_0 gcard_image_le small_image_iff the_inv_into_onto)

lemma lepoll_imp_gcard_le:
  assumes "A \<lesssim> B" "small B"
  shows "gcard A \<le> gcard B"
proof -
  have "elts (ZFC_in_HOL.set (V_of ` A)) \<approx> A" "elts (ZFC_in_HOL.set (V_of ` B)) \<approx> B"
    by (meson assms elts_set_V_of lepoll_small)+
  with \<open>A \<lesssim> B\<close> show ?thesis
    unfolding gcard_def
    by (meson lepoll_imp_Card_le eqpoll_sym lepoll_iff_leqpoll lepoll_trans)
qed

lemma subset_imp_gcard_le:
  assumes "A \<subseteq> B" "small B"
  shows "gcard A \<le> gcard B"
  by (simp add: assms lepoll_imp_gcard_le subset_imp_lepoll)

lemma gcard_le_lepoll: "\<lbrakk>gcard A \<le> \<alpha>; small A\<rbrakk> \<Longrightarrow> A \<lesssim> elts \<alpha>"
  by (meson eqpoll_sym gcard_eqpoll lepoll_trans1 less_eq_V_def subset_imp_lepoll)

lemma gcard_Union_le_cmult:
  assumes "small U" and \<kappa>: "\<And>x. x \<in> U \<Longrightarrow> gcard x \<le> \<kappa>" and sm: "\<And>x. x \<in> U \<Longrightarrow> small x"
  shows "gcard (\<Union>U) \<le> gcard U \<otimes> \<kappa>"
proof -
  have "\<exists>f. f \<in> x \<rightarrow> elts \<kappa> \<and> inj_on f x" if "x \<in> U" for x
    using \<kappa> [OF that] gcard_le_lepoll by (smt (verit) Pi_iff TC_small imageI lepoll_def subset_eq)
  then obtain \<phi> where \<phi>: "\<And>x. x \<in> U \<Longrightarrow> (\<phi> x) \<in> x \<rightarrow> elts \<kappa> \<and> inj_on (\<phi> x) x"
    by metis
  define u where "u \<equiv> \<lambda>y. @x. x \<in> U \<and> y \<in> x"
  have u: "u y \<in> U \<and> y \<in>  (u y)" if "y \<in> \<Union>( U)" for y
    unfolding u_def using that by (fast intro!: someI2)
  define \<psi> where "\<psi> \<equiv> \<lambda>y. (u y, \<phi> (u y) y)"
  have U: "elts (gcard U) \<approx> U"
    by (simp add: gcard_eqpoll)
   have "\<Union>U \<lesssim> U \<times> elts \<kappa>"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on \<psi> (\<Union> U)"
      using \<phi> u by (smt (verit) \<psi>_def inj_on_def prod.inject)
    show "\<psi> ` \<Union> U \<subseteq> U \<times> elts \<kappa>"
      using \<phi> u by (auto simp: \<psi>_def)
  qed
  also have "\<dots>  \<approx> elts (gcard U \<otimes> \<kappa>)"
    using U elts_cmult eqpoll_sym eqpoll_trans times_eqpoll_cong by blast
  finally have " (\<Union>U) \<lesssim> elts (gcard U \<otimes> \<kappa>)" .
  then show ?thesis
    by (metis cardinal_idem cmult_def gcard_eq_vcard lepoll_imp_gcard_le small_elts)
qed

lemma gcard_Times [simp]: "gcard (X \<times> Y) = gcard X \<otimes> gcard Y"
proof (cases "small X \<and> small Y")
  case True
  have "V_of ` (X \<times> Y) \<approx> (V_of ` X) \<times> (V_of ` Y)"
    by (metis V_of_image_times)
  also have "\<dots> \<approx> elts (vcard (ZFC_in_HOL.set (V_of ` X))) \<times> elts (vcard (ZFC_in_HOL.set (V_of ` Y)))"
    by (metis True cardinal_eqpoll eqpoll_sym replacement set_of_elts small_iff times_eqpoll_cong)
  also have "\<dots> \<approx> elts (vtimes (vcard (ZFC_in_HOL.set (V_of ` X))) (vcard (ZFC_in_HOL.set (V_of ` Y))))"
    using elts_VSigma by auto
  finally show ?thesis
    using True cardinal_cong by (simp add: gcard_def cmult_def)
next
  case False
  have "gcard (X \<times> Y) = 0"
    by (metis False Times_empty gcard_big_0 gcard_empty_0 small_Times_iff)
  then show ?thesis
    by (metis False cmult_0 cmult_commute gcard_big_0)
qed

subsection \<open>Countable and uncountable sets\<close>

lemma countable_iff_g_le_Aleph0: "small X \<Longrightarrow> countable X \<longleftrightarrow> gcard X \<le> \<aleph>0"
  unfolding gcard_def
  by (metis countable_iff_le_Aleph0 countable_image elts_of_set inv_V_of_image_eq replacement)

lemma countable_imp_g_le_Aleph0: "countable X \<Longrightarrow> gcard X \<le> \<aleph>0"
  by (meson countable countable_iff_g_le_Aleph0)

lemma finite_iff_g_le_Aleph0: "small X \<Longrightarrow> finite X \<longleftrightarrow> gcard X < \<aleph>0"
  by (metis Aleph_0 elts_set_V_of eqpoll_finite_iff finite_iff_less_Aleph0 gcard_def)

lemma finite_imp_g_le_Aleph0: "finite X \<Longrightarrow> gcard X < \<aleph>0"
  by (meson finite_iff_g_le_Aleph0 finite_imp_small)

lemma countable_infinite_gcard: "countable X \<and> infinite X \<longleftrightarrow> gcard X = \<aleph>0"
proof -
  have "gcard X = \<omega>"
    if "countable X" and "infinite X"
    using that countable countable_imp_g_le_Aleph0 finite_iff_g_le_Aleph0 less_V_def by auto
  moreover have "countable X" if "gcard X = \<omega>"
    by (metis Aleph_0 countable_iff_g_le_Aleph0 dual_order.refl gcard_big_0 omega_nonzero that)
  moreover have False if "gcard X = \<omega>" and "finite X"
    by (metis Aleph_0 dual_order.irrefl finite_iff_g_le_Aleph0 finite_imp_small that)
  ultimately show ?thesis
    by auto
qed

lemma uncountable_gcard: "small X \<Longrightarrow> uncountable X \<longleftrightarrow> gcard X > \<aleph>0"
  by (simp add: Ord_not_le countable_iff_g_le_Aleph0 gcard_def)

lemma uncountable_gcard_ge: "small X \<Longrightarrow> uncountable X \<longleftrightarrow> gcard X \<ge> \<aleph>1"
  by (simp add: uncountable_gcard csucc_le_Card_iff one_V_def)

lemma subset_smaller_gcard:
  assumes \<kappa>: "\<kappa> \<le> gcard X" "Card \<kappa>"
  obtains Y where "Y \<subseteq> X" "gcard Y = \<kappa>"
proof (cases "small X")
  case True
  with  subset_smaller_vcard [OF \<kappa> [unfolded gcard_def]] show ?thesis
    by (metis elts_of_set gcard_def less_eq_V_def replacement set_of_elts subset_imageE that)
next
  case False
  with assms show ?thesis
    by (metis antisym gcard_big_0 le_0 order_refl that)
qed

lemma Real_gcard: "gcard (UNIV::real set) = C_continuum"
  by (metis C_continuum_def Real_set_def gcard_def)

lemma Complex_gcard: "gcard (UNIV::complex set) = C_continuum"
  by (metis Complex_set_def Complex_vcard gcard_def)

end
