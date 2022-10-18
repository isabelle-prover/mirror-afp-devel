section \<open>Wetzel's Problem, Solved by Erdös\<close>

text \<open>Martin Aigner and Günter M. Ziegler. Proofs from THE BOOK. (Springer, 2018).
Chapter 19: Sets, functions, and the continuum hypothesis
Theorem 5 (pages 137--8)\<close>

theory Wetzels_Problem imports
  "HOL-Complex_Analysis.Complex_Analysis" "ZFC_in_HOL.General_Cardinals"
   
begin

definition Wetzel :: "(complex \<Rightarrow> complex) set \<Rightarrow> bool"
  where "Wetzel \<equiv> \<lambda>F. (\<forall>f\<in>F. f analytic_on UNIV) \<and> (\<forall>z. countable((\<lambda>f. f z) ` F))"

subsubsection \<open>When the continuum hypothesis is false\<close>

proposition Erdos_Wetzel_nonCH:
  assumes W: "Wetzel F" and NCH: "C_continuum > \<aleph>1"
  shows "countable F"
proof -
  have "\<exists>z0. gcard ((\<lambda>f. f z0) ` F) \<ge> \<aleph>1" if "uncountable F"
  proof -
    have "gcard F \<ge> \<aleph>1"
      using that uncountable_gcard_ge by force
    then obtain F' where "F' \<subseteq> F" and F': "gcard F' = \<aleph>1"
      by (meson Card_Aleph subset_smaller_gcard)
    then obtain \<phi> where \<phi>: "bij_betw \<phi> (elts \<omega>1) F'"
      by (metis TC_small eqpoll_def gcard_eqpoll)
    define S where "S \<equiv> \<lambda>\<alpha> \<beta>. {z. \<phi> \<alpha> z = \<phi> \<beta> z}"
    have co_S: "gcard (S \<alpha> \<beta>) \<le> \<aleph>0" if "\<alpha> \<in> elts \<beta>" "\<beta> \<in> elts \<omega>1" for \<alpha> \<beta>
    proof -
      have "\<phi> \<alpha> holomorphic_on UNIV" "\<phi> \<beta> holomorphic_on UNIV"
        using W \<open>F' \<subseteq> F\<close> unfolding Wetzel_def
        by (meson Ord_\<omega>1 Ord_trans \<phi> analytic_imp_holomorphic bij_betwE subsetD that)+
      moreover have "\<phi> \<alpha> \<noteq> \<phi> \<beta>"
        by (metis Ord_\<omega>1 Ord_trans \<phi> bij_betw_def inj_on_def mem_not_refl that)
      ultimately have "countable (S \<alpha> \<beta>)"
        using holomorphic_countable_equal_UNIV unfolding S_def by blast
      then show ?thesis
        using countable_imp_g_le_Aleph0 by blast
    qed
    define SS where "SS \<equiv>\<Squnion>\<beta> \<in> elts \<omega>1. \<Squnion>\<alpha> \<in> elts \<beta>. S \<alpha> \<beta>"
    have F'_eq: "F' =  \<phi> ` elts \<omega>1"
      using \<phi> bij_betw_imp_surj_on by auto
    have \<section>: "\<And>\<beta>. \<beta> \<in> elts \<omega>1 \<Longrightarrow> gcard (\<Union>\<alpha>\<in>elts \<beta>. S \<alpha> \<beta>) \<le> \<omega>"
      by (metis Aleph_0 TC_small co_S countable_UN countable_iff_g_le_Aleph0 less_\<omega>1_imp_countable)
    have "gcard SS \<le> gcard ((\<lambda>\<beta>. \<Union>\<alpha>\<in>elts \<beta>. S \<alpha> \<beta>) ` elts \<omega>1) \<otimes> \<aleph>0"
      apply (simp add: SS_def)
      by (metis (no_types, lifting) "\<section>" TC_small gcard_Union_le_cmult imageE)
    also have "\<dots>  \<le> \<aleph>1"
    proof (rule cmult_InfCard_le)
      show "gcard ((\<lambda>\<beta>. \<Union>\<alpha>\<in>elts \<beta>. S \<alpha> \<beta>) ` elts \<omega>1) \<le> \<omega>1"
        using gcard_image_le by fastforce
    qed auto
    finally have "gcard SS \<le> \<aleph>1" .
    with NCH obtain z0 where "z0 \<notin> SS"
      by (metis Complex_gcard UNIV_eq_I less_le_not_le)
    then have "inj_on (\<lambda>x. \<phi> x z0) (elts \<omega>1)"
      apply (simp add: SS_def S_def inj_on_def)
      by (metis Ord_\<omega>1 Ord_in_Ord Ord_linear)
    then have "gcard ((\<lambda>f. f z0) ` F') = \<aleph>1"
      by (smt (verit) F' F'_eq gcard_image imageE inj_on_def)
    then show ?thesis
      by (metis TC_small \<open>F' \<subseteq> F\<close> image_mono subset_imp_gcard_le)
  qed
  with W show ?thesis
    unfolding Wetzel_def by (meson countable uncountable_gcard_ge)
qed

subsubsection \<open>When the continuum hypothesis is true\<close>

lemma Rats_closure_real2: "closure (\<rat>\<times>\<rat>) = (UNIV::real set)\<times>(UNIV::real set)"
  by (simp add: Rats_closure_real closure_Times)

proposition Erdos_Wetzel_CH:
  assumes CH: "C_continuum = \<aleph>1"
  obtains F where "Wetzel F" and "uncountable F"
proof -
  define D where "D \<equiv> {z. Re z \<in> \<rat> \<and> Im z \<in> \<rat>}"
  have Deq: "D = (\<Union>x\<in>\<rat>. \<Union>y\<in>\<rat>. {Complex x y})"
    using complex.collapse by (force simp: D_def)
  with countable_rat have "countable D"
    by blast
  have "infinite D"
    unfolding Deq
    by (intro infinite_disjoint_family_imp_infinite_UNION Rats_infinite) (auto simp: disjoint_family_on_def)
  have "\<exists>w. Re w \<in> \<rat> \<and> Im w \<in> \<rat> \<and> norm (w - z) < e" if "e > 0" for z and e::real
  proof -
    obtain x y where "x\<in>\<rat>" "y\<in>\<rat>" and xy: "dist (x,y) (Re z, Im z) < e"
      using \<open>e > 0\<close> Rats_closure_real2 by (force simp: closure_approachable)
    moreover have "dist (x,y) (Re z, Im z) = norm (Complex x y - z)"
      by (simp add: norm_complex_def norm_prod_def dist_norm)
    ultimately show "\<exists>w. Re w \<in> \<rat> \<and> Im w \<in> \<rat> \<and> norm (w - z) < e"
      by (metis complex.sel)
  qed
  then have cloD: "closure D = UNIV"
    by (auto simp: D_def closure_approachable dist_complex_def)
  obtain \<zeta> where \<zeta>: "bij_betw \<zeta> (elts \<omega>1) (UNIV::complex set)"
    by (metis Complex_gcard TC_small assms eqpoll_def gcard_eqpoll)
  define inD where "inD \<equiv> \<lambda>\<beta> f. (\<forall>\<alpha> \<in> elts \<beta>. f (\<zeta> \<alpha>) \<in> D)"
  define \<Phi> where "\<Phi> \<equiv> \<lambda>\<beta> f. f \<beta> analytic_on UNIV \<and> inD \<beta> (f \<beta>) \<and> inj_on f (elts (succ \<beta>))"
  have ind_step: "\<exists>h. \<Phi> \<gamma> ((restrict f (elts \<gamma>))(\<gamma>:=h))"
    if \<gamma>: "\<gamma> \<in> elts \<omega>1" and "\<forall>\<beta> \<in> elts \<gamma>. \<Phi> \<beta> f" for \<gamma> f
  proof -
    have f: "\<forall>\<beta> \<in> elts \<gamma>. f \<beta> analytic_on UNIV \<and> inD \<beta> (f \<beta>)" 
      using that by (auto simp: \<Phi>_def)
    have inj: "inj_on f (elts \<gamma>)"
      using that by (simp add: \<Phi>_def inj_on_def) (meson Ord_\<omega>1 Ord_in_Ord Ord_linear)
    obtain h where "h analytic_on UNIV" "inD \<gamma> h" "(\<forall>\<beta> \<in> elts \<gamma>. h \<noteq> f \<beta>)"
    proof (cases "finite (elts \<gamma>)")
      case True
      then obtain \<eta> where \<eta>: "bij_betw \<eta> {..<card (elts \<gamma>)} (elts \<gamma>)"
        using bij_betw_from_nat_into_finite by blast
      define g where "g \<equiv> f o \<eta>"
      define w where "w \<equiv> \<zeta> o \<eta>"
      have gf: "\<forall>i<card (elts \<gamma>). h \<noteq> g i \<Longrightarrow> \<forall>\<beta>\<in>elts \<gamma>. h \<noteq> f \<beta>" for h
        using \<eta> by (auto simp: bij_betw_iff_bijections g_def)
      have **: "\<exists>h. h analytic_on UNIV \<and> (\<forall>i<n. h (w i) \<in> D \<and> h (w i) \<noteq> g i (w i))"
        if "n \<le> card (elts \<gamma>)" for n
        using that
      proof (induction n)
        case 0
        then show ?case
          using analytic_on_const by blast
      next
        case (Suc n)
        then obtain h where "h analytic_on UNIV" and hg: "\<forall>i<n. h(w i) \<in> D \<and> h(w i) \<noteq> g i (w i)"
          using Suc_leD by blast
        define p where "p \<equiv> \<lambda>z. \<Prod>i<n. z - w i"
        have p0: "p z = 0 \<longleftrightarrow> (\<exists>i<n. z = w i)" for z
          unfolding p_def by force
        obtain d where d: "d \<in> D - {g n (w n)}"
          using \<open>infinite D\<close> by (metis ex_in_conv finite.emptyI infinite_remove)
        define h' where "h' \<equiv> \<lambda>z. h z + p z * (d - h (w n)) / p (w n)"
        have h'_eq: "h' (w i) = h (w i)" if "i<n" for i
          using that by (force simp: h'_def p0)
        show ?case
        proof (intro exI strip conjI)
          have nless: "n < card (elts \<gamma>)"
            using Suc.prems Suc_le_eq by blast
          with \<eta> have "\<eta> n \<noteq> \<eta> i" if "i<n" for i
            using that unfolding bij_betw_iff_bijections
            by (metis lessThan_iff less_not_refl order_less_trans)
          with \<zeta> \<eta> \<gamma> have pwn_nonzero: "p (w n) \<noteq> 0"
            apply (clarsimp simp: p0 w_def bij_betw_iff_bijections)
            by (metis Ord_\<omega>1 Ord_trans nless lessThan_iff order_less_trans)
          then show "h' analytic_on UNIV"
            unfolding h'_def p_def by (intro analytic_intros \<open>h analytic_on UNIV\<close>)
          fix i
          assume "i < Suc n"
          then have \<section>: "i < n \<or> i = n"
            by linarith
          then show "h' (w i) \<in> D"
            using h'_eq hg d h'_def pwn_nonzero by force
          show "h' (w i) \<noteq> g i (w i)"
            using \<section> h'_eq hg h'_def d pwn_nonzero by fastforce
        qed
      qed
      show ?thesis 
        using ** [OF order_refl] \<eta> that gf 
        by (simp add: w_def bij_betw_iff_bijections inD_def) metis
    next
      case False
      then obtain \<eta> where \<eta>: "bij_betw \<eta> (UNIV::nat set) (elts \<gamma>)"
        by (meson \<gamma> countable_infiniteE' less_\<omega>1_imp_countable)
      then have \<eta>_inject [simp]: "\<eta> i = \<eta> j \<longleftrightarrow> i=j" for i j
        by (simp add: bij_betw_imp_inj_on inj_eq)
      define g where "g \<equiv> f o \<eta>"
      define w where "w \<equiv> \<zeta> o \<eta>"
      then have w_inject [simp]: "w i = w j \<longleftrightarrow> i=j" for i j
        by (smt (verit) Ord_\<omega>1 Ord_trans UNIV_I \<eta> \<gamma> \<zeta> bij_betw_iff_bijections comp_apply)
      define p where "p \<equiv> \<lambda>n z. \<Prod>i<n. z - w i"
      define q where "q \<equiv> \<lambda>n. \<Prod>i<n. 1 + norm (w i)"
      define h where "h \<equiv> \<lambda>n \<epsilon> z. \<Sum>i<n. \<epsilon> i * p i z"
      define BALL where "BALL \<equiv> \<lambda>n \<epsilon>. ball (h n \<epsilon> (w n)) (norm (p n (w n)) / (fact n * q n))"
                  \<comment> \<open>The demonimator above is the key to keeping the epsilons small\<close>
      define DD where "DD \<equiv> \<lambda>n \<epsilon>. D \<inter> BALL n \<epsilon> - {g n (w n)}"
      define dd where "dd \<equiv> \<lambda>n \<epsilon>. SOME x. x \<in> DD n \<epsilon>"
      have p0: "p n z = 0 \<longleftrightarrow> (\<exists>i<n. z = w i)" for z n
        unfolding p_def by force
      have [simp]: "p n (w i) = 0" if "i<n" for i n
        using that by (simp add: p0)
      have q_gt0: "0 < q n" for n
        unfolding q_def by (smt (verit) norm_not_less_zero prod_pos)
      have "DD n \<epsilon> \<noteq> {}" for n \<epsilon>
      proof -
        have "r > 0 \<Longrightarrow> infinite (D \<inter> ball z r)" for z r
          by (metis islimpt_UNIV limpt_of_closure islimpt_eq_infinite_ball cloD)
        then have "infinite (D \<inter> BALL n \<epsilon>)" for n \<epsilon>
          by (simp add: BALL_def p0 q_gt0)
        then show ?thesis
          by (metis DD_def finite.emptyI infinite_remove)
      qed
      then have dd_in_DD: "dd n \<epsilon> \<in> DD n \<epsilon>" for n \<epsilon>
        by (simp add: dd_def some_in_eq)

      have h_cong: "h n \<epsilon> = h n \<epsilon>'" if "\<And>i. i<n \<Longrightarrow> \<epsilon> i = \<epsilon>' i" for n \<epsilon> \<epsilon>'
        using that by (simp add: h_def)
      have dd_cong: "dd n \<epsilon> = dd n \<epsilon>'" if "\<And>i. i<n \<Longrightarrow> \<epsilon> i = \<epsilon>' i" for n \<epsilon> \<epsilon>'
        using that by (metis dd_def DD_def BALL_def h_cong) 
      have [simp]: "h n (cut \<epsilon> less_than n) = h n \<epsilon>" for n \<epsilon>
        by (meson cut_apply h_cong less_than_iff)
      have [simp]: "dd n (cut \<epsilon> less_than n) = dd n \<epsilon>" for n \<epsilon>
        by (meson cut_apply dd_cong less_than_iff)

      define coeff where "coeff \<equiv> wfrec less_than (\<lambda>\<epsilon> n. (dd n \<epsilon> - h n \<epsilon> (w n)) / p n (w n))"
      have coeff_eq: "coeff n = (dd n coeff - h n coeff (w n)) / p n (w n)" for n
        by (simp add: def_wfrec [OF coeff_def])

      have norm_coeff: "norm (coeff n) < 1 / (fact n * q n)" for n
        using dd_in_DD [of n coeff]
        by (simp add: q_gt0 coeff_eq DD_def BALL_def dist_norm norm_minus_commute norm_divide divide_simps)
      have norm_p_bound: "norm (p n z') \<le> q n * (1 + norm z) ^ n" 
          if "dist z z' \<le> 1" for n z z'
      proof (induction n)
        case 0
        then show ?case
          by (auto simp: p_def q_def)
      next
        case (Suc n)
        have "norm z' - norm z \<le> 1"
          by (smt (verit) dist_norm norm_triangle_ineq3 that)
        then have \<section>: "norm (z' - w n) \<le> (1 + norm (w n)) * (1 + norm z)"
          by (simp add: mult.commute add_mono distrib_left norm_triangle_le_diff)
        have "norm (p n z') * norm (z' - w n) \<le> (q n * (1 + norm z) ^ n) * norm (z' - w n)"
          by (metis Suc mult.commute mult_left_mono norm_ge_zero)
        also have "\<dots> \<le> (q n * (1 + norm z) ^ n) * (1 + norm (w n)) * ((1 + norm z))"
          by (smt (verit) "\<section>" Suc mult.assoc mult_left_mono norm_ge_zero)
        also have "\<dots> \<le> q n * (1 + norm (w n)) * ((1 + norm z) * (1 + norm z) ^ n)"
          by auto
        finally show ?case
          by (auto simp: p_def q_def norm_mult simp del: fact_Suc)
      qed

      show ?thesis
      proof
        define hh where "hh \<equiv> \<lambda>z. suminf (\<lambda>i. coeff i * p i z)"
        have "hh holomorphic_on UNIV"
        proof (rule holomorphic_uniform_sequence)
          fix n   \<comment>\<open>Many thanks to Manuel Eberl for suggesting these approach\<close>
          show "h n coeff holomorphic_on UNIV"
            unfolding h_def p_def by (intro holomorphic_intros)
        next
          fix z
          have "uniform_limit (cball z 1) (\<lambda>n. h n coeff) hh sequentially"
            unfolding hh_def h_def
          proof (rule Weierstrass_m_test)
            let ?M = "\<lambda>n. (1 + norm z) ^ n / fact n"
            have "\<exists>N. \<forall>n\<ge>N. B \<le> (1 + real n) / (1 + norm z)" for B
            proof
              show "\<forall>n\<ge>nat \<lceil>B * (1 + norm z)\<rceil>. B \<le> (1 + real n) / (1 + norm z)"
                using norm_ge_zero [of z] by (auto simp: divide_simps simp del: norm_ge_zero)
            qed
            then have L: "liminf (\<lambda>n. ereal ((1 + real n) / (1 + norm z))) = \<infinity>"
              by (simp add: Lim_PInfty flip: liminf_PInfty)
            have "\<forall>\<^sub>F n in sequentially. 0 < (1 + cmod z) ^ n / fact n"
              using norm_ge_zero [of z] by (simp del: norm_ge_zero)
            then show "summable ?M"
              by (rule ratio_test_convergence) (auto simp: add_nonneg_eq_0_iff L)
            fix n z'
            assume "z' \<in> cball z 1"
            then have "norm (coeff n * p n z') \<le> norm (coeff n) * q n * (1 + norm z) ^ n"
              by (simp add: mult.assoc mult_mono norm_mult norm_p_bound)
            also have "\<dots> \<le> (1 / fact n) * (1 + norm z) ^ n"
            proof (rule mult_right_mono)
              show "norm (coeff n) * q n \<le> 1 / fact n"
                using q_gt0 norm_coeff [of n] by (simp add: field_simps)
            qed auto
            also have "\<dots> \<le> ?M n"
              by (simp add: divide_simps)
            finally show "norm (coeff n * p n z') \<le> ?M n" .
          qed
          then show "\<exists>d>0. cball z d \<subseteq> UNIV \<and> uniform_limit (cball z d) (\<lambda>n. h n coeff) hh sequentially"
            using zero_less_one by blast
        qed auto
        then show "hh analytic_on UNIV"
          by (simp add: analytic_on_open)
        have hh_eq_dd: "hh (w n) = dd n coeff" for n
        proof -
          have "hh (w n) = h (Suc n) coeff (w n)"
            unfolding hh_def h_def by (intro suminf_finite) auto
          also have "\<dots> = dd n coeff"
            by (induction n) (auto simp add: p0 h_def p_def coeff_eq [of "Suc _"] coeff_eq [of 0])
          finally show ?thesis .
        qed
        then have "hh (w n) \<in> D" for n
          using DD_def dd_in_DD by fastforce
        then show "inD \<gamma> hh"
          unfolding inD_def by (metis \<eta> bij_betw_iff_bijections comp_apply w_def)
        have "hh (w n) \<noteq> f (\<eta> n) (w n)" for n
          using DD_def dd_in_DD g_def hh_eq_dd by auto
        then show "\<forall>\<beta>\<in>elts \<gamma>. hh \<noteq> f \<beta>"
          by (metis \<eta> bij_betw_imp_surj_on imageE)
      qed
    qed
    with f show ?thesis
      using inj by (rule_tac x="h" in exI) (auto simp: \<Phi>_def inj_on_def)
  qed
  define G where "G \<equiv> \<lambda>f \<gamma>. @h. \<Phi> \<gamma> ((restrict f (elts \<gamma>))(\<gamma>:=h))"
  define f where "f \<equiv> transrec G"
  have \<Phi>f: "\<Phi> \<beta> f" if "\<beta> \<in> elts \<omega>1" for \<beta>
    using that
  proof (induction \<beta> rule: eps_induct)
    case (step \<gamma>)
    then have IH: "\<forall>\<beta>\<in>elts \<gamma>. \<Phi> \<beta> f"
      using Ord_\<omega>1 Ord_trans by blast
    have "f \<gamma> = G f \<gamma>"
      by (metis G_def f_def restrict_apply' restrict_ext transrec)
    moreover have "\<Phi> \<gamma> ((restrict f (elts \<gamma>))(\<gamma> := G f \<gamma>))"
      by (metis ind_step[OF step.prems] G_def IH someI)
    ultimately show ?case 
      by (metis IH \<Phi>_def elts_succ fun_upd_same fun_upd_triv inj_on_restrict_eq restrict_upd)
  qed
  then have anf: "\<And>\<beta>. \<beta> \<in> elts \<omega>1 \<Longrightarrow> f \<beta> analytic_on UNIV"
    and inD: "\<And>\<alpha> \<beta>. \<lbrakk>\<beta> \<in> elts \<omega>1; \<alpha> \<in> elts \<beta>\<rbrakk> \<Longrightarrow> f \<beta> (\<zeta> \<alpha>) \<in> D"
    using \<Phi>_def inD_def by blast+
  have injf: "inj_on f (elts \<omega>1)"
    using \<Phi>f unfolding inj_on_def \<Phi>_def by (metis Ord_\<omega>1 Ord_in_Ord Ord_linear_le in_succ_iff)
  show ?thesis
  proof
    let ?F = "f ` elts \<omega>1"
    have "countable ((\<lambda>f. f z) ` f ` elts \<omega>1)" for z
    proof -
      obtain \<alpha> where \<alpha>: "\<zeta> \<alpha> = z" "\<alpha> \<in> elts \<omega>1" "Ord \<alpha>"
        by (meson Ord_\<omega>1 Ord_in_Ord UNIV_I \<zeta> bij_betw_iff_bijections)
      let ?B = "elts \<omega>1 - elts (succ \<alpha>)"
      have eq: "elts \<omega>1 = elts (succ \<alpha>) \<union> ?B"
        using \<alpha> by (metis Diff_partition Ord_\<omega>1 OrdmemD less_eq_V_def succ_le_iff)
      have "(\<lambda>f. f z) ` f ` ?B \<subseteq> D"
        using \<alpha> inD by clarsimp (meson Ord_\<omega>1 Ord_in_Ord Ord_linear)
      then have "countable ((\<lambda>f. f z) ` f ` ?B)"
        by (meson \<open>countable D\<close> countable_subset)
      moreover have "countable ((\<lambda>f. f z) ` f ` elts (succ \<alpha>))"
        by (simp add: \<alpha> less_\<omega>1_imp_countable)
      ultimately show ?thesis
        using eq by (metis countable_Un_iff image_Un)
    qed
    then show "Wetzel ?F"
      unfolding Wetzel_def by (blast intro: anf)
    show "uncountable ?F"
      using Ord_\<omega>1 countable_iff_less_\<omega>1 countable_image_inj_eq injf by blast
  qed
qed

theorem Erdos_Wetzel: "C_continuum = \<aleph>1 \<longleftrightarrow> (\<exists>F. Wetzel F \<and> uncountable F)"
  by (metis C_continuum_ge Erdos_Wetzel_CH Erdos_Wetzel_nonCH less_V_def)

text \<open>The originally submitted version of this theory included the development of cardinals 
for general Isabelle/HOL sets (as opposed to ZF sets, elements of type V), as well as other 
generally useful library material. From March 2022, that material has been moved to 
the analysis libraries or to @{theory ZFC_in_HOL.General_Cardinals}, as appropriate.\<close>

end
