(*  Title:   Monad_QuasiBorel.thy
    Author:  Michikazu Hirata, Tetsuya Sato, Tokyo Institute of Technology
*)

subsection \<open>The Probability Monad\<close>

theory Monad_QuasiBorel
  imports "Probability_Space_QuasiBorel"
begin

subsubsection \<open> The Probability Monad $P$ \<close>
definition monadP_qbs_Px :: "'a quasi_borel \<Rightarrow> 'a qbs_prob_space set" where
"monadP_qbs_Px X \<equiv> {s. qbs_prob_space_qbs s = X}"

locale in_Px =
  fixes X :: "'a quasi_borel" and s :: "'a qbs_prob_space" 
  assumes in_Px:"s \<in> monadP_qbs_Px X"
begin

lemma qbs_prob_space_X[simp]:
 "qbs_prob_space_qbs s = X"
  using in_Px by(simp add: monadP_qbs_Px_def)

end

locale in_MPx =
  fixes X :: "'a quasi_borel" and \<beta> :: "real \<Rightarrow> 'a qbs_prob_space"
  assumes ex:"\<exists>\<alpha>\<in> qbs_Mx X. \<exists>g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel.
                         \<forall>r. \<beta> r = qbs_prob_space (X,\<alpha>,g r)"
begin

lemma rep_inMPx:
 "\<exists>\<alpha> g. \<alpha> \<in> qbs_Mx X \<and> g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
        \<beta> = (\<lambda>r. qbs_prob_space (X,\<alpha>,g r))"
proof -
  obtain \<alpha> g where hb:
   "\<alpha> \<in> qbs_Mx X" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
        "\<beta> = (\<lambda>r. qbs_prob_space (X,\<alpha>,g r))"
    using ex by auto
  thus ?thesis
    by(auto intro!: exI[where x=\<alpha>] exI[where x=g] simp: hb)
qed

end

definition monadP_qbs_MPx :: "'a quasi_borel \<Rightarrow> (real \<Rightarrow> 'a qbs_prob_space) set" where
"monadP_qbs_MPx X \<equiv> {\<beta>. in_MPx X \<beta>}"

definition monadP_qbs :: "'a quasi_borel \<Rightarrow> 'a qbs_prob_space quasi_borel" where
"monadP_qbs X \<equiv> Abs_quasi_borel (monadP_qbs_Px X, monadP_qbs_MPx X)"

lemma(in qbs_prob) qbs_prob_space_in_Px:
  "qbs_prob_space (X,\<alpha>,\<mu>) \<in> monadP_qbs_Px X"
  using qbs_prob_axioms by(simp add: monadP_qbs_Px_def)

lemma rep_monadP_qbs_Px:
  assumes "s \<in> monadP_qbs_Px X"
  shows "\<exists>\<alpha> \<mu>. s = qbs_prob_space (X, \<alpha>, \<mu>) \<and> qbs_prob X \<alpha> \<mu>"
  using rep_qbs_prob_space' assms in_Px.qbs_prob_space_X
  by(auto simp: monadP_qbs_Px_def)

lemma rep_monadP_qbs_MPx:
  assumes "\<beta> \<in> monadP_qbs_MPx X"
  shows "\<exists>\<alpha> g. \<alpha> \<in> qbs_Mx X \<and> g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
        \<beta> = (\<lambda>r. qbs_prob_space (X,\<alpha>,g r))"
  using assms in_MPx.rep_inMPx
  by(auto simp: monadP_qbs_MPx_def)

lemma qbs_prob_MPx:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
    shows "qbs_prob X \<alpha> (g r)"
  using measurable_space[OF assms(2)]
  by(auto intro!: qbs_prob.intro simp: space_prob_algebra in_Mx_def real_distribution_def real_distribution_axioms_def assms(1))

lemma monadP_qbs_f[simp]: "monadP_qbs_MPx X \<subseteq> UNIV \<rightarrow> monadP_qbs_Px X"
  unfolding monadP_qbs_MPx_def
proof auto
  fix \<beta> r
  assume "in_MPx X \<beta>"
  then obtain \<alpha> g where hb:
   "\<alpha> \<in> qbs_Mx X" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
        "\<beta> = (\<lambda>r. qbs_prob_space (X,\<alpha>,g r))"
    using in_MPx.rep_inMPx by blast
  then interpret qp : qbs_prob X \<alpha> "g r"
    by(simp add: qbs_prob_MPx)
  show "\<beta> r \<in> monadP_qbs_Px X"
    by(simp add: hb(3) qp.qbs_prob_space_in_Px)
qed

lemma monadP_qbs_closed1: "qbs_closed1 (monadP_qbs_MPx X)"
  unfolding monadP_qbs_MPx_def in_MPx_def
  apply(rule qbs_closed1I)
  subgoal for \<alpha> f
    apply auto
    subgoal for \<beta> g
      apply(auto intro!: bexI[where x=\<beta>] bexI[where x="g\<circ>f"])
      done
    done
  done

lemma monadP_qbs_closed2: "qbs_closed2 (monadP_qbs_Px X) (monadP_qbs_MPx X)"
  unfolding qbs_closed2_def
proof
  fix s
  assume "s \<in> monadP_qbs_Px X"
  then obtain \<alpha> \<mu> where h:
   "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_qbs_prob_space'[of s X] monadP_qbs_Px_def by blast
  then interpret qp : qbs_prob X \<alpha> \<mu>
    by simp
  define g :: "real \<Rightarrow> real measure"
    where "g \<equiv> (\<lambda>_. \<mu>)"
  have "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
    using h prob_algebra_real_prob_measure[of \<mu>]
    by(simp add: qbs_prob_def g_def)
  thus "(\<lambda>r. s) \<in> monadP_qbs_MPx X"
    by(auto intro!: bexI[where x=\<alpha>] bexI[where x=g] simp: monadP_qbs_MPx_def in_MPx_def g_def h)
qed

lemma monadP_qbs_closed3: "qbs_closed3 (monadP_qbs_MPx (X :: 'a quasi_borel))"
proof(rule qbs_closed3I)
  fix P :: "real \<Rightarrow> nat"
  fix Fi
  assume "\<And>i. P -` {i} \<in> sets real_borel"
  then have HP_mble[measurable] : "P \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
    by (simp add: separate_measurable)
  assume "\<And>i :: nat. Fi i \<in> monadP_qbs_MPx X"
  then have "\<forall>i. \<exists>\<alpha>i. \<exists>gi. \<alpha>i \<in> qbs_Mx X \<and> gi \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
                    Fi i = (\<lambda>r. qbs_prob_space (X, \<alpha>i, gi r))"
    using in_MPx.rep_inMPx[of X] by(simp add: monadP_qbs_MPx_def)
  hence "\<exists>\<alpha>. \<forall>i. \<exists>gi. \<alpha> i \<in> qbs_Mx X \<and> gi \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
                    Fi i = (\<lambda>r. qbs_prob_space (X, \<alpha> i, gi r))"
    by(rule choice)
  then obtain \<alpha> :: "nat \<Rightarrow> real \<Rightarrow> _" where
       "\<forall>i. \<exists>gi. \<alpha> i \<in> qbs_Mx X \<and> gi \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
                     Fi i = (\<lambda>r. qbs_prob_space (X, \<alpha> i, gi r))"
    by auto
  hence  "\<exists>g. \<forall>i. \<alpha> i \<in> qbs_Mx X \<and> g i \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel \<and>
                  Fi i = (\<lambda>r. qbs_prob_space (X, \<alpha> i, g i r))"
    by(rule choice)
  then obtain g :: "nat \<Rightarrow> real \<Rightarrow> real measure" where 
       H0: "\<And>i. \<alpha> i \<in> qbs_Mx X" "\<And>i. g i \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
           "\<And>i. Fi i = (\<lambda>r. qbs_prob_space (X, \<alpha> i, g i r))"
    by blast
  hence LHS: "(\<lambda>r. Fi (P r) r) = (\<lambda>r. qbs_prob_space (X, \<alpha> (P r), g (P r) r))"
    by auto

  \<comment> \<open> Since \<open>\<nat>\<times>\<real>\<close> is standard, we have measurable functions
        \<open>nat_real.f \<in> \<nat> \<Otimes>\<^sub>M \<real> \<rightarrow>\<^sub>M \<real>\<close> and \<open>nat_real.g \<in> \<real> \<rightarrow>\<^sub>M \<nat> \<Otimes>\<^sub>M \<real>\<close>
       such that @{thm nat_real.gf_comp_id'(1)}. \<close>
       
  \<comment> \<open> The proof is divided into 3 steps.
       \begin{enumerate}
       \item  Let \<open>\<alpha>'' = uncurry \<alpha> \<circ> nat_real.g\<close>. Then \<open>\<alpha>'' \<in> qbs_Mx X\<close>.
       \item Let \<open>g'' = G(nat_real.f) \<circ> (\<lambda>r. \<delta>\<^sub>P\<^sub>(\<^sub>r\<^sub>) \<Otimes>\<^sub>M g\<^sub>P\<^sub>(\<^sub>r\<^sub>) r\<close>.
               Then \<open>g''\<close> is \<open>\<real>\<close>/\<open>G(\<real>)\<close> measurable. 
       \item Show that \<open>(\<lambda>r. Fi (P r) r) = (\<lambda>r. qbs_prob_space (X, \<alpha>'', g'' r))\<close>.
       \end{enumerate}\<close>

  \<comment> \<open> Step 1.\<close>
  define \<alpha>' :: "nat \<times> real \<Rightarrow> 'a"
    where "\<alpha>' \<equiv> case_prod \<alpha>"
  define \<alpha>'' :: "real \<Rightarrow> 'a"
    where "\<alpha>'' \<equiv> \<alpha>' \<circ> nat_real.g"

  have \<alpha>_morp: "\<alpha> \<in> \<nat>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<real>\<^sub>Q X"
    using qbs_Mx_is_morphisms[of X] H0(1)
    by(auto intro!: nat_qbs_morphism)
  hence \<alpha>'_morp: "\<alpha>' \<in> \<nat>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q  \<rightarrow>\<^sub>Q X"
    unfolding \<alpha>'_def
    by(intro uncurry_preserves_morphisms)
  hence [measurable]:"\<alpha>' \<in> nat_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M qbs_to_measure X"
    using l_preserves_morphisms[of "\<nat>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q" X]
    by(auto simp add: r_preserves_product)
  have H_Mx:"\<alpha>'' \<in> qbs_Mx X"
    unfolding \<alpha>''_def
    using qbs_morphism_comp[OF real.qbs_morphism_measurable_intro[OF nat_real.g_meas,simplified r_preserves_product] \<alpha>'_morp] qbs_Mx_is_morphisms[of X]
    by simp


  \<comment> \<open> Step 2.\<close>
  define g' :: "real \<Rightarrow> (nat \<times> real) measure"
    where "g' \<equiv> (\<lambda>r. return nat_borel (P r) \<Otimes>\<^sub>M g (P r) r)"
  define g'' :: "real \<Rightarrow> real measure"
    where "g'' \<equiv> (\<lambda>M. distr M real_borel nat_real.f) \<circ> g'"

  have [measurable]:"(\<lambda>nr. g (fst nr) (snd nr)) \<in> nat_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
    using measurable_pair_measure_countable1[of "UNIV :: nat set" "\<lambda>nr. g (fst nr) (snd nr)",simplified,OF H0(2)] measurable_cong_sets[OF sets_pair_measure_cong[of nat_borel "count_space UNIV" real_borel real_borel,OF sets_borel_eq_count_space refl] refl,of "prob_algebra real_borel"]
    by auto    
  hence [measurable]:"(\<lambda>r. g (P r) r) \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
  proof -
    have "(\<lambda>r. g (P r) r) = (\<lambda>nr. g (fst nr) (snd nr)) \<circ> (\<lambda>r. (P r, r))" by auto
    also have "... \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      by simp
    finally show ?thesis .
  qed
  have g'_mble[measurable]:"g' \<in> real_borel \<rightarrow>\<^sub>M prob_algebra (nat_borel \<Otimes>\<^sub>M real_borel)"
    unfolding g'_def by simp
  have H_mble: "g'' \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
    unfolding g''_def by simp

  \<comment> \<open> Step 3.\<close>
  have H_equiv: 
       "qbs_prob_space (X, \<alpha> (P r), g (P r) r) = qbs_prob_space (X, \<alpha>'', g'' r)" for r
  proof -
    interpret pqp: pair_qbs_prob X "\<alpha> (P r)" "g (P r) r" X \<alpha>'' "g'' r"
      using qbs_prob_MPx[OF H0(1,2)] measurable_space[OF H_mble,of r] space_prob_algebra[of real_borel] H_Mx
      by (simp add: pair_qbs_prob.intro qbs_probI)
    interpret pps: pair_prob_space "return nat_borel (P r)" "g (P r) r"
      using prob_space_return[of "P r" nat_borel]
      by(simp add: pair_prob_space_def pair_sigma_finite_def prob_space_imp_sigma_finite)
    have [measurable_cong]: "sets (return nat_borel (P r)) = sets nat_borel"
                            "sets (g' r) = sets (nat_borel \<Otimes>\<^sub>M real_borel)"
      using measurable_space[OF g'_mble,of r] space_prob_algebra by auto
    show "qbs_prob_space (X, \<alpha> (P r), g (P r) r) = qbs_prob_space (X, \<alpha>'', g'' r)"
    proof(rule pqp.qbs_prob_space_eq4)
      fix f
      assume [measurable]:"f \<in> qbs_to_measure X  \<rightarrow>\<^sub>M ennreal_borel"
      show "(\<integral>\<^sup>+ x. f (\<alpha> (P r) x) \<partial>g (P r) r) = (\<integral>\<^sup>+ x. f (\<alpha>'' x) \<partial>g'' r)"
           (is "?lhs = ?rhs")
      proof -
        have "?lhs = (\<integral>\<^sup>+s. f (\<alpha>' ((P r),s)) \<partial> (g (P r) r))"
          by(simp add: \<alpha>'_def)
        also have "... = (\<integral>\<^sup>+s. (\<integral>\<^sup>+i. f (\<alpha>' (i, s)) \<partial> (return nat_borel (P r)))  \<partial> (g (P r) r))"
          by(auto intro!: nn_integral_cong simp: nn_integral_return[of "P r" nat_borel])
        also have "... = (\<integral>\<^sup>+k. (f \<circ> \<alpha>') k \<partial> ((return nat_borel (P r)) \<Otimes>\<^sub>M (g (P r) r)))"
          by(auto intro!: pps.nn_integral_snd)
        also have "... = (\<integral>\<^sup>+k. f (\<alpha>' k) \<partial> (g' r))"
          by(simp add: g'_def)
        also have "... = (\<integral>\<^sup>+x. f x \<partial> (distr (g' r) (qbs_to_measure X) \<alpha>'))"
          by(simp add: nn_integral_distr)
        also have "... = (\<integral>\<^sup>+x. f x \<partial> (distr (g'' r) (qbs_to_measure X) \<alpha>''))"
          by(simp add: distr_distr comp_def g''_def \<alpha>''_def)
        also have "... = ?rhs"
          by(simp add: nn_integral_distr)
        finally show ?thesis .
      qed
    qed simp
  qed

  have "\<forall>r. Fi (P r) r = qbs_prob_space (X, \<alpha>'', g'' r)"
    by (metis H_equiv LHS)
  thus "(\<lambda>r. Fi (P r) r) \<in> monadP_qbs_MPx X"
    using H_mble H_Mx by(auto simp add: monadP_qbs_MPx_def in_MPx_def)
qed

lemma monadP_qbs_correct: "Rep_quasi_borel (monadP_qbs X) = (monadP_qbs_Px X, monadP_qbs_MPx X)"
  by(auto intro!: Abs_quasi_borel_inverse monadP_qbs_f simp: monadP_qbs_closed2 monadP_qbs_closed1 monadP_qbs_closed3 monadP_qbs_def)

lemma monadP_qbs_space[simp] : "qbs_space (monadP_qbs X) = monadP_qbs_Px X"
  by(simp add: qbs_space_def monadP_qbs_correct)

lemma monadP_qbs_Mx[simp] : "qbs_Mx (monadP_qbs X) = monadP_qbs_MPx X"
  by(simp add: qbs_Mx_def monadP_qbs_correct)

lemma monadP_qbs_empty_iff:
 "qbs_space X = {} \<longleftrightarrow> qbs_space (monadP_qbs X) = {}"
proof auto
  fix x
  assume 1:"qbs_space X = {}"
           "x \<in> monadP_qbs_Px X"
  then obtain \<alpha> \<mu> where "qbs_prob X \<alpha> \<mu>"
    using rep_monadP_qbs_Px by blast
  thus False
    using empty_quasi_borel_iff[of X] qbs_empty_not_qbs_prob[of \<alpha> \<mu>] 1(1)
    by auto
next
  fix x
  assume 1:"monadP_qbs_Px X = {}"
           "x \<in> qbs_space X"
  then interpret qp: qbs_prob X "\<lambda>r. x" "return real_borel 0"
    by(auto intro!: qbs_probI prob_space_return)
  have "qbs_prob_space (X,\<lambda>r. x,return real_borel 0) \<in> monadP_qbs_Px X"
    by(simp add: monadP_qbs_Px_def)
  thus False
    by(simp add: 1)
qed

text \<open> If \<open>\<beta> \<in> MPx\<close>, there exists \<open>X\<close> \<open>\<alpha>\<close> \<open>g\<close> s.t.\<open>\<beta> r = [X,\<alpha>,g r]\<close>.
       We define a function which picks \<open>X\<close> \<open>\<alpha>\<close> \<open>g\<close> from \<open>\<beta> \<in> MPx\<close>.\<close>
definition rep_monadP_qbs_MPx :: "(real \<Rightarrow> 'a qbs_prob_space) \<Rightarrow> 'a quasi_borel \<times> (real \<Rightarrow> 'a) \<times> (real \<Rightarrow> real measure)" where
"rep_monadP_qbs_MPx \<beta> \<equiv> let X = qbs_prob_space_qbs (\<beta> undefined);
                            \<alpha>g = (SOME k. (fst k) \<in> qbs_Mx X \<and> (snd k) \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel
                                          \<and> \<beta> = (\<lambda>r. qbs_prob_space (X,fst k,snd k r)))
                         in (X,\<alpha>g)"

lemma qbs_prob_measure_measurable[measurable]:
 "qbs_prob_measure \<in> qbs_to_measure (monadP_qbs (X :: 'a quasi_borel)) \<rightarrow>\<^sub>M prob_algebra (qbs_to_measure X)"
proof(rule qbs_morphism_dest,rule qbs_morphismI,simp)
  fix \<beta>
  assume "\<beta> \<in> monadP_qbs_MPx X"
  then obtain \<alpha> g where hb:
  "\<alpha> \<in> qbs_Mx X" "\<beta> = (\<lambda>r. qbs_prob_space (X, \<alpha>, g r))"
   and g[measurable]: "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"  
    using in_MPx.rep_inMPx[of X \<beta>] monadP_qbs_MPx_def by blast
  have "qbs_prob_measure \<circ> \<beta> = (\<lambda>r. distr (g r) (qbs_to_measure X) \<alpha>)"
  proof 
    fix r
    interpret qp : qbs_prob X \<alpha> "g r"
      using qbs_prob_MPx[OF hb(1) g]  by simp
    show "(qbs_prob_measure \<circ> \<beta>) r = distr (g r) (qbs_to_measure X) \<alpha>"
      by(simp add: hb(2))
  qed
  also have "... \<in> real_borel \<rightarrow>\<^sub>M prob_algebra (qbs_to_measure X) "
    using hb by simp
  finally show "qbs_prob_measure \<circ> \<beta> \<in> real_borel \<rightarrow>\<^sub>M prob_algebra (qbs_to_measure X)" .
qed

lemma qbs_l_inj:
  "inj_on qbs_prob_measure (monadP_qbs_Px X)"
  apply standard
  apply (unfold monadP_qbs_Px_def)
  apply simp
  apply transfer
  apply (auto simp: qbs_prob_eq_def qbs_prob_t_measure_def)
  done

lemma qbs_prob_measure_measurable'[measurable]:
 "qbs_prob_measure \<in> qbs_to_measure (monadP_qbs (X :: 'a quasi_borel)) \<rightarrow>\<^sub>M subprob_algebra (qbs_to_measure X)"
  by(auto simp: measurable_prob_algebraD)

subsubsection \<open> Return \<close>
definition qbs_return :: "['a quasi_borel, 'a] \<Rightarrow> 'a qbs_prob_space" where
"qbs_return X x \<equiv> qbs_prob_space (X,\<lambda>r. x,Eps real_distribution)"

lemma(in real_distribution) qbs_return_qbs_prob:
  assumes "x \<in> qbs_space X"
  shows "qbs_prob X (\<lambda>r. x) M"
  using assms 
  by(simp add: qbs_prob_def in_Mx_def real_distribution_axioms)

lemma(in real_distribution) qbs_return_computation :
  assumes "x \<in> qbs_space X"
  shows "qbs_return X x = qbs_prob_space (X,\<lambda>r. x,M)"
  unfolding qbs_return_def
proof(rule someI2[where a=M])
  fix N
  assume "real_distribution N"
  then interpret pqp: pair_qbs_prob X "\<lambda>r. x" N X "\<lambda>r. x" M
    by(simp_all add: pair_qbs_prob_def real_distribution_axioms real_distribution.qbs_return_qbs_prob[OF _ assms])
  show "qbs_prob_space (X, \<lambda>r. x, N) = qbs_prob_space (X, \<lambda>r. x, M)"
    by(auto intro!: pqp.qbs_prob_space_eq simp: distr_const[of x "qbs_to_measure X"] assms)
qed (rule real_distribution_axioms)

lemma qbs_return_morphism:
  "qbs_return X \<in> X \<rightarrow>\<^sub>Q monadP_qbs X"
proof -
  interpret rr : real_distribution "return real_borel 0"
    by(simp add: real_distribution_def real_distribution_axioms_def prob_space_return)
  show ?thesis
  proof(rule qbs_morphismI,simp)
    fix \<alpha>
    assume h:"\<alpha> \<in> qbs_Mx X"
    then have h':"\<And>l:: real. \<alpha> l \<in> qbs_space X"
      by auto
    have "\<And>l. (qbs_return X \<circ> \<alpha>) l = qbs_prob_space (X, \<alpha>, return real_borel l)"
    proof -
      fix l
      interpret pqp: pair_qbs_prob X "\<lambda>r. \<alpha> l" "return real_borel 0" X \<alpha> "return real_borel l"
        using h' by(simp add: pair_qbs_prob_def qbs_prob_def in_Mx_def h real_distribution_def prob_space_return real_distribution_axioms_def)
      have "(qbs_return X \<circ> \<alpha>) l = qbs_prob_space (X,\<lambda>r. \<alpha> l,return real_borel 0)"
        using rr.qbs_return_computation[OF h'[of l]] by simp
      also have "... = qbs_prob_space (X, \<alpha>, return real_borel l)"
        by(auto intro!: pqp.qbs_prob_space_eq simp: distr_return)
      finally show "(qbs_return X \<circ> \<alpha>) l = qbs_prob_space (X, \<alpha>, return real_borel l)" .
    qed
    thus "qbs_return X \<circ> \<alpha> \<in> monadP_qbs_MPx X"
      by(auto intro!: bexI[where x="\<alpha>"] bexI[where x="\<lambda>l. return real_borel l"] simp: h  monadP_qbs_MPx_def in_MPx_def)
  qed
qed

lemma qbs_return_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>x. qbs_return Y (f x)) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  using qbs_morphism_comp[OF assms(1) qbs_return_morphism[of Y]]
  by (simp add: comp_def)

subsubsection \<open>Bind\<close>
definition qbs_bind :: "'a qbs_prob_space \<Rightarrow> ('a \<Rightarrow> 'b qbs_prob_space)  \<Rightarrow> 'b qbs_prob_space" where
"qbs_bind s f \<equiv> (let (qbsx,\<alpha>,\<mu>) = rep_qbs_prob_space s;
                      (qbsy,\<beta>,g) = rep_monadP_qbs_MPx (f \<circ> \<alpha>) 
                     in qbs_prob_space (qbsy,\<beta>,\<mu> \<bind> g))"

adhoc_overloading Monad_Syntax.bind qbs_bind

lemma(in qbs_prob) qbs_bind_computation:
  assumes"s = qbs_prob_space (X,\<alpha>,\<mu>)"
         "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
         "\<beta> \<in> qbs_Mx Y"
   and [measurable]: "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      and "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y,\<beta>, g r))"
    shows "qbs_prob Y \<beta> (\<mu> \<bind> g)"
          "s \<bind> f = qbs_prob_space (Y,\<beta>,\<mu> \<bind> g)"
proof -
  interpret qp_bind: qbs_prob Y \<beta> "\<mu> \<bind> g"
    using assms(3,4) space_prob_algebra[of real_borel] measurable_space[OF assms(4)] events_eq_borel measurable_cong_sets[OF events_eq_borel refl,of "subprob_algebra real_borel"] measurable_prob_algebraD[OF assms(4)]
    by(auto intro!: prob_space_bind[of g real_borel] simp: qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def)
  show "qbs_prob Y \<beta> (\<mu> \<bind> g)"
    by (rule qp_bind.qbs_prob_axioms)
  show "s \<bind> f = qbs_prob_space (Y, \<beta>, \<mu> \<bind> g)"
    apply(simp add: assms(1) qbs_bind_def rep_qbs_prob_space_def qbs_prob_space.rep_def)
    apply(rule someI2[where a= "(X, \<alpha>, \<mu>)"])
  proof auto
    fix X' \<alpha>' \<mu>'
    assume h':"(X',\<alpha>',\<mu>') \<in> Rep_qbs_prob_space (qbs_prob_space (X, \<alpha>, \<mu>))"
    from if_in_Rep[OF this] interpret pqp1: pair_qbs_prob X \<alpha> \<mu> X' \<alpha>' \<mu>'
      by(simp add: pair_qbs_prob_def qbs_prob_axioms)
    have h_eq: "qbs_prob_space (X, \<alpha>, \<mu>) = qbs_prob_space (X',\<alpha>',\<mu>')"
      using if_in_Rep(3)[OF h'] by (simp add: qbs_prob_space_eq)
    note [simp] = if_in_Rep(1)[OF h']
    then obtain \<beta>' g' where hb':
     "\<beta>' \<in> qbs_Mx Y" "g' \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
       "f \<circ> \<alpha>' = (\<lambda>r. qbs_prob_space (Y, \<beta>', g' r))"
      using in_MPx.rep_inMPx[of Y "f \<circ> \<alpha>'"] qbs_morphismE(3)[OF assms(2),of \<alpha>'] pqp1.qp2.qbs_prob_axioms[simplified qbs_prob_def in_Mx_def]
      by(auto simp: monadP_qbs_MPx_def)
    note [measurable] = hb'(2)
    have [simp]:"\<And>r. qbs_prob_space_qbs (f (\<alpha>' r)) = Y"
      subgoal for r
        using fun_cong[OF hb'(3)] qbs_prob.qbs_prob_space_qbs_computation[OF qbs_prob_MPx[OF hb'(1,2),of r]]
        by simp
      done
    show "(case rep_monadP_qbs_MPx (\<lambda>a. f (\<alpha>' a)) of (qbsy, \<beta>, g) \<Rightarrow> qbs_prob_space (qbsy, \<beta>, \<mu>' \<bind> g)) =
                 qbs_prob_space (Y, \<beta>, \<mu> \<bind> g)"
      unfolding rep_monadP_qbs_MPx_def Let_def
    proof(rule someI2[where a="(\<beta>',g')"],auto simp: hb'[simplified comp_def])
      fix \<alpha>'' g''
      assume h'':"\<alpha>'' \<in> qbs_Mx Y"
                 "g'' \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
                 "(\<lambda>r. qbs_prob_space (Y, \<beta>', g' r)) = (\<lambda>r. qbs_prob_space (Y, \<alpha>'', g'' r))"
      then interpret pqp2: pair_qbs_prob Y \<alpha>'' "\<mu>' \<bind> g''" Y \<beta> "\<mu> \<bind> g"
        using space_prob_algebra[of real_borel] measurable_space[OF h''(2)] events_eq_borel measurable_cong_sets[OF events_eq_borel refl,of "subprob_algebra real_borel"] measurable_prob_algebraD[OF h''(2)] h''(3)
        by (meson pair_qbs_prob_def in_Mx_def pqp1.qp2.real_distribution_axioms prob_algebra_real_prob_measure prob_space_bind' qbs_probI qbs_prob_def qp_bind.qbs_prob_axioms sets_bind')
      note [measurable] = h''(2)
      have [measurable]:"f \<in> qbs_to_measure X \<rightarrow>\<^sub>M qbs_to_measure (monadP_qbs Y)"
        using assms(2) l_preserves_morphisms by auto
      show "qbs_prob_space (Y, \<alpha>'', \<mu>' \<bind> g'') = qbs_prob_space (Y, \<beta>, \<mu> \<bind> g)"
      proof(rule pqp2.qbs_prob_space_eq)
        show "distr (\<mu>' \<bind> g'') (qbs_to_measure Y) \<alpha>'' = distr (\<mu> \<bind> g) (qbs_to_measure Y) \<beta>"
             (is "?lhs = ?rhs")
        proof -
          have "?lhs = \<mu>' \<bind> (\<lambda>x. distr (g'' x) (qbs_to_measure Y) \<alpha>'')"
            by(auto intro!: distr_bind[where K=real_borel] simp: measurable_prob_algebraD)
          also have "... = \<mu>' \<bind> (\<lambda>x. qbs_prob_measure (qbs_prob_space (Y,\<alpha>'',g'' x)))"
            by(auto intro!: bind_cong simp: qbs_prob_MPx[OF h''(1,2)] qbs_prob.qbs_prob_measure_computation)
          also have "... = \<mu>' \<bind> (\<lambda>x. (qbs_prob_measure  ((f \<circ> \<alpha>') x)))"
            by(simp add: hb'(3) h''(3))
          also have "... = \<mu>' \<bind> (\<lambda>x. (qbs_prob_measure \<circ> f)  (\<alpha>' x))"
            by(simp add: comp_def)
          also have "... = distr \<mu>' (qbs_to_measure X) \<alpha>' \<bind> qbs_prob_measure \<circ> f"
            by(rule bind_distr[where K="qbs_to_measure Y",symmetric],auto)
          also have "... = distr \<mu> (qbs_to_measure X) \<alpha> \<bind> qbs_prob_measure \<circ> f"
            using pqp1.qbs_prob_space_eq_inverse(1)[OF h_eq]
            by(simp add: qbs_prob_eq_def)
          also have "... = \<mu> \<bind> (\<lambda>x. (qbs_prob_measure \<circ> f)  (\<alpha> x))"
            by(rule bind_distr[where K="qbs_to_measure Y"],auto)
          also have "... = \<mu> \<bind> (\<lambda>x. (qbs_prob_measure  ((f \<circ> \<alpha>) x)))"
            by(simp add: comp_def)
          also have "... = \<mu> \<bind> (\<lambda>x. qbs_prob_measure (qbs_prob_space (Y,\<beta>,g x)))"
            by(auto simp: assms(5))
          also have "... = \<mu> \<bind> (\<lambda>x. distr (g x) (qbs_to_measure Y) \<beta>)"
            by(auto intro!: bind_cong simp: qbs_prob_MPx[OF assms(3)] qbs_prob.qbs_prob_measure_computation)
          also have "... = ?rhs"
            by(auto intro!: distr_bind[where K=real_borel,symmetric] simp: measurable_prob_algebraD)
          finally show ?thesis .
        qed
      qed simp
    qed
  qed (rule in_Rep)
qed

lemma qbs_bind_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  shows "(\<lambda>x. x \<bind> f) \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
proof(rule qbs_morphismI,simp)
  fix \<beta>
  assume "\<beta> \<in> monadP_qbs_MPx X"
  then obtain \<alpha> g where hb:
   "\<alpha> \<in> qbs_Mx X" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "\<beta> = (\<lambda>r. qbs_prob_space (X, \<alpha>, g r))"
    using rep_monadP_qbs_MPx by blast
  obtain \<gamma> g' where hc:
   "\<gamma> \<in> qbs_Mx Y" "g' \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "f \<circ> \<alpha> = (\<lambda>r. qbs_prob_space (Y, \<gamma>, g' r))"
    using rep_monadP_qbs_MPx[of "f \<circ> \<alpha>" Y] qbs_morphismE(3)[OF assms hb(1),simplified]
    by auto
  note [measurable] = hb(2) hc(2)
  show "(\<lambda>x. x \<bind> f) \<circ> \<beta> \<in> monadP_qbs_MPx Y"
  proof -
    have "(\<lambda>x. x \<bind> f) \<circ> \<beta> = (\<lambda>r. \<beta> r \<bind> f)"
      by auto
    also have "... \<in> monadP_qbs_MPx Y"
      unfolding monadP_qbs_MPx_def in_MPx_def
      by(auto intro!: bexI[where x="\<gamma>"] bexI[where x="\<lambda>r. g r \<bind> g'"] simp: hc(1) hb(3) qbs_prob.qbs_bind_computation[OF qbs_prob_MPx[OF hb(1,2)] _ assms hc])
    finally show ?thesis .
  qed
qed

lemma qbs_return_comp:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "(qbs_return X \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (X,\<alpha>,return real_borel r))"
proof
  fix r
  interpret pqp: pair_qbs_prob X "\<lambda>k. \<alpha> r" "return real_borel 0" X \<alpha> "return real_borel r"
    by(simp add: assms qbs_Mx_to_X(2)[OF assms] pair_qbs_prob_def qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def prob_space_return)
  show "(qbs_return X \<circ> \<alpha>) r = qbs_prob_space (X, \<alpha>, return real_borel r)"
    by(auto intro!: pqp.qbs_prob_space_eq simp: distr_return pqp.qp1.qbs_return_computation qbs_Mx_to_X(2)[OF assms])
qed

lemma qbs_bind_return':
  assumes "x \<in> monadP_qbs_Px X"
  shows "x \<bind> qbs_return X = x"
proof -
  obtain \<alpha> \<mu> where h1:"qbs_prob X \<alpha> \<mu>" "x = qbs_prob_space (X, \<alpha>, \<mu>)"
    using assms rep_monadP_qbs_Px by blast
  then interpret qp: qbs_prob X \<alpha> \<mu>
    by simp
  show ?thesis
    using qp.qbs_bind_computation[OF h1(2) qbs_return_morphism _ measurable_return_prob_space qbs_return_comp[OF qp.in_Mx]]
    by(simp add: h1(2) bind_return'' prob_space_return qbs_probI)
qed

lemma qbs_bind_return:
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
      and "x \<in> qbs_space X"
    shows "qbs_return X x \<bind> f = f x"
proof -
  have "f x \<in> monadP_qbs_Px Y"
    using assms by auto
  then obtain \<beta> \<mu> where hf:"qbs_prob Y \<beta> \<mu>" "f x = qbs_prob_space (Y, \<beta>, \<mu>)"
    using rep_monadP_qbs_Px by blast
  then interpret rd: real_distribution "return real_borel 0"
    by(simp add: qbs_prob_def prob_space_return real_distribution_def real_distribution_axioms_def)
  interpret rd': real_distribution \<mu>
    using hf(1) by(simp add: qbs_prob_def)
  interpret qp: qbs_prob X "\<lambda>r. x" "return real_borel 0"
    using assms(2) by(auto simp: qbs_prob_def in_Mx_def rd.real_distribution_axioms)
  show ?thesis
    by(auto intro!: qp.qbs_bind_computation(2)[OF rd.qbs_return_computation[OF assms(2)] assms(1) _ measurable_const[of \<mu>],of \<beta>,simplified bind_const'[OF rd.prob_space_axioms rd'.subprob_space_axioms]]
              simp: hf[simplified qbs_prob_def in_Mx_def] prob_algebra_real_prob_measure)
qed

lemma qbs_bind_assoc:
  assumes "s \<in> monadP_qbs_Px X"
          "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
      and "g \<in> Y \<rightarrow>\<^sub>Q monadP_qbs Z"
   shows "s \<bind> (\<lambda>x. f x \<bind> g) = (s \<bind> f) \<bind> g"
proof -
  obtain \<alpha> \<mu> where H0:"qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using assms rep_monadP_qbs_Px by blast
  then have "f \<circ> \<alpha> \<in> monadP_qbs_MPx Y"
    using assms(2) by(auto simp: qbs_prob_def in_Mx_def)
  from rep_monadP_qbs_MPx[OF this] obtain \<beta> g1 where H1:
   "\<beta> \<in> qbs_Mx Y" "g1 \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   " (f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g1 r))"
    by auto
  hence "g \<circ> \<beta> \<in> monadP_qbs_MPx Z"
    using assms by(simp add: qbs_morphism_def)
  from rep_monadP_qbs_MPx[OF this] obtain \<gamma> g2 where H2:
   "\<gamma> \<in> qbs_Mx Z" "g2 \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(g \<circ> \<beta>) = (\<lambda>r. qbs_prob_space (Z, \<gamma>, g2 r))"
    by auto
  note [measurable] = H1(2) H2(2)
  interpret rd: real_distribution \<mu>
    using H0(1) by(simp add: qbs_prob_def)
  have LHS: "(s \<bind> f) \<bind> g = qbs_prob_space (Z, \<gamma>, \<mu> \<bind> g1 \<bind> g2)"
    by(rule qbs_prob.qbs_bind_computation(2)[OF qbs_prob.qbs_bind_computation[OF H0 assms(2) H1] assms(3) H2])
  have RHS: "s \<bind> (\<lambda>x. f x \<bind> g) =  qbs_prob_space (Z, \<gamma>, \<mu> \<bind> (\<lambda>x. g1 x \<bind> g2))"
    apply(auto intro!: qbs_prob.qbs_bind_computation[OF H0 qbs_morphism_comp[OF assms(2) qbs_bind_morphism'[OF assms(3)],simplified comp_def]]
                 simp: real_distribution_def real_distribution_axioms_def qbs_prob_def qbs_prob_MPx[OF H2(1,2),simplified qbs_prob_def] sets_bind'[OF measurable_space[OF H1(2)] H2(2)] prob_space_bind'[OF measurable_space[OF H1(2)] H2(2)] measurable_space[OF H2(2)] space_prob_algebra[of real_borel] H2(1))
  proof
    fix r
    show "((\<lambda>x. f x \<bind> g) \<circ> \<alpha>) r = qbs_prob_space (Z, \<gamma>, g1 r \<bind> g2)" (is "?lhs = ?rhs") for r
      by(auto intro!: qbs_prob.qbs_bind_computation(2)[of Y \<beta>]
                simp: qbs_prob_MPx[OF H1(1,2),of r] assms(3) H2 fun_cong[OF H1(3),simplified comp_def])
  qed
  have ba: "\<mu> \<bind> g1 \<bind> g2 = \<mu> \<bind> (\<lambda>x. g1 x \<bind> g2)"
    by(auto intro!: bind_assoc[where N=real_borel and R=real_borel] simp: measurable_prob_algebraD)
  show ?thesis
    by(simp add: LHS RHS ba)
qed

lemma qbs_bind_cong:
  assumes "s \<in> monadP_qbs_Px X"
          "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    shows "s \<bind> f = s \<bind> g"
proof -
  obtain \<alpha> \<mu> where h0:
  "qbs_prob X \<alpha> \<mu>"  "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then have "f \<circ> \<alpha> \<in> monadP_qbs_MPx Y"
    using assms(3) h0(1) by(auto simp: qbs_prob_def in_Mx_def)
  from rep_monadP_qbs_MPx[OF this] obtain \<gamma> k where h1:
   "\<gamma> \<in> qbs_Mx Y" "k \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<gamma>, k r))"
    by auto
  have hg:"g \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    using qbs_morphism_cong[OF assms(2,3)] by simp
  have hgs: "f \<circ> \<alpha> = g \<circ> \<alpha>"
    using h0(1) assms(2) by(force simp: qbs_prob_def in_Mx_def)

  show ?thesis
    by(simp add: qbs_prob.qbs_bind_computation(2)[OF h0 assms(3) h1]
                 qbs_prob.qbs_bind_computation(2)[OF h0 hg h1[simplified hgs]])
qed

subsubsection \<open> The Functorial Action $P(f)$\<close>
definition monadP_qbs_Pf :: "['a quasi_borel, 'b quasi_borel,'a \<Rightarrow> 'b,'a qbs_prob_space] \<Rightarrow> 'b qbs_prob_space" where
"monadP_qbs_Pf _ Y f sx \<equiv> sx \<bind> qbs_return Y \<circ> f"

lemma monadP_qbs_Pf_morphism:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "monadP_qbs_Pf X Y f \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
  unfolding monadP_qbs_Pf_def
  by(rule qbs_bind_morphism'[OF qbs_morphism_comp[OF assms qbs_return_morphism]])

lemma(in qbs_prob) monadP_qbs_Pf_computation:
  assumes "s = qbs_prob_space (X,\<alpha>,\<mu>)"
      and "f \<in> X \<rightarrow>\<^sub>Q Y"
    shows "qbs_prob Y (f \<circ> \<alpha>) \<mu>"
      and "monadP_qbs_Pf X Y f s = qbs_prob_space (Y,f \<circ> \<alpha>,\<mu>)"
   by(auto intro!: qbs_bind_computation[OF assms(1) qbs_morphism_comp[OF assms(2) qbs_return_morphism],of "f \<circ> \<alpha>" "return real_borel" ,simplified bind_return''[OF M_is_borel]]
             simp: monadP_qbs_Pf_def qbs_return_comp[OF qbs_morphismE(3)[OF assms(2) in_Mx],simplified comp_assoc[symmetric]] qbs_morphismE(3)[OF assms(2) in_Mx] prob_space_return)

text \<open> We show that P is a functor i.e. P preserves identity and composition.\<close>
lemma monadP_qbs_Pf_id:
  assumes "s \<in> monadP_qbs_Px X"
  shows "monadP_qbs_Pf X X id s = s"
  using qbs_bind_return'[OF assms] by(simp add: monadP_qbs_Pf_def)

lemma monadP_qbs_Pf_comp:
  assumes "s \<in> monadP_qbs_Px X"
          "f \<in> X \<rightarrow>\<^sub>Q Y"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z" 
    shows "((monadP_qbs_Pf Y Z g) \<circ> (monadP_qbs_Pf X Y f)) s = monadP_qbs_Pf X Z (g \<circ> f) s"
proof -
  obtain \<alpha> \<mu> where h:
  "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  hence "qbs_prob Y (f \<circ> \<alpha>) \<mu>"
        "monadP_qbs_Pf X Y f s = qbs_prob_space (Y,f \<circ> \<alpha>,\<mu>)"
    using qbs_prob.monadP_qbs_Pf_computation[OF _ _ assms(2)] by auto
  from qbs_prob.monadP_qbs_Pf_computation[OF this assms(3)] qbs_prob.monadP_qbs_Pf_computation[OF h qbs_morphism_comp[OF assms(2,3)]]
  show ?thesis
    by(simp add: comp_assoc)
qed

subsubsection \<open> Join \<close>
definition qbs_join :: "'a qbs_prob_space qbs_prob_space \<Rightarrow> 'a qbs_prob_space" where
"qbs_join \<equiv> (\<lambda>sst. sst \<bind> id)"

lemma qbs_join_morphism:
  "qbs_join \<in> monadP_qbs (monadP_qbs X) \<rightarrow>\<^sub>Q monadP_qbs X"
  by(simp add: qbs_join_def qbs_bind_morphism'[OF qbs_morphism_ident])

lemma qbs_join_computation:
  assumes "qbs_prob (monadP_qbs X) \<beta> \<mu>"
          "ssx = qbs_prob_space (monadP_qbs X,\<beta>,\<mu>)"
          "\<alpha> \<in> qbs_Mx X"
          "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      and "\<beta> =(\<lambda>r.  qbs_prob_space (X,\<alpha>,g r))"
    shows "qbs_prob X \<alpha> (\<mu> \<bind> g)" "qbs_join ssx = qbs_prob_space (X,\<alpha>, \<mu> \<bind> g)"
  using qbs_prob.qbs_bind_computation[OF assms(1,2) qbs_morphism_ident assms(3,4)]
  by(auto simp: assms(5) qbs_join_def)

subsubsection \<open> Strength \<close>
definition qbs_strength :: "['a quasi_borel,'b quasi_borel,'a \<times> 'b qbs_prob_space] \<Rightarrow> ('a \<times> 'b) qbs_prob_space" where
"qbs_strength W X = (\<lambda>(w,sx). let (_,\<alpha>,\<mu>) = rep_qbs_prob_space sx
                         in qbs_prob_space (W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>))"

lemma(in qbs_prob) qbs_strength_computation:
  assumes "w \<in> qbs_space W"
      and "sx = qbs_prob_space (X,\<alpha>,\<mu>)"
    shows "qbs_prob (W \<Otimes>\<^sub>Q X) (\<lambda>r. (w,\<alpha> r)) \<mu>"
          "qbs_strength W X (w,sx) = qbs_prob_space (W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>)"
proof -
  interpret qp1: qbs_prob "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w,\<alpha> r)" \<mu>
    by(auto intro!: qbs_probI simp: assms(1) pair_qbs_Mx_def comp_def)
  show "qbs_prob (W \<Otimes>\<^sub>Q X) (\<lambda>r. (w,\<alpha> r)) \<mu>"
       "qbs_strength W X (w,sx) = qbs_prob_space (W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>)"
     apply(simp_all add: qp1.qbs_prob_axioms qbs_strength_def rep_qbs_prob_space_def qbs_prob_space.rep_def)
    apply(rule someI2[where a="(X,\<alpha>,\<mu>)"])
  proof(auto simp: in_Rep assms(2))
    fix X' \<alpha>' \<mu>'
    assume h:"(X',\<alpha>',\<mu>') \<in> Rep_qbs_prob_space (qbs_prob_space (X, \<alpha>, \<mu>))"
    from if_in_Rep(1,2)[OF this] interpret pqp: pair_qbs_prob "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w, \<alpha>' r)" \<mu>' "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w,\<alpha> r)" \<mu>
      by(simp add: pair_qbs_prob_def qp1.qbs_prob_axioms)
       (auto intro!: qbs_probI simp: pair_qbs_Mx_def comp_def assms(1) qbs_prob_def in_Mx_def)
    note [simp] = qbs_prob_eq2_dest[OF if_in_Rep(3)[OF h,simplified qbs_prob_eq_equiv12]]
    show "qbs_prob_space (W \<Otimes>\<^sub>Q X, \<lambda>r. (w, \<alpha>' r), \<mu>') = qbs_prob_space (W \<Otimes>\<^sub>Q X, \<lambda>r. (w, \<alpha> r), \<mu>)"
    proof(rule pqp.qbs_prob_space_eq2)
      fix f
      assume "f \<in> qbs_to_measure (W \<Otimes>\<^sub>Q X) \<rightarrow>\<^sub>M real_borel"
      note qbs_morphism_dest[OF qbs_morphismE(2)[OF curry_preserves_morphisms[OF qbs_morphism_measurable_intro[OF this]] assms(1),simplified]]
      show "(\<integral>y. f ((\<lambda>r. (w, \<alpha>' r)) y) \<partial> \<mu>') = (\<integral>y. f ((\<lambda>r. (w, \<alpha> r)) y) \<partial> \<mu>)"
           (is "?lhs = ?rhs")
      proof -
        have "?lhs = (\<integral>y. curry f w (\<alpha>' y) \<partial> \<mu>')" by auto
        also have "... = (\<integral>y. curry f w (\<alpha> y) \<partial> \<mu>)"
          by(rule qbs_prob_eq2_dest(4)[OF if_in_Rep(3)[OF h,simplified qbs_prob_eq_equiv12],symmetric]) fact
        also have "... = ?rhs" by auto
        finally show ?thesis .
      qed
    qed simp
  qed
qed

lemma qbs_strength_natural:
  assumes "f \<in> X \<rightarrow>\<^sub>Q X'"
          "g \<in> Y \<rightarrow>\<^sub>Q Y'"
          "x \<in> qbs_space X"
      and "sy \<in> monadP_qbs_Px Y"
    shows "(monadP_qbs_Pf (X \<Otimes>\<^sub>Q Y) (X' \<Otimes>\<^sub>Q Y') (map_prod f g) \<circ> qbs_strength X Y) (x,sy) = (qbs_strength X' Y' \<circ> map_prod f (monadP_qbs_Pf Y Y' g)) (x,sy)"
          (is "?lhs = ?rhs")
proof -
  obtain \<beta> \<nu> where hy:
   "qbs_prob Y \<beta> \<nu>" "sy = qbs_prob_space (Y,\<beta>,\<nu>)"
    using rep_monadP_qbs_Px[OF assms(4)] by auto
  have "qbs_prob (X \<Otimes>\<^sub>Q Y) (\<lambda>r. (x, \<beta> r)) \<nu>"
       "qbs_strength X Y (x, sy) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, \<lambda>r. (x, \<beta> r), \<nu>)"
    using qbs_prob.qbs_strength_computation[OF hy(1) assms(3) hy(2)] by auto
  hence LHS:"?lhs = qbs_prob_space (X' \<Otimes>\<^sub>Q Y',map_prod f g \<circ> (\<lambda>r. (x, \<beta> r)),\<nu>)"
    by(simp add: qbs_prob.monadP_qbs_Pf_computation[OF _ _ qbs_morphism_map_prod[OF assms(1,2)]])

  have "map_prod f (monadP_qbs_Pf Y Y' g) (x,sy) = (f x,qbs_prob_space (Y',g \<circ> \<beta>,\<nu>))"
       "qbs_prob Y' (g \<circ> \<beta>) \<nu>"
    by(auto simp: qbs_prob.monadP_qbs_Pf_computation[OF hy assms(2)])
  hence RHS:"?rhs = qbs_prob_space (X' \<Otimes>\<^sub>Q Y',\<lambda>r. (f x, (g \<circ> \<beta>) r),\<nu>)"
    using qbs_prob.qbs_strength_computation[OF _ _ refl,of Y' "g \<circ> \<beta>" \<nu> "f x" X'] assms(1,3)
    by auto

  show "?lhs = ?rhs"
    unfolding LHS RHS
    by(simp add: comp_def)
qed

lemma qbs_strength_ab_r:
  assumes "\<alpha> \<in> qbs_Mx X"
          "\<beta> \<in> monadP_qbs_MPx Y"
          "\<gamma> \<in> qbs_Mx Y"
 and [measurable]:"g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      and "\<beta> = (\<lambda>r. qbs_prob_space (Y,\<gamma>,g r))"
    shows "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<gamma> \<circ> real_real.g) (distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f)"         
          "qbs_strength X Y (\<alpha> r, \<beta> r) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<gamma> \<circ> real_real.g, distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f)"
proof -
  have [measurable_cong]: "sets (g r) = sets real_borel"
                          "sets (return real_borel r) = sets real_borel"
    using measurable_space[OF assms(4),of r]
    by(simp_all add: space_prob_algebra)
  interpret qp: qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<gamma> \<circ> real_real.g" "distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f"
  proof(auto intro!: qbs_probI)
    show "map_prod \<alpha> \<gamma> \<circ> real_real.g \<in> pair_qbs_Mx X Y"
      using qbs_closed1_dest[OF assms(1)] qbs_closed1_dest[OF assms(3)]
      by(auto simp: comp_def qbs_prob_def in_Mx_def pair_qbs_Mx_def)
  next
    show "prob_space (distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f) "
      using measurable_space[OF assms(4),of r]
      by(auto intro!: prob_space.prob_space_distr simp: prob_algebra_real_prob_measure prob_space_pair prob_space_return real_distribution.axioms(1))
  qed
  interpret pqp: pair_qbs_prob "X \<Otimes>\<^sub>Q Y" "\<lambda>l. (\<alpha> r, \<gamma> l)" "g r" "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<gamma> \<circ> real_real.g" "distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f"
    by(simp add: qbs_prob.qbs_strength_computation[OF qbs_prob_MPx[OF assms(3,4)] qbs_Mx_to_X(2)[OF assms(1)] fun_cong[OF assms(5)],of r] pair_qbs_prob_def qp.qbs_prob_axioms)
  have [measurable]: "map_prod \<alpha> \<gamma> \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
  proof -
    have "map_prod \<alpha> \<gamma> \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
      using assms(1,3) by(auto intro!: qbs_morphism_map_prod simp: qbs_Mx_is_morphisms)
    hence "map_prod \<alpha> \<gamma> \<in> qbs_to_measure (\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q) \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
      using l_preserves_morphisms by auto
    thus ?thesis
      by simp
  qed
  hence [measurable]:"(\<lambda>l. (\<alpha> r, \<gamma> l)) \<in> real_borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
    using pqp.qp1.in_Mx qbs_Mx_are_measurable by blast

  show "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<gamma> \<circ> real_real.g) (distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f)"         
       "qbs_strength X Y (\<alpha> r, \<beta> r) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<gamma> \<circ> real_real.g, distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f)"
     apply(simp_all add: qp.qbs_prob_axioms qbs_prob.qbs_strength_computation(2)[OF qbs_prob_MPx[OF assms(3,4)] qbs_Mx_to_X(2)[OF assms(1)] fun_cong[OF assms(5)],of r])
  proof(rule pqp.qbs_prob_space_eq)
    show "distr (g r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (\<lambda>l. (\<alpha> r, \<gamma> l)) = distr (distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma> \<circ> real_real.g)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = distr (g r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma> \<circ> Pair r)"
        by(simp add: comp_def)
      also have "... = distr (distr (g r) (real_borel \<Otimes>\<^sub>M real_borel) (Pair r)) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma>)"
        by(auto intro!: distr_distr[symmetric])
      also have "... = distr (return real_borel r \<Otimes>\<^sub>M g r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma>)"
      proof -
        have "return real_borel r \<Otimes>\<^sub>M g r = distr (g r) (real_borel \<Otimes>\<^sub>M real_borel) (\<lambda>l. (r,l))"
        proof(auto intro!: measure_eqI)
          fix A
          assume h':"A \<in> sets (real_borel \<Otimes>\<^sub>M real_borel)"
          show "emeasure (return real_borel r \<Otimes>\<^sub>M g r) A = emeasure (distr (g r) (real_borel \<Otimes>\<^sub>M real_borel) (Pair r)) A"
                (is "?lhs' = ?rhs'")
          proof -
            have "?lhs' = \<integral>\<^sup>+ x. emeasure (g r) (Pair x -` A) \<partial>return real_borel r"
              by(auto intro!: pqp.qp1.emeasure_pair_measure_alt simp: h')
            also have "... = emeasure (g r) (Pair r -` A)"
              by(auto intro!: nn_integral_return pqp.qp1.measurable_emeasure_Pair simp: h')
            also have "... = ?rhs'"
              by(simp add: emeasure_distr[OF _ h'])
            finally show ?thesis .
          qed
        qed
        thus ?thesis by simp
      qed
      also have "... = ?rhs"
        by(rule distr_distr[of "map_prod \<alpha> \<gamma> \<circ> real_real.g" real_borel "qbs_to_measure (X \<Otimes>\<^sub>Q Y)" real_real.f "return real_borel r \<Otimes>\<^sub>M g r",simplified comp_assoc,simplified,symmetric])
      finally show ?thesis .
    qed
  qed simp
qed


lemma qbs_strength_morphism:
 "qbs_strength X Y \<in> X \<Otimes>\<^sub>Q monadP_qbs Y \<rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
proof(rule pair_qbs_morphismI,simp)
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx X"
           "\<beta> \<in> monadP_qbs_MPx Y"
  then obtain \<gamma> g where hb:
    "\<gamma> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
    "\<beta> = (\<lambda>r. qbs_prob_space (Y, \<gamma>, g r))"
    using rep_monadP_qbs_MPx[of \<beta>] by blast
  note [measurable] = hb(2)
  show "qbs_strength X Y \<circ> (\<lambda>r. (\<alpha> r, \<beta> r)) \<in> monadP_qbs_MPx (X \<Otimes>\<^sub>Q Y)"
    using qbs_strength_ab_r[OF h hb]
    by(auto intro!: bexI[where x="map_prod \<alpha> \<gamma> \<circ> real_real.g"] bexI[where x="\<lambda>r. distr (return real_borel r \<Otimes>\<^sub>M g r) real_borel real_real.f"]
              simp: monadP_qbs_MPx_def in_MPx_def qbs_prob_def in_Mx_def)
qed

lemma qbs_bind_morphism'':
 "(\<lambda>(f,x). x \<bind> f) \<in> exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q (monadP_qbs X) \<rightarrow>\<^sub>Q (monadP_qbs Y)"
proof(rule qbs_morphism_cong[of _ "qbs_join \<circ> (monadP_qbs_Pf (exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q X) (monadP_qbs Y) qbs_eval) \<circ> (qbs_strength (exp_qbs X (monadP_qbs Y)) X)"], auto)
  fix f
  fix sx
  assume h:"f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
           "sx \<in> monadP_qbs_Px X"
  then obtain \<alpha> \<mu> where h0:"qbs_prob X \<alpha> \<mu>" "sx = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[of sx X] by auto
  hence "f \<circ> \<alpha> \<in> monadP_qbs_MPx Y"
    using h(1) by(auto simp: qbs_prob_def in_Mx_def)
  then obtain \<beta> g where h1: 
  "\<beta> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
  "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g r))"
    using rep_monadP_qbs_MPx[of "f \<circ> \<alpha>" Y] by blast

  show "qbs_join (monadP_qbs_Pf (exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q X) (monadP_qbs Y) qbs_eval (qbs_strength (exp_qbs X (monadP_qbs Y)) X (f, sx))) =
           sx \<bind> f"
    by(simp add: qbs_join_computation[OF qbs_prob.monadP_qbs_Pf_computation[OF qbs_prob.qbs_strength_computation[OF h0(1) _ h0(2),of f "exp_qbs X (monadP_qbs Y)"] qbs_eval_morphism] h1(1,2),simplified qbs_eval_def comp_def,simplified,OF h(1) h1(3)[simplified comp_def]] qbs_prob.qbs_bind_computation[OF h0 h(1) h1])
next
  show "qbs_join \<circ>  monadP_qbs_Pf (exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q X) (monadP_qbs Y) qbs_eval \<circ> qbs_strength (exp_qbs X (monadP_qbs Y)) X \<in> exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
    using qbs_join_morphism monadP_qbs_Pf_morphism[OF qbs_eval_morphism]
    by(auto intro!: qbs_morphism_comp simp: qbs_strength_morphism)
qed

lemma qbs_bind_morphism''':
  "(\<lambda>f x. x \<bind> f) \<in> exp_qbs X (monadP_qbs Y) \<rightarrow>\<^sub>Q exp_qbs (monadP_qbs X) (monadP_qbs Y)"
  using qbs_bind_morphism'' curry_preserves_morphisms[of "\<lambda>(f, x). qbs_bind x f"]
  by fastforce

lemma qbs_bind_morphism:
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
      and "g \<in> X \<rightarrow>\<^sub>Q exp_qbs Y (monadP_qbs Z)"
    shows "(\<lambda>x. f x \<bind> g x) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Z"
  using qbs_morphism_comp[OF qbs_morphism_tuple[OF assms(2,1)] qbs_bind_morphism'']
  by(simp add: comp_def)

lemma qbs_bind_morphism'''':
  assumes "x \<in> monadP_qbs_Px X"
  shows "(\<lambda>f. x \<bind> f) \<in> exp_qbs X (monadP_qbs Y) \<rightarrow>\<^sub>Q monadP_qbs Y"
  by(rule qbs_morphismE(2)[OF arg_swap_morphism[OF qbs_bind_morphism'''],simplified,OF assms])

lemma qbs_strength_law1:
  assumes "x \<in> qbs_space (unit_quasi_borel \<Otimes>\<^sub>Q monadP_qbs X)"
  shows "snd x = (monadP_qbs_Pf (unit_quasi_borel \<Otimes>\<^sub>Q X) X snd \<circ> qbs_strength unit_quasi_borel X) x"
proof -
  obtain \<alpha> \<mu> where h:
   "qbs_prob X \<alpha> \<mu>" "(snd x) = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[of "snd x" X] assms by auto
  have [simp]: "((),snd x) = x"
    using SigmaE assms by auto
  show ?thesis
    using qbs_prob.monadP_qbs_Pf_computation[OF qbs_prob.qbs_strength_computation[OF h(1) _ h(2),of "fst x" "unit_quasi_borel",simplified] snd_qbs_morphism]
    by(simp add: h(2) comp_def)
qed

lemma qbs_strength_law2:
  assumes "x \<in> qbs_space ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q monadP_qbs Z)"
  shows "(qbs_strength X (Y \<Otimes>\<^sub>Q Z) \<circ> (map_prod id (qbs_strength Y Z)) \<circ> (\<lambda>((x,y),z). (x,(y,z)))) x =
         (monadP_qbs_Pf ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z) (X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)) (\<lambda>((x,y),z). (x,(y,z))) \<circ> qbs_strength (X \<Otimes>\<^sub>Q Y) Z) x"
         (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where h:
   "qbs_prob Z \<alpha> \<mu>" "snd x = qbs_prob_space (Z, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[of "snd x" Z] assms by auto
  have "?lhs = qbs_prob_space (X \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q Z, \<lambda>r. (fst (fst x), snd (fst x), \<alpha> r), \<mu>)"
    using assms  qbs_prob.qbs_strength_computation[OF h(1) _ h(2),of "snd (fst x)" Y]
    by(auto intro!: qbs_prob.qbs_strength_computation)
  also have "... = ?rhs"
    using qbs_prob.monadP_qbs_Pf_computation[OF qbs_prob.qbs_strength_computation[OF h(1) _ h(2),of "fst x" "X \<Otimes>\<^sub>Q Y"] qbs_morphism_pair_assoc1] assms
    by(auto simp: comp_def)
  finally show ?thesis .
qed

lemma qbs_strength_law3:
  assumes "x \<in> qbs_space (X \<Otimes>\<^sub>Q Y)"
  shows "qbs_return (X \<Otimes>\<^sub>Q Y) x = (qbs_strength X Y \<circ> (map_prod id (qbs_return Y))) x"
proof -
  interpret qp: qbs_prob Y "\<lambda>r. snd x" "return real_borel 0"
    using assms by(auto intro!: qbs_probI simp: prob_space_return)
  show ?thesis
    using qp.qbs_strength_computation[OF _ qp.qbs_return_computation[of "snd x" Y],of "fst x" X] assms
    by(auto simp: qp.qbs_return_computation[OF assms])
qed

lemma qbs_strength_law4:
  assumes "x \<in> qbs_space (X \<Otimes>\<^sub>Q monadP_qbs (monadP_qbs Y))"
  shows "(qbs_strength X Y \<circ> map_prod id qbs_join) x = (qbs_join \<circ> monadP_qbs_Pf (X \<Otimes>\<^sub>Q monadP_qbs Y) (monadP_qbs (X \<Otimes>\<^sub>Q Y))(qbs_strength X Y) \<circ> qbs_strength X (monadP_qbs Y)) x"
        (is "?lhs = ?rhs")
proof -
  obtain \<beta> \<mu> where h0:
  "qbs_prob (monadP_qbs Y) \<beta> \<mu>" "snd x = qbs_prob_space (monadP_qbs Y, \<beta>, \<mu>)"
    using rep_monadP_qbs_Px[of "snd x" "monadP_qbs Y"] assms by auto
  then obtain \<gamma> g where h1:
   "\<gamma> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "\<beta> = (\<lambda>r. qbs_prob_space (Y, \<gamma>, g r))"
    using rep_monadP_qbs_MPx[of \<beta> Y] by(auto simp: qbs_prob_def in_Mx_def)
  have "?lhs = qbs_prob_space (X \<Otimes>\<^sub>Q Y, \<lambda>r. (fst x, \<gamma> r), \<mu> \<bind> g)"
    using qbs_prob.qbs_strength_computation[OF qbs_join_computation(1)[OF h0 h1] _ qbs_join_computation(2)[OF h0 h1],of "fst x" X] assms
    by auto
  also have "... = ?rhs"
  proof -
    have "qbs_strength X Y \<circ> (\<lambda>r. (fst x, \<beta> r)) = (\<lambda>r. qbs_prob_space (X \<Otimes>\<^sub>Q Y, \<lambda>r. (fst x, \<gamma> r), g r))"
    proof
      show "(qbs_strength X Y \<circ> (\<lambda>r. (fst x, \<beta> r))) r = qbs_prob_space (X \<Otimes>\<^sub>Q Y, \<lambda>r. (fst x, \<gamma> r), g r)" for r
        using qbs_prob.qbs_strength_computation(2)[OF qbs_prob_MPx[OF h1(1,2),of r] _ fun_cong[OF h1(3)],of "fst x" X] assms
        by auto
    qed
    thus ?thesis
      using qbs_join_computation(2)[OF qbs_prob.monadP_qbs_Pf_computation[OF qbs_prob.qbs_strength_computation[OF h0(1) _ h0(2),of "fst x" X] qbs_strength_morphism] _ h1(2),of "\<lambda>r. (fst x, \<gamma> r)",symmetric] assms h1(1)
      by(auto simp: pair_qbs_Mx_def comp_def)
  qed
  finally show ?thesis .
qed


lemma qbs_return_Mxpair:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "\<beta> \<in> qbs_Mx Y"
    shows "qbs_return (X \<Otimes>\<^sub>Q Y) (\<alpha> r, \<beta> k) = qbs_prob_space (X \<Otimes>\<^sub>Q Y,map_prod \<alpha> \<beta> \<circ> real_real.g, distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f)"
          "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f)"
proof -
  note [measurable_cong] = sets_return[of real_borel]
  interpret qp: qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> real_real.g" "distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f"
    using qbs_closed1_dest[OF assms(1)] qbs_closed1_dest[OF assms(2)]
    by(auto intro!: qbs_probI prob_space.prob_space_distr prob_space_pair
              simp: pair_qbs_Mx_def comp_def prob_space_return)
  show "qbs_return (X \<Otimes>\<^sub>Q Y) (\<alpha> r, \<beta> k) = qbs_prob_space (X \<Otimes>\<^sub>Q Y,map_prod \<alpha> \<beta> \<circ> real_real.g, distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f)"
       "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f)"
  proof -
    show "qbs_return (X \<Otimes>\<^sub>Q Y) (\<alpha> r, \<beta> k) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (return real_borel r \<Otimes>\<^sub>M return real_borel k) real_borel real_real.f)"
         (is "?lhs = ?rhs")
    proof -
      have 1:"(\<lambda>r. qbs_prob_space (Y, \<beta>, return real_borel k)) \<in> monadP_qbs_MPx Y"
        by(auto intro!: in_MPx.intro bexI[where x=\<beta>] bexI[where x="\<lambda>r. return real_borel k"] simp: monadP_qbs_MPx_def assms(2))
      have "?lhs = (qbs_strength X Y \<circ> map_prod id (qbs_return Y)) (\<alpha> r, \<beta> k)"
        by(intro qbs_strength_law3[of "(\<alpha> r, \<beta> k)" X Y]) (use assms in auto)
      also have "... = qbs_strength X Y (\<alpha> r, qbs_prob_space (Y, \<beta>, return real_borel k))"
        using fun_cong[OF qbs_return_comp[OF assms(2)]] by simp
      also have "... = ?rhs"
        by(intro qbs_strength_ab_r(2)[OF assms(1) 1 assms(2) _ refl,of r]) auto
      finally show ?thesis .
    qed
  qed(rule qp.qbs_prob_axioms)
qed


lemma pair_return_return:
  assumes "l \<in> space M"
      and "r \<in> space N"
    shows "return M l \<Otimes>\<^sub>M return N r = return (M \<Otimes>\<^sub>M N) (l,r)"
proof(auto intro!: measure_eqI)
  fix A
  assume h:"A \<in> sets (M \<Otimes>\<^sub>M N)"
  show "emeasure (return M l \<Otimes>\<^sub>M return N r) A = indicator A (l, r)"
       (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator A (x, y) \<partial>return N r \<partial>return M l)"
      by(auto intro!: sigma_finite_measure.emeasure_pair_measure prob_space_imp_sigma_finite simp: h prob_space_return assms)
    also have "... = (\<integral>\<^sup>+ x. indicator A (x, r) \<partial>return M l)"
      using h by(auto intro!: nn_integral_cong nn_integral_return simp: assms(2))
    also have "... = ?rhs"
      using h by(auto intro!: nn_integral_return simp: assms)
    finally show ?thesis .
  qed
qed

lemma bind_bind_return_distr:
  assumes "real_distribution \<mu>"
      and "real_distribution \<nu>"
    shows "\<mu> \<bind> (\<lambda>r. \<nu> \<bind> (\<lambda>l. distr (return real_borel r \<Otimes>\<^sub>M return real_borel l) real_borel real_real.f))
           = distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f"
    (is "?lhs = ?rhs")
proof -
  interpret rd1: real_distribution \<mu> by fact
  interpret rd2: real_distribution \<nu> by fact
  interpret pp: pair_prob_space \<mu> \<nu>
    by (simp add: pair_prob_space.intro pair_sigma_finite_def rd1.prob_space_axioms rd1.sigma_finite_measure_axioms rd2.prob_space_axioms rd2.sigma_finite_measure_axioms)
  have "?lhs = \<mu> \<bind> (\<lambda>r. \<nu> \<bind> (\<lambda>l. distr (return (real_borel \<Otimes>\<^sub>M real_borel) (r,l)) real_borel real_real.f))"
    using pair_return_return[of _ real_borel _ real_borel] by simp
  also have "... = \<mu> \<bind> (\<lambda>r. \<nu> \<bind> (\<lambda>l. distr (return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)) real_borel real_real.f))"
  proof -
    have "return (real_borel \<Otimes>\<^sub>M real_borel) = return (\<mu> \<Otimes>\<^sub>M \<nu>)"
      by(auto intro!: return_sets_cong sets_pair_measure_cong)
    thus ?thesis by simp
  qed
  also have "... = \<mu> \<bind> (\<lambda>r. distr (\<nu> \<bind> (\<lambda>l. (return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)))) real_borel real_real.f)"
    by(auto intro!: bind_cong distr_bind[symmetric,where K="\<mu> \<Otimes>\<^sub>M \<nu>"])
  also have "... = distr (\<mu> \<bind> (\<lambda>r. \<nu> \<bind> (\<lambda>l. return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)))) real_borel real_real.f"
    by(auto intro!: distr_bind[symmetric,where K="\<mu> \<Otimes>\<^sub>M \<nu>"])
  also have "... = ?rhs"
    by(simp add: pp.pair_measure_eq_bind[symmetric])
  finally show ?thesis .
qed

lemma(in pair_qbs_probs) qbs_bind_return_qp:
  shows "qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y))) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
        "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
proof -
  show "qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
       (is "?lhs = ?rhs")
  proof -
    have "?lhs = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, \<nu> \<bind> (\<lambda>l. \<mu> \<bind> (\<lambda>r. distr (return real_borel r \<Otimes>\<^sub>M return real_borel l) real_borel real_real.f)))"
    proof(auto intro!: qp2.qbs_bind_computation(2) measurable_bind_prob_space2[where N=real_borel] simp: in_Mx[simplified])
      show "(\<lambda>y. qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) \<in> Y \<rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
        using qbs_morphism_const[of _ "monadP_qbs X" Y,simplified,OF qp1.qbs_prob_space_in_Px] curry_preserves_morphisms[OF qbs_morphism_pair_swap[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]]
        by (auto intro!: qbs_bind_morphism)
    next
      show "(\<lambda>y. qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) \<circ> \<beta> = (\<lambda>r. qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, \<mu> \<bind> (\<lambda>l. distr (return real_borel l \<Otimes>\<^sub>M return real_borel r) real_borel real_real.f)))"
        by standard
           (auto intro!: qp1.qbs_bind_computation(2) qbs_morphism_comp[OF qbs_morphism_Pair2[of _ Y] qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"],simplified comp_def]
                  simp: in_Mx[simplified] qbs_return_Mxpair[OF qp1.in_Mx qp2.in_Mx] qbs_Mx_to_X(2))
    qed
    also have "... = ?rhs"
    proof -
      have "\<nu> \<bind> (\<lambda>l. \<mu> \<bind> (\<lambda>r. distr (return real_borel r \<Otimes>\<^sub>M return real_borel l) real_borel real_real.f)) = distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f"
        by(auto intro!: bind_rotate[symmetric,where N=real_borel] measurable_prob_algebraD
                  simp: bind_bind_return_distr[symmetric,OF qp1.real_distribution_axioms qp2.real_distribution_axioms])
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
  show "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
    by(rule qbs_prob_axioms)
qed

lemma(in pair_qbs_probs) qbs_bind_return_pq:
  shows "qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y))) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
        "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> real_real.g) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
proof(simp_all add: qbs_bind_return_qp(2))
  show "qbs_prob_space (X, \<alpha>, \<mu>) \<bind> (\<lambda>x. qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
       (is "?lhs = _")
  proof -
    have "?lhs = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, \<mu> \<bind> (\<lambda>r. \<nu> \<bind> (\<lambda>l. distr (return real_borel r \<Otimes>\<^sub>M return real_borel l) real_borel real_real.f)))"
    proof(auto intro!: qp1.qbs_bind_computation(2) measurable_bind_prob_space2[where N=real_borel])
      show "(\<lambda>x. qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) \<in> X \<rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
        using qbs_morphism_const[of _ "monadP_qbs Y" X,simplified,OF qp2.qbs_prob_space_in_Px] curry_preserves_morphisms[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]
        by(auto intro!: qbs_bind_morphism simp: curry_def)
    next
      show "(\<lambda>x. qbs_prob_space (Y, \<beta>, \<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y))) \<circ> \<alpha> = (\<lambda>r. qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, \<nu> \<bind> (\<lambda>l. distr (return real_borel r \<Otimes>\<^sub>M return real_borel l) real_borel real_real.f)))"
        by standard
          (auto intro!: qp2.qbs_bind_computation(2) qbs_morphism_comp[OF qbs_morphism_Pair1[of _ X] qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"],simplified comp_def]
                  simp:  qbs_return_Mxpair[OF qp1.in_Mx qp2.in_Mx] qbs_Mx_to_X(2))
    qed
    thus ?thesis
      by(simp add: bind_bind_return_distr[OF qp1.real_distribution_axioms qp2.real_distribution_axioms])
  qed
qed

lemma qbs_bind_return_rotate:
  assumes "p \<in> monadP_qbs_Px X"
      and "q \<in> monadP_qbs_Px Y"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))"
proof -
  obtain \<alpha> \<mu> where hp:
    "qbs_prob X \<alpha> \<mu>" "p = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  obtain \<beta> \<nu> where hq:
    "qbs_prob Y \<beta> \<nu>" "q = qbs_prob_space (Y, \<beta>, \<nu>)"
    using rep_monadP_qbs_Px[OF assms(2)] by auto
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_probs_def hp hq)
  show ?thesis
    by(simp add: hp(2) hq(2) pqp.qbs_bind_return_pq(1) pqp.qbs_bind_return_qp)
qed

lemma qbs_pair_bind_return1:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> monadP_qbs_Px X"
      and "q \<in> monadP_qbs_Px Y"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = (q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
          (is "?lhs = ?rhs")
proof -
  note [simp] = qbs_morphism_const[of _ "monadP_qbs X",simplified,OF assms(2)]
                qbs_morphism_Pair1'[OF _ assms(1)] qbs_morphism_Pair2'[OF _ assms(1)]
                curry_preserves_morphisms[OF qbs_morphism_pair_swap[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]],simplified curry_def,simplified]
                qbs_morphism_Pair2'[OF _ qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]
                arg_swap_morphism[OF curry_preserves_morphisms[OF assms(1)],simplified curry_def]
                curry_preserves_morphisms[OF qbs_morphism_comp[OF qbs_morphism_pair_swap[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]] qbs_bind_morphism'[OF assms(1)]],simplified curry_def comp_def,simplified]
  have [simp]:"(\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) \<in> Y \<rightarrow>\<^sub>Q monadP_qbs Z"
              "(\<lambda>y. p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y) \<bind> f)) \<in> Y \<rightarrow>\<^sub>Q monadP_qbs Z"
    by(auto intro!: qbs_bind_morphism[where Y=X] simp: curry_def)
  have "?lhs = q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y) \<bind> f))"
    by(auto intro!: qbs_bind_cong[OF assms(3),where Y=Z] qbs_bind_cong[OF assms(2),where Y=Z] simp: qbs_bind_return[OF assms(1)])
  also have "... = q \<bind> (\<lambda>y. (p \<bind> (\<lambda>x. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y))) \<bind> f)"
    by(auto intro!: qbs_bind_cong[OF assms(3),where Y=Z] qbs_bind_assoc[OF assms(2) _ assms(1)] simp: )
  also have "... = ?rhs"
    by(auto intro!: qbs_bind_assoc[OF assms(3)_ assms(1)] qbs_bind_morphism[where Y=X])
  finally show ?thesis .
qed

lemma qbs_pair_bind_return2:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> monadP_qbs_Px X"
      and "q \<in> monadP_qbs_Px Y"
    shows "p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y))) = (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
          (is "?lhs = ?rhs")      
proof -
  note [simp] = qbs_morphism_const[of _ "monadP_qbs Y",simplified,OF assms(3)]
                qbs_morphism_Pair1'[OF _ assms(1)] curry_preserves_morphisms[OF assms(1),simplified curry_def]
                qbs_morphism_Pair1'[OF _ qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"]]
                curry_preserves_morphisms[OF qbs_morphism_comp[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"] qbs_bind_morphism'[OF assms(1)]],simplified curry_def comp_def,simplified]
                curry_preserves_morphisms[OF qbs_return_morphism[of "X \<Otimes>\<^sub>Q Y"],simplified curry_def]
  have [simp]: "(\<lambda>x. q \<bind> (\<lambda>y. f (x, y))) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Z"
               "(\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x, y) \<bind> f)) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Z"
     by(auto intro!: qbs_bind_morphism[where Y=Y])
  have "?lhs = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y) \<bind> f))"
    by(auto intro!: qbs_bind_cong[OF assms(2),where Y=Z] qbs_bind_cong[OF assms(3),where Y=Z] simp: qbs_bind_return[OF assms(1)])
  also have "... = p \<bind> (\<lambda>x. (q \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y))) \<bind> f)"
    by(auto intro!: qbs_bind_cong[OF assms(2),where Y=Z] qbs_bind_assoc[OF assms(3) _ assms(1)])
  also have "... = ?rhs"
    by(auto intro!: qbs_bind_assoc[OF assms(2) _ assms(1)] qbs_bind_morphism[where Y=Y])
  finally show ?thesis .
qed

lemma qbs_bind_rotate:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> monadP_qbs_Px X"
      and "q \<in> monadP_qbs_Px Y"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y)))"
  using qbs_pair_bind_return1[OF assms(1) assms(2) assms(3)] qbs_bind_return_rotate[OF assms(2) assms(3)] qbs_pair_bind_return2[OF assms(1) assms(2) assms(3)]
  by simp


lemma(in pair_qbs_probs) qbs_bind_bind_return:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "qbs_prob Z (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g)) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
    and "qbs_prob_space (X,\<alpha>,\<mu>) \<bind> (\<lambda>x. qbs_prob_space (Y,\<beta>,\<nu>) \<bind> (\<lambda>y. qbs_return Z (f (x,y)))) = qbs_prob_space (Z,f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g),distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
        (is "?lhs = ?rhs")
proof -
  show "qbs_prob Z (f \<circ> (map_prod \<alpha> \<beta> \<circ> real_real.g)) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f)"
    using qbs_bind_return_qp(2) qbs_morphismE(3)[OF assms] by(simp add: qbs_prob_def in_Mx_def)
next
  have "?lhs = (qbs_prob_space (X,\<alpha>,\<mu>) \<bind> (\<lambda>x. qbs_prob_space (Y,\<beta>,\<nu>) \<bind> (\<lambda>y. qbs_return (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> qbs_return Z \<circ> f"
    using qbs_pair_bind_return2[OF qbs_morphism_comp[OF assms qbs_return_morphism] qp1.qbs_prob_space_in_Px qp2.qbs_prob_space_in_Px]
    by(simp add: comp_def)
  also have "... = qbs_prob_space (X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> real_real.g, distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f) \<bind> qbs_return Z \<circ> f"
    by(simp add: qbs_bind_return_pq(1))
  also have "... = ?rhs"
    by(rule monadP_qbs_Pf_computation[OF refl assms,simplified monadP_qbs_Pf_def])
  finally show "?lhs = ?rhs" .
qed

subsubsection \<open> Properties of Return and Bind \<close>
lemma qbs_prob_measure_return:
  assumes "x \<in> qbs_space X"
  shows "qbs_prob_measure (qbs_return X x) = return (qbs_to_measure X) x"
proof -
  interpret qp: qbs_prob X "\<lambda>r. x" "return real_borel 0"
    by(auto intro!: qbs_probI simp: prob_space_return assms)
  show ?thesis
    by(simp add: qp.qbs_return_computation[OF assms] distr_return)
qed

lemma qbs_prob_measure_bind:
  assumes "s \<in> monadP_qbs_Px X"
      and "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    shows "qbs_prob_measure (s \<bind> f) = qbs_prob_measure s \<bind> qbs_prob_measure \<circ> f"
          (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where hs:
  "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by blast
  hence "f \<circ> \<alpha> \<in> monadP_qbs_MPx Y"
    using assms(2) by(auto simp: qbs_prob_def in_Mx_def)
  then obtain \<beta> g where hbg:
      "\<beta> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g r))"
    using rep_monadP_qbs_MPx by blast
  note [measurable] = hbg(2)
  have [measurable]:"f \<in> qbs_to_measure X \<rightarrow>\<^sub>M qbs_to_measure (monadP_qbs Y)"
    using l_preserves_morphisms assms(2) by auto 
  interpret pqp: pair_qbs_probs X \<alpha> \<mu> Y \<beta> "\<mu> \<bind> g"
    by(simp add: pair_qbs_probs_def hs(1) qbs_prob.qbs_bind_computation[OF hs assms(2) hbg])

  have "?lhs = distr (\<mu> \<bind> g) (qbs_to_measure Y) \<beta>"
    by(simp add: pqp.qp1.qbs_bind_computation[OF hs(2) assms(2) hbg])
  also have "... = \<mu> \<bind> (\<lambda>x. distr (g x) (qbs_to_measure Y) \<beta>)"
    by(auto intro!: distr_bind[where K=real_borel] measurable_prob_algebraD)
  also have "... = \<mu> \<bind> (\<lambda>x. qbs_prob_measure (qbs_prob_space (Y,\<beta>,g x)))"
    using measurable_space[OF hbg(2)]
    by(auto intro!: bind_cong qbs_prob.qbs_prob_measure_computation[symmetric] qbs_probI simp: space_prob_algebra)
  also have "... = \<mu> \<bind> (\<lambda>x. qbs_prob_measure ((f \<circ> \<alpha>) x))"
    by(simp add: hbg(3))
  also have "... = \<mu> \<bind> (\<lambda>x. (qbs_prob_measure \<circ> f) (\<alpha> x))" by simp
  also have "... = distr \<mu> (qbs_to_measure X) \<alpha> \<bind> qbs_prob_measure \<circ> f"
    by(intro bind_distr[symmetric,where K="qbs_to_measure Y"]) auto
  also have "... = ?rhs"
    by(simp add: hs(2))
  finally show ?thesis .
qed

lemma qbs_of_return:
  assumes "x \<in> qbs_space X"
  shows "qbs_prob_space_qbs (qbs_return X x) = X"
  using real_distribution.qbs_return_computation[OF _ assms,of "return real_borel 0"]
        qbs_prob.qbs_prob_space_qbs_computation[of X "\<lambda>r. x" "return real_borel 0"] assms
  by(auto simp: qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def prob_space_return)

lemma qbs_of_bind:
  assumes "s \<in> monadP_qbs_Px X"
      and "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
    shows "qbs_prob_space_qbs (s \<bind> f) = Y"
proof -
  obtain \<alpha> \<mu> where hs:
   "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  hence "f \<circ> \<alpha> \<in> monadP_qbs_MPx Y"
    using assms(2) by(auto simp: qbs_prob_def in_Mx_def)
  then obtain \<beta> g where hbg:
      "\<beta> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
      "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g r))"
    using rep_monadP_qbs_MPx by blast
  show ?thesis
    using qbs_prob.qbs_bind_computation[OF hs assms(2) hbg] qbs_prob.qbs_prob_space_qbs_computation
    by simp
qed

subsubsection \<open> Properties of Integrals\<close>
lemma qbs_integrable_return:
  assumes "x \<in> qbs_space X" 
      and "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    shows "qbs_integrable (qbs_return X x) f"
  using assms(2) nn_integral_return[of x "qbs_to_measure X" "\<lambda>x. \<bar>f x\<bar>",simplified,OF assms(1)]
  by(auto intro!: qbs_integrable_if_integrable integrableI_bounded
            simp: qbs_prob_measure_return[OF assms(1)] )

lemma qbs_integrable_bind_return:
  assumes "s \<in> monadP_qbs_Px Y"
          "f \<in> Z \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "qbs_integrable (s \<bind> (\<lambda>y. qbs_return Z (g y))) f = qbs_integrable s (f \<circ> g)"
proof -
  obtain \<alpha> \<mu> where hs:
   "qbs_prob Y \<alpha> \<mu>" "s = qbs_prob_space (Y, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then interpret qp: qbs_prob Y \<alpha> \<mu> by simp
  show ?thesis (is "?lhs = ?rhs")
  proof -
    have "qbs_return Z \<circ> (g \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Z, g \<circ> \<alpha>, return real_borel r))"
      by(rule qbs_return_comp) (use assms(3) qp.in_Mx in blast)
    hence hb:"qbs_prob Z (g \<circ> \<alpha>) \<mu>"
             "s \<bind> (\<lambda>y. qbs_return Z (g y)) = qbs_prob_space (Z, g \<circ> \<alpha>, \<mu>)"
       by(auto intro!: qbs_prob.qbs_bind_computation[OF hs qbs_morphism_comp[OF assms(3) qbs_return_morphism,simplified comp_def] qbs_morphismE(3)[OF assms(3) qp.in_Mx],of "return real_borel",simplified bind_return''[of \<mu> real_borel,simplified]])
         (simp_all add: comp_def)
    have "?lhs = integrable \<mu> (f \<circ> (g \<circ> \<alpha>))"
      using assms(2)
      by(auto intro!: qbs_prob.qbs_integrable_iff_integrable[OF hb(1),simplified comp_def] simp: hb(2) comp_def)
    also have "... = ?rhs"
      using qbs_morphism_comp[OF assms(3,2)]
      by(auto intro!: qbs_prob.qbs_integrable_iff_integrable[OF hs(1),symmetric] simp: hs(2) comp_def)
    finally show ?thesis .
  qed
qed


lemma qbs_prob_ennintegral_morphism:
  assumes "L \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
      and "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<lambda>x. qbs_prob_ennintegral (L x) (f x)) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
proof(rule qbs_morphismI,simp_all)
  fix \<alpha>
  assume h0:"\<alpha> \<in> qbs_Mx X"
  then obtain \<beta> g where h:
   "\<beta> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(L \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g r))"
    using rep_monadP_qbs_MPx[of "L \<circ> \<alpha>" Y] qbs_morphismE(3)[OF assms(1)] by auto
  note [measurable] = h(2)
  have [measurable]: "(\<lambda>(r, y). f (\<alpha> r) (\<beta> y)) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M ennreal_borel"
  proof -
    have "(\<lambda>(r, y). f (\<alpha> r) (\<beta> y)) = case_prod f \<circ> map_prod \<alpha> \<beta>"
      by auto
    also have "... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      apply(rule qbs_morphism_comp[OF qbs_morphism_map_prod uncurry_preserves_morphisms[OF assms(2)]])
      using h0 h(1) by(auto simp: qbs_Mx_is_morphisms)
    finally show ?thesis
      by auto
  qed
  have "(\<lambda>x. qbs_prob_ennintegral (L x) (f x)) \<circ> \<alpha> = (\<lambda>r. qbs_prob_ennintegral ((L \<circ> \<alpha>) r) ((f \<circ> \<alpha>) r))"
    by auto
  also have "... = (\<lambda>r. (\<integral>\<^sup>+ x. (f \<circ> \<alpha>) r (\<beta> x) \<partial>(g r)))"
    apply standard
    using h0 by(auto intro!: qbs_prob.qbs_prob_ennintegral_def[OF qbs_prob_MPx[OF h(1,2)]] qbs_morphismE(2)[OF assms(2),simplified] simp: h(3))
  also have "... \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
    using assms(2) h0 h(1)
    by(auto intro!: nn_integral_measurable_subprob_algebra2[where N=real_borel] simp: measurable_prob_algebraD)
  finally show "(\<lambda>x. qbs_prob_ennintegral (L x) (f x)) \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel " .
qed

lemma qbs_morphism_ennintegral_fst:
  assumes "q \<in> monadP_qbs_Px Y"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<lambda>x. \<integral>\<^sup>+\<^sub>Q y. f (x, y) \<partial>q) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  by(rule qbs_prob_ennintegral_morphism[OF qbs_morphism_const[of _  "monadP_qbs Y",simplified,OF assms(1)] curry_preserves_morphisms[OF assms(2)],simplified curry_def])

lemma qbs_morphism_ennintegral_snd:
  assumes "p \<in> monadP_qbs_Px X"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "(\<lambda>y. \<integral>\<^sup>+\<^sub>Q x. f (x, y) \<partial>p) \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using qbs_morphism_ennintegral_fst[OF assms(1) qbs_morphism_pair_swap[OF assms(2)]]
  by fastforce

lemma qbs_prob_ennintegral_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "(\<lambda>s. qbs_prob_ennintegral s f) \<in> monadP_qbs X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  apply(rule qbs_prob_ennintegral_morphism[of _ _ X])
  using qbs_morphism_ident[of "monadP_qbs X"]
   apply (simp add: id_def)
  using assms qbs_morphism_const[of f "exp_qbs X \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"]
  by simp

lemma qbs_prob_ennintegral_return:
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "x \<in> qbs_space X"
    shows "qbs_prob_ennintegral (qbs_return X x) f = f x"
  using assms
  by(auto intro!: nn_integral_return
            simp: qbs_prob_ennintegral_def2[OF qbs_of_return[OF assms(2)] assms(1)] qbs_prob_measure_return[OF assms(2)])

lemma qbs_prob_ennintegral_bind:
  assumes "s \<in> monadP_qbs_Px X"
          "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
      and "g \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "qbs_prob_ennintegral (s \<bind> f) g = qbs_prob_ennintegral s (\<lambda>y. (qbs_prob_ennintegral (f y) g))"
          (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where hs:
   "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then interpret qp: qbs_prob X \<alpha> \<mu> by simp
  obtain \<beta> h where hb:
   "\<beta> \<in> qbs_Mx Y" "h \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, h r))"
    using rep_monadP_qbs_MPx[OF qbs_morphismE(3)[OF assms(2) qp.in_Mx,simplified]]
    by auto
  hence h:"qbs_prob Y \<beta> (\<mu> \<bind> h)"
          "s \<bind> f = qbs_prob_space (Y, \<beta>, \<mu> \<bind> h)"
    using qp.qbs_bind_computation[OF hs(2) assms(2) hb] by auto
  hence LHS:"?lhs = (\<integral>\<^sup>+ x. g (\<beta> x) \<partial>(\<mu> \<bind> h))"
    using qbs_prob.qbs_prob_ennintegral_def[OF h(1) assms(3)]
    by simp
  note [measurable] = hb(2)

  have "\<And>r. qbs_prob_ennintegral (f (\<alpha> r)) g = (\<integral>\<^sup>+ y. g (\<beta> y) \<partial>(h r))"
    using qbs_prob.qbs_prob_ennintegral_def[OF qbs_prob_MPx[OF hb(1,2)] assms(3)] hb(3)[simplified comp_def]
    by metis
  hence "?rhs = (\<integral>\<^sup>+ r. (\<integral>\<^sup>+ y. (g \<circ> \<beta>) y \<partial>(h r)) \<partial>\<mu>)"
    by(auto intro!: nn_integral_cong
              simp: qbs_prob.qbs_prob_ennintegral_def[OF hs(1)  qbs_prob_ennintegral_morphism[OF assms(2) qbs_morphism_const[of _ "exp_qbs Y \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 ",simplified,OF assms(3)]]] hs(2))
  also have "... = (integral\<^sup>N (\<mu> \<bind> h) (g \<circ> \<beta>))"
    apply(intro nn_integral_bind[symmetric,of _ real_borel])
    using assms(3) hb(1)
    by(auto intro!: measurable_prob_algebraD hb(2))
  finally show ?thesis
    using LHS by(simp add: comp_def)
qed

lemma qbs_prob_ennintegral_bind_return:
  assumes "s \<in> monadP_qbs_Px Y"
          "f \<in> Z \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "qbs_prob_ennintegral (s \<bind> (\<lambda>y. qbs_return Z (g y))) f = qbs_prob_ennintegral s (f \<circ> g)"
  apply(simp add: qbs_prob_ennintegral_bind[OF assms(1) qbs_return_morphism'[OF assms(3)] assms(2)])
  using assms(1,3)
  by(auto intro!: qbs_prob_ennintegral_cong qbs_prob_ennintegral_return[OF assms(2)]
            simp: monadP_qbs_Px_def)

lemma qbs_prob_integral_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  shows "(\<lambda>s. qbs_prob_integral s f) \<in> monadP_qbs X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
proof(rule qbs_morphismI;simp)
  fix \<alpha>
  assume "\<alpha> \<in> monadP_qbs_MPx X"
  then obtain \<beta> g where h:
   "\<beta> \<in> qbs_Mx X" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "\<alpha> = (\<lambda>r. qbs_prob_space (X, \<beta>, g r))"
    using rep_monadP_qbs_MPx[of \<alpha> X] by auto
  note [measurable] = h(2)
  have [measurable]: "f \<circ> \<beta> \<in> real_borel \<rightarrow>\<^sub>M real_borel"
    using assms h(1) by auto
  have "(\<lambda>s. qbs_prob_integral s f) \<circ> \<alpha> = (\<lambda>r. \<integral> x. f (\<beta> x) \<partial>g r)"
    apply standard
    using assms qbs_prob_MPx[OF h(1,2)] by(auto intro!: qbs_prob.qbs_prob_integral_def simp: h(3))
  also have "... = (\<lambda>M. integral\<^sup>L M (f \<circ> \<beta>)) \<circ> g"
    by (simp add: comp_def)
  also have "... \<in> real_borel \<rightarrow>\<^sub>M real_borel"
    by(auto intro!: measurable_comp[where N="subprob_algebra real_borel"] 
              simp: integral_measurable_subprob_algebra measurable_prob_algebraD)
  finally show "(\<lambda>s. qbs_prob_integral s f) \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M real_borel" .
qed

lemma qbs_morphism_integral_fst:
  assumes "q \<in> monadP_qbs_Px Y"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    shows "(\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
proof(rule qbs_morphismI,simp_all)
  fix \<alpha>
  assume ha:"\<alpha> \<in> qbs_Mx X"
  obtain \<beta> \<nu> where hq:
  "qbs_prob Y \<beta> \<nu>" "q = qbs_prob_space (Y, \<beta>, \<nu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then interpret qp: qbs_prob Y \<beta> \<nu> by simp
  have "(\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<circ> \<alpha> = (\<lambda>x. \<integral> y. f (\<alpha> x, \<beta> y) \<partial>\<nu>)"
    apply standard
    using qbs_morphism_Pair1'[OF qbs_Mx_to_X(2)[OF ha] assms(2)]
    by(auto intro!: qp.qbs_prob_integral_def
              simp: hq(2))
  also have "... \<in> borel_measurable borel"
    using qbs_morphism_comp[OF qbs_morphism_map_prod assms(2),of \<alpha> "\<real>\<^sub>Q" \<beta> "\<real>\<^sub>Q",simplified comp_def map_prod_def split_beta'] ha qp.in_Mx
    by(auto intro!: qp.borel_measurable_lebesgue_integral
              simp: qbs_Mx_is_morphisms)
  finally show "(\<lambda>x. \<integral>\<^sub>Q y. f (x, y) \<partial>q) \<circ> \<alpha> \<in> borel_measurable borel" .
qed

lemma qbs_morphism_integral_snd:
  assumes "p \<in> monadP_qbs_Px X"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    shows "(\<lambda>y. \<integral>\<^sub>Q x. f (x, y) \<partial>p) \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  using qbs_morphism_integral_fst[OF assms(1) qbs_morphism_pair_swap[OF assms(2)]]
  by simp

lemma qbs_prob_integral_morphism:
  assumes "L \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
          "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y \<real>\<^sub>Q"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> qbs_integrable (L x) (f x)"
    shows "(\<lambda>x. qbs_prob_integral (L x) (f x)) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
proof(rule qbs_morphismI;simp)
  fix \<alpha>
  assume h0:"\<alpha> \<in> qbs_Mx X"
  then obtain \<beta> g where h:
   "\<beta> \<in> qbs_Mx Y" "g \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(L \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, g r))"
    using rep_monadP_qbs_MPx[of "L \<circ> \<alpha>" Y] qbs_morphismE(3)[OF assms(1)] by auto
  have "(\<lambda>x. qbs_prob_integral (L x) (f x)) \<circ> \<alpha> = (\<lambda>r. qbs_prob_integral ((L \<circ> \<alpha>) r) ((f \<circ> \<alpha>) r))"
    by auto
  also have "... = (\<lambda>r. enn2real (qbs_prob_ennintegral ((L \<circ> \<alpha>) r) (\<lambda>x. ennreal ((f \<circ> \<alpha>) r x)))
                      - enn2real (qbs_prob_ennintegral ((L \<circ> \<alpha>) r) (\<lambda>x. ennreal (- (f \<circ> \<alpha>) r x))))"
    using h0 assms(3) by(auto intro!: real_qbs_prob_integral_def)
  also have "... \<in> real_borel \<rightarrow>\<^sub>M real_borel"
  proof -
    have h2:"L \<circ> \<alpha> \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q monadP_qbs Y"
      using qbs_morphismE(3)[OF assms(1) h0] by(auto simp: qbs_Mx_is_morphisms)
    have [measurable]:"(\<lambda>x. f (fst x) (snd x)) \<in> qbs_to_measure (X \<Otimes>\<^sub>Q Y) \<rightarrow>\<^sub>M real_borel"
      using uncurry_preserves_morphisms[OF assms(2)] by(auto simp: split_beta')
    have h3:"(\<lambda>r x. ennreal ((f \<circ> \<alpha>) r x)) \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs Y \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    proof(auto intro!: curry_preserves_morphisms[of "(\<lambda>(r,x). ennreal ((f \<circ> \<alpha>) r x))",simplified curry_def,simplified])
     have "(\<lambda>(r, y). ennreal (f (\<alpha> r) y)) = ennreal \<circ> case_prod f \<circ> map_prod \<alpha> id"
        by auto
      also have "... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
        apply(rule qbs_morphism_comp[where Y="X \<Otimes>\<^sub>Q Y"])
        using h0 qbs_morphism_map_prod[OF _ qbs_morphism_ident,of \<alpha> "\<real>\<^sub>Q" X Y]
        by(auto simp: qbs_Mx_is_morphisms)
      finally show "(\<lambda>(r, y). ennreal (f (\<alpha> r) y)) \<in> qbs_to_measure (\<real>\<^sub>Q \<Otimes>\<^sub>Q Y) \<rightarrow>\<^sub>M ennreal_borel"
        by auto
    qed
    have h4:"(\<lambda>r x. ennreal (- (f \<circ> \<alpha>) r x)) \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs Y \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    proof(auto intro!: curry_preserves_morphisms[of "(\<lambda>(r,x). ennreal (- (f \<circ> \<alpha>) r x))",simplified curry_def,simplified])
      have "(\<lambda>(r, y). ennreal (- f (\<alpha> r) y)) = ennreal \<circ> (\<lambda>r. - r) \<circ> case_prod f \<circ> map_prod \<alpha> id"
        by auto
      also have "... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
        apply(rule qbs_morphism_comp[where Y="X \<Otimes>\<^sub>Q Y"])
        using h0 qbs_morphism_map_prod[OF _ qbs_morphism_ident,of \<alpha> "\<real>\<^sub>Q" X Y]
        by(auto simp: qbs_Mx_is_morphisms)
      finally show "(\<lambda>(r, y). ennreal (- f (\<alpha> r) y)) \<in> qbs_to_measure (\<real>\<^sub>Q \<Otimes>\<^sub>Q Y) \<rightarrow>\<^sub>M ennreal_borel"
        by auto
    qed
    have "(\<lambda>r. qbs_prob_ennintegral ((L \<circ> \<alpha>) r) (\<lambda>x. ennreal ((f \<circ> \<alpha>) r x))) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
         "(\<lambda>r. qbs_prob_ennintegral ((L \<circ> \<alpha>) r) (\<lambda>x. ennreal (- (f \<circ> \<alpha>) r x))) \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
      using qbs_prob_ennintegral_morphism[OF h2 h3] qbs_prob_ennintegral_morphism[OF h2 h4]
      by auto
    thus ?thesis by simp
  qed
  finally show "(\<lambda>x. qbs_prob_integral (L x) (f x)) \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M real_borel" .
qed

lemma qbs_prob_integral_morphism'':
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "L \<in> Y \<rightarrow>\<^sub>Q monadP_qbs X"
    shows "(\<lambda>y. qbs_prob_integral (L y) f) \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  using qbs_morphism_comp[OF assms(2) qbs_prob_integral_morphism'[OF assms(1)]]
  by(simp add: comp_def)

lemma qbs_prob_integral_return:
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "x \<in> qbs_space X"
    shows "qbs_prob_integral (qbs_return X x) f = f x"
  using assms
  by(auto intro!: integral_return
        simp add: qbs_prob_integral_def2 qbs_prob_measure_return[OF assms(2)])

lemma qbs_prob_integral_bind:
  assumes "s \<in> monadP_qbs_Px X"
          "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
          "g \<in> Y \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "\<exists>K. \<forall>y \<in> qbs_space Y.\<bar>g y\<bar> \<le> K"
    shows "qbs_prob_integral (s \<bind> f) g = qbs_prob_integral s (\<lambda>y. (qbs_prob_integral (f y) g))"
          (is "?lhs = ?rhs")
proof -
  obtain K where hK:
   "\<And>y. y \<in> qbs_space Y \<Longrightarrow> \<bar>g y\<bar> \<le> K"
    using assms(4) by auto
  obtain \<alpha> \<mu> where hs:
   "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then obtain \<beta> h where hb:
   "\<beta> \<in> qbs_Mx Y" "h \<in> real_borel \<rightarrow>\<^sub>M prob_algebra real_borel"
   "(f \<circ> \<alpha>) = (\<lambda>r. qbs_prob_space (Y, \<beta>, h r))"
    using rep_monadP_qbs_MPx[of "f \<circ> \<alpha>" Y] qbs_morphismE(3)[OF assms(2)]
    by(auto simp add: qbs_prob_def in_Mx_def)
  note [measurable] = hb(2)
  interpret rd: real_distribution \<mu> by(simp add: hs(1)[simplified qbs_prob_def])
  have h:"qbs_prob Y \<beta> (\<mu> \<bind> h)"
         "s \<bind> f = qbs_prob_space (Y, \<beta>, \<mu> \<bind> h)"
    using qbs_prob.qbs_bind_computation[OF hs assms(2) hb] by auto

  hence "?lhs = (\<integral> x. g (\<beta> x) \<partial>(\<mu> \<bind> h))"
    by(simp add: qbs_prob.qbs_prob_integral_def[OF h(1) assms(3)])
  also have "... = (integral\<^sup>L (\<mu> \<bind> h) (g \<circ> \<beta>))" by(simp add: comp_def)
  also have "... = (\<integral> r. (\<integral> y. (g \<circ> \<beta>) y \<partial>(h r)) \<partial>\<mu>)"
    apply(rule integral_bind[of _ real_borel K _ _ 1])
    using assms(3) hb(1) hK measurable_space[OF hb(2)]
    by(auto intro!: measurable_prob_algebraD
         simp: space_prob_algebra prob_space.emeasure_le_1)
  also have "... = ?rhs"
    by(auto intro!: Bochner_Integration.integral_cong
       simp: qbs_prob.qbs_prob_integral_def[OF qbs_prob_MPx[OF hb(1,2)] assms(3)] fun_cong[OF hb(3),simplified comp_def] hs(2) qbs_prob.qbs_prob_integral_def[OF hs(1) qbs_prob_integral_morphism''[OF assms(3,2)]])
  finally show ?thesis .
qed

lemma qbs_prob_integral_bind_return:
  assumes "s \<in> monadP_qbs_Px Y"
          "f \<in> Z \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "qbs_prob_integral (s \<bind> (\<lambda>y. qbs_return Z (g y))) f = qbs_prob_integral s (f \<circ> g)"
proof -
  obtain \<alpha> \<mu> where hs:
   "qbs_prob Y \<alpha> \<mu>" "s = qbs_prob_space (Y, \<alpha>, \<mu>)"
    using rep_monadP_qbs_Px[OF assms(1)] by auto
  then interpret qp: qbs_prob Y \<alpha> \<mu> by simp
  have hb:"qbs_prob Z (g \<circ> \<alpha>) \<mu>"
          "s \<bind> (\<lambda>y. qbs_return Z (g y)) = qbs_prob_space (Z, g \<circ> \<alpha>, \<mu>)"
    by(auto intro!: qp.qbs_bind_computation[OF hs(2) qbs_return_morphism'[OF assms(3)] qbs_morphismE(3)[OF assms(3) qp.in_Mx],of "return real_borel",simplified bind_return''[of \<mu> real_borel,simplified] comp_def]
           simp: comp_def qbs_return_comp[OF qbs_morphismE(3)[OF assms(3) qp.in_Mx],simplified comp_def])
  thus ?thesis
    by(simp add: hb(2) qbs_prob.qbs_prob_integral_def[OF hb(1) assms(2)] hs(2) qbs_prob.qbs_prob_integral_def[OF hs(1) qbs_morphism_comp[OF assms(3,2)]])
qed

lemma qbs_prob_var_bind_return:
  assumes "s \<in> monadP_qbs_Px Y"
          "f \<in> Z \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "qbs_prob_var (s \<bind> (\<lambda>y. qbs_return Z (g y))) f = qbs_prob_var s (f \<circ> g)"
proof -
  have 1:"(\<lambda>x. (f x - qbs_prob_integral s (f \<circ> g))\<^sup>2) \<in> Z \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using assms(2,3) by auto
  thus ?thesis
    using qbs_prob_integral_bind_return[OF assms(1) 1 assms(3)] qbs_prob_integral_bind_return[OF assms]
    by(simp add: comp_def qbs_prob_var_def)
qed

end