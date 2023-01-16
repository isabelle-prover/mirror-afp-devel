(*  Title:   StandardBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Standard Borel Spaces\<close>
theory StandardBorel
  imports "HOL-Probability.Probability"
begin

text \<open>A standard Borel space is the Borel space associated with a Polish space.
      Here, we define standard Borel spaces in another, but equivallent, way.
      See \<^cite>\<open>"Heunen_2017"\<close> Proposition 5. \<close>
abbreviation "real_borel \<equiv> borel :: real measure"
abbreviation "nat_borel \<equiv> borel :: nat measure"
abbreviation "ennreal_borel \<equiv> borel :: ennreal measure"
abbreviation "bool_borel \<equiv> borel :: bool measure"


subsection \<open> Definition \<close>
locale standard_borel =
  fixes M :: "'a measure"
  assumes exist_fg: "\<exists>f \<in> M \<rightarrow>\<^sub>M real_borel. \<exists>g \<in> real_borel \<rightarrow>\<^sub>M M.
                     \<forall>x \<in> space M.  (g \<circ> f) x = x"
begin

abbreviation "fg \<equiv> (SOME k. (fst k) \<in> M \<rightarrow>\<^sub>M real_borel \<and> 
                           (snd k) \<in> real_borel \<rightarrow>\<^sub>M M \<and>
                           (\<forall>x \<in> space M.  ((snd k) \<circ> (fst k)) x = x))"

definition "f \<equiv> (fst fg)"
definition "g \<equiv> (snd fg)"

lemma 
  shows f_meas[simp,measurable]    :  "f \<in> M \<rightarrow>\<^sub>M real_borel"
    and g_meas[simp,measurable]    :  "g \<in> real_borel \<rightarrow>\<^sub>M M"
    and gf_comp_id[simp]:  "\<And>x. x \<in> space M \<Longrightarrow> (g \<circ> f) x = x"
                           "\<And>x. x \<in> space M \<Longrightarrow> g (f x) = x"
proof -
  obtain f' g' where h:
    "f' \<in> M \<rightarrow>\<^sub>M real_borel" "g' \<in> real_borel \<rightarrow>\<^sub>M M" "\<forall>x \<in> space M.  (g' \<circ> f') x = x"
    using exist_fg by blast
  have "f \<in> borel_measurable M \<and> g \<in> real_borel \<rightarrow>\<^sub>M M \<and> (\<forall>x\<in>space M. (g \<circ> f) x = x)"
    unfolding f_def g_def
    by(rule someI2[where a="(f',g')"]) (use h in auto)
  thus "f \<in> borel_measurable M" "g \<in> real_borel \<rightarrow>\<^sub>M M"
       "\<And>x. x \<in> space M \<Longrightarrow> (g \<circ> f) x = x" "\<And>x. x \<in> space M \<Longrightarrow> g (f x) = x"
    by auto
qed

lemma standard_borel_sets[simp]:
  assumes "sets M = sets Y"
  shows "standard_borel Y"
  unfolding standard_borel_def
  using measurable_cong_sets[OF assms refl,of real_borel] measurable_cong_sets[OF refl assms,of real_borel] sets_eq_imp_space_eq[OF assms] exist_fg
  by simp

lemma f_inj:
  "inj_on f (space M)"
  by standard (use gf_comp_id(2) in fastforce)

lemma singleton_sets:
  assumes "x \<in> space M"
    shows "{x} \<in> sets M"
proof -
  let ?y = "f x"
  let ?U = "f -` {?y}"
  have "?U \<inter> space M \<in> sets M"
    using borel_measurable_vimage f_meas by blast
  moreover have "?U \<inter> space M = {x}"
    using assms f_inj by(auto simp:inj_on_def)
  ultimately show ?thesis
    by simp
qed

lemma countable_space_discrete:
  assumes "countable (space M)"
  shows "sets M = sets (count_space (space M))"
proof
  show "sets (count_space (space M)) \<subseteq> sets M"
  proof auto
    fix U
    assume 1:"U \<subseteq> space M"
    then have 2:"countable U"
      using assms countable_subset by auto
    have 3:"U = (\<Union>x\<in>U. {x})" by auto
    moreover have "... \<in> sets M"
      by(rule sets.countable_UN''[of U "\<lambda>x. {x}"]) (use 1 2 singleton_sets in auto)
    ultimately show "U \<in> sets M"
      by simp
  qed
qed (simp add: sets.sets_into_space subsetI)

end

lemma standard_borelI:
  assumes "f \<in> Y \<rightarrow>\<^sub>M real_borel"
          "g \<in> real_borel \<rightarrow>\<^sub>M Y"
      and "\<And>y. y \<in> space Y \<Longrightarrow>  (g \<circ> f) y = y"
    shows "standard_borel Y"
  unfolding standard_borel_def
  by (intro bexI[OF _ assms(1)] bexI[OF _ assms(2)]) (auto dest: assms(3))


locale standard_borel_space_UNIV = standard_borel +
  assumes space_UNIV:"space M = UNIV"
begin

lemma gf_comp_id'[simp]:
  "g \<circ> f = id" "g (f x) = x"
  using space_UNIV gf_comp_id
  by(simp_all add: id_def comp_def)

lemma f_inj':
  "inj f"
  using f_inj by(simp add: space_UNIV)

lemma g_surj':
  "surj g"
  using gf_comp_id'(2) surjI by blast

end

lemma standard_borel_space_UNIVI:
  assumes "f \<in> Y \<rightarrow>\<^sub>M real_borel"
          "g \<in> real_borel \<rightarrow>\<^sub>M Y"
          "(g \<circ> f) = id"
      and "space Y = UNIV"
    shows "standard_borel_space_UNIV Y"
  using assms
  by(auto intro!: standard_borelI simp: standard_borel_space_UNIV_def standard_borel_space_UNIV_axioms_def)

lemma standard_borel_space_UNIVI':
  assumes "standard_borel Y"
      and "space Y = UNIV"
    shows "standard_borel_space_UNIV Y"
  using assms by(simp add: standard_borel_space_UNIV_def standard_borel_space_UNIV_axioms_def)

subsection \<open> $\mathbb{R}$, $\mathbb{N}$, Boolean, $[0,\infty]$ \<close>
text \<open> $\mathbb{R}$ is a standard Borel space. \<close>
interpretation real : standard_borel_space_UNIV "real_borel"
  by(auto intro!: standard_borel_space_UNIVI)  

text\<open> A non-empty Borel subspace of $\mathbb{R}$ is also a standard Borel space. \<close>
lemma real_standard_borel_subset:
  assumes "U \<in> sets real_borel"
      and "U \<noteq> {}"
    shows "standard_borel (restrict_space real_borel U)"
proof -
  have std1: "id \<in> (restrict_space real_borel U) \<rightarrow>\<^sub>M real_borel"
    by (simp add: measurable_restrict_space1)
  obtain x where hx : "x \<in> U"
    using assms(2) by auto
  define g :: "real \<Rightarrow> real"
    where "g \<equiv> (\<lambda>r. if r \<in> U then r else x)"
  have "g \<in> real_borel \<rightarrow>\<^sub>M real_borel"
    unfolding g_def by(rule borel_measurable_continuous_on_if) (simp_all add: assms(1))
  hence std2: "g \<in> real_borel \<rightarrow>\<^sub>M (restrict_space real_borel U)"
    by(auto intro!: measurable_restrict_space2 simp: g_def hx)
  have std3: "\<forall>y\<in> space (restrict_space real_borel U). (g \<circ> id) y = y"
    by(simp add: g_def space_restrict_space)
  show ?thesis
    using std1 std2 std3 standard_borel_def by blast
qed

text \<open> A non-empty measurable subset of a standard Borel space is also a standard Borel space.\<close>
lemma(in standard_borel) standard_borel_subset:
  assumes "U \<in> sets M"
          "U \<noteq> {}"
    shows "standard_borel (restrict_space M U)"
proof -
  let ?ginvU = "g -` U"
  have hgu1:"?ginvU \<in> sets real_borel"
    using assms(1) g_meas measurable_sets_borel by blast
  have hgu2:"f ` U \<subseteq> ?ginvU"
    using gf_comp_id sets.sets_into_space[OF assms(1)] by fastforce
  hence hgu3:"?ginvU \<noteq> {}"
    using assms(2) by blast
  interpret r_borel_set: standard_borel "restrict_space real_borel ?ginvU"
    by(rule real_standard_borel_subset[OF hgu1 hgu3])
 
  have std1: "r_borel_set.f \<circ> f \<in> (restrict_space M U) \<rightarrow>\<^sub>M real_borel"
    using sets.sets_into_space[OF assms(1)]
    by(auto intro!: measurable_comp[where N="restrict_space real_borel ?ginvU"] measurable_restrict_space3)
  have std2: "g \<circ> r_borel_set.g \<in> real_borel \<rightarrow>\<^sub>M (restrict_space M U)"
    by(auto intro!: measurable_comp[where N="restrict_space real_borel ?ginvU"] measurable_restrict_space3[OF g_meas])
  have std3: "\<forall>x\<in> space (restrict_space M U). ((g \<circ> r_borel_set.g) \<circ> (r_borel_set.f \<circ> f)) x = x"
    by (simp add: space_restrict_space)
  show ?thesis
    using std1 std2 std3 standard_borel_def by blast
qed

text \<open> $\mathbb{N}$ is a standard Borel space. \<close>
interpretation nat : standard_borel_space_UNIV nat_borel
proof -
  define n_to_r :: "nat \<Rightarrow> real"
    where "n_to_r \<equiv> (\<lambda>n. of_real n)"
  define r_to_n :: "real \<Rightarrow> nat"
    where "r_to_n \<equiv> (\<lambda>r. nat \<lfloor>r\<rfloor>)"

  have n_to_r_measurable: "n_to_r \<in> nat_borel \<rightarrow>\<^sub>M real_borel"
    using borel_measurable_count_space measurable_cong_sets sets_borel_eq_count_space
    by blast
  have r_to_n_measurable: "r_to_n \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
    by(simp add: r_to_n_def)
  have n_to_r_to_n_id: "r_to_n \<circ> n_to_r = id"
    by(simp add: n_to_r_def r_to_n_def comp_def id_def)
  show "standard_borel_space_UNIV nat_borel"
    using standard_borel_space_UNIVI[OF n_to_r_measurable r_to_n_measurable n_to_r_to_n_id]
    by simp
qed

text \<open> For a countable space $X$, $X$ is a standard Borel space iff $X$ is a discrete space. \<close>
lemma countable_standard_iff:
  assumes "space X \<noteq> {}"
      and "countable (space X)"
  shows "standard_borel X \<longleftrightarrow> sets X = sets (count_space (space X))"
proof
  show "standard_borel X \<Longrightarrow> sets X = sets (count_space (space X))"
    using standard_borel.countable_space_discrete assms by simp
next
  assume h[measurable_cong]: "sets X = sets (count_space (space X))"
  show "standard_borel X"
  proof(rule standard_borelI[where f="nat.f \<circ> to_nat_on (space X)" and g="from_nat_into (space X) \<circ> nat.g"])
    show "nat.f \<circ> to_nat_on (space X) \<in> borel_measurable X"
      by simp
  next
    have [simp]: "from_nat_into (space X) \<in> UNIV \<rightarrow> (space X)"
      using from_nat_into[OF assms(1)] by simp
    hence [measurable]: "from_nat_into (space X) \<in> nat_borel \<rightarrow>\<^sub>M X"
      using measurable_count_space_eq1[of _ _ X] measurable_cong_sets[OF sets_borel_eq_count_space]
      by blast
    show "from_nat_into (space X) \<circ> nat.g \<in> real_borel \<rightarrow>\<^sub>M X"
      by simp
  next
    fix x
    assume "x \<in> space X"
    then show "(from_nat_into (space X) \<circ> nat.g \<circ> (nat.f \<circ> to_nat_on (space X))) x = x"
      using from_nat_into_to_nat_on[OF assms(2)] by simp
  qed
qed

text \<open> $\mathbb{B}$ is a standard Borel space. \<close>
lemma to_bool_measurable:
  assumes "f -` {True} \<inter> space M  \<in> sets M"
  shows "f \<in> M \<rightarrow>\<^sub>M bool_borel"
proof(rule measurableI)
  fix A
  assume h:"A \<in> sets bool_borel"
  have h2: "f -` {False} \<inter> space M  \<in> sets M"
  proof -
    have "- {False} = {True}"
      by auto
    thus ?thesis
      by(simp add: vimage_sets_compl_iff[where A="{False}"] assms)
  qed
  have "A \<subseteq> {True,False}"
    by auto
  then consider "A = {}" | "A = {True}" | "A = {False}" | "A = {True,False}"
    by auto
  thus "f -` A \<inter> space M \<in> sets M"
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      by(simp add: assms)
  next
    case 3
    then show ?thesis
      by(simp add: h2)
  next
    case 4
    then have "f -` A = f -` {True} \<union> f -` {False}"
      by auto
    thus ?thesis
      using assms h2
      by (metis Int_Un_distrib2 sets.Un)
  qed
qed simp

interpretation bool : standard_borel_space_UNIV bool_borel
  using countable_standard_iff[of bool_borel]
  by(auto intro!: standard_borel_space_UNIVI' simp: sets_borel_eq_count_space)


text \<open> $[0,\infty]$ (the set of extended non-negative real numbers) is a standard Borel space.  \<close>
interpretation ennreal : standard_borel_space_UNIV ennreal_borel
proof -
  define preal_to_real :: "ennreal \<Rightarrow> real"
    where "preal_to_real \<equiv> (\<lambda>r. if r = \<infinity> then -1
                                           else enn2real r)"
  define real_to_preal :: "real \<Rightarrow> ennreal"
    where "real_to_preal \<equiv> (\<lambda>r. if r = -1 then \<infinity>
                                          else ennreal r)"
  have preal_to_real_measurable: "preal_to_real \<in> ennreal_borel \<rightarrow>\<^sub>M real_borel"
    unfolding preal_to_real_def by simp
  have real_to_preal_measurable: "real_to_preal \<in> real_borel \<rightarrow>\<^sub>M ennreal_borel"
    unfolding real_to_preal_def by simp
  have preal_real_preal_id: "real_to_preal \<circ> preal_to_real = id"
  proof
    fix r :: ennreal
    show "(real_to_preal \<circ> preal_to_real) r = id r"
      using ennreal_enn2real_if[of r] ennreal_neg
      by(auto simp add: real_to_preal_def preal_to_real_def)
  qed
  show "standard_borel_space_UNIV ennreal_borel"
    using standard_borel_space_UNIVI[OF preal_to_real_measurable real_to_preal_measurable preal_real_preal_id]
    by simp
qed

subsection \<open> $\mathbb{R}\times\mathbb{R}$ \<close>
definition real_to_01open :: "real \<Rightarrow> real" where
"real_to_01open r \<equiv> arctan r / pi + 1 / 2"

definition real_to_01open_inverse :: "real \<Rightarrow> real" where
"real_to_01open_inverse r \<equiv> tan (pi * r - (pi / 2))"

lemma real_to_01open_inverse_correct:
 "real_to_01open_inverse \<circ> real_to_01open = id"
  by(auto simp add: real_to_01open_def real_to_01open_inverse_def distrib_left tan_arctan)

lemma real_to_01open_inverse_correct':
  assumes "0 < r" "r < 1"
  shows "real_to_01open (real_to_01open_inverse r) = r"
  unfolding real_to_01open_def real_to_01open_inverse_def
proof -
  have "arctan (tan (pi * r - pi / 2)) = pi * r - pi / 2"
    using  arctan_unique[of "pi * r - pi / 2"] assms
    by simp
  hence "arctan (tan (pi * r - pi / 2)) / pi + 1 / 2 = ((pi * r) - pi / 2)/ pi + 1/2"
    by simp
  also have "... = r - 1/2 + 1/2"
    by (metis (no_types, opaque_lifting) divide_inverse mult.left_neutral nonzero_mult_div_cancel_left pi_neq_zero right_diff_distrib)
  finally show "arctan (tan (pi * r - pi / 2)) / pi + 1 / 2 = r"
    by simp
qed

lemma real_to_01open_01 :
 "0 < real_to_01open r \<and> real_to_01open r < 1"
proof
  have "- pi / 2 < arctan r" by(simp add: arctan_lbound)
  hence "0 < arctan r + pi / 2" by simp
  hence "0 < (1 / pi) * (arctan r + pi / 2)" by simp
  thus "0 < real_to_01open r"
    by (simp add: add_divide_distrib real_to_01open_def)
next
  have "arctan r < pi / 2" using arctan_ubound by simp
  hence "arctan r + pi / 2 < pi" by simp
  hence "(1 / pi) * (arctan r + pi / 2) < 1" by simp
  thus "real_to_01open r < 1"
    by(simp add: real_to_01open_def add_divide_distrib)
qed

lemma real_to_01open_continuous:
 "continuous_on UNIV real_to_01open"
proof -
  have "continuous_on UNIV ((\<lambda>x. x / pi + 1 / 2) \<circ> arctan)"
  proof (rule continuous_on_compose)
    show "continuous_on UNIV arctan"
      by (simp add: continuous_on_arctan)
  next
    show "continuous_on (range arctan) (\<lambda>x. x / pi + 1 / 2)"
      by(auto intro!: continuous_on_add continuous_on_divide)
  qed
  thus ?thesis
    by(simp add: real_to_01open_def)
qed

lemma real_to_01open_inverse_continuous:
 "continuous_on {0<..<1} real_to_01open_inverse"
  unfolding real_to_01open_inverse_def
proof(rule Transcendental.continuous_on_tan)
  have [simp]: "(\<lambda>x. pi * x - pi / 2) = (\<lambda>x. x - pi/2) \<circ> (\<lambda>x. pi * x)"
    by auto
  have "continuous_on {0<..<1} ..."
  proof(rule continuous_on_compose)
    show "continuous_on {0<..<1} ((*) pi)"
      by simp
  next
    show "continuous_on ((*) pi ` {0<..<1}) (\<lambda>x. x - pi / 2)"
      using continuous_on_diff[of "(*) pi ` {0<..<1}" "\<lambda>x. x"]
      by simp
  qed
  thus "continuous_on {0<..<1} (\<lambda>x. pi * x - pi / 2)" by simp
next
  have "\<forall>r\<in>{0<..<1::real}. -(pi/2) < pi * r - pi / 2 \<and> pi * r - pi / 2 < pi/2"
    by simp
  thus "\<forall>r\<in>{0<..<1::real}. cos (pi * r - pi / 2) \<noteq> 0"
    using cos_gt_zero_pi by fastforce
qed

lemma real_to_01open_inverse_measurable:
 "real_to_01open_inverse \<in> restrict_space real_borel {0<..<1} \<rightarrow>\<^sub>M real_borel"
  using borel_measurable_continuous_on_restrict real_to_01open_inverse_continuous
  by simp

fun r01_binary_expansion'' :: "real \<Rightarrow> nat \<Rightarrow> nat \<times> real \<times> real" where
"r01_binary_expansion'' r 0 = (if 1/2 \<le> r then (1,1  ,1/2)
                                            else (0,1/2,  0))" |
"r01_binary_expansion'' r (Suc n) = (let (_,ur,lr) = r01_binary_expansion'' r n;
                                           k = (ur + lr)/2 in
                                           (if k \<le> r then (1,ur,k)
                                                     else (0,k,lr)))"


text \<open> $a_n$  where $r = 0.a_0 a_1 a_2 ....$ for $0 < r < 1$.\<close>
definition r01_binary_expansion' :: "real \<Rightarrow> nat \<Rightarrow> nat" where
"r01_binary_expansion' r n \<equiv> fst (r01_binary_expansion'' r n)"

text \<open>$a_n = 0$ or $1$.\<close>
lemma real01_binary_expansion'_0or1:
  "r01_binary_expansion' r n \<in> {0,1}"
  by (cases n) (simp_all add: r01_binary_expansion'_def split_beta' Let_def)

(* S_n = a_0 + ... + a_n *)
definition r01_binary_sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> real" where
"r01_binary_sum a n \<equiv> (\<Sum>i=0..n. real (a i) * ((1/2)^(Suc i)))"

definition r01_binary_sum_lim :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where
"r01_binary_sum_lim  \<equiv> lim \<circ> r01_binary_sum" 


definition r01_binary_expression :: "real \<Rightarrow> nat \<Rightarrow> real" where
"r01_binary_expression \<equiv> r01_binary_sum \<circ> r01_binary_expansion'"

lemma r01_binary_expansion_lr_r_ur:
  assumes "0 < r" "r < 1"
  shows "(snd (snd (r01_binary_expansion'' r n))) \<le> r \<and>
         r < (fst (snd (r01_binary_expansion'' r n)))"
  using assms by (induction n) (simp_all add:split_beta' Let_def)

text \<open>\<open>0 \<le> lr \<and> lr < ur \<and> ur \<le> 1\<close>.\<close>
lemma r01_binary_expansion_lr_ur_nn:
  shows "0 \<le> snd (snd (r01_binary_expansion'' r n)) \<and>
         snd (snd (r01_binary_expansion'' r n)) < fst (snd (r01_binary_expansion'' r n)) \<and>
         fst (snd (r01_binary_expansion'' r n)) \<le> 1"
  by (induction n) (simp_all add:split_beta' Let_def)

lemma r01_binary_expansion_diff:
  shows "(fst (snd (r01_binary_expansion'' r n))) - (snd (snd (r01_binary_expansion'' r n))) = (1/2)^(Suc n)"
proof(induction n)
  case (Suc n')
  then show ?case
  proof(cases "r01_binary_expansion'' r n'")
    case 1:(fields a ur lr)
    assume "fst (snd (r01_binary_expansion'' r n')) - snd (snd (r01_binary_expansion'' r n')) = (1 / 2) ^ (Suc n')"
    then have 2:"ur - lr = (1/2)^(Suc n')" by (simp add: 1)
    show ?thesis
    proof -
      have [simp]:"ur * 4 - (ur * 4 + lr * 4) / 2 = (ur - lr) * 2"
        by(simp add: division_ring_class.add_divide_distrib)
      have "ur * 4 - (ur * 4 + lr * 4) / 2 = (1 / 2) ^ n'"
        by(simp add: 2)
      moreover have "(ur * 4 + lr * 4) / 2 - lr * 4 = (1 / 2) ^ n'"
        by(simp add: division_ring_class.add_divide_distrib ring_class.right_diff_distrib[symmetric] 2)
      ultimately show ?thesis
        by(simp add: 1 Let_def)
    qed
  qed
qed simp

text \<open>\<open>lrn = Sn\<close>.\<close>
lemma r01_binary_expression_eq_lr:
  "snd (snd (r01_binary_expansion'' r n)) = r01_binary_expression r n"
proof(induction n)
  case 0
  then show ?case
    by(simp add: r01_binary_expression_def r01_binary_sum_def r01_binary_expansion'_def)
next
  case 1:(Suc n')
  show ?case
  proof (cases "r01_binary_expansion'' r n'")
    case 2:(fields a ur lr)
    then have ih:"lr = (\<Sum>i = 0..n'. real (fst (r01_binary_expansion'' r i)) * (1 / 2) ^ i / 2)"
      using 1 by(simp add: r01_binary_expression_def r01_binary_sum_def r01_binary_expansion'_def)
    have 3:"(ur + lr) / 2 = lr + (1/2)^(Suc (Suc n'))"
      using r01_binary_expansion_diff[of r n'] 2 by simp
    show ?thesis
      by(simp add: r01_binary_expression_def r01_binary_sum_def r01_binary_expansion'_def 2 Let_def 3) fact
  qed
qed

lemma r01_binary_expression'_sum_range:
 "\<exists>k::nat.  (snd (snd (r01_binary_expansion'' r n))) = real k/2^(Suc n) \<and>
             k < 2^(Suc n) \<and>
            ((r01_binary_expansion' r n) = 0 \<longrightarrow> even k) \<and>
            ((r01_binary_expansion' r n) = 1 \<longrightarrow> odd k)"
proof -
  have [simp]:"(snd (snd (r01_binary_expansion'' r n))) = (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i)))"
    using r01_binary_expression_eq_lr[of r n] by(simp add: r01_binary_expression_def r01_binary_sum_def)
  have "\<exists>k::nat. (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i))) = real k/2^(Suc n) \<and>
             k < 2^(Suc n) \<and>
            ((r01_binary_expansion' r n) = 0 \<longrightarrow> even k) \<and>
            ((r01_binary_expansion' r n) = 1 \<longrightarrow> odd k)"
  proof(induction n)
    case 0
    consider "r01_binary_expansion' r 0 = 0" | "r01_binary_expansion' r 0 = 1"
      using real01_binary_expansion'_0or1[of r 0] by auto
    then show ?case
      by cases auto
  next
    case (Suc n')
    then obtain k :: nat where ih:
     "(\<Sum>i = 0..n'. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i) = real k / 2^(Suc n') \<and> k < 2^(Suc n')"
      by auto
    have "(\<Sum>i = 0..Suc n'. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i) = (\<Sum>i = 0..n'. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i) + real (r01_binary_expansion' r (Suc n')) * (1 / 2) ^ Suc (Suc n')"
      by simp
    also have "... = real k / 2^(Suc n') + (real (r01_binary_expansion' r (Suc n')))/ 2^ Suc (Suc n')"
    proof -
      have "\<And>r ra n. (r::real) * (1 / ra) ^ n = r / ra ^ n"
        by (simp add: power_one_over)
      then show ?thesis
        using ih by presburger
    qed
    also have "... = (2*real k) / 2^(Suc (Suc n')) + (real (r01_binary_expansion' r (Suc n')))/ 2^ Suc (Suc n')"
      by simp
    also have "... = (2*(real k) + real (r01_binary_expansion' r (Suc n')))/2 ^ Suc (Suc n')"
      by (simp add: add_divide_distrib)
    also have "... = (real (2*k + r01_binary_expansion' r (Suc n')))/2 ^ Suc (Suc n')"
      by simp
    finally have "(\<Sum>i = 0..Suc n'. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i) = real (2 * k + r01_binary_expansion' r (Suc n')) / 2 ^ Suc (Suc n')" .
    moreover have "2 * k + r01_binary_expansion' r (Suc n') < 2^Suc (Suc n')"
    proof -
      have "k + 1 \<le> 2^Suc n'"
        using ih by simp
      hence "2*k + 2 \<le> 2^Suc (Suc n')"
        by simp
      thus ?thesis
        using real01_binary_expansion'_0or1[of r "Suc n'"]
        by auto
    qed
    moreover have "r01_binary_expansion' r (Suc n') = 0 \<longrightarrow> even (2 * k + r01_binary_expansion' r (Suc n'))"
      by simp
    moreover have "r01_binary_expansion' r (Suc n') = 1 \<longrightarrow> odd (2 * k + r01_binary_expansion' r (Suc n'))"
      by simp
    ultimately show ?case by fastforce
  qed
  thus ?thesis
    by simp
qed

text \<open>\<open>an = bn \<leftrightarrow> Sn = S'n\<close>.\<close>
lemma r01_binary_expansion'_expression_eq:
  "r01_binary_expansion' r1 = r01_binary_expansion' r2 \<longleftrightarrow>
   r01_binary_expression r1 = r01_binary_expression r2"
proof
  assume "r01_binary_expansion' r1 = r01_binary_expansion' r2"
  then show "r01_binary_expression r1 = r01_binary_expression r2"
    by(simp add: r01_binary_expression_def)
next
  assume "r01_binary_expression r1 = r01_binary_expression r2"
  then have 1:"\<And>n. r01_binary_sum (r01_binary_expansion' r1) n = r01_binary_sum (r01_binary_expansion' r2) n"
    by(simp add: r01_binary_expression_def)
  show "r01_binary_expansion' r1 = r01_binary_expansion' r2"
  proof
    fix n
    show " r01_binary_expansion' r1 n = r01_binary_expansion' r2 n"
    proof(cases n)
      case 0
      then show ?thesis
        using 1[of 0] by(simp add: r01_binary_sum_def)
    next
      fix n'
      case (Suc n')
      have "r01_binary_sum (r01_binary_expansion' r1) n - r01_binary_sum (r01_binary_expansion' r1) n' = r01_binary_sum (r01_binary_expansion' r2) n - r01_binary_sum (r01_binary_expansion' r2) n'"
        by(simp add: 1)
      thus ?thesis
        using \<open>n = Suc n'\<close> by(simp add: r01_binary_sum_def)
    qed
  qed
qed

lemma power2_e:
 "\<And>e::real. 0 < e \<Longrightarrow> \<exists>n::nat. real_of_rat (1/2)^n < e"
  by (simp add: real_arch_pow_inv)

lemma r01_binary_expression_converges_to_r:
  assumes "0 < r"
     and  "r < 1"
   shows "LIMSEQ (r01_binary_expression r)  r"
proof
  fix e :: real
  assume "0 < e"
  then obtain k :: nat where hk:"real_of_rat (1/2)^k < e"
    using power2_e by auto
  show "\<forall>\<^sub>F x in sequentially. dist (r01_binary_expression r x) r < e"
  proof(rule eventually_sequentiallyI[of k])
    fix m
    assume "k \<le> m"
    have "\<bar> r - r01_binary_expression r m \<bar> < e"
    proof (cases "r01_binary_expansion'' r m")
      case 1:(fields a ur lr)
      then have "\<bar>r - r01_binary_expression r m\<bar> = \<bar>r - lr\<bar>"
        by (metis r01_binary_expression_eq_lr snd_conv)
      also have "... = r - lr"
        using r01_binary_expansion_lr_r_ur[OF assms] 1        
        by (metis abs_of_nonneg diff_ge_0_iff_ge snd_conv)
      also have "... < e"
      proof -
        have "r - lr \<le> ur - lr"
          using r01_binary_expansion_lr_r_ur[of r] assms 1
          by (metis diff_right_mono fst_conv less_imp_le snd_conv)
        also have "... = (1/2)^(Suc m)"
          using r01_binary_expansion_diff[of r m]
          by(simp add: 1)
        also have "... \<le> (1/2)^(Suc k)"
          using \<open>k \<le> m\<close> by simp
        also have "... < (1/2)^k" by simp
        finally show ?thesis
          using hk by (simp add: of_rat_divide)
      qed
      finally show ?thesis .
    qed      
    then show "dist (r01_binary_expression r m) r < e"
      by (simp add: dist_real_def)
  qed
qed

lemma r01_binary_expression_correct:
  assumes "0 < r"
     and  "r < 1"
   shows "r = (\<Sum>n. real (r01_binary_expansion' r n) * (1/2)^(Suc n))"
proof -
  have "(\<lambda>n. (\<lambda>n. \<Sum>i<n. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i) (Suc n)) = r01_binary_expression r"
  proof -
    have "\<And>n. {..<Suc n} = {0..n}" by auto
    thus ?thesis
      by(auto simp add: r01_binary_expression_def r01_binary_sum_def)
  qed
  hence "LIMSEQ (\<lambda>n. \<Sum>i<n. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i)  r"
    using r01_binary_expression_converges_to_r[OF assms] LIMSEQ_imp_Suc[of "\<lambda>n. \<Sum>i<n. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i" r]
    by simp
  thus ?thesis
    using suminf_eq_lim[of "\<lambda>n. real (r01_binary_expansion' r n) * (1/2)^(Suc n)"] assms limI[of "(\<lambda>n. \<Sum>i<n. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i)" r]
    by simp
qed


text \<open>\<open>S0 \<le> S1 \<le> S2 \<le> ...\<close>.\<close>
lemma binary_sum_incseq:
   "incseq (r01_binary_sum a)"
  by(simp add: incseq_Suc_iff r01_binary_sum_def)

lemma r01_eq_iff:
  assumes "0 < r1" "r1 < 1"
          "0 < r2" "r2 < 1"
    shows "r1 = r2 \<longleftrightarrow> r01_binary_expansion' r1 = r01_binary_expansion' r2"
proof auto
  assume "r01_binary_expansion' r1 = r01_binary_expansion' r2"
  then have 1:"r01_binary_expression r1 = r01_binary_expression r2"
    using r01_binary_expansion'_expression_eq[of r1 r2] by simp
  have "r1 = lim (r01_binary_expression r1)"
    using limI[of _ r1] r01_binary_expression_converges_to_r[of r1] assms(1,2)
    by simp
  also have "... = lim (r01_binary_expression r2)"
    by (simp add: 1)
  also have "... = r2"
    using limI[of _ r2] r01_binary_expression_converges_to_r[of r2] assms(3,4)
    by simp
  finally show "r1 = r2" .
qed

lemma power_half_summable:
 "summable (\<lambda>n. ((1::real) / 2) ^ Suc n)"
  using power_half_series summable_def by blast


lemma binary_expression_summable:
   assumes "\<And>n. a n \<in> {0,1 :: nat}"
   shows "summable (\<lambda>n. real (a n) * (1/2)^(Suc n))"
proof -
  have "summable (\<lambda>n::nat. \<bar>real (a n) * ((1::real) / (2::real)) ^ Suc n\<bar>)"
  proof(rule summable_rabs_comparison_test[of "\<lambda>n. real (a n) * (1/2)^(Suc n)" "\<lambda>n. (1/2)^(Suc n)"])
    have "\<And>n. \<bar>real (a n) * (1 / 2) ^ Suc n\<bar> \<le> (1 / 2)^(Suc n)"
    proof -
      fix n
      have "\<bar>real (a n) * (1 / 2) ^ Suc n\<bar> = real (a n) * (1 / 2) ^ Suc n"
        using assms by simp
      also have "... \<le> (1 / 2) ^ Suc n"
      proof -
        consider "a n = 0" | "a n = 1"
          using assms by (meson insertE singleton_iff)
        then show ?thesis
          by(cases,auto)
      qed
      finally show "\<bar>real (a n) * (1 / 2) ^ Suc n\<bar> \<le> (1 / 2)^(Suc n)" .
    qed
    thus "\<exists>N. \<forall>n\<ge>N. \<bar>real (a n) * (1 / 2) ^ Suc n\<bar> \<le> (1 / 2) ^ Suc n"
      by simp
  next
    show "summable (\<lambda>n. ((1::real) / 2) ^ Suc n)"
      using power_half_summable by simp
  qed
  thus ?thesis by simp
qed

lemma binary_expression_gteq0:
  assumes "\<And>n. a n \<in> {0,1 :: nat}"
  shows "0 \<le> (\<Sum>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k))"
proof -
  have "(\<Sum>n. 0) \<le> (\<Sum>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k))"
    using binary_expression_summable[of a] summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" k] suminf_le[of "\<lambda>n. 0" "\<lambda>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k)"] assms
    by simp
  thus ?thesis by simp
qed

lemma binary_expression_leeq1:
  assumes "\<And>n. a n \<in> {0,1 :: nat}"
  shows "(\<Sum>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k)) \<le> 1"
proof -
  have "(\<Sum>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k)) \<le> (\<Sum>n. (1/2)^(Suc n))"
  proof(rule suminf_le)
    fix n
    have 1:"real (a (n + k)) * (1 / 2) ^ Suc (n + k) \<le> (1 / 2) ^ Suc (n + k)"
      using assms[of "n+k"] by auto
    have 2:"((1::real) / 2) ^ Suc (n + k) \<le> (1 / 2) ^ Suc n"
      by simp
    show "real (a (n + k)) * (1 / 2) ^ Suc (n + k) \<le> (1 / 2) ^ Suc n"
      by(rule order.trans[OF 1 2])
  next
    show "summable (\<lambda>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k))"
      using binary_expression_summable[of a] summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" k] assms
      by simp
  next
    show "summable (\<lambda>n. ((1::real) / 2) ^ Suc n)"
      using power_half_summable by simp
  qed
  thus ?thesis
    using power_half_series sums_unique by fastforce
qed

lemma binary_expression_less_than:
  assumes "\<And>n. a n \<in> {0,1 :: nat}"
  shows "(\<Sum>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k)) \<le> (\<Sum>n. (1 / 2) ^ Suc (n + k))"
proof(rule suminf_le)
  fix n
  show "real (a (n + k)) * (1 / 2) ^ Suc (n + k) \<le> (1 / 2) ^ Suc (n + k)"
    using assms[of "n + k"] by auto
next
  show "summable (\<lambda>n. real (a (n + k)) * (1 / 2) ^ Suc (n + k))"
    using summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" k] binary_expression_summable[of a] assms
    by simp
next
  show "summable (\<lambda>n. ((1::real) / 2) ^ Suc (n + k))"
    using power_half_summable summable_iff_shift[of "\<lambda>n. ((1::real) / 2) ^ Suc n" k]
    by simp
qed

lemma lim_sum_ai:
  assumes "\<And>n. a n \<in> {0,1 :: nat}"
  shows "lim (\<lambda>n. (\<Sum>i=0..n. real (a i) * (1/2)^(Suc i))) = (\<Sum>n::nat. real (a n) * (1/2)^(Suc n))"
proof -
  have "\<And>n::nat. {0..n} = {..n}" by auto
  hence "LIMSEQ (\<lambda>n. \<Sum>i=0..n. real (a i) * (1 / 2) ^ Suc i) (\<Sum>n. real (a n) * (1 / 2) ^ Suc n)"
    using summable_LIMSEQ'[of "\<lambda>n. real (a n) * (1/2)^(Suc n)"] binary_expression_summable[of a] assms
    by simp
  thus "lim (\<lambda>n. (\<Sum>i=0..n. real (a i) * (1/2)^(Suc i))) = (\<Sum>n. real (a n) * (1 / 2) ^ Suc n)"
    using limI by simp
qed

lemma half_1_minus_sum:
 "1 - (\<Sum>i<k. ((1::real) / 2) ^ Suc i) = (1/2)^k"
  by(induction k) auto

lemma half_sum:
  "(\<Sum>n. ((1::real) / 2) ^ (Suc (n + k))) = (1/2)^k"
  using suminf_split_initial_segment[of "\<lambda>n. ((1::real) / 2) ^ (Suc n)" k] half_1_minus_sum[of k] power_half_series sums_unique[of "\<lambda>n. (1 / 2) ^ Suc n" 1] power_half_summable
  by fastforce

lemma ai_exists0_less_than_sum:
  assumes "\<And>n. a n \<in> {0,1}"
          "i \<ge> m"
      and "a i = 0"
    shows "(\<Sum>n::nat. real (a (n + m)) * (1/2)^(Suc (n + m))) < (1 / 2) ^ m"
proof -
  have "(\<Sum>n::nat. real (a (n + m)) * (1/2)^(Suc (n + m))) = (\<Sum>n<i-m. real (a (n + m)) * (1/2)^(Suc (n + m))) + (\<Sum>n::nat. real (a (n + i)) * (1/2)^(Suc (n + i)))"
    using suminf_split_initial_segment[of "\<lambda>n. real (a (n + m)) * (1/2)^(Suc (n + m))" "i-m"] assms(1) binary_expression_summable[of a] summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" m] assms(2)
    by simp
  also have "... < (1 / 2) ^ m"
  proof -
    have "(\<Sum>n. real (a (n + i)) * (1 / 2) ^ Suc (n + i)) \<le> (1 / 2) ^ Suc i"
    proof -
      have "(\<Sum>n::nat. real (a (n + i)) * (1/2)^(Suc (n + i))) = (\<Sum>n::nat. real (a (Suc n + i)) * (1/2)^(Suc (Suc n + i)))"
        using suminf_split_head[of "\<lambda>n. real (a (n + i)) * (1/2)^(Suc (n + i))"] assms(1,3) binary_expression_summable[of a] summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" i]
        by simp
      also have "... = (\<Sum>n::nat. real (a (n + Suc i)) * (1/2)^(Suc n + Suc i))"
        by simp
      also have "... \<le> (\<Sum>n::nat. (1/2)^(Suc n + Suc i))"
        using binary_expression_less_than[of a "Suc i"] assms(1)
        by simp
      also have "... = (1/2)^(Suc i)"
        using half_sum[of "Suc i"] by simp
      finally show ?thesis .
    qed
    moreover have "(\<Sum>n<i - m. real (a (n + m)) * (1 / 2) ^ Suc (n + m)) \<le> (1/2)^m - (1/2)^i"
    proof -
      have "(\<Sum>n<i - m. real (a (n + m)) * (1 / 2) ^ Suc (n + m)) \<le> (\<Sum>n<i - m. (1 / 2) ^ Suc (n + m))"
      proof -
        have "real (a i) * (1 / 2) ^ Suc i \<le> (1 / 2) ^ Suc i" for i
          using assms(1)[of i] by auto
        thus ?thesis
          by (simp add: sum_mono)
      qed
      also have "... = (\<Sum>n. (1 / 2) ^ Suc (n + m)) - (\<Sum>n. (1 / 2) ^ Suc (n + (i - m) + m))"
        using suminf_split_initial_segment[of "\<lambda>n. (1 / 2) ^ Suc (n + m)" "i-m"] power_half_summable summable_iff_shift[of "\<lambda>n. ((1::real) / 2) ^ Suc n" m]
        by fastforce
      also have "... = (\<Sum>n. (1 / 2) ^ Suc (n + m)) - (\<Sum>n. (1 / 2) ^ Suc (n + i))"
        using assms(2) by simp
      also have "... = (1/2)^m - (1/2)^i"
        using half_sum by fastforce
      finally show ?thesis .
    qed
    ultimately have "(\<Sum>n<i - m. real (a (n + m)) * (1 / 2) ^ Suc (n + m)) + (\<Sum>n. real (a (n + i)) * (1 / 2) ^ Suc (n + i)) \<le> (1 / 2) ^ Suc i + (1 / 2) ^ m - (1 / 2) ^ i"
      by linarith
    also have "... < (1 / 2) ^ m "
      by simp
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma ai_exists0_less_than1:
  assumes "\<And>n. a n \<in> {0,1}"
      and "\<exists>i. a i = 0"
    shows "(\<Sum>n::nat. real (a n) * (1/2)^(Suc n)) < 1"
  using ai_exists0_less_than_sum[of a 0] assms
  by auto

lemma ai_1_gt:
  assumes "\<And>n. a n \<in> {0,1}"
      and "a i = 1"
    shows "(1/2)^(Suc i) \<le> (\<Sum>n::nat. real (a (n+i)) * (1/2)^(Suc (n+i)))"
proof -
  have 1:"(\<Sum>n::nat. real (a (n+i)) * (1/2)^(Suc (n+i))) = (1 / 2) ^ Suc (0 + i) + (\<Sum>n. real (a (Suc n + i)) * (1 / 2) ^ Suc (Suc n + i))"
    using suminf_split_head[of "\<lambda>n. real (a (n+i)) * (1/2)^(Suc (n+i))"] binary_expression_summable[of a] summable_iff_shift[of "\<lambda>n. real (a n) * (1 / 2) ^ Suc n" i] assms
    by simp
  show ?thesis
    using 1 binary_expression_gteq0[of a "Suc i"] assms(1)
    by simp
qed

lemma ai_exists1_gt0:
  assumes "\<And>n. a n \<in> {0,1}"
      and "\<exists>i. a i = 1"
    shows "0 < (\<Sum>n::nat. real (a n) * (1/2)^(Suc n))"
proof -
  obtain k where h1: "a k = 1"
    using assms(2) by auto
  have "(1/2)^(Suc k) = (\<Sum>n::nat. (if n = k then (1/2)^(Suc k) else (0::real)))"
  proof -
    have "(\<lambda>n. if n \<in> {k} then (1 / 2) ^ Suc k else (0::real)) = (\<lambda>n. if n = k then (1/2)^(Suc k) else 0)"
      by simp
    moreover have "(\<lambda>n. if n \<in> {k} then (1 / 2) ^ Suc k else (0::real)) sums (\<Sum>r\<in>{k}. (1 / 2) ^ Suc k)"
      using sums_If_finite_set[of "{k}" "\<lambda>n. ((1::real)/2)^(Suc k)"] by simp
    ultimately have "(\<lambda>n. if n = k then (1 / 2) ^ Suc k else (0::real)) sums (1/2)^(Suc k)"
      by simp
    thus ?thesis
      using sums_unique[of "\<lambda>n. if n = k then (1 / 2) ^ Suc k else (0::real)" "(1/2)^(Suc k)"]
      by simp
  qed
  also have "(\<Sum>n::nat. (if n = k then (1/2)^(Suc k) else 0)) \<le> (\<Sum>n::nat. real (a n) * (1/2)^(Suc n))"
  proof(rule suminf_le)
    show "\<And>n. (if n = k then (1 / 2) ^ Suc k else 0) \<le> real (a n) * (1 / 2) ^ Suc n"
    proof -
      fix n
      show "(if n = k then (1 / 2) ^ Suc k else 0) \<le> real (a n) * (1 / 2) ^ Suc n"
        by(cases "n = k"; simp add: h1)
    qed
  next
    show "summable (\<lambda>n. if n = k then (1 / 2) ^ Suc k else (0::real))"
      using summable_single[of k "\<lambda>n. ((1::real) / 2) ^ Suc k"]
      by simp
  next
    show "summable (\<lambda>n. real (a n) * (1 / 2) ^ Suc n)"
      using binary_expression_summable[of a] assms(1)
      by simp
  qed
  finally have "(1 / 2) ^ Suc k \<le> (\<Sum>n. real (a n) * (1 / 2) ^ Suc n)" .
  moreover have "0 < ((1::real) / 2) ^ Suc k" by simp
  ultimately show ?thesis by linarith
qed


lemma r01_binary_expression_ex0:
  assumes "0 < r" "r < 1"
  shows "\<exists>i.  r01_binary_expansion' r i = 0"
proof (rule ccontr)
  assume "\<not> (\<exists> i. r01_binary_expansion' r i = 0)"
  then have "\<And>i. r01_binary_expansion' r i = 1"
    using real01_binary_expansion'_0or1[of r] by blast
  hence 1:"r01_binary_expression r = (\<lambda>n. \<Sum>i=0..n. ((1/2)^(Suc i)))"
    by(auto simp: r01_binary_expression_def r01_binary_sum_def)
  have "LIMSEQ (r01_binary_expression r)  1"
  proof -
    have "LIMSEQ (\<lambda>n. \<Sum>i=0..n. (((1::real)/2)^(Suc i))) 1"
      using power_half_series sums_def'[of "\<lambda>n. ((1::real)/2)^(Suc n)" 1]
      by simp
    thus ?thesis
      using 1 by simp
  qed
  moreover have "LIMSEQ (r01_binary_expression r) r"
    using r01_binary_expression_converges_to_r[of r] assms
    by simp
  ultimately have "r = 1"
    using LIMSEQ_unique by auto
  thus False
    using assms by simp
qed

lemma r01_binary_expression_ex1:
  assumes "0 < r" "r < 1"
  shows "\<exists>i.  r01_binary_expansion' r i = 1"
proof (rule ccontr)
  assume "\<not> (\<exists>i. r01_binary_expansion' r i = 1)"
  then have "\<And>i. r01_binary_expansion' r i = 0"
    using real01_binary_expansion'_0or1[of r] by blast
  hence 1:"r01_binary_expression r = (\<lambda>n. \<Sum>i=0..n. 0)"
    by(auto simp add: r01_binary_expression_def r01_binary_sum_def)
  hence "LIMSEQ (r01_binary_expression r) 0"
    by simp
  moreover have "LIMSEQ (r01_binary_expression r) r"
    using r01_binary_expression_converges_to_r[of r] assms
    by simp
  ultimately have "r = 0"
    using LIMSEQ_unique by auto
  thus False
    using assms by simp
qed

lemma r01_binary_expansion'_gt1:
  "1 \<le> r \<longleftrightarrow> (\<forall>n. r01_binary_expansion' r n = 1)"
proof auto
  fix n
  assume h:"1 \<le> r"
  show "r01_binary_expansion' r n = Suc 0"
    unfolding r01_binary_expansion'_def
  proof(cases n)
    case 0
    then show "fst (r01_binary_expansion'' r n) = Suc 0"
      using h by simp
  next
    case 2:(Suc n')
    show "fst (r01_binary_expansion'' r n) = Suc 0"
    proof(cases "r01_binary_expansion'' r n'")
      case 3:(fields a ur lr)
      then have "(ur + lr) / 2 \<le> 1"
        using r01_binary_expansion_lr_ur_nn[of r "Suc n'"]
        by (cases "((ur + lr) / 2) \<le> r") (auto simp: Let_def) 
      thus "fst (r01_binary_expansion'' r n) = Suc 0"
        using h by(simp add: 2 3 Let_def)
    qed
  qed
next
  assume h:"\<forall>n. r01_binary_expansion' r n = Suc 0"
  show "1 \<le> r"
  proof(rule ccontr)
    assume "\<not> 1 \<le> r"
    then consider "r \<le> 0" | "0 < r \<and> r < 1"
      by linarith
    then show "False"
    proof cases
      case 1
      then have "r01_binary_expansion' r 0 = 0"
        by(simp add: r01_binary_expansion'_def)
      then show ?thesis
        using h by simp
    next
      case 2
      then have "\<exists>i.  r01_binary_expansion' r i = 0"
        using r01_binary_expression_ex0[of r] by simp
      then show ?thesis
        using h by simp
    qed
  qed
qed

lemma r01_binary_expansion'_lt0:
 "r \<le> 0 \<longleftrightarrow> (\<forall>n. r01_binary_expansion' r n = 0)"
proof auto
  fix n
  assume h:"r \<le> 0"
  show "r01_binary_expansion' r n = 0"
  proof(cases n)
    case 0
    then show ?thesis
      using h by(simp add: r01_binary_expansion'_def)
  next
    case hn:(Suc n')
    then show ?thesis
      unfolding r01_binary_expansion'_def
    proof(cases "r01_binary_expansion'' r n'")
      case 1:(fields a ur lr)
      then have "0 < ((ur + lr) / 2)"
        using r01_binary_expansion_lr_ur_nn[of r n']
        by simp
      hence "r < ..."
        using h by linarith       
      then show "fst (r01_binary_expansion'' r n) = 0 "
        by(simp add: 1 hn Let_def)
    qed
  qed
next
  assume h:"\<forall>n. r01_binary_expansion' r n = 0"
  show "r \<le> 0"
  proof(rule ccontr)
    assume "\<not> r \<le> 0"
    then consider "0 < r \<and> r < 1" | "1 \<le> r" by linarith
    thus False
    proof cases
      case 1
      then have "\<exists>i. r01_binary_expansion' r i = 1"
        using r01_binary_expression_ex1[of r] by simp
      then show ?thesis
        using h by simp
    next
      case 2
      then show ?thesis
        using r01_binary_expansion'_gt1[of r] h by simp
    qed
  qed
qed
    

text \<open>The sequence $111111\dots$ does not appear in $r = 0.a_1 a_2\dots$. \<close>
lemma r01_binary_expression_ex0_strong:
  assumes "0 < r" "r < 1"
  shows "\<exists>i\<ge>n. r01_binary_expansion' r i = 0"
proof(cases "r01_binary_expansion'' r n")
  case 1:(fields a ur lr)
  show ?thesis
  proof(rule ccontr)
    assume "\<not> (\<exists>i\<ge>n. r01_binary_expansion' r i = 0)"
    then have h:"\<forall>i\<ge>n. r01_binary_expansion' r i = 1"
      using real01_binary_expansion'_0or1[of r] by blast
    
    have "r = (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i))) + (\<Sum>i::nat. real (r01_binary_expansion' r (i + (Suc n))) * ((1/2)^(Suc (i + (Suc n)))))"
    proof -
      have "r = (\<Sum>l. real (r01_binary_expansion' r l) * (1 / 2) ^ Suc l)"
        using r01_binary_expression_correct[of r] assms by simp
      also have "... = (\<Sum>l. real (r01_binary_expansion' r (l + Suc n)) * (1 / 2) ^ Suc (l + Suc n)) + (\<Sum>i<Suc n. real (r01_binary_expansion' r i) * (1 / 2) ^ Suc i)"
        apply(rule suminf_split_initial_segment)
        apply(rule binary_expression_summable)
        using real01_binary_expansion'_0or1[of r] by simp
      also have "... = (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i))) + (\<Sum>i::nat. real (r01_binary_expansion' r (i + (Suc n))) * ((1/2)^(Suc (i + (Suc n)))))"
      proof -
        have "\<And>n. {..<Suc n} = {0..n}" by auto
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    also have "... = (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i))) + (\<Sum>i::nat. ((1/2)^(Suc (i + (Suc n)))))"
      using h by simp
    also have "... = (\<Sum>i=0..n. real (r01_binary_expansion' r i) * ((1/2)^(Suc i))) + (1/2)^(Suc n)"
      using half_sum[of "Suc n"] by simp
    also have "... = lr + (1/2)^(Suc n)"
      using 1 r01_binary_expression_eq_lr[of r n]
      by(simp add: r01_binary_expression_def r01_binary_sum_def)
    also have "... = ur"
      using r01_binary_expansion_diff[of r n]
      by(simp add: 1)
    finally have "r = ur" .
    moreover have "r < ur"
      using r01_binary_expansion_lr_r_ur[of r n] assms 1
      by simp
    ultimately show False
      by simp
  qed
qed

text \<open> A binary expression is well-formed when $111\dots$ does not appear in the tail of the sequence \<close>
definition biexp01_well_formed :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
"biexp01_well_formed a \<equiv> (\<forall>n. a n \<in> {0,1}) \<and> (\<forall>n. \<exists>m\<ge>n. a m = 0)"

lemma biexp01_well_formedE:
  assumes "biexp01_well_formed a"
  shows "(\<forall>n. a n \<in> {0,1}) \<and> (\<forall>n. \<exists>m\<ge>n. a m = 0)"
  using assms by(simp add: biexp01_well_formed_def)

lemma biexp01_well_formedI:
  assumes "\<And>n. a n \<in> {0,1}"
      and "\<And>n. \<exists>m\<ge>n. a m = 0"
    shows "biexp01_well_formed a"
  using assms by(simp add: biexp01_well_formed_def)

lemma r01_binary_expansion_well_formed:
  assumes "0 < r" "r < 1"
  shows "biexp01_well_formed (r01_binary_expansion' r)"
  using r01_binary_expression_ex0_strong[of r] assms real01_binary_expansion'_0or1[of r]
  by(simp add: biexp01_well_formed_def)

lemma biexp01_well_formed_comb:
  assumes "biexp01_well_formed a"
      and "biexp01_well_formed b"
    shows "biexp01_well_formed (\<lambda>n. if even n then a (n div 2)
                                              else b ((n-1) div 2))"
proof(rule biexp01_well_formedI)
  show "\<And>n. (if even n then a (n div 2) else b ((n - 1) div 2)) \<in> {0, 1}"
    using assms biexp01_well_formedE by simp
next
  fix n
  obtain m where 1:"m\<ge>n \<and> a m = 0"
    using assms biexp01_well_formedE by blast
  then have "a ((2*m) div 2) = 0" by simp
  hence "(if even (2*m) then a (2*m div 2) else b ((2*m - 1) div 2)) = 0"
    by simp
  moreover have "2*m \<ge> n" using 1 by simp
  ultimately show "\<exists>m\<ge>n. (if even m then a (m div 2) else b ((m - 1) div 2)) = 0"
    by auto
qed



lemma nat_complete_induction:
  assumes "P (0 :: nat)"
      and "\<And>n. (\<And>m. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)"
    shows "P n"
proof(cases n)
  case 0
  then show ?thesis
    using assms(1) by simp
next
  case h:(Suc n')
  have "P (Suc n')"
  proof(rule assms(2))
    show "\<And>m. m \<le> n' \<Longrightarrow> P m"
    proof(induction n')
      case 0
      then show ?case
        using assms(1) by simp
    next
      case (Suc n'')
      then show ?case
        by (metis assms(2) le_SucE)
    qed
  qed
  thus ?thesis
    using h by simp
qed

text \<open> \<open>(\<Sum>m. real (a m) * (1 / 2) ^ Suc m) n = a n\<close>.\<close>
lemma biexp01_well_formed_an:
  assumes "biexp01_well_formed a"
  shows "r01_binary_expansion' (\<Sum>m. real (a m) * (1 / 2) ^ Suc m) n = a n"
proof(rule nat_complete_induction[of _ n])
  show "r01_binary_expansion' (\<Sum>m. real (a m) * (1 / 2) ^ Suc m) 0 = a 0"
  proof (auto simp add: r01_binary_expansion'_def)
    assume h:"1 \<le> (\<Sum>m. real (a m) * (1 / 2) ^ m / 2) * 2"
    show "Suc 0 = a 0"
    proof(rule ccontr)
      assume "Suc 0 \<noteq> a 0"
      then have "a 0 = 0"
        using assms(1) biexp01_well_formedE[of a] by auto
      hence "(\<Sum>m. real (a m) * (1 / 2) ^ (Suc m)) = (\<Sum>m. real (a (Suc m)) * (1 / 2) ^ (Suc (Suc m)))"
        using suminf_split_head[of "\<lambda>m. real (a m) * (1 / 2) ^ (Suc m)"] binary_expression_summable[of a] assms biexp01_well_formedE
        by simp
      also have "... < 1/2"
        using ai_exists0_less_than_sum[of a 1] assms biexp01_well_formedE[of a]
        by auto
      finally have "(\<Sum>m. real (a m) * (1 / 2) ^ m / 2) < 1/2"
        by simp
      thus False
        using h by simp
    qed
  next
    assume h:"\<not> 1 \<le> (\<Sum>m. real (a m) * (1 / 2) ^ m / 2) * 2"
    show "a 0 = 0"
    proof(rule ccontr)
      assume "a 0 \<noteq> 0"
      then have "a 0 = 1"
        using assms(1) biexp01_well_formedE[of a]
        by (meson insertE singletonD)
      hence "1/2 \<le> (\<Sum>m. real (a m) * (1 / 2) ^ (Suc m))"
        using ai_1_gt[of a 0] assms(1) biexp01_well_formedE[of a]
        by auto
      thus False
        using h by simp
    qed
  qed
next
  fix n :: nat
  assume ih:"(\<And>m. m \<le> n \<Longrightarrow> r01_binary_expansion' (\<Sum>m. real (a m) * (1 / 2) ^ Suc m) m = a m)"
  show "r01_binary_expansion' (\<Sum>m. real (a m) * (1 / 2) ^ Suc m) (Suc n) = a (Suc n)"
  proof(cases "r01_binary_expansion'' (\<Sum>m. real (a m) * (1 / 2) ^ Suc m) n")
    case h:(fields bn ur lr)
    then have hlr:"lr = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k)"
      using r01_binary_expression_eq_lr[of "\<Sum>m. real (a m) * (1 / 2) ^ Suc m" n] ih
      by(simp add: r01_binary_expression_def r01_binary_sum_def)
    have hlr2:"(ur + lr) / 2 = lr + (1/2)^(Suc (Suc n))"
    proof -
      have "(ur + lr) / 2 = lr + (1/2)^(Suc (Suc n))"
        using r01_binary_expansion_diff[of "\<Sum>m. real (a m) * (1 / 2) ^ Suc m" n] h by simp
      show ?thesis
        by (simp add: \<open>(ur + lr) / 2 = lr + (1 / 2) ^ Suc (Suc n)\<close> of_rat_add of_rat_divide of_rat_power)
    qed
    show ?thesis
      using h
    proof(auto simp add: r01_binary_expansion'_def Let_def)
      assume h1: "(ur + lr) \<le> (\<Sum>m. real (a m) * (1 / 2) ^ m / 2) * 2"
      show "Suc 0 = a (Suc n)"
      proof(rule ccontr)
        assume "Suc 0 \<noteq> a (Suc n)"
        then have "a (Suc n) = 0"
          using assms(1) biexp01_well_formedE[of a] by auto
        have "(\<Sum>m. real (a m) * (1 / 2) ^ m / 2) < (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (1/2)^(Suc (Suc n))"
        proof -
          have "(\<Sum>m. real (a m) * (1 / 2) ^ (Suc m)) = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (m+Suc n)) * (1 / 2) ^ Suc (m + Suc n))"
          proof -
            have "{0..n} = {..<Suc n}" by auto
            thus ?thesis
              using suminf_split_initial_segment[of "\<lambda>m. real (a m) * (1 / 2) ^ (Suc m)" "Suc n"] binary_expression_summable[of a] assms(1) biexp01_well_formedE[of a]
              by simp
          qed
          also have "... = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (Suc m + Suc n)) * (1 / 2) ^ Suc (Suc m + Suc n))"
            using suminf_split_head[of "\<lambda>m. real (a (m + Suc n)) * (1 / 2) ^ (Suc (m + Suc n))"] binary_expression_summable[of a] assms(1) biexp01_well_formedE[of a] Series.summable_iff_shift[of "\<lambda>m. real (a m) * (1 / 2) ^ (Suc m)" "Suc n"] \<open>a (Suc n) = 0\<close>
            by simp
          also have "... = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (m + Suc (Suc n))) * (1 / 2) ^ Suc (m + Suc (Suc n)))"
            by simp
          also have "... < (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (1/2)^Suc (Suc n)"
            using ai_exists0_less_than_sum[of a "Suc (Suc n)"] assms(1) biexp01_well_formedE[of a]
            by auto
          finally show ?thesis by simp
        qed
        thus False
          using h1 hlr2 hlr by simp
      qed
    next
      assume h2:"\<not> ur + lr \<le> (\<Sum>m. real (a m) * (1 / 2) ^ m / 2) * 2"
      show "a (Suc n) = 0"
      proof(rule ccontr)
        assume "a (Suc n) \<noteq> 0"
        then have "a (Suc n) = 1"
          using biexp01_well_formedE[OF assms(1)]
          by (meson insertE singletonD)
        have "(\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (1/2)^(Suc (Suc n)) \<le> (\<Sum>m. real (a m) * (1 / 2) ^ m / 2)"
        proof -
          have "(\<Sum>m. real (a m) * (1 / 2) ^ (Suc m)) = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (m+Suc n)) * (1 / 2) ^ Suc (m + Suc n))"
          proof -
            have "{0..n} = {..<Suc n}" by auto
            thus ?thesis
              using suminf_split_initial_segment[of "\<lambda>m. real (a m) * (1 / 2) ^ (Suc m)" "Suc n"] binary_expression_summable[of a] assms(1) biexp01_well_formedE[of a]
              by simp
          qed
          also have "... = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (Suc m + Suc n)) * (1 / 2) ^ Suc (Suc m + Suc n)) + (1 / 2) ^ Suc (Suc n)"
            using suminf_split_head[of "\<lambda>m. real (a (m + Suc n)) * (1 / 2) ^ (Suc (m + Suc n))"] binary_expression_summable[of a] assms(1) biexp01_well_formedE[of a] Series.summable_iff_shift[of "\<lambda>m. real (a m) * (1 / 2) ^ (Suc m)" "Suc n"] \<open>a (Suc n) = 1\<close>
            by simp
          also have "... = (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (\<Sum>m. real (a (m + Suc (Suc n))) * (1 / 2) ^ Suc (m + (Suc (Suc n)))) + (1 / 2) ^ Suc (Suc n)"
            by simp
          also have "... \<ge> (\<Sum>k=0..n. real (a k) * (1 / 2) ^ Suc k) + (1 / 2) ^ Suc (Suc n)"
            using binary_expression_gteq0[of a "Suc (Suc n)"] assms(1) biexp01_well_formedE[of a] by simp
          finally show ?thesis by simp
        qed
        thus False
          using h2 hlr2 hlr by simp
      qed
    qed
  qed
qed


lemma f01_borel_measurable:
  assumes "f -` {0::real} \<in> sets real_borel"
          "f -` {1} \<in> sets borel"
      and "\<And>r::real. f r \<in> {0,1}"
    shows "f \<in> borel_measurable real_borel"
proof(rule measurableI)
  fix U :: "real set"
  assume "U \<in> sets borel"
  consider "1 \<in> U \<and> 0 \<in> U" | "1 \<in> U \<and> 0 \<notin> U" | "1 \<notin> U \<and> 0 \<in> U" | "1 \<notin> U \<and> 0 \<notin> U"
    by auto
  then show "f -` U \<inter> space real_borel \<in> sets borel"
  proof cases
    case 1
    then have "f -` U = UNIV"
      using assms(3) by auto
    then show ?thesis by simp
  next
    case 2
    then have "f -` U = f -` {1}"
      using assms(3) by fastforce
    then show ?thesis
      using assms(2) by simp
  next
    case 3
    then have "f -` U = f -` {0}"
      using assms(3) by fastforce
    then show ?thesis
      using assms(1) by simp
  next
    case 4
    then have "f -` U = {}"
      using assms(3) by (metis all_not_in_conv insert_iff vimage_eq)
    then show ?thesis by simp
  qed
qed simp


lemma r01_binary_expansion'_measurable:
 "(\<lambda>r. real (r01_binary_expansion' r n)) \<in> borel_measurable (borel :: real measure)"
proof -
  have "(\<lambda>r. real (r01_binary_expansion' r n)) -`{0} \<in> sets borel \<and> (\<lambda>r. real (r01_binary_expansion' r n)) -`{1} \<in> sets borel"
  proof -
    let ?A = "{..0::real} \<union> (\<Union>i\<in>{l::nat. l < 2^(Suc n) \<and> even l} . {i/2^(Suc n)..<(Suc i)/2^(Suc n)})"
    let ?B = "{1::real..} \<union> (\<Union>i\<in>{l::nat. l < 2^(Suc n) \<and> odd l} .  {i/2^(Suc n)..<(Suc i)/2^(Suc n)})"
    have "?A \<in> sets borel" by simp
    have "?B \<in> sets borel" by simp
    have hE:"?A \<inter> ?B = {}"
    proof auto
      fix r :: real
      fix l :: nat
      assume h: "r \<le> 0"
                "odd l"
                "real l / (2 * 2 ^ n) \<le> r"
      then have "0 < l" by(cases l; auto)
      hence "0 < real l / (2 * 2 ^ n)" by simp
      thus False
        using h by simp
    next
      fix r :: real
      fix l :: nat
      assume h: "l < 2 * 2 ^ n"
                "even l"
                "1 \<le> r"
                "r < (1 + real l) / (2 * 2 ^ n)"
      then have "1 + real l \<le> 2 * 2 ^ n"
        by (simp add: nat_less_real_le)
      moreover have "1 + real l \<noteq> 2 * 2 ^ n"
        using h by auto
      ultimately have "1 + real l < 2 * 2 ^ n" by simp
      hence "(1 + real l) / (2 * 2 ^ n) < 1" by simp
      thus False using h by linarith
    next
      fix r :: real
      fix l1 l2 :: nat
      assume h: "even l1" "odd l2"
                "real l1 / (2 * 2 ^ n) \<le> r" "r < (1 + real l1) / (2 * 2 ^ n)"
                "real l2 / (2 * 2 ^ n) \<le> r" "r < (1 + real l2) / (2 * 2 ^ n)"
      then consider "l1 < l2" | "l2 < l1"  by fastforce
      thus False
      proof cases
        case 1
        then have "(1 + real l1) / (2 * 2 ^ n) \<le> real l2 / (2 * 2 ^ n)"
          by (simp add: frac_le)
        then show ?thesis
          using h by simp
      next
        case 2
        then have "(1 + real l2) / (2 * 2 ^ n) \<le> real l1 / (2 * 2 ^ n)"
          by (simp add: frac_le)
        then show ?thesis
          using h by simp
      qed
    qed
    have hU:"?A \<union> ?B = UNIV"
    proof
      show "?A \<union> ?B \<subseteq> UNIV" by simp
    next
      show "UNIV \<subseteq> ?A \<union> ?B"
      proof
        fix r :: real
        consider "r \<le> 0" | "0 < r \<and> r < 1" | "1 \<le> r" by linarith
        then show "r \<in> ?A \<union> ?B"
        proof cases
          case 1
          then show ?thesis by simp
        next
          case 2
          show ?thesis
          proof(cases "r01_binary_expansion'' r n")
            case hc:(fields a ur lr)
            then have hlu:"lr \<le> r \<and> r < ur"
              using 2 r01_binary_expansion_lr_r_ur[of r n] by simp
            obtain k :: nat where hk:
             "lr = real k / 2 ^ Suc n \<and> k < 2 ^ Suc n"
              using r01_binary_expression'_sum_range[of r n] hc
              by auto
            hence "ur = real (Suc k) / 2^Suc n"
              using r01_binary_expansion_diff[of r n] hc
              by (simp add: add_divide_distrib power_one_over)
            thus ?thesis
              using hlu hk by auto
          qed
        next
          case 3
          then show ?thesis by simp
        qed
      qed
    qed
    have hi1:"- ?A = ?B"
    proof -
      have "?B \<subseteq> - ?A"
        using hE by blast
      moreover have "-?A \<subseteq> ?B"
      proof -
        have "-(?A \<union> ?B) = {}"
          using hU by simp
        hence "(-?A) \<inter> (-?B) = {}" by simp
        thus ?thesis
          by blast
      qed
      ultimately show ?thesis
        by blast
    qed
    have hi2: "?A = -?B"
      using hi1 by blast

    let ?U0 = "(\<lambda>r. real (r01_binary_expansion' r n)) -`{0}"
    let ?U1 = "(\<lambda>r. real (r01_binary_expansion' r n)) -`{1}"

    have hU':"?U0 \<union> ?U1 = UNIV"
    proof -
      have "?U0 \<union> ?U1 = (\<lambda>r. real (r01_binary_expansion' r n)) -`{0,1}"
        by auto
      thus ?thesis
        using real01_binary_expansion'_0or1[of _ n] by auto
    qed
    have hE':"?U0 \<inter> ?U1 = {}"
      by auto

    have hiu1:"- ?U0 = ?U1"
      using hE' hU' by fastforce

    have hiu2:"- ?U1 = ?U0"
      using hE' hU' by fastforce

    have "?U0 \<subseteq> ?A"
    proof
      fix r
      assume "r \<in> ?U0"
      then have h1:"r01_binary_expansion' r n = 0"
        by simp
      then consider "r \<le> 0" | "0 < r \<and> r < 1"
        using r01_binary_expansion'_gt1[of r] by fastforce
      thus "r \<in> ?A"
      proof cases
        case 1
        then show ?thesis by simp
      next
        case 2
        then have 3:"(snd (snd (r01_binary_expansion'' r n))) \<le> r \<and>
                     r < (fst (snd (r01_binary_expansion'' r n)))"
          using r01_binary_expansion_lr_r_ur[of r n] by simp
        obtain k where 4: 
          "(snd (snd (r01_binary_expansion'' r n))) =
           real k / 2 ^ Suc n \<and>
           k < 2 ^ Suc n \<and> even k"
          using r01_binary_expression'_sum_range[of r n] h1
          by auto
        have "(fst (snd (r01_binary_expansion'' r n))) = real (Suc k) / 2 ^ Suc n"
        proof -
          have "(fst (snd (r01_binary_expansion'' r n))) = (snd (snd (r01_binary_expansion'' r n))) + (1/2)^Suc n"
            using r01_binary_expansion_diff[of r n] by linarith
          thus ?thesis
            using 4
            by (simp add: add_divide_distrib power_one_over)
        qed
        thus ?thesis
          using 3 4 by auto
      qed
    qed

    have "?U1 \<subseteq> ?B"
    proof
      fix r
      assume "r \<in> ?U1"
      then have h1:"r01_binary_expansion' r n = 1"
        by simp
      then consider "1 \<le> r" | "0 < r \<and> r < 1"
        using r01_binary_expansion'_lt0[of r] by fastforce
      thus "r \<in> ?B"
      proof cases
        case 1
        then show ?thesis by simp
      next
        case 2
        then have 3:"(snd (snd (r01_binary_expansion'' r n))) \<le> r \<and>
                     r < (fst (snd (r01_binary_expansion'' r n)))"
          using r01_binary_expansion_lr_r_ur[of r n] by simp
        obtain k where 4: 
          "(snd (snd (r01_binary_expansion'' r n))) =
           real k / 2 ^ Suc n \<and>
           k < 2 ^ Suc n \<and> odd k"
          using StandardBorel.r01_binary_expression'_sum_range[of r n] h1
          by auto
        have "(fst (snd (r01_binary_expansion'' r n))) = real (Suc k) / 2 ^ Suc n"
        proof -
          have "(fst (snd (r01_binary_expansion'' r n))) = (snd (snd (r01_binary_expansion'' r n))) + (1/2)^Suc n"
            using r01_binary_expansion_diff[of r n] by simp
          thus ?thesis
            using 4
            by (simp add: add_divide_distrib power_one_over)
        qed
        thus ?thesis
          using 3 4 by auto
      qed
    qed

    have "?U0 = ?A"
    proof
      show "?U0 \<subseteq> ?A" by fact
    next
      show "?A \<subseteq> ?U0"
        using  \<open>?U1 \<subseteq> ?B\<close> Compl_subset_Compl_iff[of ?U0 ?A] hi1 hiu1
        by blast
    qed

    have "?U1 = ?B"
      using \<open>?U0 = ?A\<close> hi1 hiu1 by auto
    show ?thesis
      using \<open>?U0 = ?A\<close> \<open>?U1 = ?B\<close> \<open>?A \<in> sets borel\<close> \<open>?B \<in> sets borel\<close>
      by simp
  qed
  thus ?thesis
    using f01_borel_measurable[of "(\<lambda>r. real (r01_binary_expansion' r n))"] real01_binary_expansion'_0or1[of _ n]
    by simp
qed



(* (0,1) \<Rightarrow> [0,1]\<times>[0,1]. *)
definition r01_to_r01_r01_fst' :: "real \<Rightarrow> nat \<Rightarrow> nat" where
"r01_to_r01_r01_fst' r n \<equiv> r01_binary_expansion' r (2*n)"

lemma r01_to_r01_r01_fst'in01:
  "\<And>n. r01_to_r01_r01_fst' r n \<in> {0,1}"
  using real01_binary_expansion'_0or1 by (simp add: r01_to_r01_r01_fst'_def)

definition r01_to_r01_r01_fst_sum :: "real \<Rightarrow> nat \<Rightarrow> real" where
"r01_to_r01_r01_fst_sum \<equiv> r01_binary_sum \<circ> r01_to_r01_r01_fst'"

definition r01_to_r01_r01_fst :: "real \<Rightarrow> real" where
"r01_to_r01_r01_fst = lim \<circ> r01_to_r01_r01_fst_sum"

lemma r01_to_r01_r01_fst_def':
  "r01_to_r01_r01_fst r = (\<Sum>n. real (r01_binary_expansion' r (2*n)) * (1/2)^(n+1))"
proof -
  have "r01_to_r01_r01_fst_sum r = (\<lambda>n. \<Sum>i=0..n. real (r01_binary_expansion' r (2*i)) * (1/2)^(i+1))"
    by(auto simp add: r01_to_r01_r01_fst_sum_def r01_binary_sum_def r01_to_r01_r01_fst'_def)
  thus ?thesis
    using lim_sum_ai real01_binary_expansion'_0or1
    by(simp add: r01_to_r01_r01_fst_def)
qed

lemma r01_to_r01_r01_fst_measurable:
 "r01_to_r01_r01_fst \<in> borel_measurable borel"
  unfolding r01_to_r01_r01_fst_def'
  using r01_binary_expansion'_measurable by auto


definition r01_to_r01_r01_snd' :: "real \<Rightarrow> nat \<Rightarrow> nat" where
"r01_to_r01_r01_snd' r n = r01_binary_expansion' r (2*n + 1)"

lemma r01_to_r01_r01_snd'in01:
  "\<And>n. r01_to_r01_r01_snd' r n \<in> {0,1}"
  using real01_binary_expansion'_0or1 by (simp add: r01_to_r01_r01_snd'_def)


definition r01_to_r01_r01_snd_sum :: "real \<Rightarrow> nat \<Rightarrow> real" where
"r01_to_r01_r01_snd_sum \<equiv> r01_binary_sum \<circ> r01_to_r01_r01_snd'"

definition r01_to_r01_r01_snd :: "real \<Rightarrow> real" where
"r01_to_r01_r01_snd = lim \<circ> r01_to_r01_r01_snd_sum"

lemma r01_to_r01_r01_snd_def':
  "r01_to_r01_r01_snd r = (\<Sum>n. real (r01_binary_expansion' r (2*n + 1)) * (1/2)^(n+1))"
proof -
  have "r01_to_r01_r01_snd_sum r = (\<lambda>n. \<Sum>i=0..n. real (r01_binary_expansion' r (2*i + 1)) * (1/2)^(i+1))"
    by(auto simp add: r01_to_r01_r01_snd_sum_def r01_binary_sum_def r01_to_r01_r01_snd'_def)
  thus ?thesis
    using lim_sum_ai real01_binary_expansion'_0or1
    by(simp add: r01_to_r01_r01_snd_def)
qed

lemma r01_to_r01_r01_snd_measurable:
 "r01_to_r01_r01_snd \<in> borel_measurable borel"
  unfolding r01_to_r01_r01_snd_def'
  using r01_binary_expansion'_measurable by auto


definition r01_to_r01_r01 :: "real \<Rightarrow> real \<times> real" where
"r01_to_r01_r01 r = (r01_to_r01_r01_fst r,r01_to_r01_r01_snd r)"

lemma r01_to_r01_r01_image:
 "r01_to_r01_r01 r \<in> {0..1}\<times>{0..1}"
  using r01_to_r01_r01_fst_def'[of r] r01_to_r01_r01_snd_def'[of r] real01_binary_expansion'_0or1
        binary_expression_gteq0[of "\<lambda>n. r01_binary_expansion' r (2*n)" 0] binary_expression_leeq1[of "\<lambda>n. r01_binary_expansion' r (2*n)" 0] binary_expression_gteq0[of "\<lambda>n. r01_binary_expansion' r (2*n+1)" 0] binary_expression_leeq1[of "\<lambda>n. r01_binary_expansion' r (2*n+1)" 0]
  by(simp add: r01_to_r01_r01_def)

lemma r01_to_r01_r01_measurable:
 "r01_to_r01_r01 \<in> real_borel \<rightarrow>\<^sub>M real_borel \<Otimes>\<^sub>M real_borel"
  unfolding r01_to_r01_r01_def
  using borel_measurable_Pair[of r01_to_r01_r01_fst borel r01_to_r01_r01_snd] r01_to_r01_r01_fst_measurable r01_to_r01_r01_snd_measurable
  by(simp add: borel_prod)

lemma r01_to_r01_r01_3over4:
 "r01_to_r01_r01 (3/4) = (1/2,1/2)"
proof -
  have h0:"r01_binary_expansion' (3/4) 0 = 1"
    by (simp add: r01_binary_expansion'_def)
  have h1:"r01_binary_expansion' (3/4) 1 = 1"
    by (simp add: r01_binary_expansion'_def Let_def of_rat_divide)
  have hn:"\<And>n. n>1\<Longrightarrow> r01_binary_expansion' (3/4) n = 0"
  proof -
    fix n :: nat
    assume h:"1 < n"
    show "r01_binary_expansion' (3 / 4) n = 0"
    proof(rule ccontr)
      assume "r01_binary_expansion' (3 / 4) n \<noteq> 0"
      have "3/4 < (\<Sum>i=0..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i))"
      proof -
        have "(\<Sum>i=0..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)) = real (r01_binary_expansion' (3/4) 0) * (1/2)^(Suc 0) + (\<Sum>i=(Suc 0)..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i))"
          by(rule sum.atLeast_Suc_atMost) (simp add: h)
        also have "... = real (r01_binary_expansion' (3/4) 0) * (1/2)^(Suc 0) + (real (r01_binary_expansion' (3/4) 1) * (1/2)^(Suc 1) + (\<Sum>i=(Suc (Suc 0))..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)))"
          using sum.atLeast_Suc_atMost[OF order.strict_implies_order[OF h],of "\<lambda>i. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)"]
          by simp
        also have "... = 3/4 + (\<Sum>i=2..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i))"
          using h0 h1 by(simp add: numeral_2_eq_2)
        also have "... > 3/4"
        proof -
          have "(\<Sum>i=2..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)) = (\<Sum>i=2..n-1. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)) + real (r01_binary_expansion' (3/4) n) * (1/2)^Suc n"
            by (metis (no_types, lifting) h One_nat_def Suc_pred less_2_cases_iff less_imp_add_positive order_less_irrefl plus_1_eq_Suc sum.cl_ivl_Suc zero_less_Suc)
          hence "real (r01_binary_expansion' (3/4) n) * (1/2)^Suc n \<le> (\<Sum>i=2..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i))"
            using ordered_comm_monoid_add_class.sum_nonneg[of "{2..n-1}" "\<lambda>i. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)"]
            by simp
          moreover have "0 < real (r01_binary_expansion' (3/4) n) * (1/2)^Suc n"
            using \<open>r01_binary_expansion' (3 / 4) n \<noteq> 0\<close> by simp
          ultimately have "0 < (\<Sum>i=2..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i))"
            by simp
          thus ?thesis by simp
        qed
        finally show "3 / 4 < (\<Sum>i = 0..n. real (r01_binary_expansion' (3 / 4) i) * (1 / 2) ^ Suc i)" .
      qed
      moreover have "(\<Sum>i=0..n. real (r01_binary_expansion' (3/4) i) * (1/2)^(Suc i)) \<le> 3/4"
        using r01_binary_expansion_lr_r_ur[of "3/4" n] r01_binary_expression_eq_lr[of "3/4" n]
        by(simp add: r01_binary_expression_def r01_binary_sum_def)
      ultimately show False by simp
    qed
  qed
  show ?thesis
  proof
    have "fst (r01_to_r01_r01 (3 / 4)) = (\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * n)) * (1 / 2) ^ Suc n)"
      by(simp add: r01_to_r01_r01_def r01_to_r01_r01_fst_def')
    also have "... = 1/2 + (\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n)) * (1 / 2) ^ Suc (Suc n))"
      using suminf_split_head[of "\<lambda>n. real (r01_binary_expansion' (3 / 4) (2 * n)) * (1 / 2) ^ Suc n"] binary_expression_summable[of "\<lambda>n. r01_binary_expansion' (3/4) (2*n)"] real01_binary_expansion'_0or1[of "3/4"] h0
      by simp
    also have "... = 1/2"
    proof -
      have "\<forall>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n)) * (1 / 2) ^ Suc (Suc n) = 0"
        using hn by simp
      hence "(\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n)) * (1 / 2) ^ Suc (Suc n)) = 0"
        by simp
      thus ?thesis
        by simp
    qed
    finally show "fst (r01_to_r01_r01 (3 / 4)) = fst (1 / 2, 1 / 2)"
      by simp
  next
    have "snd (r01_to_r01_r01 (3 / 4)) = (\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * n + 1)) * (1 / 2) ^ Suc n)"
      by(simp add: r01_to_r01_r01_def r01_to_r01_r01_snd_def')
    also have "... = 1/2 + (\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n + 1)) * (1 / 2) ^ Suc (Suc n))"
      using suminf_split_head[of "\<lambda>n. real (r01_binary_expansion' (3 / 4) (2 * n + 1)) * (1 / 2) ^ Suc n"] binary_expression_summable[of "\<lambda>n. r01_binary_expansion' (3/4) (2*n + 1)"] real01_binary_expansion'_0or1[of "3/4"] h1
      by simp
    also have "... = 1/2"
    proof -
      have "\<forall>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n + 1)) * (1 / 2) ^ Suc (Suc n) = 0"
        using hn by simp
      hence "(\<Sum>n. real (r01_binary_expansion' (3 / 4) (2 * Suc n + 1)) * (1 / 2) ^ Suc (Suc n)) = 0"
        by simp
      thus ?thesis
        by simp
    qed
    finally show "snd (r01_to_r01_r01 (3 / 4)) = snd (1 / 2, 1 / 2)"
      by simp
  qed
qed


(* (0,1)\<times>(0,1) \<Rightarrow> (0,1). *)
definition r01_r01_to_r01' :: "real \<times> real \<Rightarrow> nat \<Rightarrow> nat" where
"r01_r01_to_r01' rs \<equiv> (\<lambda>n. if even n then r01_binary_expansion' (fst rs) (n div 2)
                                      else r01_binary_expansion' (snd rs) ((n-1) div 2))"

lemma r01_r01_to_r01'in01:
  "\<And>n. r01_r01_to_r01' rs n \<in> {0,1}"
  using real01_binary_expansion'_0or1 by (simp add: r01_r01_to_r01'_def)

lemma r01_r01_to_r01'_well_formed:
  assumes "0 < r1" "r1 < 1"
      and "0 < r2" "r2 < 1"
    shows "biexp01_well_formed (r01_r01_to_r01' (r1,r2))"
  using biexp01_well_formed_comb[of "r01_binary_expansion' (fst (r1,r2))" "r01_binary_expansion' (snd (r1,r2))"] r01_binary_expansion_well_formed[of r1] r01_binary_expansion_well_formed[of r2] assms
  by (auto simp add: r01_r01_to_r01'_def)

definition r01_r01_to_r01_sum :: "real \<times> real \<Rightarrow> nat \<Rightarrow> real" where
"r01_r01_to_r01_sum \<equiv> r01_binary_sum \<circ> r01_r01_to_r01'"

definition r01_r01_to_r01 :: "real \<times> real \<Rightarrow> real" where
"r01_r01_to_r01 \<equiv> lim \<circ> r01_r01_to_r01_sum"

lemma r01_r01_to_r01_def':
 "r01_r01_to_r01 (r1,r2) = (\<Sum>n. real (r01_r01_to_r01' (r1,r2) n) * (1/2)^(n+1))"
proof -
  have "r01_r01_to_r01_sum (r1,r2) = (\<lambda>n. (\<Sum>i = 0..n. real (r01_r01_to_r01' (r1,r2) i) * (1 / 2) ^ Suc i))"
    by(auto simp add: r01_r01_to_r01_sum_def r01_binary_sum_def)
  thus ?thesis
    using lim_sum_ai[of "\<lambda>n. r01_r01_to_r01' (r1,r2) n"] r01_r01_to_r01'in01
    by(simp add: r01_r01_to_r01_def)
qed

lemma r01_r01_to_r01_measurable:
 "r01_r01_to_r01 \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M real_borel"
proof -
  have "r01_r01_to_r01 = (\<lambda>x. \<Sum>n. real (r01_r01_to_r01' x n) * (1/2)^(n+1))"
    using r01_r01_to_r01_def' by auto
  also have "... \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M real_borel"
  proof(rule borel_measurable_suminf)
    fix n :: nat
    have "(\<lambda>x. real (r01_r01_to_r01' x n) * (1 / 2) ^ (n + 1)) = (\<lambda>r. r * (1/2)^(n+1)) \<circ> (\<lambda>x. real (r01_r01_to_r01' x n))"
      by auto
    also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
    proof(rule measurable_comp[of _ _ borel])
      have "(\<lambda>x. real (r01_r01_to_r01' x n))
           = (\<lambda>x. if even n then real (r01_binary_expansion' (fst x) (n div 2)) else real (r01_binary_expansion' (snd x) ((n - 1) div 2)))"
        by (auto simp add: r01_r01_to_r01'_def)
      also have "... \<in>  borel_measurable (borel \<Otimes>\<^sub>M borel)"
        using r01_binary_expansion'_measurable by simp
      finally show "(\<lambda>x. real (r01_r01_to_r01' x n)) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)" .
    next
      show "(\<lambda>r::real. r * (1 / 2) ^ (n + 1)) \<in> borel_measurable borel"
        by simp
    qed
    finally show "(\<lambda>x. real (r01_r01_to_r01' x n) * (1 / 2) ^ (n + 1)) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)" .
  qed
  finally show ?thesis .
qed

lemma r01_r01_to_r01_image:
  assumes "0 < r1" "r1 < 1"
    shows "r01_r01_to_r01 (r1,r2) \<in> {0<..<1}"
proof -
  obtain i where "r01_binary_expansion' r1 i = 1"
    using r01_binary_expression_ex1[of r1] assms(1,2)
    by auto
  hence hi:"r01_r01_to_r01' (r1,r2) (2*i) = 1"
    by(simp add: r01_r01_to_r01'_def)
  obtain j where "r01_binary_expansion' r1 j = 0"
    using r01_binary_expression_ex0[of r1] assms(1,2)
    by auto
  hence hj:"r01_r01_to_r01' (r1,r2) (2*j) = 0"
    by(simp add: r01_r01_to_r01'_def)
  show ?thesis
    using ai_exists1_gt0[of "r01_r01_to_r01' (r1,r2)"] ai_exists0_less_than1[of "r01_r01_to_r01' (r1,r2)"] r01_r01_to_r01'in01[of "(r1,r2)"] r01_r01_to_r01_def'[of r1 r2] hi hj
    by auto
qed

lemma r01_r01_to_r01_image':
  assumes "0 < r2" "r2 < 1"
    shows "r01_r01_to_r01 (r1,r2) \<in> {0<..<1}"
proof -
  obtain i where "r01_binary_expansion' r2 i = 1"
    using r01_binary_expression_ex1[of r2] assms(1,2)
    by auto
  hence hi:"r01_r01_to_r01' (r1,r2) (2*i + 1) = 1"
    by(simp add: r01_r01_to_r01'_def)
  obtain j where "r01_binary_expansion' r2 j = 0"
    using r01_binary_expression_ex0[of r2] assms(1,2)
    by auto
  hence hj:"r01_r01_to_r01' (r1,r2) (2*j + 1) = 0"
    by(simp add: r01_r01_to_r01'_def)
  show ?thesis
    using ai_exists1_gt0[of "r01_r01_to_r01' (r1,r2)"] ai_exists0_less_than1[of "r01_r01_to_r01' (r1,r2)"] r01_r01_to_r01'in01[of "(r1,r2)"] r01_r01_to_r01_def'[of r1 r2] hi hj
    by auto
qed


lemma r01_r01_to_r01_binary_nth:
  assumes "0 < r1" "r1 < 1"
      and "0 < r2" "r2 < 1"
    shows "r01_binary_expansion' r1 n = r01_binary_expansion' (r01_r01_to_r01 (r1,r2)) (2*n) \<and>
           r01_binary_expansion' r2 n = r01_binary_expansion' (r01_r01_to_r01 (r1,r2)) (2*n + 1)"
proof -
  have "\<And>n. r01_binary_expansion' (r01_r01_to_r01 (r1,r2)) n = r01_r01_to_r01' (r1,r2) n"
    using r01_r01_to_r01_def'[of r1 r2] biexp01_well_formed_an[of "r01_r01_to_r01' (r1,r2)"] r01_r01_to_r01'_well_formed[of r1 r2] assms
    by simp
  thus ?thesis
    by(simp add: r01_r01_to_r01'_def)
qed

lemma r01_r01__r01__r01_r01_id:
  assumes "0 < r1" "r1 < 1"
          "0 < r2" "r2 < 1"
    shows "(r01_to_r01_r01 \<circ> r01_r01_to_r01) (r1,r2) = (r1,r2)"
proof
  show "fst ((r01_to_r01_r01 \<circ> r01_r01_to_r01) (r1, r2)) = fst (r1, r2)"
  proof -
    have "fst ((r01_to_r01_r01 \<circ> r01_r01_to_r01) (r1, r2)) = r01_to_r01_r01_fst (r01_r01_to_r01 (r1,r2))"
      by(simp add: r01_to_r01_r01_def)
    also have "... = (\<Sum>n. real (r01_binary_expansion' (r01_r01_to_r01 (r1, r2)) (2 * n)) * (1 / 2) ^ (n + 1))"
      using r01_to_r01_r01_fst_def'[of "r01_r01_to_r01 (r1,r2)"] by simp
    also have "... = (\<Sum>n. real (r01_binary_expansion' r1 n) * (1 / 2) ^ (n + 1))"
      using r01_r01_to_r01_binary_nth[of r1 r2] assms by simp
    also have "... = r1"
      using r01_binary_expression_correct[of r1] assms(1,2)
      by simp
    finally show ?thesis by simp
  qed
next
  show "snd ((r01_to_r01_r01 \<circ> r01_r01_to_r01) (r1, r2)) = snd (r1, r2)"
  proof -
    have "snd ((r01_to_r01_r01 \<circ> r01_r01_to_r01) (r1, r2)) = r01_to_r01_r01_snd (r01_r01_to_r01 (r1,r2))"
      by(simp add: r01_to_r01_r01_def)
    also have "... = (\<Sum>n. real (r01_binary_expansion' (r01_r01_to_r01 (r1, r2)) (2 * n + 1)) * (1 / 2) ^ (n + 1))"
      using r01_to_r01_r01_snd_def'[of "r01_r01_to_r01 (r1,r2)"] by simp
    also have "... = (\<Sum>n. real (r01_binary_expansion' r2 n) * (1 / 2) ^ (n + 1))"
      using r01_r01_to_r01_binary_nth[of r1 r2] assms by simp
    also have "... = r2"
      using r01_binary_expression_correct[of r2] assms(3,4)
      by simp
    finally show ?thesis by simp
  qed
qed

text \<open> We first show that \<open>M \<Otimes>\<^sub>M N\<close> is a standard Borel space for standard Borel spaces \<open>M\<close> and \<open>N\<close>.\<close>
lemma pair_measurable[measurable]:
  assumes "f \<in> X \<rightarrow>\<^sub>M Y"
      and "g \<in> X' \<rightarrow>\<^sub>M Y'"
    shows "map_prod f g \<in> X \<Otimes>\<^sub>M X' \<rightarrow>\<^sub>M Y \<Otimes>\<^sub>M Y'"
  using assms by(auto simp add: measurable_pair_iff)

lemma pair_standard_borel_standard:
  assumes "standard_borel M"
      and "standard_borel N"
    shows "standard_borel (M \<Otimes>\<^sub>M N)"
proof -
  \<comment> \<open> First, define the measurable function $\mathbb{R} \times \mathbb{R} \rightarrow \mathbb{R}$.\<close>
  define rr_to_r :: "real \<times> real \<Rightarrow> real"
    where "rr_to_r \<equiv> real_to_01open_inverse \<circ> r01_r01_to_r01 \<circ> (\<lambda>(x,y). (real_to_01open x, real_to_01open y))"
  \<comment> \<open> $\mathbb{R}\times\mathbb{R} \rightarrow (0,1)\times(0,1) \rightarrow (0,1) \rightarrow \mathbb{R}$.\<close>
  have 1[measurable]: "rr_to_r \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M real_borel"
  proof -
    have "(\<lambda>(x,y). (real_to_01open x, real_to_01open y)) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M real_borel \<Otimes>\<^sub>M real_borel"
      using borel_measurable_continuous_onI[OF real_to_01open_continuous]
      by simp
    from measurable_restrict_space2[OF _ this,of "{0<..<1}\<times>{0<..<1}"]
    have [measurable]:"(\<lambda>(x,y). (real_to_01open x, real_to_01open y)) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0<..<1}\<times>{0<..<1})"
      by(simp add: split_beta' real_to_01open_01)
    have [measurable]: "r01_r01_to_r01 \<in> restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0<..<1}\<times>{0<..<1}) \<rightarrow>\<^sub>M restrict_space real_borel {0<..<1}"
      using r01_r01_to_r01_image' by(auto intro!: measurable_restrict_space3[OF r01_r01_to_r01_measurable])
    thus ?thesis
      using borel_measurable_continuous_on_restrict[OF real_to_01open_inverse_continuous]
      by(simp add: rr_to_r_def)
  qed
  \<comment> \<open> Next, define the measurable function $\mathbb{R}\rightarrow \mathbb{R}\times\mathbb{R}$.\<close>
  define r_to_01 :: "real \<Rightarrow> real"
    where "r_to_01 \<equiv> (\<lambda>r. if r \<in> real_to_01open -` (r01_to_r01_r01 -` ({0<..<1}\<times>{0<..<1})) then real_to_01open r else 3/4)"
  define r01_to_r01_r01' :: "real \<Rightarrow> real \<times> real"
    where "r01_to_r01_r01' \<equiv> (\<lambda>r. if r \<in> r01_to_r01_r01 -` ({0<..<1}\<times>{0<..<1}) then r01_to_r01_r01 r else (1/2,1/2))"
  define r_to_rr :: "real \<Rightarrow> real \<times> real"
    where "r_to_rr \<equiv> (\<lambda>(x,y). (real_to_01open_inverse x, real_to_01open_inverse y)) \<circ> r01_to_r01_r01' \<circ> r_to_01"
  \<comment> \<open> $\mathbb{R} \rightarrow (0,1) \rightarrow (0,1)\times(0,1) \rightarrow \mathbb{R}\times\mathbb{R}$.\<close>
  have 2[measurable]: "r_to_rr \<in> real_borel \<rightarrow>\<^sub>M real_borel \<Otimes>\<^sub>M real_borel"
  proof -
    have 1: "{0<..<1}\<times>{0<..<1} \<in> sets (restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0..1}\<times>{0..1}))"
      by(auto simp: sets_restrict_space_iff)
    have 2[measurable]: "real_to_01open \<in> real_borel \<rightarrow>\<^sub>M restrict_space real_borel {0<..<1}"
      using measurable_restrict_space2[OF _ borel_measurable_continuous_onI[OF real_to_01open_continuous] ,of "{0<..<1}"]
      by(simp add: real_to_01open_01)
    have 3: "real_to_01open -` space (restrict_space real_borel {0<..<1}) = UNIV"
      using real_to_01open_01 by auto
    have "r01_to_r01_r01 \<in> restrict_space real_borel {0<..<1} \<rightarrow>\<^sub>M restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0..1}\<times>{0..1})"
      using r01_to_r01_r01_image measurable_restrict_space3[OF r01_to_r01_r01_measurable] by simp
    note 4 = measurable_sets[OF this 1]
    note 5 = measurable_sets[OF 2 4,simplified vimage_Int 3,simplified]
    have [measurable]:"r_to_01 \<in> real_borel \<rightarrow>\<^sub>M restrict_space real_borel {0<..<1}"
      unfolding r_to_01_def
      by(rule  measurable_If_set) (auto intro!: measurable_restrict_space2 simp: 5)
    have [measurable]: "r01_to_r01_r01' \<in> restrict_space real_borel {0<..<1} \<rightarrow>\<^sub>M restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0<..<1}\<times>{0<..<1})"
      using 4 r01_to_r01_r01_measurable
      by(auto intro!: measurable_restrict_space3 simp: r01_to_r01_r01'_def)
    have [measurable]: "(\<lambda>(x,y). (real_to_01open_inverse x, real_to_01open_inverse y)) \<in> restrict_space (real_borel \<Otimes>\<^sub>M real_borel) ({0<..<1}\<times>{0<..<1}) \<rightarrow>\<^sub>M real_borel \<Otimes>\<^sub>M real_borel"
      using borel_measurable_continuous_on_restrict[OF continuous_on_Pair[OF continuous_on_compose[of "{0<..<1::real}\<times>{0<..<1::real}",OF continuous_on_fst[OF continuous_on_id'],simplified,OF real_to_01open_inverse_continuous] continuous_on_compose[of "{0<..<1::real}\<times>{0<..<1::real}",OF continuous_on_snd[OF continuous_on_id'],simplified,OF real_to_01open_inverse_continuous]]]
      by(simp add: split_beta' borel_prod)
    show ?thesis
      by(simp add: r_to_rr_def)
  qed
  have 3: "\<And>x. r_to_rr (rr_to_r x) = x"
    using r01_to_r01_r01_image r01_r01_to_r01_image r01_r01__r01__r01_r01_id real_to_01open_01  real_to_01open_inverse_correct' fun_cong[OF real_to_01open_inverse_correct]
    by(auto simp add: r01_to_r01_r01'_def r_to_01_def comp_def split_beta' r_to_rr_def rr_to_r_def)

  interpret s1: standard_borel M by fact
  interpret s2: standard_borel N by fact
  show ?thesis
    by(auto intro!: standard_borelI[where f="rr_to_r \<circ> map_prod s1.f s2.f" and g="map_prod s1.g s2.g \<circ> r_to_rr"] simp: 3 space_pair_measure)
qed

lemma pair_standard_borel_spaceUNIV:
  assumes "standard_borel_space_UNIV M"
      and "standard_borel_space_UNIV N"
    shows "standard_borel_space_UNIV (M \<Otimes>\<^sub>M N)"
  apply(rule standard_borel_space_UNIVI')
  using assms pair_standard_borel_standard[of M N]
  by(auto simp add: standard_borel_space_UNIV_def standard_borel_space_UNIV_axioms_def space_pair_measure)


locale pair_standard_borel = s1: standard_borel M + s2: standard_borel N
  for M :: "'a measure" and N :: "'b measure"
begin

sublocale standard_borel "M \<Otimes>\<^sub>M N"
  by(auto intro!: pair_standard_borel_standard)

end

locale pair_standard_borel_space_UNIV = s1: standard_borel_space_UNIV M + s2: standard_borel_space_UNIV N
  for M :: "'a measure" and N :: "'b measure"
begin

sublocale pair_standard_borel M N
  by standard

sublocale standard_borel_space_UNIV "M \<Otimes>\<^sub>M N"
  by(auto intro!: pair_standard_borel_spaceUNIV
      simp: s1.standard_borel_space_UNIV_axioms s2.standard_borel_space_UNIV_axioms)

end


text \<open>$\mathbb{R}\times\mathbb{R}$ is a standard Borel space.\<close>
interpretation real_real : pair_standard_borel_space_UNIV real_borel real_borel
  by(auto intro!: pair_standard_borel_spaceUNIV simp: real.standard_borel_space_UNIV_axioms pair_standard_borel_space_UNIV_def)

subsection \<open> $\mathbb{N}\times\mathbb{R}$ \<close>
text \<open> $\mathbb{N}\times\mathbb{R}$ is a standard Borel space. \<close>
interpretation nat_real: pair_standard_borel_space_UNIV nat_borel real_borel
  by(auto intro!: pair_standard_borel_spaceUNIV
       simp: real.standard_borel_space_UNIV_axioms nat.standard_borel_space_UNIV_axioms pair_standard_borel_space_UNIV_def)

end