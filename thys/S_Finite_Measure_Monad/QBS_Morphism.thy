(*  Title:   QBS_Morphism.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)
subsection \<open> Morphisms of Quasi-Borel Spaces \<close>
theory QBS_Morphism

imports
 "QuasiBorel"

begin

abbreviation qbs_morphism :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>Q" 60) where 
  "X \<rightarrow>\<^sub>Q Y \<equiv> qbs_space (X \<Rightarrow>\<^sub>Q Y)"

lemma qbs_morphismI: "(\<And>\<alpha>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> f \<circ> \<alpha> \<in> qbs_Mx Y) \<Longrightarrow> f \<in> X \<rightarrow>\<^sub>Q Y"
  by(auto simp: exp_qbs_space)

lemma qbs_morphism_def: "X \<rightarrow>\<^sub>Q Y = {f\<in>qbs_space X \<rightarrow> qbs_space Y. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}"
  unfolding exp_qbs_space
proof safe
  fix f x
  assume h:"x \<in> qbs_space X " "\<forall>\<alpha>\<in>qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y"
  then have "(\<lambda>r. x) \<in> qbs_Mx X"
    by simp
  hence "f \<circ> (\<lambda>r. x) \<in> qbs_Mx Y"
    using h by blast
  with qbs_Mx_to_X show "f x \<in> qbs_space Y"
    by auto
qed auto                     

lemma qbs_morphism_Mx:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "\<alpha> \<in> qbs_Mx X"
  shows "f \<circ> \<alpha> \<in> qbs_Mx Y"
  using assms by(auto simp: qbs_morphism_def)

lemma qbs_morphism_space:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "x \<in> qbs_space X"
  shows "f x \<in> qbs_space Y"
  using assms by(auto simp: qbs_morphism_def)

lemma qbs_morphism_ident[simp]:
   "id \<in> X \<rightarrow>\<^sub>Q X"
  by(auto intro: qbs_morphismI)

lemma qbs_morphism_ident'[simp]:
   "(\<lambda>x. x) \<in> X \<rightarrow>\<^sub>Q X"
  using qbs_morphism_ident by(simp add: id_def)

lemma qbs_morphism_comp:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "g \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "g \<circ> f \<in> X \<rightarrow>\<^sub>Q Z"
  using assms by (simp add: comp_assoc Pi_def qbs_morphism_def)

lemma qbs_morphism_compose_rev:
  assumes "f \<in> Y \<rightarrow>\<^sub>Q Z" and "g \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>x. f (g x)) \<in> X \<rightarrow>\<^sub>Q Z"
  using qbs_morphism_comp[OF assms(2,1)] by(simp add: comp_def)

lemma qbs_morphism_compose:
  assumes "g \<in> X \<rightarrow>\<^sub>Q Y" and "f \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>x. f (g x)) \<in> X \<rightarrow>\<^sub>Q Z"
  using qbs_morphism_compose_rev[OF assms(2,1)] .

lemma qbs_morphism_cong':
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and "f \<in> X \<rightarrow>\<^sub>Q Y"
    shows "g \<in> X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume 1:"\<alpha> \<in> qbs_Mx X"
  have "g \<circ> \<alpha> = f \<circ> \<alpha>"
  proof
    fix x
    have "\<alpha> x \<in> qbs_space X"
      using 1 qbs_decomp[of X] qbs_Mx_to_X by auto
    thus "(g \<circ> \<alpha>) x = (f \<circ> \<alpha>) x"
      using assms(1) by simp
  qed
  thus "g \<circ> \<alpha> \<in> qbs_Mx Y"
    using 1 assms(2) by(simp add: qbs_morphism_def)
qed

lemma qbs_morphism_cong:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
  shows "f \<in> X \<rightarrow>\<^sub>Q Y \<longleftrightarrow> g \<in> X \<rightarrow>\<^sub>Q Y"
  using assms by(auto simp: qbs_morphism_cong'[of _ f g] qbs_morphism_cong'[of _ g f])

lemma qbs_morphism_const:
  assumes "y \<in> qbs_space Y"
  shows "(\<lambda>x. y) \<in> X \<rightarrow>\<^sub>Q Y"
  using assms by (auto intro: qbs_morphismI)

lemma qbs_morphism_from_empty: "qbs_space X = {} \<Longrightarrow> f \<in> X \<rightarrow>\<^sub>Q Y"
  by(auto intro!: qbs_morphismI simp: qbs_empty_equiv)

lemma unit_quasi_borel_terminal: "\<exists>! f. f \<in> X \<rightarrow>\<^sub>Q unit_quasi_borel"
  by(fastforce simp: qbs_morphism_def)

definition to_unit_quasi_borel :: "'a \<Rightarrow> unit" ("!\<^sub>Q") where
"to_unit_quasi_borel \<equiv> (\<lambda>r.())"

lemma to_unit_quasi_borel_morphism:
 "!\<^sub>Q \<in> X \<rightarrow>\<^sub>Q unit_quasi_borel"
  by(auto simp add: to_unit_quasi_borel_def qbs_morphism_def)

lemma qbs_morphism_subD:
  assumes "f \<in> X \<rightarrow>\<^sub>Q sub_qbs Y A"
  shows "f \<in> X \<rightarrow>\<^sub>Q Y"
  using qbs_morphism_Mx[OF assms] by(auto intro!: qbs_morphismI simp: sub_qbs_Mx)

lemma qbs_morphism_subI1:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x \<in> A"
  shows "f \<in> X \<rightarrow>\<^sub>Q sub_qbs Y A"
  using qbs_morphism_space[OF assms(1)] qbs_morphism_Mx[OF assms(1)] assms(2) qbs_Mx_to_X[of _ X]
  by(auto intro!: qbs_morphismI simp: sub_qbs_Mx)

lemma qbs_morphism_subI2:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "f \<in> sub_qbs X A \<rightarrow>\<^sub>Q Y"
  using qbs_morphism_Mx[OF assms] by(auto intro!: qbs_morphismI simp: sub_qbs_Mx)

corollary qbs_morphism_subsubI:
  assumes "f \<in>  X \<rightarrow>\<^sub>Q Y" "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  shows "f \<in> sub_qbs X A \<rightarrow>\<^sub>Q sub_qbs Y B"
  by(rule qbs_morphism_subI1) (auto intro!: qbs_morphism_subI2 assms simp: sub_qbs_space)

lemma map_qbs_morphism_f: "f \<in> X \<rightarrow>\<^sub>Q map_qbs f X"
  by(auto intro!: qbs_morphismI simp: map_qbs_Mx)

lemma map_qbs_morphism_inverse_f:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> g (f x) = x"
  shows "g \<in> map_qbs f X \<rightarrow>\<^sub>Q X"
proof -
  { 
    fix \<alpha>
    assume h:"\<alpha> \<in> qbs_Mx X"
    from qbs_Mx_to_X[OF this] assms have "g \<circ> (f \<circ> \<alpha>) = \<alpha>"
      by auto
    with h have "g \<circ> (f \<circ> \<alpha>) \<in> qbs_Mx X" by simp
  }
  thus ?thesis
    by(auto intro!: qbs_morphismI simp: map_qbs_Mx)
qed

lemma pair_qbs_morphismI:
  assumes "\<And>\<alpha> \<beta>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> \<beta> \<in> qbs_Mx Y 
           \<Longrightarrow> (\<lambda>r. f (\<alpha> r, \<beta> r)) \<in> qbs_Mx Z"
  shows "f \<in> (X \<Otimes>\<^sub>Q Y) \<rightarrow>\<^sub>Q Z"
  using assms by(fastforce intro!: qbs_morphismI simp: pair_qbs_Mx comp_def)

lemma pair_qbs_MxD:
  assumes "\<gamma> \<in> qbs_Mx (X \<Otimes>\<^sub>Q Y)"
  obtains \<alpha> \<beta> where "\<alpha> \<in> qbs_Mx X" "\<beta> \<in> qbs_Mx Y" "\<gamma> = (\<lambda>x. (\<alpha> x, \<beta> x))"
  using assms by(auto simp: pair_qbs_Mx)

lemma pair_qbs_MxI:
  assumes "(\<lambda>x. fst (\<gamma> x)) \<in> qbs_Mx X" and "(\<lambda>x. snd (\<gamma> x)) \<in> qbs_Mx Y"
  shows "\<gamma> \<in> qbs_Mx (X \<Otimes>\<^sub>Q Y)"
  using assms by(auto simp: pair_qbs_Mx comp_def)

lemma
  shows fst_qbs_morphism: "fst \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q X"
    and snd_qbs_morphism: "snd \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Y"
  by(auto intro!: pair_qbs_morphismI simp: comp_def)

lemma qbs_morphism_pair_iff:
 "f \<in> X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q Z \<longleftrightarrow> fst \<circ> f \<in> X \<rightarrow>\<^sub>Q Y \<and> snd \<circ> f \<in> X \<rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphism_comp fst_qbs_morphism snd_qbs_morphism)
    (auto dest: qbs_morphism_Mx intro!: qbs_morphismI simp: pair_qbs_Mx comp_assoc[symmetric])

lemma qbs_morphism_Pair:
  assumes "f \<in> Z \<rightarrow>\<^sub>Q X"
      and "g \<in> Z \<rightarrow>\<^sub>Q Y"
    shows "(\<lambda>z. (f z, g z)) \<in> Z \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
  unfolding qbs_morphism_pair_iff
  using assms by (auto simp: comp_def)

lemma qbs_morphism_curry: "curry \<in> exp_qbs (X \<Otimes>\<^sub>Q Y) Z \<rightarrow>\<^sub>Q exp_qbs X (exp_qbs Y Z)"
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx exp_qbs_Mx comp_def)  

corollary curry_preserves_morphisms:
  assumes "(\<lambda>xy. f (fst xy) (snd xy)) \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "f \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Z"
  using qbs_morphism_space[OF qbs_morphism_curry assms] by (auto simp: curry_def)

lemma qbs_morphism_eval:
 "(\<lambda>fx. (fst fx) (snd fx)) \<in> (X \<Rightarrow>\<^sub>Q Y) \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx exp_qbs_Mx comp_def)

corollary qbs_morphism_app:
  assumes "f \<in> X \<rightarrow>\<^sub>Q (Y \<Rightarrow>\<^sub>Q Z)" "g \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>x. (f x) (g x)) \<in> X \<rightarrow>\<^sub>Q Z"
  by(rule qbs_morphism_cong'[where f="(\<lambda>fx. (fst fx) (snd fx)) \<circ> (\<lambda>x. (f x, g x))",OF _ qbs_morphism_comp[OF qbs_morphism_Pair[OF assms] qbs_morphism_eval]]) auto

ML_file \<open>qbs.ML\<close>

attribute_setup qbs = \<open>
  Attrib.add_del Qbs.qbs_add Qbs.qbs_del\<close>
 "declaration of qbs rule"

method_setup qbs = \<open> Scan.lift (Scan.succeed (METHOD o Qbs.qbs_tac))\<close>

simproc_setup qbs ("x \<in> qbs_space X") = \<open>K Qbs.simproc\<close>

declare
  fst_qbs_morphism[qbs]
  snd_qbs_morphism[qbs]
  qbs_morphism_const[qbs]
  qbs_morphism_ident[qbs]
  qbs_morphism_ident'[qbs]
  qbs_morphism_curry[qbs]

lemma [qbs]:
  shows qbs_morphism_Pair1: "Pair \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q (X \<Otimes>\<^sub>Q Y)"
  by(auto intro!: qbs_morphismI simp: exp_qbs_Mx pair_qbs_Mx comp_def)

lemma qbs_morphism_case_prod[qbs]: "case_prod \<in> exp_qbs X (exp_qbs Y Z) \<rightarrow>\<^sub>Q exp_qbs (X \<Otimes>\<^sub>Q Y) Z"
  by(fastforce intro!: qbs_morphismI simp: exp_qbs_Mx pair_qbs_Mx comp_def split_beta')

lemma uncurry_preserves_morphisms:
  assumes [qbs]:"(\<lambda>x y. f (x,y)) \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Z"
  shows "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  by(rule qbs_morphism_cong'[where f="case_prod (\<lambda>x y. f (x,y))"],simp) qbs

lemma qbs_morphism_comp'[qbs]:"comp \<in> Y \<Rightarrow>\<^sub>Q Z \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphismI simp: exp_qbs_Mx)

lemma arg_swap_morphism:
  assumes "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y Z"
  shows "(\<lambda>y x. f x y) \<in> Y \<rightarrow>\<^sub>Q exp_qbs X Z"
  using assms by simp

lemma exp_qbs_comp_morphism:
  assumes "f \<in> W \<rightarrow>\<^sub>Q exp_qbs X Y"
      and "g \<in> W \<rightarrow>\<^sub>Q exp_qbs Y Z"
    shows "(\<lambda>w. g w \<circ> f w) \<in> W \<rightarrow>\<^sub>Q exp_qbs X Z"
  using assms by qbs

lemma arg_swap_morphism_map_qbs1:
  assumes "g \<in> exp_qbs W (exp_qbs X Y) \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>k. g (k \<circ> f)) \<in> exp_qbs (map_qbs f W) (exp_qbs X Y) \<rightarrow>\<^sub>Q Z"
  using assms map_qbs_morphism_f by qbs

lemma qbs_morphism_map_prod[qbs]: "map_prod \<in> X \<Rightarrow>\<^sub>Q Y \<rightarrow>\<^sub>Q (W \<Rightarrow>\<^sub>Q Z) \<Rightarrow>\<^sub>Q (X \<Otimes>\<^sub>Q W) \<Rightarrow>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)"
  by(auto intro!: qbs_morphismI simp: exp_qbs_Mx pair_qbs_Mx map_prod_def comp_def case_prod_beta')

lemma qbs_morphism_pair_swap:
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>(x,y). f (y,x)) \<in> Y \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Z"
  using assms by simp

lemma
  shows qbs_morphism_pair_assoc1: "(\<lambda>((x,y),z). (x,(y,z))) \<in> (X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)"
    and qbs_morphism_pair_assoc2: "(\<lambda>(x,(y,z)). ((x,y),z)) \<in> X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z) \<rightarrow>\<^sub>Q (X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z"
  by simp_all

lemma Inl_qbs_morphism[qbs]: "Inl \<in> X \<rightarrow>\<^sub>Q X \<Oplus>\<^sub>Q Y"
  by(auto intro!: qbs_morphismI bexI[where x="{}"] simp: copair_qbs_Mx copair_qbs_Mx_def comp_def)

lemma Inr_qbs_morphism[qbs]: "Inr \<in> Y \<rightarrow>\<^sub>Q X \<Oplus>\<^sub>Q Y"
  by(auto intro!: qbs_morphismI bexI[where x="UNIV"] simp: copair_qbs_Mx copair_qbs_Mx_def comp_def)

lemma case_sum_qbs_morphism[qbs]: "case_sum \<in> X \<Rightarrow>\<^sub>Q Z \<rightarrow>\<^sub>Q (Y \<Rightarrow>\<^sub>Q Z) \<Rightarrow>\<^sub>Q (X \<Oplus>\<^sub>Q Y \<Rightarrow>\<^sub>Q Z)"
  by(auto intro!: qbs_morphismI qbs_Mx_indicat simp: copair_qbs_Mx copair_qbs_Mx_def exp_qbs_Mx case_sum_if)

lemma map_sum_qbs_morphism[qbs]: "map_sum \<in> X \<Rightarrow>\<^sub>Q Y \<rightarrow>\<^sub>Q (X' \<Rightarrow>\<^sub>Q Y') \<Rightarrow>\<^sub>Q (X \<Oplus>\<^sub>Q X' \<Rightarrow>\<^sub>Q Y \<Oplus>\<^sub>Q Y')"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q Y)"
  then have ha[measurable]: "\<forall>(k :: real \<Rightarrow> real)\<in>borel_measurable borel. \<forall>a\<in>qbs_Mx X. (\<lambda>r. \<alpha> (k r) (a r)) \<in> qbs_Mx Y"
    by (auto simp: exp_qbs_Mx)
  show "map_sum \<circ> \<alpha> \<in> qbs_Mx ((X' \<Rightarrow>\<^sub>Q Y') \<Rightarrow>\<^sub>Q X \<Oplus>\<^sub>Q X' \<Rightarrow>\<^sub>Q Y \<Oplus>\<^sub>Q Y')"
    unfolding exp_qbs_Mx
  proof safe
    fix \<beta> b and f g :: "real \<Rightarrow> real"
    assume h[measurable]: "\<forall>(k :: real \<Rightarrow> real)\<in>borel_measurable borel. \<forall>b\<in>qbs_Mx X'. (\<lambda>r. \<beta> (k r) (b r)) \<in> qbs_Mx Y'"
         "f \<in> borel_measurable borel" "g \<in> borel_measurable borel"
     and b: "b \<in> qbs_Mx (X \<Oplus>\<^sub>Q X')"  
    show "(\<lambda>r. (map_sum \<circ> \<alpha>) (f (g r)) (\<beta> (g r)) (b r)) \<in> qbs_Mx (Y \<Oplus>\<^sub>Q Y')"
    proof(rule copair_qbs_MxD[OF b])
      fix a
      assume "a \<in> qbs_Mx X" "b = (\<lambda>r. Inl (a r))"
      with ha show "(\<lambda>r. (map_sum \<circ> \<alpha>) (f (g r)) (\<beta> (g r)) (b r)) \<in> qbs_Mx (Y \<Oplus>\<^sub>Q Y')"
        by(auto simp: copair_qbs_Mx copair_qbs_Mx_def intro!: bexI[where x="{}"])
    next
      fix a
      assume "a \<in> qbs_Mx X'" "b = (\<lambda>r. Inr (a r))"
      with h(1) show "(\<lambda>r. (map_sum \<circ> \<alpha>) (f (g r)) (\<beta> (g r)) (b r)) \<in> qbs_Mx (Y \<Oplus>\<^sub>Q Y')"
        by(auto simp: copair_qbs_Mx copair_qbs_Mx_def intro!: bexI[where x="UNIV"])
    next
      fix S a a'
      assume "S \<in> sets borel" "S \<noteq> {}" "S \<noteq> UNIV" "a \<in> qbs_Mx X" "a' \<in> qbs_Mx X'" "b = (\<lambda>r. if r \<in> S then Inl (a r) else Inr (a' r))"
      with h ha show "(\<lambda>r. (map_sum \<circ> \<alpha>) (f (g r)) (\<beta> (g r)) (b r)) \<in> qbs_Mx (Y \<Oplus>\<^sub>Q Y')"
        by simp (fastforce simp: copair_qbs_Mx copair_qbs_Mx_def intro!: bexI[where x=S])
    qed
  qed
qed

lemma qbs_morphism_component_singleton[qbs]:
  assumes "i \<in> I"
  shows "(\<lambda>x. x i) \<in> (\<Pi>\<^sub>Q i\<in>I. (M i)) \<rightarrow>\<^sub>Q M i"
  by(auto intro!: qbs_morphismI simp: comp_def assms PiQ_Mx)

lemma qbs_morphism_component_singleton':
  assumes "f \<in> Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. X i)" "g \<in> Z \<rightarrow>\<^sub>Q Y" "i \<in> I"
  shows "(\<lambda>x. f (g x) i) \<in> Z \<rightarrow>\<^sub>Q X i"
  by(auto intro!: qbs_morphism_compose[OF assms(2)] qbs_morphism_compose[OF assms(1)] qbs_morphism_component_singleton assms)

lemma product_qbs_canonical1:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> Y \<rightarrow>\<^sub>Q X i"
      and "\<And>i. i \<notin> I \<Longrightarrow> f i = (\<lambda>y. undefined)"
    shows "(\<lambda>y i. f i y) \<in> Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. X i)"
  using assms qbs_morphism_Mx[OF assms(1)] by(auto intro!: qbs_morphismI simp: PiQ_Mx comp_def)

lemma product_qbs_canonical2:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> Y \<rightarrow>\<^sub>Q X i"
          "\<And>i. i \<notin> I \<Longrightarrow> f i = (\<lambda>y. undefined)"
          "g \<in> Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. X i)"
          "\<And>i. i \<in> I \<Longrightarrow> f i = (\<lambda>x. x i) \<circ> g"
      and "y \<in> qbs_space Y"
    shows "g y = (\<lambda>i. f i y)"
proof(intro ext)
  fix i
  show "g y i = f i y"
  proof(cases "i \<in> I")
    case True
    then show ?thesis
      using assms(4)[of i] by simp
  next
    case False
    with qbs_morphism_space[OF assms(3)] assms(2,3,5) show ?thesis
      by(auto simp: PiQ_Mx PiQ_space)
  qed
qed

lemma merge_qbs_morphism:
 "merge I J \<in> (\<Pi>\<^sub>Q i\<in>I. (M i)) \<Otimes>\<^sub>Q (\<Pi>\<^sub>Q j\<in>J. (M j)) \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I\<union>J. (M i))"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx ((\<Pi>\<^sub>Q i\<in>I. (M i)) \<Otimes>\<^sub>Q (\<Pi>\<^sub>Q j\<in>J. (M j)))"
  show "merge I J \<circ> \<alpha> \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>I\<union>J. (M i))"
  proof -
    {
      fix i
      assume "i \<in> I \<union> J"
      then consider "i \<in> I" | "i \<in> I \<and> i \<in> J" | "i \<notin> I \<and> i \<in> J"
        by auto
      hence "(\<lambda>r. (merge I J \<circ> \<alpha>) r i) \<in> qbs_Mx (M i)"
        by cases (insert h, auto simp: merge_def split_beta' pair_qbs_Mx PiQ_Mx)
    }
    thus ?thesis
      by(auto simp: PiQ_Mx) (auto simp: merge_def split_beta')
  qed
qed

lemma ini_morphism[qbs]:
  assumes "j \<in> I"
  shows "(\<lambda>x. (j,x)) \<in> X j \<rightarrow>\<^sub>Q (\<amalg>\<^sub>Q i\<in>I. X i)"
  by(fastforce intro!: qbs_morphismI exI[where x="\<lambda>r. j"] simp: coprod_qbs_Mx_def comp_def assms coprod_qbs_Mx)

lemma coprod_qbs_canonical1:
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> f i \<in> X i \<rightarrow>\<^sub>Q Y"
    shows "(\<lambda>(i,x). f i x) \<in> (\<amalg>\<^sub>Q i \<in>I. X i) \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (coprod_qbs I X)"
  then obtain \<beta> g where ha:
   "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (g r, \<beta> (g r) r))" and hg[measurable]:"g \<in> borel \<rightarrow>\<^sub>M count_space I"
    by(fastforce simp: coprod_qbs_Mx_def coprod_qbs_Mx)
  define f' where "f' \<equiv> (\<lambda>i r. f i (\<beta> i r))"
  have "range g \<subseteq> I"
    using measurable_space[OF hg] by auto
  hence 1:"(\<And>i. i \<in> range g \<Longrightarrow> f' i \<in> qbs_Mx Y)"
    using qbs_morphism_Mx[OF assms(2) ha(1),simplified comp_def]
    by(auto simp: f'_def)
  have "(\<lambda>(i, x). f i x) \<circ> \<alpha> = (\<lambda>r. f' (g r) r)"
    by(auto simp: ha(2) f'_def)
  also have "... \<in> qbs_Mx Y"
    by(auto intro!: qbs_closed3_dest2'[OF assms(1) hg,of f',OF 1])
  finally show "(\<lambda>(i, x). f i x) \<circ> \<alpha> \<in> qbs_Mx Y " .
qed

lemma coprod_qbs_canonical1':
  assumes "countable I"
      and "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f (i,x)) \<in> X i \<rightarrow>\<^sub>Q Y"
    shows  "f \<in> (\<amalg>\<^sub>Q i \<in>I. X i) \<rightarrow>\<^sub>Q Y"
  using coprod_qbs_canonical1[where f="curry f"] assms by(auto simp: curry_def)

lemma None_qbs[qbs]: "None \<in> qbs_space (option_qbs X)"
  by(simp add: option_qbs_space)

lemma Some_qbs[qbs]: "Some \<in> X \<rightarrow>\<^sub>Q option_qbs X"
proof -
  have 1: "Some = (\<lambda>x. case x of Inl y \<Rightarrow> Some y | Inr y \<Rightarrow> None) \<circ> Inl"
    by standard auto
  show ?thesis
    unfolding option_qbs_def
    by(rule qbs_morphism_cong'[OF _ qbs_morphism_comp[OF Inl_qbs_morphism map_qbs_morphism_f]]) (simp add: 1)
qed

lemma case_option_qbs_morphism[qbs]: "case_option \<in> qbs_space (Y \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q option_qbs X \<Rightarrow>\<^sub>Q Y)"
proof(rule curry_preserves_morphisms[OF arg_swap_morphism])
  have "(\<lambda>x y. case x of None \<Rightarrow> fst y | Some z \<Rightarrow> snd y z) = (\<lambda>x y. case x of Inr _ \<Rightarrow> fst y | Inl z \<Rightarrow> snd y z) \<circ> (\<lambda>z. case z of Some x \<Rightarrow> Inl x | None \<Rightarrow> Inr ())"
    by standard+ (simp add: option.case_eq_if)
  also have "... \<in> option_qbs X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q Y"
    unfolding option_qbs_def by(rule qbs_morphism_comp[OF  map_qbs_morphism_inverse_f]) (auto simp: copair_qbs_space)
  finally show " (\<lambda>x y. case x of None \<Rightarrow> fst y | Some x \<Rightarrow> snd y x) \<in> option_qbs X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q Y" .
qed

lemma rec_option_qbs_morphism[qbs]: "rec_option \<in> qbs_space (Y \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q option_qbs X \<Rightarrow>\<^sub>Q Y)"
proof -
  have [simp]: "rec_option = case_option"
    by standard+ (metis option.case_eq_if option.exhaust_sel option.simps(6) option.simps(7)) 
  show ?thesis by simp
qed

lemma bind_option_qbs_morphism[qbs]: "(\<bind>) \<in> qbs_space (option_qbs X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q option_qbs Y) \<Rightarrow>\<^sub>Q option_qbs Y)"
  by(simp add: Option.bind_def)

lemma Let_qbs_morphism[qbs]: "Let \<in> X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q Y"
proof -
  have [simp]:"Let = (\<lambda>x f. f x)" by standard+ auto
  show ?thesis by simp
qed

end