(*  Title:   Binary_Product_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Product Spaces\<close>

theory Binary_Product_QuasiBorel
  imports "Measure_QuasiBorel_Adjunction"
begin

subsubsection \<open> Binary Product Spaces \<close>
definition pair_qbs_Mx :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real => 'a \<times> 'b) set" where
"pair_qbs_Mx X Y \<equiv> {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"

definition pair_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<times> 'b) quasi_borel" (infixr "\<Otimes>\<^sub>Q" 80) where
"pair_qbs X Y = Abs_quasi_borel (qbs_space X \<times> qbs_space Y, pair_qbs_Mx X Y)"


lemma pair_qbs_f[simp]: "pair_qbs_Mx X Y \<subseteq> UNIV \<rightarrow> qbs_space X \<times> qbs_space Y"
  unfolding pair_qbs_Mx_def
  by (auto simp: mem_Times_iff[of _ "qbs_space X" "qbs_space Y"]; fastforce)

lemma pair_qbs_closed1: "qbs_closed1 (pair_qbs_Mx (X::'a quasi_borel) (Y::'b quasi_borel))"
  unfolding pair_qbs_Mx_def qbs_closed1_def
  by (metis (no_types, lifting) comp_assoc mem_Collect_eq qbs_closed1_dest)

lemma pair_qbs_closed2: "qbs_closed2 (qbs_space X \<times> qbs_space Y) (pair_qbs_Mx X Y)"
  unfolding qbs_closed2_def pair_qbs_Mx_def
  by auto

lemma pair_qbs_closed3: "qbs_closed3 (pair_qbs_Mx (X::'a quasi_borel) (Y::'b quasi_borel))"
proof(auto simp add: qbs_closed3_def pair_qbs_Mx_def)
  fix P :: "real \<Rightarrow> nat"
  fix Fi :: "nat \<Rightarrow> real \<Rightarrow> 'a \<times> 'b"
  define Fj :: "nat \<Rightarrow> real \<Rightarrow> 'a" where "Fj \<equiv> \<lambda>j.(fst \<circ> Fi j)"
  assume "\<forall>i. fst \<circ> Fi i \<in> qbs_Mx X \<and> snd \<circ> Fi i \<in> qbs_Mx Y"
  then have "\<forall>i. Fj i \<in> qbs_Mx X" by (simp add: Fj_def)
  moreover assume "\<forall>i. P -` {i} \<in> sets real_borel"
  ultimately have "(\<lambda>r. Fj (P r) r) \<in> qbs_Mx X"
    by auto
  moreover have "fst \<circ> (\<lambda>r. Fi (P r) r) = (\<lambda>r. Fj (P r) r)" by (auto simp add: Fj_def)
  ultimately show "fst \<circ> (\<lambda>r. Fi (P r) r) \<in> qbs_Mx X" by simp
next
  fix P :: "real \<Rightarrow> nat"
  fix Fi :: "nat \<Rightarrow> real \<Rightarrow> 'a \<times> 'b"
  define Fj :: "nat \<Rightarrow> real \<Rightarrow> 'b" where "Fj \<equiv> \<lambda>j.(snd \<circ> Fi j)"
  assume "\<forall>i. fst \<circ> Fi i \<in> qbs_Mx X \<and> snd \<circ> Fi i \<in> qbs_Mx Y"
  then have "\<forall>i. Fj i \<in> qbs_Mx Y" by (simp add: Fj_def)
  moreover assume "\<forall>i. P -` {i} \<in> sets real_borel"
  ultimately have "(\<lambda>r. Fj (P r) r) \<in> qbs_Mx Y"
    by auto
  moreover have "snd \<circ> (\<lambda>r. Fi (P r) r) = (\<lambda>r. Fj (P r) r)" by (auto simp add: Fj_def)
  ultimately show "snd \<circ> (\<lambda>r. Fi (P r) r) \<in> qbs_Mx Y" by simp
qed

lemma pair_qbs_correct: "Rep_quasi_borel (X \<Otimes>\<^sub>Q Y) = (qbs_space X \<times> qbs_space Y, pair_qbs_Mx X Y)"
  unfolding pair_qbs_def
  by(auto intro!: Abs_quasi_borel_inverse pair_qbs_f simp: pair_qbs_closed3 pair_qbs_closed2 pair_qbs_closed1)

lemma pair_qbs_space[simp]: "qbs_space (X \<Otimes>\<^sub>Q Y) = qbs_space X \<times> qbs_space Y"
  by (simp add: qbs_space_def pair_qbs_correct)

lemma pair_qbs_Mx[simp]: "qbs_Mx (X \<Otimes>\<^sub>Q Y) = pair_qbs_Mx X Y"
  by (simp add: qbs_Mx_def pair_qbs_correct)


lemma pair_qbs_morphismI:
  assumes "\<And>\<alpha> \<beta>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> \<beta> \<in> qbs_Mx Y 
           \<Longrightarrow> f \<circ> (\<lambda>r. (\<alpha> r, \<beta> r)) \<in> qbs_Mx Z"
    shows "f \<in> (X \<Otimes>\<^sub>Q Y) \<rightarrow>\<^sub>Q Z"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume 1:"\<alpha> \<in> qbs_Mx (X \<Otimes>\<^sub>Q Y)"
  have "f \<circ> \<alpha> = f \<circ> (\<lambda>r. ((fst \<circ> \<alpha>) r, (snd \<circ> \<alpha>) r))"
    by auto
  also have "... \<in> qbs_Mx Z"
    using 1 assms[of "fst \<circ> \<alpha>" "snd \<circ> \<alpha>"]
    by(simp add: pair_qbs_Mx_def)
  finally show "f \<circ> \<alpha> \<in> qbs_Mx Z" .
qed


lemma fst_qbs_morphism:
  "fst \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q X"
  by(auto simp add: qbs_morphism_def pair_qbs_Mx_def)

lemma snd_qbs_morphism:
  "snd \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Y"
  by(auto simp add: qbs_morphism_def pair_qbs_Mx_def)

lemma qbs_morphism_pair_iff:
 "f \<in> X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q Z \<longleftrightarrow> fst \<circ> f \<in> X \<rightarrow>\<^sub>Q Y \<and> snd \<circ> f \<in> X \<rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphismI qbs_morphism_comp[OF _ fst_qbs_morphism,of f X Y Z ]qbs_morphism_comp[OF _ snd_qbs_morphism,of f X Y Z]
            simp: pair_qbs_Mx_def comp_assoc[symmetric])

lemma qbs_morphism_Pair1:
  assumes "x \<in> qbs_space X"
  shows "Pair x \<in> Y \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
  using assms
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx_def comp_def)

lemma qbs_morphism_Pair1':
  assumes "x \<in> qbs_space X"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
    shows "(\<lambda>y. f (x,y)) \<in> Y \<rightarrow>\<^sub>Q Z"
  using qbs_morphism_comp[OF qbs_morphism_Pair1[OF assms(1)] assms(2)]
  by(simp add: comp_def)

lemma qbs_morphism_Pair2:
  assumes "y \<in> qbs_space Y"
  shows "(\<lambda>x. (x,y)) \<in> X \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
  using assms
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx_def comp_def)

lemma qbs_morphism_Pair2':
  assumes "y \<in> qbs_space Y"
      and "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
    shows "(\<lambda>x. f (x,y)) \<in> X \<rightarrow>\<^sub>Q Z"
  using qbs_morphism_comp[OF qbs_morphism_Pair2[OF assms(1)] assms(2)]
  by(simp add: comp_def)

lemma qbs_morphism_fst'':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>k. f (fst k)) \<in> X \<Otimes>\<^sub>Q Z \<rightarrow>\<^sub>Q Y"
  using qbs_morphism_comp[OF fst_qbs_morphism assms,of Z]
  by(simp add: comp_def)

lemma qbs_morphism_snd'':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>k. f (snd k)) \<in> Z \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
  using qbs_morphism_comp[OF snd_qbs_morphism assms,of Z]
  by(simp add: comp_def)

lemma qbs_morphism_tuple:
  assumes "f \<in> Z \<rightarrow>\<^sub>Q X"
      and "g \<in> Z \<rightarrow>\<^sub>Q Y"
    shows "(\<lambda>z. (f z, g z)) \<in> Z \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
proof(rule qbs_morphismI,simp)
  fix \<alpha>
  assume  h:"\<alpha> \<in> qbs_Mx Z"
  then have "(\<lambda>z. (f z, g z)) \<circ> \<alpha> \<in> UNIV \<rightarrow> qbs_space X \<times> qbs_space Y"
    using assms qbs_morphismE(2)[OF assms(1)] qbs_morphismE(2)[OF assms(2)]
    by fastforce
  moreover have "fst \<circ> ((\<lambda>z. (f z, g z)) \<circ> \<alpha>) = f \<circ> \<alpha>" by auto
  moreover have "... \<in> qbs_Mx X" 
    using assms(1) h by auto
  moreover have "snd \<circ> ((\<lambda>z. (f z, g z)) \<circ> \<alpha>) = g \<circ> \<alpha>" by auto
  moreover have "... \<in> qbs_Mx Y"
    using assms(2) h by auto
  ultimately show "(\<lambda>z. (f z, g z)) \<circ> \<alpha> \<in> pair_qbs_Mx X Y"
    by (simp add: pair_qbs_Mx_def)
qed

lemma qbs_morphism_map_prod:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
      and "g \<in> X' \<rightarrow>\<^sub>Q Y'"
    shows "map_prod f g \<in> X \<Otimes>\<^sub>Q X'\<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q Y'"
proof(rule pair_qbs_morphismI)
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx X"
           "\<beta> \<in> qbs_Mx X'"
  have [simp]: "fst \<circ> (map_prod f g \<circ> (\<lambda>r. (\<alpha> r, \<beta> r))) = f \<circ> \<alpha>" by auto
  have [simp]: "snd \<circ> (map_prod f g \<circ> (\<lambda>r. (\<alpha> r, \<beta> r))) = g \<circ> \<beta>" by auto
  show "map_prod f g \<circ> (\<lambda>r. (\<alpha> r, \<beta> r)) \<in> qbs_Mx (Y \<Otimes>\<^sub>Q Y')"
    using h assms by(auto simp: pair_qbs_Mx_def)
qed

lemma qbs_morphism_pair_swap':
  "(\<lambda>(x,y). (y,x)) \<in> (X::'a quasi_borel) \<Otimes>\<^sub>Q (Y::'b quasi_borel) \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q X"
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx_def split_beta' comp_def)

lemma qbs_morphism_pair_swap:
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>(x,y). f (y,x)) \<in> Y \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Z"
proof -
  have "(\<lambda>(x,y). f (y,x)) = f \<circ> (\<lambda>(x,y). (y,x))" by auto
  thus ?thesis
    using qbs_morphism_comp[of "(\<lambda>(x,y). (y,x))" "Y \<Otimes>\<^sub>Q X" _ f] qbs_morphism_pair_swap' assms
    by auto
qed

lemma qbs_morphism_pair_assoc1:
 "(\<lambda>((x,y),z). (x,(y,z))) \<in> (X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)"
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx_def split_beta' comp_def)

lemma qbs_morphism_pair_assoc2:
 "(\<lambda>(x,(y,z)). ((x,y),z)) \<in> X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z) \<rightarrow>\<^sub>Q (X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z"
  by(auto intro!: qbs_morphismI simp: pair_qbs_Mx_def split_beta' comp_def)

lemma pair_qbs_fst:
  assumes "qbs_space Y \<noteq> {}"
  shows "map_qbs fst (X \<Otimes>\<^sub>Q Y) = X"
proof(rule qbs_eqI)
  show "qbs_Mx (map_qbs fst (X \<Otimes>\<^sub>Q Y)) = qbs_Mx X"
  proof auto
    fix \<alpha>x
    assume hx:"\<alpha>x \<in> qbs_Mx X"
    obtain \<alpha>y where hy:"\<alpha>y \<in> qbs_Mx Y"
      using qbs_empty_equiv[of Y] assms
      by auto
    show "\<exists>\<alpha>\<in>pair_qbs_Mx X Y. \<alpha>x = fst \<circ> \<alpha>"
      by(auto intro!: exI[where x="\<lambda>r. (\<alpha>x r, \<alpha>y r)"] simp: pair_qbs_Mx_def hx hy comp_def)
  qed (simp add: pair_qbs_Mx_def)
qed

lemma pair_qbs_snd:
  assumes "qbs_space X \<noteq> {}"
  shows "map_qbs snd (X \<Otimes>\<^sub>Q Y) = Y"
proof(rule qbs_eqI)
  show "qbs_Mx (map_qbs snd (X \<Otimes>\<^sub>Q Y)) = qbs_Mx Y"
  proof auto
    fix \<alpha>y
    assume hy:"\<alpha>y \<in> qbs_Mx Y"
    obtain \<alpha>x where hx:"\<alpha>x \<in> qbs_Mx X"
      using qbs_empty_equiv[of X] assms
      by auto
    show "\<exists>\<alpha>\<in>pair_qbs_Mx X Y. \<alpha>y = snd \<circ> \<alpha>"
      by(auto intro!: exI[where x="\<lambda>r. (\<alpha>x r, \<alpha>y r)"] simp: pair_qbs_Mx_def hx hy comp_def)
  qed (simp add: pair_qbs_Mx_def)
qed

text \<open> The following lemma corresponds to \<^cite>\<open>"Heunen_2017"\<close> Proposition 19(1). \<close>
lemma r_preserves_product :
  "measure_to_qbs (X \<Otimes>\<^sub>M Y) = measure_to_qbs X \<Otimes>\<^sub>Q measure_to_qbs Y"
  by(auto intro!: qbs_eqI simp: measurable_pair_iff pair_qbs_Mx_def)

lemma l_product_sets[simp,measurable_cong]:
  "sets (qbs_to_measure X \<Otimes>\<^sub>M qbs_to_measure Y) \<subseteq> sets (qbs_to_measure (X \<Otimes>\<^sub>Q Y))"
proof(rule sets_pair_in_sets,simp)
  fix A B
  assume h:"A \<in> sigma_Mx X"
           "B \<in> sigma_Mx Y"
  then obtain Ua Ub where hu:
   "A = Ua \<inter> qbs_space X" "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel"
   "B = Ub \<inter> qbs_space Y" "\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` Ub \<in> sets real_borel"
    by(auto simp add: sigma_Mx_def)
  show "A \<times> B \<in> sigma_Mx (X \<Otimes>\<^sub>Q Y)"
  proof(simp add: sigma_Mx_def, rule exI[where x="Ua \<times> Ub"])
    show "A \<times> B = Ua \<times> Ub \<inter> qbs_space X \<times> qbs_space Y \<and>
    (\<forall>\<alpha>\<in>pair_qbs_Mx X Y. \<alpha> -` (Ua \<times> Ub) \<in> sets real_borel)"
      using hu by(auto simp add: pair_qbs_Mx_def vimage_Times)
  qed
qed

lemma(in pair_standard_borel) l_r_r_sets[simp,measurable_cong]:
 "sets (qbs_to_measure (measure_to_qbs M \<Otimes>\<^sub>Q measure_to_qbs N)) = sets (M \<Otimes>\<^sub>M N)"
  by(simp only: r_preserves_product[symmetric]) (rule standard_borel_lr_sets_ident)

end