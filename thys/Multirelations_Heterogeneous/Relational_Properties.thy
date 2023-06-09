section \<open>Properties of Binary Relations\<close>

theory Relational_Properties

imports Main

begin

text \<open>This is a general-purpose theory for enrichments of Rel, which is still quite basic,
but helpful for developing properties of multirelations.\<close>

notation relcomp (infixl ";" 75)
notation converse ("_\<^sup>\<smile>" [1000] 999)

type_synonym ('a,'b) rel = "('a \<times> 'b) set"

lemma modular_law: "R ; S \<inter> T \<subseteq> (R \<inter> T ; S\<^sup>\<smile>) ; S"
  by blast

lemma compl_conv: "-(R\<^sup>\<smile>) = (-R)\<^sup>\<smile>"
  by fastforce

definition top :: "('a,'b) rel" where
  "top = {(a,b) |a b. True}"

abbreviation "neg R \<equiv> Id \<inter> -R"


subsection \<open>Univalence, totality, determinism, and related properties\<close>

definition univalent :: "('a,'b) rel \<Rightarrow> bool" where
  "univalent R = (R\<^sup>\<smile> ; R \<subseteq> Id)"

definition total :: "('a,'b) rel \<Rightarrow> bool" where
  "total R = (Id \<subseteq> R ; R\<^sup>\<smile>)"

definition injective :: "('a,'b) rel \<Rightarrow> bool" where
  "injective R = (R ; R\<^sup>\<smile> \<subseteq> Id)"

definition surjective :: "('a,'b) rel \<Rightarrow> bool" where
  "surjective R = (Id \<subseteq> R\<^sup>\<smile> ; R)"

definition deterministic :: "('a,'b) rel \<Rightarrow> bool" where
  "deterministic R = (univalent R \<and> total R)"

definition bijective :: "('a,'b) rel \<Rightarrow> bool" where
  "bijective R = (injective R \<and> surjective R)"

lemma univalent_set: "univalent R = (\<forall>a b c. (a,b) \<in> R \<and> (a,c) \<in> R \<longrightarrow> b = c)"
  unfolding univalent_def converse_unfold Id_def by force

text \<open>Univalent relations feature as single-valued relations in Main.\<close>

lemma univ_single_valued: "univalent R = single_valued R"
  unfolding univalent_set single_valued_def by auto

lemma total_set: "total R = (\<forall>a. \<exists>b. (a,b) \<in> R)"
  unfolding total_def converse_unfold Id_def by force

lemma total_var: "total R = (R ; top = top)"
  unfolding total_set top_def by force

lemma deterministic_set: "deterministic R = (\<forall>a . \<exists>!B . (a,B) \<in> R)"
  unfolding deterministic_def univalent_set total_set by force

lemma deterministic_var1: "deterministic R = (R ; -Id = -R)"
  unfolding deterministic_set Id_def by force

lemma deterministic_var2: "deterministic R = (\<forall>S. R ; -S = -(R ; S))"
  unfolding deterministic_set by (standard, force, blast)

lemma inj_univ: "injective R = univalent (R\<^sup>\<smile>)"
  by (simp add: injective_def univalent_def)

lemma injective_set: "injective S = (\<forall>a b c. (a,c) \<in> S \<and> (b,c) \<in> S \<longrightarrow> a = b)"
  by (meson converseD converseI inj_univ univalent_set)

lemma surj_tot: "surjective R = total (R\<^sup>\<smile>)"
  by (simp add: surjective_def total_def)

lemma surjective_set: "surjective S = (\<forall>b. \<exists>a. (a,b) \<in> S)"
  by (simp add: surj_tot total_set)

lemma surj_var: "surjective R = (R\<^sup>\<smile> ; top = top)"
  by (simp add: surj_tot total_var)

lemma bij_det: "bijective R = deterministic (R\<^sup>\<smile>)"
  by (simp add: bijective_def deterministic_def inj_univ surj_tot)

lemma univ_relcomp: "univalent R \<Longrightarrow> univalent S \<Longrightarrow> univalent (R ; S)"
  by (simp add: single_valued_relcomp univ_single_valued)

lemma tot_relcomp: "total R \<Longrightarrow> total S \<Longrightarrow> total (R ; S)"
  by (meson relcomp.simps total_set)

lemma det_relcomp: "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> deterministic (R ; S)"
  by (simp add: deterministic_def tot_relcomp univ_relcomp)

lemma inj_relcomp: "injective R \<Longrightarrow> injective S \<Longrightarrow> injective (R ; S)"
  by (simp add: converse_relcomp inj_univ univ_relcomp)

lemma surj_relcomp: "surjective R \<Longrightarrow> surjective S \<Longrightarrow> surjective (R ; S)"
  by (simp add: converse_relcomp surj_tot tot_relcomp)

lemma bij_relcomp: "bijective R \<Longrightarrow> bijective S \<Longrightarrow> bijective (R ; S)"
  by (simp add: bijective_def inj_relcomp surj_relcomp)

lemma det_Id: "deterministic Id"
  by (simp add: deterministic_var1)

lemma bij_Id: "bijective Id"
  by (simp add: bij_det det_Id)

lemma tot_top: "total top"
  by (simp add: top_def total_set)

lemma tot_surj: "surjective top"
  by (simp add: surjective_set top_def)

lemma det_meet_distl: "univalent R \<Longrightarrow> R ; (S \<inter> T) = R ; S \<inter> R ; T"
  unfolding univalent_set relcomp_def relcompp_apply by force

lemma inj_meet_distr: "injective T \<Longrightarrow> (R \<inter> S) ; T = R ; T \<inter> S ; T"
  unfolding injective_def converse_def Id_def relcomp.simps by force

lemma univ_modular: "univalent S \<Longrightarrow> R ; S \<inter> T = (R \<inter> T ; S\<^sup>\<smile>) ; S"
  unfolding univalent_set converse_unfold relcomp.simps by force


subsection \<open>Inverse image and the diagonal and graph functors\<close>

definition Invim :: "('a,'b) rel \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "Invim R = Image (R\<^sup>\<smile>)"

definition Delta :: "'a set \<Rightarrow> ('a,'a) rel" ("\<Delta>") where
  "\<Delta> P = {(p,p) |p. p \<in> P}"

definition Grph :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'b) rel" where
  "Grph f = {(x,y). y = f x}"

lemma Image_Grph [simp]: "Image \<circ> Grph = image"
  unfolding Image_def Grph_def image_def by auto

subsection \<open>Relational domain, codomain and modalities\<close>

text \<open>Domain and codomain (range) maps have been defined in Main, but they return sets instead of relations.\<close>

definition dom :: "('a,'b) rel \<Rightarrow> ('a,'a) rel" where
  "dom R = Id \<inter> R ; R\<^sup>\<smile>"

definition cod :: "('a,'b) rel \<Rightarrow> ('b,'b) rel" where
  "cod R = dom (R\<^sup>\<smile>)"

definition rel_fdia :: "('a,'b) rel \<Rightarrow> ('b,'b) rel \<Rightarrow> ('a,'a) rel" ("(|_\<rangle>_)" [61,81] 82) where
  "|R\<rangle> Q = dom (R ; dom Q)"

definition rel_bdia :: "('a,'b) rel \<Rightarrow> ('a,'a) rel \<Rightarrow> ('b,'b) rel" ("(\<langle>_|_)" [61,81] 82) where
  "rel_bdia R = rel_fdia (R\<^sup>\<smile>)"

definition rel_fbox :: "('a,'b) rel \<Rightarrow> ('b,'b) rel \<Rightarrow> ('a,'a) rel" ("(|_]_)" [61,81] 82) where
  "|R]Q = neg (dom (R ; neg (dom Q)))"

definition rel_bbox :: "('a,'b) rel \<Rightarrow> ('a,'a) rel \<Rightarrow> ('b,'b) rel" ("([_|_)" [61,81] 82) where
  "rel_bbox R = rel_fbox (R\<^sup>\<smile>)"

lemma rel_bdia_def_var: "rel_bdia = rel_fdia \<circ> converse"
  unfolding rel_fdia_def fun_eq_iff comp_def rel_bdia_def by simp

lemma dom_set: "dom R = {(a,a) |a. \<exists>b. (a,b) \<in> R}"
  unfolding dom_def Id_def converse_unfold relcomp_unfold by force

lemma dom_Domain: "dom = \<Delta> \<circ> Domain"
  unfolding fun_eq_iff dom_set Delta_def Domain_def by clarsimp blast

lemma cod_set: "cod R = {(b,b) |b. \<exists>a. (a,b) \<in> R}"
  by (smt (verit) Collect_cong cod_def converseD converseI dom_set)

lemma cod_Range: "cod = \<Delta> \<circ> Range"
  unfolding fun_eq_iff cod_set Delta_def Range_def by clarsimp blast

lemma rel_fdia_set: "|R\<rangle> Q = {(a,a) |a. \<exists>b. (a,b) \<in> R \<and> (b,b) \<in> dom Q}"
  unfolding rel_fdia_def dom_set relcomp_unfold by force

lemma rel_bdia_set: "\<langle>R| P = {(b,b) |b. \<exists>a. (a,b) \<in> R \<and> (a,a) \<in> dom P}"
  by (smt (verit, best) Collect_cong converseD converseI rel_bdia_def rel_fdia_set)

lemma rel_fbox_set: "|R] Q = {(a,a) |a. \<forall>b. (a,b) \<in> R \<longrightarrow> (b,b) \<in> dom Q}"
  unfolding rel_fbox_def dom_set relcomp_unfold by force

lemma rel_bbox_set: "[R| P = {(b,b) |b. \<forall>a. (a,b) \<in> R \<longrightarrow> (a,a) \<in> dom P}"
  by (smt (verit) Collect_cong converseD converseI rel_bbox_def rel_fbox_set)

lemma dom_alt_def: "dom R = Id \<inter> R ; top"
  unfolding dom_set top_def Id_def by force

lemma dom_gla: "(dom R \<subseteq> Id \<inter> S) = (R \<subseteq> (Id \<inter> S) ; R)"
  unfolding dom_set Id_def relcomp_unfold by blast

lemma dom_gla_top: "(dom R \<subseteq> Id \<inter> S) = (R \<subseteq> (Id \<inter> S) ; top)"
  unfolding dom_set Id_def top_def relcomp_unfold by blast

lemma dom_subid: "(dom R = R) = (R = Id \<inter> R)"
  by (metis (no_types, lifting) Id_O_R R_O_Id dom_alt_def dom_gla_top equalityD1 inf.absorb_iff2 inf.commute inf.idem le_inf_iff relcomp_mono)

lemma dom_cod: "(dom R = R) = (cod R = R)"
  by (metis dom_def cod_def converse_Id converse_Int converse_converse converse_relcomp)

lemma dom_top: "R ; top = dom R ; top"
  unfolding dom_set top_def by blast

lemma top_dom: "dom R = dom (R ; top)"
  unfolding dom_def top_def by blast

lemma cod_top: "cod R = Id \<inter> top ; R"
  by (metis dom_def cod_def converse_Id converse_Int converse_converse converse_relcomp dom_alt_def surj_var tot_surj)

lemma dom_conv [simp]: "(dom R)\<^sup>\<smile> = dom R"
  by (simp add: dom_def converse_Int converse_relcomp)

lemma total_dom: "total R = (dom R = Id)"
  by (metis dom_def inf.orderE inf_le2 total_def)

lemma surj_cod: "surjective R = (cod R = Id)"
  by (simp add: cod_def surj_tot total_dom)

lemma fdia_demod: "( |R\<rangle> P \<subseteq> dom Q) = (R ; dom P \<subseteq> dom Q ; R)"
  unfolding rel_fdia_set dom_set relcomp_unfold by force

lemma bbox_demod: "(dom P \<subseteq> [R| Q) = (R ; dom P \<subseteq> dom Q ; R)"
  unfolding rel_bbox_set dom_def by force

lemma bdia_demod: "(\<langle>R| P \<subseteq> dom Q) = (dom P ; R \<subseteq> R ; dom Q)"
proof -
  have "(\<langle>R| P \<subseteq> dom Q) = ( |R\<^sup>\<smile>\<rangle> P \<subseteq> dom Q)"
    by (simp add: rel_bdia_def)
  also have "\<dots> = ((R\<^sup>\<smile>) ; dom P \<subseteq> dom Q ; (R\<^sup>\<smile>))"
    by (simp add: fdia_demod)
  also have "\<dots> = (((dom P ; R)\<^sup>\<smile>) \<subseteq> ((R ; dom Q)\<^sup>\<smile>))"
    by (simp add: converse_relcomp)
  also have "\<dots> = (dom P ; R \<subseteq> R ; dom Q)"
    by simp
  finally show ?thesis.
qed

lemma fbox_demod: "(dom P \<subseteq> |R] Q) = (dom P ; R \<subseteq> R ; dom Q)"
  unfolding rel_fbox_set dom_set relcomp_unfold by force

lemma fdia_demod_top: "( |R\<rangle> P \<subseteq> dom Q) = (R ; dom P ; top \<subseteq> dom Q ; top)"
  by (metis dom_def dom_gla_top rel_fdia_def top_dom)

lemma bbox_demod_top: "(dom P \<subseteq> [R| Q) = (R ; dom P ; top \<subseteq> dom Q ; top)"
  unfolding rel_bbox_def rel_fbox_def dom_def top_def by force

lemma fdia_bbox_galois: "( |R\<rangle> P \<subseteq> dom Q) = (dom P \<subseteq> [R| Q)"
  by (meson bbox_demod_top fdia_demod_top)

lemma bdia_fbox_galois: "(\<langle>R| P \<subseteq> dom Q) = (dom P \<subseteq> |R] Q)"
  by (simp add: fdia_bbox_galois rel_bbox_def rel_bdia_def)

lemma fdia_bdia_conjugation: "( |R\<rangle> P \<subseteq> neg (dom Q)) = (\<langle>R| Q \<subseteq> neg (dom P))"
  unfolding rel_fdia_set rel_bdia_set dom_set by force

lemma bfox_bbox_conjugation: "(neg (dom Q) \<subseteq> |R] P) = (neg (dom P) \<subseteq> [R| Q)"
  unfolding rel_fbox_set rel_bbox_set dom_set by clarsimp blast


subsection \<open>Residuation\<close>

definition lres :: "('a,'c) rel \<Rightarrow> ('b,'c) rel \<Rightarrow> ('a,'b) rel" (infixl "\<sslash>" 75)
  where "R \<sslash> S = {(a,b). \<forall>c. (b,c) \<in> S \<longrightarrow> (a,c) \<in> R}"

definition rres :: "('c,'a) rel \<Rightarrow> ('c,'b) rel \<Rightarrow> ('a,'b) rel" (infixl "\<setminus>" 75)
  where "R \<setminus> S = {(b,a). \<forall>c. (c,b) \<in> R \<longrightarrow> (c,a) \<in> S}"

lemma rres_lres_conv: "R \<setminus> S = (S\<^sup>\<smile> \<sslash> R\<^sup>\<smile>)\<^sup>\<smile>"
  unfolding rres_def lres_def by clarsimp fastforce

lemma lres_galois: "(R ; S \<subseteq> T) = (R \<subseteq> T \<sslash> S)"
  unfolding lres_def by blast

lemma rres_galois: "(R ; S \<subseteq> T) = (S \<subseteq> R \<setminus> T)"
  by (metis converse_converse converse_mono converse_relcomp lres_galois rres_lres_conv)

lemma lres_compl: "R \<sslash> S = -(-R ; S\<^sup>\<smile>)"
  unfolding lres_def converse_unfold by force

lemma rres_compl: "R \<setminus> S = -(R\<^sup>\<smile> ; -S)"
  unfolding rres_def converse_unfold by force

lemma lres_simp [simp]: "(R \<sslash> R) ; R = R"
  by (metis Id_O_R lres_galois relcomp_mono subsetI subsetI subset_antisym)

lemma rres_simp [simp]: "R ; (R \<setminus> R) = R"
  by (metis converse_converse converse_relcomp lres_simp rres_lres_conv)

lemma lres_curry: "R \<sslash> (T ; S) = (R \<sslash> S) \<sslash> T"
  by (metis (no_types, opaque_lifting) O_assoc dual_order.refl lres_galois subset_antisym)

lemma rres_curry: "(R ; S) \<setminus> T = S \<setminus> (R \<setminus> T)"
  by (simp add: converse_relcomp lres_curry rres_lres_conv)

lemma lres_Id: "Id \<subseteq> R \<sslash> R"
  unfolding lres_def Id_def by force

lemma det_lres: "deterministic R \<Longrightarrow> (R ; S) \<sslash> S = R ; (S \<sslash> S)"
  by (metis (no_types, lifting) O_assoc deterministic_var2 lres_compl)

lemma det_rres: "deterministic (R\<^sup>\<smile>) \<Longrightarrow> S \<setminus> (S ; R) = (S \<setminus> S) ; R"
  by (simp add: converse_relcomp det_lres rres_lres_conv)

lemma rres_bij: "bijective S \<Longrightarrow> (R \<setminus> T) ; S = R \<setminus> (T ; S)"
  unfolding bijective_def injective_set surjective_set relcomp_unfold cod_def Id_def rres_def by clarsimp blast

lemma lres_bij: "bijective S \<Longrightarrow> (R \<sslash> T\<^sup>\<smile>) ; S = R \<sslash> (T ; S)\<^sup>\<smile>"
  unfolding bijective_def injective_set surjective_set relcomp_unfold cod_def Id_def lres_def converse_unfold by blast

lemma dom_rres_top: "(dom P \<subseteq> R \<setminus> (dom Q ; top)) = (dom P ; top \<subseteq> R \<setminus> (dom Q ; top))"
  unfolding dom_def top_def rres_def relcomp_unfold Id_def converse_unfold by clarsimp blast

lemma dom_rres_top_var: "(dom P \<subseteq> R \<setminus> (dom Q ; top)) = (P ; top \<subseteq> R \<setminus> (Q ; top))"
  by (metis dom_rres_top dom_top)

lemma fdia_rres_top: "( |R\<rangle>P \<subseteq> dom Q) = (dom P \<subseteq> R \<setminus> (dom Q ; top))"
  by (metis dom_alt_def dom_gla_top rel_fdia_def rres_galois)

lemma fdia_rres_top_var: "( |R\<rangle> P \<subseteq> dom Q) = (dom P \<subseteq> R \<setminus> (Q ; top))"
  by (metis dom_top fdia_rres_top)

lemma dom_galois_var2: "( |R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q) = (Id \<inter> P \<subseteq> R \<setminus> ((Id \<inter> Q) ; top))"
  by (metis dom_subid fdia_rres_top_var inf_sup_aci(4))

lemma rres_top: "R \<setminus> (dom Q ; top) ; top = R \<setminus> (dom Q ; top)"
  unfolding rres_def top_def dom_def relcomp_unfold by clarsimp

lemma ddd_var: "( |R\<rangle> P \<subseteq> dom Q) = (dom P \<subseteq> dom ((R \<setminus> (dom Q ; top)) ; top))"
  unfolding rel_fdia_def dom_def rres_def top_def relcomp_unfold Id_def by force

lemma wlp_prop: "dom ((R \<setminus> (dom Q ; top)) ; top) = neg (cod (neg (dom Q); R))"
  unfolding rres_def Id_def cod_def dom_def top_def relcomp_unfold by fastforce

lemma wlp_prop_var: "dom ((R \<setminus> (dom Q ; top))) = neg (cod ((neg (dom Q)); R))"
  by (metis rres_top wlp_prop)

lemma dom_demod: "( |R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q) = (R ; (Id \<inter> P) \<subseteq> (Id \<inter> Q) ; R)"
proof
  assume "|R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q"
  hence "R ; (Id \<inter> P) \<subseteq> (Id \<inter> Q) ; R ; (Id \<inter> P)"
    by (metis O_assoc dom_gla dom_subid inf.absorb_iff2 inf_le1 rel_fdia_def)
  thus "R ; (Id \<inter> P) \<subseteq> (Id \<inter> Q) ; R"
    by auto
next
  assume "R ; (Id \<inter> P) \<subseteq> (Id \<inter> Q) ; R"
  hence "|R\<rangle> (Id \<inter> P) \<subseteq> dom ((Id \<inter> Q) ; R)"
    by (metis (no_types, lifting) dom_subid dom_top fdia_demod_top inf.absorb_iff2 inf_le1 relcomp_distrib2 sup.order_iff)
  hence "|R\<rangle> (Id \<inter> P) \<subseteq> (Id \<inter> Q) \<inter> dom R"
    unfolding dom_def Id_def by blast
  thus "|R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q"
    by blast
qed

lemma fdia_bbox_galois_var: "( |R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q) = (Id \<inter> P \<subseteq> Id \<inter> - cod ((Id \<inter> -Q); R))"
  unfolding rel_fdia_def dom_def cod_def Id_def by blast

lemma dom_demod_var2: "( |R\<rangle> (Id \<inter> P) \<subseteq> Id \<inter> Q) = (Id \<inter> P \<subseteq> R \<setminus> ((Id \<inter> Q) ; R))"
  by (meson dom_demod rres_galois)


subsection \<open>Symmetric quotient\<close>

definition syq :: "('c,'a) rel \<Rightarrow> ('c,'b) rel \<Rightarrow> ('a,'b) rel" (infixl "\<div>" 75)
  where "R \<div> S = (R \<setminus> S) \<inter> (R\<^sup>\<smile> \<sslash> S\<^sup>\<smile>)"

lemma syq_set: "R \<div> S = {(a,b). \<forall>c. (c,a) \<in> R \<longleftrightarrow> (c,b) \<in> S}"
  unfolding syq_def relcomp_unfold lres_def rres_def by force

lemma converse_syq [simp]: "(R \<div> S)\<^sup>\<smile> = S \<div> R"
  unfolding syq_def converse_def rres_def lres_def by blast

lemma syq_compl: "R \<div> S = - (R\<^sup>\<smile> ; -S) \<inter> - (-(R\<^sup>\<smile>) ; S)"
  by (simp add: lres_compl rres_compl syq_def)

lemma syq_compl2 [simp]: "-R \<div> -S = R \<div> S"
  unfolding syq_compl by blast

lemma syq_expand1: "R ; (R \<div> S) = S \<inter> (top ; (R \<div> S))"
  unfolding syq_set top_def relcomp_unfold by force

lemma syq_expand2: "(R \<div> S) ; S\<^sup>\<smile> = R\<^sup>\<smile> \<inter> ((R \<div> S) ; top)"
  unfolding syq_set top_def relcomp_unfold by force

lemma syq_comp1: "(R \<div> S) ; (S \<div> T) = (R \<div> T) \<inter> (top ; (S \<div> T))"
  unfolding syq_set top_def relcomp_unfold by fastforce

lemma syq_comp2: "(R \<div> S) ; (S \<div> T) = (R \<div> T) \<inter> ((R \<div> S) ; top)"
  unfolding syq_set top_def relcomp_unfold by fastforce

lemma syq_bij: "bijective T \<Longrightarrow> (R \<div> S) ; T = R \<div> (S ; T)"
  by (simp add: bijective_def inj_meet_distr lres_bij rres_bij syq_def)

end
