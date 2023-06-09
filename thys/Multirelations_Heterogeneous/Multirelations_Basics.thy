section \<open>Basic Properties of Multirelations\<close>

theory Multirelations_Basics

imports Power_Allegories_Properties

begin

text \<open>This theory extends a previous AFP entry for multirelations with one single objects to
proper multirelations in Rel.\<close>

subsection \<open>Peleg composition, parallel composition (inner union) and units\<close>

type_synonym ('a,'b) mrel = "('a,'b set) rel"

definition s_prod :: "('a,'b) mrel \<Rightarrow> ('b,'c) mrel \<Rightarrow> ('a,'c) mrel" (infixl "\<cdot>" 75) where
  "R \<cdot> S = {(a,A). (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>(f ` B)))}"

definition s_id :: "('a,'a) mrel" ("1\<^sub>\<sigma>") where
  "1\<^sub>\<sigma> = (\<Union>a. {(a,{a})})"

definition p_prod :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel \<Rightarrow> ('a,'b) mrel" (infixl "\<parallel>" 70) where
  "R \<parallel> S = {(a,A). (\<exists>B C. A = B \<union> C \<and> (a,B) \<in> R \<and> (a,C) \<in> S)}"

definition p_id :: "('a,'b) mrel" ("1\<^sub>\<pi>") where
  "1\<^sub>\<pi> = (\<Union>a. {(a,{})})"

definition U :: "('a,'b) mrel" where
  "U = {(a,A) |a A. True}"

abbreviation "NC \<equiv> U - 1\<^sub>\<pi>"

named_theorems mr_simp
declare s_prod_def [mr_simp] p_prod_def [mr_simp] s_id_def [mr_simp] p_id_def [mr_simp] U_def [mr_simp]

lemma s_prod_idl [simp]: "1\<^sub>\<sigma> \<cdot> R = R"
  by (auto simp: mr_simp)

lemma s_prod_idr [simp]: "R \<cdot> 1\<^sub>\<sigma> = R"
  by (auto simp: mr_simp) (metis UN_singleton)

lemma p_prod_ild [simp]: "1\<^sub>\<pi> \<parallel> R = R"
  by (simp add: mr_simp)

lemma c_prod_idr [simp]: "R \<parallel> 1\<^sub>\<pi> = R"
  by (simp add: mr_simp)

lemma cl7 [simp]: "1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  by (auto simp: mr_simp)

lemma p_prod_assoc: "R \<parallel> S \<parallel> T = R \<parallel> (S \<parallel> T)"
  apply (rule set_eqI, clarsimp simp: mr_simp)
  by (metis (no_types, lifting) sup_assoc)

lemma p_prod_comm: "R \<parallel> S = S \<parallel> R"
  by (auto simp: mr_simp)

lemma subidem_par: "R \<subseteq> R \<parallel> R"
  by (auto simp: mr_simp)

lemma meet_le_par: "R \<inter> S \<subseteq> R \<parallel> S"
  by (auto simp: mr_simp)

lemma s_prod_distr: "(R \<union> S) \<cdot> T = R \<cdot> T \<union> S \<cdot> T"
  by (auto simp: mr_simp)

lemma s_prod_sup_distr: "(\<Union>X) \<cdot> S = (\<Union>R \<in> X. R \<cdot> S)"
  by (auto simp: mr_simp)

lemma s_prod_subdistl: "R \<cdot> S \<union> R \<cdot> T \<subseteq> R \<cdot> (S \<union> T)"
  by (auto simp: mr_simp)

lemma s_prod_sup_subdistl: "X \<noteq> {} \<Longrightarrow> (\<Union>S \<in> X. R \<cdot> S) \<subseteq> R \<cdot> \<Union>X"
  by (simp add: mr_simp) blast

lemma s_prod_isol: "R \<subseteq> S \<Longrightarrow> R \<cdot> T \<subseteq> S \<cdot> T"
  by (metis s_prod_distr sup.order_iff)

lemma s_prod_isor: "R \<subseteq> S \<Longrightarrow> T \<cdot> R \<subseteq> T \<cdot> S"
  by (metis le_supE s_prod_subdistl sup.absorb_iff1)

lemma s_prod_zerol [simp]: "{} \<cdot> R = {}"
  by (force simp: mr_simp)

lemma s_prod_wzeror: "R \<cdot> {} \<subseteq> R"
  by (force simp: mr_simp)

lemma p_prod_zeror [simp]: "R \<parallel> {} = {}"
  by (simp add: mr_simp)

lemma s_prod_p_idl [simp]: "1\<^sub>\<pi> \<cdot> R = 1\<^sub>\<pi>"
  by (force simp: mr_simp)

lemma p_id_st: "R \<cdot> 1\<^sub>\<pi> = {(a,{}) |a. \<exists>B. (a,B) \<in> R}"
  by (force simp: mr_simp)

lemma c6: "R \<cdot> 1\<^sub>\<pi> \<subseteq> 1\<^sub>\<pi>"
  by (clarsimp simp: mr_simp)

lemma p_prod_distl: "R \<parallel> (S \<union> T) = R \<parallel> S \<union> R \<parallel> T"
  by (fastforce simp: mr_simp)

lemma p_prod_sup_distl: "R \<parallel> (\<Union>X) = (\<Union>S \<in> X. R \<parallel> S)"
  by (fastforce simp: mr_simp)

lemma p_prod_isol: "R \<subseteq> S \<Longrightarrow> R \<parallel> T \<subseteq> S \<parallel> T"
  by (metis p_prod_comm p_prod_distl sup.orderE sup.orderI)

lemma p_prod_isor: "R \<subseteq> S \<Longrightarrow> T \<parallel> R \<subseteq> T \<parallel> S"
  by (simp add: p_prod_comm p_prod_isol)

lemma s_prod_assoc1: "(R \<cdot> S) \<cdot> T \<subseteq> R \<cdot> (S \<cdot> T)"
  by (clarsimp simp: mr_simp) metis

lemma seq_conc_subdistr: "(R \<parallel> S) \<cdot> T \<subseteq> R \<cdot> T \<parallel> S \<cdot> T"
  by (clarsimp simp: mr_simp UnI1 UnI2) blast

lemma U_U [simp]: "U \<cdot> U = U"
  by (simp add: mr_simp) blast

lemma U_par_idem [simp]: "U \<parallel> U = U"
  by (simp add: U_def equalityI subidem_par)

lemma p_id_NC: "R - 1\<^sub>\<pi> = R \<inter> NC"
  by (simp add: Diff_eq U_def)

lemma NC_NC [simp]: "NC \<cdot> NC = NC"
  by (rule set_eqI, clarsimp simp: mr_simp, metis SUP_bot_conv(2) UN_constant insert_not_empty)

lemma nc_par_idem [simp]: "NC \<parallel> NC = NC"
  by (force simp: mr_simp)

lemma cl4:
  assumes "T \<parallel> T \<subseteq> T"
  shows "R \<cdot> T \<parallel> S \<cdot> T \<subseteq> (R \<parallel> S) \<cdot> T"
proof clarify
  fix a A
  assume "(a,A) \<in> R \<cdot> T \<parallel> S \<cdot> T"
  hence "\<exists>B C. A = B \<union> C \<and> (\<exists>D. (a,D) \<in> R \<and> (\<exists>f. (\<forall>d \<in> D. (d,f d) \<in> T) \<and> B = \<Union> ((\<lambda>x. f x) ` D))) \<and> (\<exists>E. (a,E) \<in> S \<and> (\<exists>g. (\<forall>e \<in> E. (e,g e) \<in> T) \<and> C = \<Union> ((\<lambda>x. g x)` E)))"
    by (simp add: mr_simp)
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D. (d,f d) \<in> T) \<and> (\<forall>e \<in> E. (e,g e) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` D)) \<union> (\<Union> ((\<lambda>x. g x)` E)))"
    by (auto simp: mr_simp)
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D-E. (d,f d) \<in> T) \<and> (\<forall>e \<in> E-D. (e,g e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x,f x) \<in> T \<and> (x,g x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. g x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. f y \<union> g y) ` (D \<inter> E)))))"
    by auto blast
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D-E. (d,f d) \<in> T) \<and> (\<forall>e \<in> E-D. (e,g e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x,f x \<union> g x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. g x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. f y \<union> g y) ` (D \<inter> E)))))"
    apply clarify
    subgoal for D E f g
      apply (rule exI[of _ D])
      apply (rule exI[of _ E])
      apply clarify
      apply (rule exI[of _ f])
      apply (rule exI[of _ g])
      using assms by (auto simp: p_prod_def, blast)
    done
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>h. (\<forall>d \<in> D-E. (d,h d) \<in> T) \<and> (\<forall>e \<in> E-D. (e, h e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x, h x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. h x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. h x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. h y) ` (D \<inter> E)))))"
    apply clarify
    subgoal for D E f g 
      apply (rule exI[of _ D])
      apply (rule exI[of _ E])
      apply clarify
      apply (rule exI[of _ "\<lambda>x. if x \<in> (D - E) then f x else (if x \<in> D \<inter> E then (f x \<union> g x) else g x)"])
      by auto
    done
  hence "(\<exists>B. (a,B) \<in> R \<parallel> S \<and> (\<exists>h. (\<forall>b\<in>B. (b,h b) \<in> T) \<and> A = \<Union>((\<lambda>x. h x) ` B)))"
    by clarsimp blast
  thus "(a,A) \<in> (R \<parallel> S) \<cdot> T"
    by (simp add: mr_simp)
qed

lemma cl3: "R \<cdot> (S \<parallel> T) \<subseteq> R \<cdot> S \<parallel> R \<cdot> T"
proof clarify
  fix a A
  assume "(a,A) \<in> R \<cdot> (S \<parallel> T)"
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. \<exists>C D. f b = C \<union> D \<and> (b,C) \<in> S \<and> (b,D) \<in> T) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
    by (clarsimp simp: mr_simp)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f g h. (\<forall>b \<in> B. f b = g b \<union> h b \<and> (b,g b) \<in> S \<and> (b,h b) \<in> T) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
    by (clarsimp simp: bchoice, metis)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>g h. (\<forall>b \<in> B. (b,g b) \<in> S \<and> (b,h b) \<in> T) \<and> A = (\<Union> ((\<lambda>x. g x) ` B)) \<union> (\<Union> ((\<lambda>x. h x) ` B)))"
    by blast
  hence "\<exists>C D. (\<exists>B. (a,B) \<in> R \<and> (\<exists>g. (\<forall>b \<in> B. (b,g b) \<in> S) \<and> C = \<Union> ((\<lambda>x. g x) ` B))) \<and> (\<exists>B. (a,B) \<in> R \<and> (\<exists>h. (\<forall>b \<in> B. (b,h b) \<in> T) \<and> D = \<Union> ((\<lambda>x. h x)` B))) \<and> A = C \<union> D"
    by blast
  thus "(a,A) \<in> R \<cdot> S \<parallel> R \<cdot> T"
    by (auto simp: mr_simp)
qed

lemma p_id_assoc1: "(1\<^sub>\<pi> \<cdot> R) \<cdot> S = 1\<^sub>\<pi> \<cdot> (R \<cdot> S)"
  by simp

lemma p_id_assoc2: "(R \<cdot> 1\<^sub>\<pi>) \<cdot> T = R \<cdot> (1\<^sub>\<pi> \<cdot> T)"
  by (rule set_eqI, clarsimp simp: mr_simp) fastforce

lemma cl1 [simp]: "R \<cdot> 1\<^sub>\<pi> \<union> R \<cdot> NC = R \<cdot> U"
  by (rule set_eqI, clarsimp simp: mr_simp, metis UN_constant UN_empty)

lemma tarski_aux:
  assumes "R - 1\<^sub>\<pi> \<noteq> {}"
  and "(a,A) \<in> NC"
  shows "(a,A) \<in> NC \<cdot> ((R - 1\<^sub>\<pi>) \<cdot> NC)"
  using assms apply (clarsimp simp: mr_simp)
  by (metis UN_constant insert_not_empty singletonD)

lemma tarski:
  assumes "R - 1\<^sub>\<pi> \<noteq> {}"
  shows "NC \<cdot> ((R - 1\<^sub>\<pi>) \<cdot> NC) = NC"
  by standard (simp add: U_def p_id_def s_prod_def, force, metis assms tarski_aux subrelI)

lemma tarski_var:
  assumes "R \<inter> NC \<noteq> {}"
  shows "NC \<cdot> ((R \<inter> NC) \<cdot> NC) = NC"
  by (metis assms p_id_NC tarski)

lemma s_le_nc: "1\<^sub>\<sigma> \<subseteq> NC"
  by (auto simp: mr_simp)

lemma U_nc [simp]: "U \<cdot> NC = U"
  by (metis NC_NC cl1 s_prod_distr s_prod_idl s_prod_p_idl)

lemma x_y_split [simp]: "(R \<inter> NC) \<cdot> S \<union> R \<cdot> {} = R \<cdot> S"
  by (auto simp: mr_simp)

lemma c_nc_comp1 [simp]: "1\<^sub>\<pi> \<union> NC = U"
  using cl1 s_prod_idl by blast

subsection \<open>Tests\<close>

lemma s_id_st: "R \<inter> 1\<^sub>\<sigma> = {(a,{a}) |a. (a,{a}) \<in> R}"
  by (force simp: mr_simp)

lemma subid_aux2:
  assumes "(a,A) \<in> R \<inter> 1\<^sub>\<sigma>"
  shows "A = {a}"
  using assms by (auto simp: mr_simp)

lemma s_prod_test_aux1:
  assumes "(a,A) \<in> R \<cdot> (P \<inter> 1\<^sub>\<sigma>)"
  shows "((a,A) \<in> R \<and> (\<forall>a \<in> A. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>)))"
  using assms by (auto simp: mr_simp)

lemma s_prod_test_aux2:
  assumes "(a,A) \<in> R"
  and "\<forall>a \<in> A. (a,{a}) \<in> S"
  shows "(a,A) \<in> R \<cdot> S"
  using assms by (fastforce simp: mr_simp)

lemma s_prod_test: "(a,A) \<in> R \<cdot> (P \<inter> 1\<^sub>\<sigma>) \<longleftrightarrow> (a,A) \<in> R \<and> (\<forall>a \<in> A. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>))"
  by (meson s_prod_test_aux1 s_prod_test_aux2)

lemma s_prod_test_var: "R \<cdot> (P \<inter> 1\<^sub>\<sigma>) = {(a,A). (a,A) \<in> R \<and> (\<forall>a \<in> A. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>))}"
  apply (rule antisym)
  by (fastforce simp: mr_simp)+

lemma test_s_prod_aux1:
  assumes "(a,A) \<in> (P \<inter> 1\<^sub>\<sigma>) \<cdot> R"
  shows "(a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>) \<and> (a,A) \<in> R"
  using assms by (auto simp: mr_simp)

lemma test_s_prod_aux2:
  assumes "(a,A) \<in> R"
  and "(a,{a}) \<in> P"
  shows "(a,A) \<in> P \<cdot> R"
  using assms s_prod_def by fastforce

lemma test_s_prod: "(a,A) \<in> (P \<inter> 1\<^sub>\<sigma>) \<cdot> R \<longleftrightarrow> (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>) \<and> (a,A) \<in> R"
  by (meson test_s_prod_aux1 test_s_prod_aux2)

lemma test_s_prod_var: "(P \<inter> 1\<^sub>\<sigma>) \<cdot> R = {(a,A). (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>) \<and> (a,A) \<in> R}"
  by (simp add: set_eq_iff test_s_prod)

lemma test_assoc1: "(R \<cdot> (P \<inter> 1\<^sub>\<sigma>)) \<cdot> S = R \<cdot> ((P \<inter> 1\<^sub>\<sigma>) \<cdot> S)"
  apply (rule antisym)
  apply (simp add: s_prod_assoc1)
  apply (clarsimp simp: mr_simp)
  by (metis UN_singleton)

lemma test_assoc2: "((P \<inter> 1\<^sub>\<sigma>) \<cdot> R) \<cdot> S = (P \<inter> 1\<^sub>\<sigma>) \<cdot> (R \<cdot> S)"
  apply (rule antisym)
  apply (simp add: s_prod_assoc1)
  by (fastforce simp: mr_simp s_prod_assoc1)

lemma test_assoc3: "(R \<cdot> S) \<cdot> (P \<inter> 1\<^sub>\<sigma>) = R \<cdot> (S \<cdot> (P \<inter> 1\<^sub>\<sigma>))"
proof (rule antisym)
  show "(R \<cdot> S) \<cdot> (P \<inter> 1\<^sub>\<sigma>) \<subseteq> R \<cdot> (S \<cdot> (P \<inter> 1\<^sub>\<sigma>))"
    by (simp add: s_prod_assoc1)
  show "R \<cdot> (S \<cdot> (P \<inter> 1\<^sub>\<sigma>)) \<subseteq> (R \<cdot> S) \<cdot> (P \<inter> 1\<^sub>\<sigma>)"
    proof clarify
    fix a A
    assume hyp1: "(a, A) \<in> R \<cdot> (S \<cdot> (P \<inter> 1\<^sub>\<sigma>))"
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S \<cdot> (P \<inter> 1\<^sub>\<sigma>)) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (simp add: s_prod_test s_prod_def)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S \<and> (\<forall>a\<in>f b. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>))) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (simp add: s_prod_test)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S) \<and> (\<forall>a\<in>\<Union>((\<lambda>x. f x) ` B). (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>)) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by auto
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S) \<and> (\<forall>a\<in>A. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>)) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by auto blast
    hence "(a,A) \<in> R \<cdot> S \<and> (\<forall>a\<in>A. (a,{a}) \<in> (P \<inter> 1\<^sub>\<sigma>))"
      by (auto simp: mr_simp)
    thus "(a,A) \<in> (R \<cdot> S) \<cdot> (P \<inter> 1\<^sub>\<sigma>)"
      by (simp add: s_prod_test)
  qed
qed

lemma s_distl_test: "(P \<inter> 1\<^sub>\<sigma>) \<cdot> (S \<union> T) = (P \<inter> 1\<^sub>\<sigma>) \<cdot> S \<union> (P \<inter> 1\<^sub>\<sigma>) \<cdot> T"
  by (fastforce simp: mr_simp)

lemma s_distl_sup_test: "(P \<inter> 1\<^sub>\<sigma>) \<cdot> \<Union>X = (\<Union>S \<in> X. (P \<inter> 1\<^sub>\<sigma>) \<cdot> S)"
  by (auto simp: mr_simp)

lemma subid_par_idem [simp]: "(P \<inter> 1\<^sub>\<sigma>) \<parallel> (P \<inter> 1\<^sub>\<sigma>) = (P \<inter> 1\<^sub>\<sigma>)"
  by (auto simp: mr_simp)

lemma seq_conc_subdistrl: "(P \<inter> 1\<^sub>\<sigma>) \<cdot> (S \<parallel> T) = ((P \<inter> 1\<^sub>\<sigma>) \<cdot> S) \<parallel> ((P \<inter> 1\<^sub>\<sigma>) \<cdot> T)"
  apply (rule antisym)
  apply (simp add: cl3)
  by (fastforce simp: mr_simp)

lemma test_s_prod_is_meet [simp]: "(P \<inter> 1\<^sub>\<sigma>) \<cdot> (Q \<inter> 1\<^sub>\<sigma>) = P \<inter> Q \<inter> 1\<^sub>\<sigma>"
  by (auto simp: mr_simp)

lemma test_p_prod_is_meet [simp]: "(P \<inter> 1\<^sub>\<sigma>) \<parallel> (Q \<inter> 1\<^sub>\<sigma>) = (P \<inter> 1\<^sub>\<sigma>) \<inter> (Q \<inter> 1\<^sub>\<sigma>)"
  by (auto simp: mr_simp)

lemma test_multipliciativer: "(P \<inter> Q \<inter> 1\<^sub>\<sigma>) \<cdot> T = ((P \<inter> 1\<^sub>\<sigma>) \<cdot> T) \<inter> ((Q \<inter> 1\<^sub>\<sigma>) \<cdot> T)"
  by (auto simp: mr_simp)

lemma cl9 [simp]: "(R \<inter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = R \<inter> 1\<^sub>\<sigma>"
  by (auto simp: mr_simp)

lemma s_subid_closed [simp]: "R \<inter> NC \<inter> 1\<^sub>\<sigma> = R \<inter> 1\<^sub>\<sigma>"
  using s_le_nc by auto

lemma sub_id_le_nc: "R \<inter> 1\<^sub>\<sigma> \<subseteq> NC"
  by (simp add: le_infI2 s_le_nc)

lemma x_y_prop: "1\<^sub>\<sigma> \<inter> ((R \<inter> NC) \<cdot> S) = 1\<^sub>\<sigma> \<inter> R \<cdot> S"
  by (auto simp: mr_simp)

lemma s_nc_U: "1\<^sub>\<sigma> \<inter> R \<cdot> NC = 1\<^sub>\<sigma> \<inter> R \<cdot> U"
  by (rule set_eqI, clarsimp simp: mr_simp, metis SUP_constant UN_empty insert_not_empty)

lemma sid_le_nc_var: "1\<^sub>\<sigma> \<inter> R \<subseteq> 1\<^sub>\<sigma> \<inter> (R \<parallel> NC)"
  using meet_le_par s_le_nc by fastforce

lemma s_nc_par_U: "1\<^sub>\<sigma> \<inter> (R \<parallel> NC) = 1\<^sub>\<sigma> \<inter> (R \<parallel> U)"
  by (metis c_nc_comp1 c_prod_idr inf_sup_distrib1 le_iff_sup p_prod_distl sid_le_nc_var)

lemma s_id_par_s_prod: "(P \<inter> 1\<^sub>\<sigma>) \<parallel> (Q \<inter> 1\<^sub>\<sigma>) = (P \<inter> 1\<^sub>\<sigma>) \<cdot> (Q \<inter> 1\<^sub>\<sigma>)"
  by force

subsection \<open>Parallel subidentities\<close>

lemma p_id_zero_st: "R \<inter> 1\<^sub>\<pi> = {(a,{}) |a. (a,{}) \<in> R}"
  by (auto simp: mr_simp)

lemma p_subid_iff: "R \<subseteq> 1\<^sub>\<pi> \<longleftrightarrow> R \<cdot> 1\<^sub>\<pi> = R"
  by (clarsimp simp: mr_simp, safe, simp_all) blast+

lemma p_subid_iff_var: "R \<subseteq> 1\<^sub>\<pi> \<longleftrightarrow> R \<cdot> {} = R"
  by (clarsimp simp: mr_simp, safe, simp_all) blast+

lemma term_par_idem [simp]: "(R \<inter> 1\<^sub>\<pi>) \<parallel> (R \<inter> 1\<^sub>\<pi>) = (R \<inter> 1\<^sub>\<pi>)"
  by (metis Int_Un_eq(4) c_prod_idr p_prod_distl subidem_par subset_Un_eq)

lemma c1 [simp]: "R \<cdot> 1\<^sub>\<pi> \<parallel> R = R"
  apply (rule set_eqI, clarsimp simp: mr_simp)
  by (metis (no_types, lifting) SUP_bot SUP_bot_conv(2) sup_bot_left)

lemma p_id_zero: "R \<inter> 1\<^sub>\<pi> = R \<cdot> {}"
  by (auto simp: mr_simp)

lemma cl5: "(R \<cdot> S) \<cdot> (T \<cdot> {}) = R \<cdot> (S \<cdot> (T \<cdot> {}))"
proof (rule antisym)
  show "(R \<cdot> S) \<cdot> (T \<cdot> {}) \<subseteq> R \<cdot> (S \<cdot> (T \<cdot> {}))"
    by (metis s_prod_assoc1)
  show " R \<cdot> (S \<cdot> (T \<cdot> {})) \<subseteq> (R \<cdot> S) \<cdot> (T \<cdot> {})"
  proof clarify
    fix a::"'a" and A::"'f set"
    assume "(a,A) \<in> R \<cdot> (S \<cdot> (T \<cdot> {}))"
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<exists>g. (\<forall>x \<in> C. (x,g x) \<in> T \<cdot> {}) \<and> f b = \<Union>((\<lambda>x. g x) ` C)))) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (clarsimp simp: mr_simp)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}) \<and> f b = {})) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (clarsimp simp: mr_simp) fastforce
    hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}))) \<and> A = {}"
      by fastforce
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S \<and> (\<forall>x \<in> f b. (x,{}) \<in> T \<cdot> {}))) \<and> A = {}"
      by (metis (mono_tags))
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> (\<forall>x \<in> \<Union>((\<lambda>x. f x) ` B). (x,{}) \<in> T \<cdot> {})) \<and> A = {}"
      by (metis UN_E)
    hence "\<exists>C B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b, f b) \<in> S) \<and> C = \<Union>((\<lambda>x. f x) ` B) \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {})) \<and> A = {}"
      by metis
    hence "\<exists>C. (a,C) \<in> R \<cdot> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}) \<and> A = {}"
      by (auto simp: mr_simp)
    thus "(a,A) \<in> (R \<cdot> S) \<cdot> (T \<cdot> {})"
      by (clarsimp simp: mr_simp) blast
  qed
qed

lemma c4: "(R \<cdot> S) \<cdot> 1\<^sub>\<pi> = R \<cdot> (S \<cdot> 1\<^sub>\<pi>)"
proof -
  have "(R \<cdot> S) \<cdot> 1\<^sub>\<pi> = {(a,{}) | a. \<exists>B. (a,B) \<in> R \<cdot> S}"
    by (simp add: p_id_st)
  also have "\<dots> = R \<cdot> {(a,{}) | a. \<exists>B. (a,B) \<in> S}"
    apply (clarsimp simp: mr_simp)
    apply safe
    apply blast
    apply clarsimp
    by metis
  also have "\<dots> = R \<cdot> (S \<cdot> 1\<^sub>\<pi>)"
    by (simp add: p_id_st)
  finally show ?thesis.
qed

lemma c3: "(R \<parallel> S) \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> 1\<^sub>\<pi>"
  by (simp add: Orderings.order_eq_iff cl4 seq_conc_subdistr)

lemma p_id_idem [simp]: "(R \<cdot> 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi>"
  by (simp add: c4)

lemma x_c_par_idem [simp]: "R \<cdot> 1\<^sub>\<pi> \<parallel> R \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi>"
  by (metis c1 p_id_idem)

lemma x_zero_le_c: "R \<cdot> {} \<subseteq> 1\<^sub>\<pi>"
  by (simp add: c4 p_subid_iff)

lemma p_subid_lb1: "R \<cdot> {} \<parallel> S \<cdot> {} \<subseteq> R \<cdot> {}"
  by (metis c_prod_idr p_prod_isor x_zero_le_c)

lemma p_subid_lb2: "R \<cdot> {} \<parallel> S \<cdot> {} \<subseteq> S \<cdot> {}"
  using p_prod_comm p_subid_lb1 by blast

lemma p_subid_idem [simp]: "R \<cdot> {} \<parallel> R \<cdot> {} = R \<cdot> {}"
  by (simp add: p_subid_lb1 subidem_par subset_antisym)

lemma p_subid_glb: "T \<cdot> {} \<subseteq> R \<cdot> {} \<Longrightarrow> T \<cdot> {} \<subseteq> S \<cdot> {} \<Longrightarrow> T \<cdot> {} \<subseteq> (R \<cdot> {}) \<parallel> (S \<cdot> {})"
  by (auto simp: mr_simp)

lemma p_subid_glb_iff: "T \<cdot> {} \<subseteq> R \<cdot> {} \<and> T \<cdot> {} \<subseteq> S \<cdot> {} \<longleftrightarrow> T \<cdot> {} \<subseteq> (R \<cdot> {}) \<parallel> (S \<cdot> {})"
  by (auto simp: mr_simp)

lemma x_c_glb: "(T::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<subseteq> (R::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<Longrightarrow> T \<cdot> 1\<^sub>\<pi> \<subseteq> (S::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<Longrightarrow> T \<cdot> 1\<^sub>\<pi> \<subseteq> (R \<cdot> 1\<^sub>\<pi>) \<parallel> (S \<cdot> 1\<^sub>\<pi>)"
  by (smt (verit, best) order_subst1 p_id_idem p_prod_isol p_prod_isor s_prod_isol x_c_par_idem)

lemma x_c_lb1: "R \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> 1\<^sub>\<pi> \<subseteq> R \<cdot> 1\<^sub>\<pi>"
  by (metis c6 c_prod_idr p_prod_isor)

lemma x_c_lb2: "R \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> 1\<^sub>\<pi> \<subseteq> S \<cdot> 1\<^sub>\<pi>"
  using p_prod_comm x_c_lb1 by blast

lemma x_c_glb_iff: "(T::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<subseteq> (R::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<and> T \<cdot> 1\<^sub>\<pi> \<subseteq> (S::('a,'b) mrel) \<cdot> 1\<^sub>\<pi> \<longleftrightarrow> T \<cdot> 1\<^sub>\<pi> \<subseteq> (R \<cdot> 1\<^sub>\<pi>) \<parallel> (S \<cdot> 1\<^sub>\<pi>)"
  by (meson subset_trans x_c_glb x_c_lb1 x_c_lb2)

lemma nc_iff1: "R \<subseteq> NC \<longleftrightarrow> R \<inter> 1\<^sub>\<pi> = {}"
  by (metis (no_types, lifting) Diff_Diff_Int Int_Diff Int_absorb diff_shunt_var p_id_NC)

lemma nc_iff2: "R \<subseteq> NC \<longleftrightarrow> R \<cdot> {} = {}"
  by (metis c4 nc_iff1 p_id_zero s_prod_zerol)

lemma zero_assoc3: "(R \<cdot> S) \<cdot> {} = R \<cdot> (S \<cdot> {})"
  by (metis cl5 s_prod_zerol)

lemma x_zero_interr: "R \<cdot> {} \<parallel> S \<cdot> {} = (R \<parallel> S) \<cdot> {}"
  by (clarsimp simp: mr_simp) blast

lemma p_subid_interr: "R \<cdot> T \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> T \<cdot> 1\<^sub>\<pi> = (R \<parallel> S) \<cdot> T \<cdot> 1\<^sub>\<pi>"
proof -
  have "R \<cdot> T \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> T \<cdot> 1\<^sub>\<pi> = (R \<cdot> {(a,{}) |a. \<exists>B. (a,B) \<in> T}) \<parallel> (S \<cdot> {(a,{}) |a. \<exists>B. (a,B) \<in> T})"
    by (metis c4 p_id_st)
  also have "\<dots> = (R \<parallel> S) \<cdot> {(a,{}) |a. \<exists>B. (a,B) \<in> T}"
    apply (rule antisym)
    apply (metis cl4 dual_order.refl p_id_st x_c_par_idem)
    by (simp add: seq_conc_subdistr)
  also have "\<dots> = (R \<parallel> S) \<cdot> T \<cdot> 1\<^sub>\<pi>"
    by (metis c4 p_id_st)
  finally show ?thesis.
qed

lemma cl2 [simp]: "1\<^sub>\<pi> \<inter> (R \<union> NC) = R \<cdot> {}"
  by (metis Diff_disjoint Int_Un_distrib inf_commute p_id_zero sup_bot.right_neutral)

lemma cl6 [simp]: "R \<cdot> {} \<cdot> S = R \<cdot> {}"
  by (metis c4 p_id_assoc2 s_prod_p_idl s_prod_zerol)

lemma cl11 [simp]: "(R \<inter> NC) \<cdot> 1\<^sub>\<pi> \<parallel> NC = (R \<inter> NC) \<cdot> NC"
  apply (rule antisym)
  apply (clarsimp simp: mr_simp)
  apply (metis UN_constant)
  apply (clarsimp simp: mr_simp)
  by (metis UN_empty2 UN_insert Un_empty_left equals0I insert_absorb sup_bot_right)

lemma x_split [simp]: "(R \<inter> NC) \<union> (R \<inter> 1\<^sub>\<pi>) = R"
  by (metis Un_Diff_Int p_id_NC)

lemma x_split_var [simp]: "(R \<inter> NC) \<union> R \<cdot> {} = R"
  by (metis p_id_zero x_split)

lemma s_x_c [simp]: "1\<^sub>\<sigma> \<inter> R \<cdot> 1\<^sub>\<pi> = {}"
  using c6 s_le_nc by fastforce

lemma s_x_zero [simp]: "1\<^sub>\<sigma> \<inter> R \<cdot> {} = {}"
  using cl6 s_x_c by blast

lemma c_nc [simp]: "R \<cdot> 1\<^sub>\<pi> \<inter> NC = {}"
  using c6 by blast

lemma zero_nc [simp]: "R \<cdot> {} \<inter> NC = {}"
  using x_zero_le_c by fastforce

lemma nc_zero [simp]: "(R \<inter> NC) \<cdot> {} = {}"
  using nc_iff2 by auto

lemma c_def [simp]: "U \<cdot> {} = 1\<^sub>\<pi>"
  by (metis c_nc_comp1 cl2 cl6 inf_commute p_id_zero s_prod_p_idl)

lemma U_c [simp]: "U \<cdot> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  by (metis U_U c_def zero_assoc3)

lemma nc_c [simp]: "NC \<cdot> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  by (auto simp: mr_simp)

lemma nc_U [simp]: "NC \<cdot> U = U"
  using NC_NC c_nc_comp1 cl1 nc_c by blast

lemma x_c_nc_split [simp]: "((R \<inter> NC) \<cdot> NC) \<union> (R \<cdot> {} \<parallel> NC) = (R \<cdot> 1\<^sub>\<pi>) \<parallel> NC"
  by (metis cl11 p_prod_comm p_prod_distl x_y_split)

lemma x_c_U_split [simp]: "R \<cdot> U \<union> (R \<cdot> {} \<parallel> U) = R \<cdot> 1\<^sub>\<pi> \<parallel> U"
  apply (rule set_eqI, clarsimp simp: mr_simp)
  by (metis SUP_constant UN_extend_simps(2))

lemma p_subid_par_eq_meet [simp]: "R \<cdot> {} \<parallel> S \<cdot> {} = R \<cdot> {} \<inter> S \<cdot> {}"
  by (auto simp: mr_simp)

lemma p_subid_par_eq_meet_var [simp]: "R \<cdot> 1\<^sub>\<pi> \<parallel> S \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi> \<inter> S \<cdot> 1\<^sub>\<pi>"
  by (metis c_def p_subid_par_eq_meet zero_assoc3)

lemma x_zero_add_closed: "R \<cdot> {} \<union> S \<cdot> {} = (R \<union> S) \<cdot> {}"
  by (simp add: s_prod_distr)

lemma x_zero_meet_closed: "R \<cdot> {} \<inter> S \<cdot> {} = (R \<inter> S) \<cdot> {}"
  by (force simp: mr_simp)

lemma scomp_univalent_pres: "univalent R \<Longrightarrow> univalent S \<Longrightarrow> univalent (R \<cdot> S)"
  unfolding univalent_set s_prod_def
  apply clarsimp
  by (metis Sup.SUP_cong)

lemma "univalent s_id"
  unfolding univalent_set s_id_def by simp

lemma det_peleg: "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> deterministic (R \<cdot> S)"
  unfolding deterministic_set s_prod_def
  apply clarsimp
  apply safe
  apply metis
  apply (metis UN_I)
  by (metis UN_I)

lemma deterministic_sid: "deterministic 1\<^sub>\<sigma>"
  unfolding deterministic_set s_id_def by simp


subsection \<open>Domain\<close>

definition Dom :: "('a,'b) mrel \<Rightarrow> ('a,'a) mrel" where
  "Dom R = {(a,{a}) |a. \<exists>B. (a,B) \<in> R}"

named_theorems mrd_simp
declare mr_simp [mrd_simp] Dom_def [mrd_simp]

lemma d_def_expl: "Dom R = R \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma>"
  by (force simp: mrd_simp set_eqI)

lemma s_subid_iff2: "(R \<inter> 1\<^sub>\<sigma> = R) = (Dom R = R)"
  by (metis c6 cl9 d_def_expl inf.order_iff p_prod_comm p_prod_ild p_prod_isor)

lemma cl8_var: "Dom R \<cdot> S = R \<cdot> 1\<^sub>\<pi> \<parallel> S"
  apply (rule antisym)
  apply (metis d_def_expl p_id_assoc2 s_prod_idl s_prod_p_idl seq_conc_subdistr)
  by (force simp: mrd_simp)

lemma cl8 [simp]: "R \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> \<cdot> S = R \<cdot> 1\<^sub>\<pi> \<parallel> S"
  by simp

lemma cl10_var: "Dom (R - 1\<^sub>\<pi>) = 1\<^sub>\<sigma> \<inter> ((R - 1\<^sub>\<pi>) \<cdot> NC)"
  apply (rule set_eqI, clarsimp simp: mrd_simp)
  apply safe
  apply (metis SUP_constant insert_not_empty)
  by blast

lemma c10: "(R \<inter> NC) \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma> \<inter> ((R \<inter> NC) \<cdot> NC)"
  by (metis Int_Diff cl10_var d_def_expl)

lemma cl9_var [simp]: "Dom (R \<inter> 1\<^sub>\<sigma>) = R \<inter> 1\<^sub>\<sigma>"
  by (simp add: d_def_expl)

lemma d_s_id [simp]: "Dom R \<inter> 1\<^sub>\<sigma> = Dom R"
  by (metis cl8_var d_def_expl p_prod_comm p_prod_ild s_subid_iff2)

lemma d_s_id_ax: "Dom R \<subseteq> 1\<^sub>\<sigma>"
  by (simp add: le_iff_inf)

lemma d_assoc1: "Dom R \<cdot> (S \<cdot> T) = (Dom R \<cdot> S) \<cdot> T"
  by (metis d_s_id test_assoc2)

lemma d_meet_distr_var: "(Dom R \<inter> Dom S) \<cdot> T = Dom R \<cdot> T \<inter> Dom S \<cdot> T"
  by (metis (no_types, lifting) d_s_id inf_assoc test_multipliciativer)

lemma d_idem [simp]: "Dom (Dom R) = Dom R"
  by (meson d_s_id s_subid_iff2)

lemma cd_2_var: "Dom (R \<cdot> 1\<^sub>\<pi>) \<cdot> S = R \<cdot> 1\<^sub>\<pi> \<parallel> S"
  by (simp add: cl8_var p_id_assoc2)

lemma dc_prop1 [simp]: "Dom R \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi>"
  by (simp add: cl8_var)

lemma dc_prop2 [simp]: "Dom (R \<cdot> 1\<^sub>\<pi>) = Dom R"
  by (simp add: d_def_expl p_id_assoc2)

lemma ds_prop [simp]: "Dom R \<parallel> 1\<^sub>\<sigma> = Dom R"
  by (simp add: p_prod_assoc d_def_expl)

lemma dc [simp]: "Dom 1\<^sub>\<pi> = 1\<^sub>\<sigma>"
  by (simp add: d_def_expl)

lemma cd_iso [simp]: "Dom (R \<cdot> 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi>"
  by simp

lemma dc_iso [simp]: "Dom (Dom R \<cdot> 1\<^sub>\<pi>) = Dom R"
  by simp

lemma d_s_id_inter [simp]: "Dom R \<cdot> Dom S = Dom R \<inter> Dom S"
  by (metis d_s_id inf_assoc test_s_prod_is_meet)

lemma d_conc6: "Dom (R \<parallel> S) = Dom R \<parallel> Dom S"
  by (metis (no_types, lifting) c3 d_def_expl ds_prop p_prod_assoc p_prod_comm)

lemma d_conc_inter [simp]: "Dom R \<parallel> Dom S = Dom R \<inter> Dom S"
  by (metis d_s_id test_p_prod_is_meet)

lemma d_conc_s_prod_ax: "Dom R \<parallel> Dom S = Dom R \<cdot> Dom S"
  by simp

lemma d_rest_ax [simp]: "Dom R \<cdot> R = R"
  by (simp add: cl8_var)

lemma d_loc_ax [simp]: "Dom (R \<cdot> Dom S) = Dom (R \<cdot> S)"
  by (metis c4 dc_prop1 dc_prop2)

lemma assoc_p_subid: "(R \<cdot> S) \<cdot> (T \<cdot> 1\<^sub>\<pi>) = R \<cdot> (S \<cdot> (T \<cdot> 1\<^sub>\<pi>))"
  by (smt (verit, del_insts) c4 cd_iso d_idem d_loc_ax p_id_idem s_subid_iff2 test_assoc3)

lemma d_exp_ax [simp]: "Dom (Dom R \<cdot> S) = Dom R \<cdot> Dom S"
  by (metis d_conc6 d_conc_s_prod_ax d_idem d_loc_ax)

lemma d_comm_ax: "Dom R \<cdot> Dom S = Dom S \<cdot> Dom R"
  by force

lemma d_s_id_prop [simp]: "Dom 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  by (simp add: d_def_expl)

lemma d_s_prod_closed [simp]: "Dom (Dom R \<cdot> Dom S) = Dom R \<cdot> Dom S"
  using d_exp_ax d_loc_ax by blast

lemma d_p_prod_closed [simp]: "Dom (Dom R \<parallel> Dom S) = Dom R \<parallel> Dom S"
  using d_s_prod_closed by auto

lemma d_idem2 [simp]: "Dom R \<cdot> Dom R = Dom R"
  by (metis d_exp_ax d_rest_ax)

lemma d_assoc: "(Dom R \<cdot> Dom S) \<cdot> Dom T = Dom R \<cdot> (Dom S \<cdot> Dom T)"
  using d_assoc1 by blast

lemma iso_1 [simp]: "Dom R \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = Dom R"
  using d_def_expl by force

lemma d_idem_par [simp]: "Dom R \<parallel> Dom R = Dom R"
  by (simp add: d_conc_s_prod_ax)

lemma d_inter_r: "Dom R \<cdot> (S \<parallel> T) = Dom R \<cdot> S \<parallel> Dom R \<cdot> T"
  by (metis d_s_id seq_conc_subdistrl)

lemma d_add_ax: "Dom (R \<union> S) = Dom R \<union> Dom S"
  by (simp add: d_def_expl p_prod_comm p_prod_distl s_prod_distr)

lemma d_sup_add: "Dom (\<Union>X) = (\<Union>R \<in> X. Dom R)"
  by (auto simp: mrd_simp)

lemma d_distl: "Dom R \<cdot> (S \<union> T) = Dom R \<cdot> S \<union> Dom R \<cdot> T"
  by (metis d_s_id s_distl_test)

lemma d_sup_distl: "Dom R \<cdot> \<Union>X = (\<Union>S \<in> X. Dom R \<cdot> S)"
  by (metis d_s_id s_distl_sup_test)

lemma d_zero_ax [simp]: "Dom {} = {}"
  by (simp add: d_def_expl p_prod_comm)

lemma d_absorb1 [simp]: "Dom R \<union> Dom R \<cdot> Dom S = Dom R"
  by simp

lemma d_absorb2 [simp]: "Dom R \<cdot> (Dom R \<union> Dom S) = Dom R"
  by (metis d_absorb1 d_idem2 d_s_id s_distl_test)

lemma d_dist1: "Dom R \<cdot> (Dom S \<union> Dom T) = Dom R \<cdot> Dom S \<union> Dom R \<cdot> Dom T"
  by (simp add: cl8_var p_prod_distl)

lemma d_dist2: "Dom R \<union> (Dom S \<cdot> Dom T) = (Dom R \<union> Dom S) \<cdot> (Dom R \<union> Dom T)"
  by (smt (verit) boolean_algebra.disj_conj_distrib d_add_ax d_s_id_inter dc_prop2)

lemma d_add_prod_closed [simp]: "Dom (Dom R \<union> Dom S) = Dom R \<union> Dom S"
  by (simp add: d_add_ax)

lemma x_zero_prop: "R \<cdot> {} \<parallel> S = Dom (R \<cdot> {}) \<cdot> S"
  by (simp add: cl8_var)

lemma cda_add_ax: "Dom ((R \<union> S) \<cdot> T) = Dom (R \<cdot> T) \<union> Dom (S \<cdot> T)"
  by (simp add: d_add_ax s_prod_distr)

lemma d_x_zero: "Dom (R \<cdot> {}) = R \<cdot> {} \<parallel> 1\<^sub>\<sigma>"
  by (simp add: d_def_expl)

lemma cda_ax2:
  assumes "(R \<parallel> S) \<cdot> Dom T = R \<cdot> Dom T \<parallel> S \<cdot> Dom T"
  shows "Dom ((R \<parallel> S) \<cdot> T) = Dom (R \<cdot> T) \<cdot> Dom (S \<cdot> T)"
  by (metis assms d_conc6 d_conc_s_prod_ax d_loc_ax)

lemma d_lb1: "Dom R \<cdot> Dom S \<subseteq> Dom R"
  using d_absorb1 by blast

lemma d_lb2: "Dom R \<cdot> Dom S \<subseteq> Dom S"
  using d_comm_ax d_lb1 by blast

lemma d_glb: "Dom T \<subseteq> Dom R \<and> Dom T \<subseteq> Dom S \<Longrightarrow> Dom T \<subseteq> Dom R \<cdot> Dom S"
  by simp

lemma d_glb_iff: "Dom T \<subseteq> Dom R \<and> Dom T \<subseteq> Dom S \<longleftrightarrow> Dom T \<subseteq> Dom R \<cdot> Dom S"
  by force

lemma d_interr: "R \<cdot> Dom P \<parallel> S \<cdot> Dom P = (R \<parallel> S) \<cdot> Dom P"
  by (simp add: cl4 seq_conc_subdistr subset_antisym)

lemma cl10_d: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> (R \<inter> NC) \<cdot> NC"
  by (simp add: c10 d_def_expl)

lemma cl11_d [simp]: "Dom (R \<inter> NC) \<cdot> NC = (R \<inter> NC) \<cdot> NC"
  by (simp add: cl8_var)

lemma cl10_d_var1: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> R \<cdot> NC"
  by (simp add: cl10_d x_y_prop)

lemma cl10_d_var2: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> (R \<inter> NC) \<cdot> U"
  by (simp add: cl10_d_var1 s_nc_U x_y_prop)

lemma cl10_d_var3: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> R \<cdot> U"
  by (simp add: cl10_d_var1 s_nc_U)

lemma d_U [simp]: "Dom U = 1\<^sub>\<sigma>"
  by (metis U_c dc dc_prop2)

lemma d_nc [simp]: "Dom NC = 1\<^sub>\<sigma>"
  by (metis dc dc_prop2 nc_c)

lemma alt_d_def_nc_nc: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> (((R \<inter> NC) \<cdot> 1\<^sub>\<pi>) \<parallel> NC)"
  using c10 cl11_d cl8_var d_def_expl by blast

lemma alt_d_def_nc_U: "Dom (R \<inter> NC) = 1\<^sub>\<sigma> \<inter> (((R \<inter> NC) \<cdot> 1\<^sub>\<pi>) \<parallel> U)"
  using alt_d_def_nc_nc s_nc_par_U by blast

lemma d_def_split [simp]: "Dom (R \<inter> NC) \<union> Dom (R \<cdot> {}) = Dom R"
  by (metis d_add_ax d_loc_ax d_zero_ax p_id_zero x_split)

lemma d_def_split_var [simp]: "Dom (R \<inter> NC) \<union> ((R \<cdot> {}) \<parallel> 1\<^sub>\<sigma>) = Dom R"
  using d_def_split d_x_zero by blast

lemma ax7 [simp]: "(1\<^sub>\<sigma> \<inter> R \<cdot> U) \<union> (R \<cdot> {} \<parallel> 1\<^sub>\<sigma>) = Dom R"
  using cl10_d_var3 d_def_split d_x_zero by blast

lemma dom12_d: "Dom R = 1\<^sub>\<sigma> \<inter> (R \<cdot> 1\<^sub>\<pi> \<parallel> NC)"
  by (metis cl10_d_var3 cl8_var d_idem d_s_id inf.orderE s_nc_par_U sub_id_le_nc)

lemma dom12_d_U: "Dom R = 1\<^sub>\<sigma> \<inter> (R \<cdot> 1\<^sub>\<pi> \<parallel> U)"
  by (simp add: dom12_d s_nc_par_U)

lemma dom_def_var: "Dom R = (R \<cdot> U \<inter> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
  by (simp add: d_def_expl p_id_zero zero_assoc3)

lemma ax5_d [simp]: "Dom (R \<inter> NC) \<cdot> U = (R \<inter> NC) \<cdot> U"
  by (metis cl1 cl11_d dc_prop1)

lemma ax5_0 [simp]: "Dom (R \<cdot> {}) \<cdot> U = R \<cdot> {} \<parallel> U"
  using x_zero_prop by auto

lemma x_c_U_split2: "Dom R \<cdot> NC = (R \<inter> NC) \<cdot> NC \<union> (R \<cdot> {} \<parallel> NC)"
  by (simp add: cl8_var)

lemma x_c_U_split3: "Dom R \<cdot> U = (R \<inter> NC) \<cdot> U \<union> (R \<cdot> {} \<parallel> U)"
  by (metis ax5_0 ax5_d d_def_split s_prod_distr)

lemma x_c_U_split_d: "Dom R \<cdot> U = R \<cdot> U \<union> (R \<cdot> {} \<parallel> U)"
  by (simp add: cl8_var)

lemma x_U_prop2: "R \<cdot> NC = Dom (R \<inter> NC) \<cdot> NC \<union> R \<cdot> {}"
  by simp

lemma x_U_prop3: "R \<cdot> U = Dom (R \<inter> NC) \<cdot> U \<union> R \<cdot> {}"
  by (metis ax5_d x_y_split)

lemma d_x_nc [simp]: "Dom (R \<cdot> NC) = Dom R"
  by (metis d_loc_ax d_nc dc dc_prop2)

lemma d_x_U [simp]: "Dom (R \<cdot> U) = Dom R"
  by (metis d_U d_loc_ax dc dc_prop2)

lemma d_llp1: "Dom R \<subseteq> Dom S \<Longrightarrow> R \<subseteq> Dom S \<cdot> R"
  by (metis d_rest_ax s_prod_isol)

lemma d_llp2: "R \<subseteq> Dom S \<cdot> R \<Longrightarrow> Dom R \<subseteq> Dom S"
  by (metis d_assoc1 d_exp_ax d_meet_distr_var d_rest_ax d_s_id_inter inf.absorb_iff2)

lemma demod1: "Dom (R \<cdot> S) \<subseteq> Dom T \<Longrightarrow> R \<cdot> Dom S \<subseteq> Dom T \<cdot> R"
proof -
  assume h: "Dom (R \<cdot> S) \<subseteq> Dom T"
  have "R \<cdot> Dom S = Dom (R \<cdot> Dom S) \<cdot> (R \<cdot> Dom S)"
    using d_rest_ax by blast
  also have "\<dots> \<subseteq> Dom T \<cdot> (R \<cdot> Dom S)"
    by (metis d_loc_ax h s_prod_distr subset_Un_eq)
  also have "\<dots> \<subseteq> Dom T \<cdot> R"
    by (metis d_s_id_ax s_prod_idr s_prod_isor)
  finally show "R \<cdot> Dom S \<subseteq> Dom T \<cdot> R".
qed

lemma demod2: "R \<cdot> Dom S \<subseteq> Dom T \<cdot> R \<Longrightarrow> Dom (R \<cdot> S) \<subseteq> Dom T"
proof -
  assume h: "R \<cdot> Dom S \<subseteq> Dom T \<cdot> R"
  have "Dom (R \<cdot> S) = Dom (R \<cdot> Dom S)"
    by auto
  also have "\<dots> \<subseteq> Dom (Dom T \<cdot> R)"
    by (metis d_add_ax h subset_Un_eq)
  also have "\<dots> = Dom T \<cdot> Dom R"
    by simp
  also have "\<dots> \<subseteq> Dom T"
    by (simp add: d_lb1)
  finally show "Dom (R \<cdot> S) \<subseteq> Dom T".
qed

lemma d_meet_closed [simp]: "Dom (Dom x \<inter> Dom y) = Dom x \<inter> Dom y"
  by (metis d_s_id inf_assoc s_subid_iff2)

lemma d_add_var: "Dom P \<cdot> R \<union> Dom Q \<cdot> R = Dom (P \<union> Q) \<cdot> R"
  by (simp add: d_add_ax s_prod_distr)

lemma d_interr_U: "Dom x \<cdot> U \<parallel> Dom y \<cdot> U = Dom (x \<parallel> y) \<cdot> U"
  by (metis U_nc U_par_idem cl4 d_conc6 seq_conc_subdistr subset_antisym)

lemma d_meet: "Dom x \<cdot> z \<inter> Dom y \<cdot> z = (Dom x \<inter> Dom y) \<cdot> z"
  by (simp add: d_meet_distr_var)

lemma cs_hom_meet: "Dom (x \<cdot> 1\<^sub>\<pi> \<inter> y \<cdot> 1\<^sub>\<pi>) = Dom (x \<cdot> 1\<^sub>\<pi>) \<inter> Dom (y \<cdot> 1\<^sub>\<pi>)"
  by (metis d_conc6 d_conc_inter dc_prop2 p_subid_par_eq_meet_var)

lemma iso3 [simp]: "Dom (Dom x \<cdot> U) = Dom x "
  by simp

lemma iso4 [simp]: "Dom (x \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> U = x \<cdot> 1\<^sub>\<pi> \<parallel> U"
  by (metis cl8_var iso3)

lemma iso3_sharp [simp]: "Dom (Dom (x \<inter> NC) \<cdot> NC) = Dom (x \<inter> NC)"
  by simp

lemma iso4_sharp [simp]: "Dom ((x \<inter> NC) \<cdot> NC) \<cdot> NC = (x \<inter> NC) \<cdot> NC"
  by simp

subsection \<open>Vectors\<close>

lemma vec_iff1:
  assumes "\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R)"
  shows "R \<cdot> 1\<^sub>\<pi> \<parallel> U = R"
  using assms by (auto simp: mr_simp)

lemma vec_iff2:
  assumes "R \<cdot> 1\<^sub>\<pi> \<parallel> U = R"
  shows "(\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R))"
  using assms apply (clarsimp simp: mr_simp)
  by (smt (z3) SUP_bot case_prod_conv mem_Collect_eq sup_bot_left)

lemma vec_iff: "(\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R)) \<longleftrightarrow> R \<cdot> 1\<^sub>\<pi> \<parallel> U = R"
  by (metis vec_iff1 vec_iff2)

lemma U_par_zero [simp]: "{} \<cdot> R \<parallel> U = {}"
  by (simp add: p_prod_comm)

lemma U_par_s_id [simp]: "1\<^sub>\<sigma> \<cdot> 1\<^sub>\<pi> \<parallel> U = U"
  by auto

lemma U_par_p_id [simp]: "1\<^sub>\<pi> \<cdot> 1\<^sub>\<pi> \<parallel> U = U"
  by auto

lemma U_par_nc [simp]: "NC \<cdot> 1\<^sub>\<pi> \<parallel> U = U"
  by auto


subsection \<open>Up-closure and Parikh composition\<close>

definition s_prod_pa :: "('a,'b) mrel \<Rightarrow> ('b,'c) mrel \<Rightarrow> ('a,'c) mrel" (infixl "\<otimes>" 75) where
  "R \<otimes> S = {(a,A). (\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (b,A) \<in> S))}"

lemma U_par_st: "(a,A) \<in> R \<parallel> U \<longleftrightarrow> (\<exists>B. B \<subseteq> A \<and> (a,B) \<in> R)"
  by (auto simp: mr_simp)

lemma p_id_U: "R \<parallel> U = {(a,B). \<exists>A. (a,A) \<in> R \<and> A \<subseteq> B}"
  by (clarsimp simp: mr_simp) blast

lemma ucl_iff: "(\<forall>a A B. (a,A) \<in> R \<and> A \<subseteq> B \<longrightarrow> (a,B) \<in> R) \<longleftrightarrow> R \<parallel> U = R"
  by (clarsimp simp: mr_simp) blast

lemma upclosed_ext: "R \<subseteq> R \<parallel> U"
  by (clarsimp simp: mr_simp) blast

lemma onelem: "R \<cdot> S \<parallel> U \<subseteq> R \<otimes> (S \<parallel> U)"
  by (auto simp: s_prod_def p_prod_def U_def s_prod_pa_def)

lemma twolem: "R \<otimes> (S \<parallel> U) \<subseteq> R \<cdot> S \<parallel> U"
proof clarify
  fix a A
  assume "(a,A) \<in> R \<otimes> (S \<parallel> U)"
  hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (b,A) \<in> S \<parallel> U)"
    by (auto simp: s_prod_pa_def)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. \<exists>C. C \<subseteq> A \<and> (b,C) \<in> S)"
    by (clarsimp simp: mr_simp) blast
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. f b \<subseteq> A \<and> (b,f b) \<in> S))"
    by metis
  hence "\<exists>C. C \<subseteq> A \<and> (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> C = \<Union> ((\<lambda>x. f x) ` B)))"
    by clarsimp blast
  hence "\<exists>C. C \<subseteq> A \<and> (a,C) \<in> R \<cdot> S"
    by (clarsimp simp: mr_simp)
  thus "(a,A) \<in> (R \<cdot> S) \<parallel> U"
    by (clarsimp simp: mr_simp) blast
  qed

lemma pe_pa_sim: "R \<cdot> S \<parallel> U = R \<otimes> (S \<parallel> U)"
  by (metis antisym onelem twolem)

lemma pe_pa_sim_var: "(R \<parallel> U) \<cdot> (S \<parallel> U) \<parallel> U = (R \<parallel> U) \<otimes> (S \<parallel> U)"
  apply (rule order.antisym)
  by (simp add: p_prod_assoc pe_pa_sim)+

lemma pa_assoc1: "((R \<parallel> U) \<otimes> (S \<parallel> U)) \<otimes> (T \<parallel> U) \<subseteq> (R \<parallel> U) \<otimes> ((S \<parallel> U) \<otimes> (T \<parallel> U))"
  by (clarsimp simp: p_prod_def s_prod_pa_def U_def, metis)

lemma up_closed_par_is_meet: "(R \<parallel> U) \<parallel> (S \<parallel> U) = (R \<parallel> U) \<inter> (S \<parallel> U)"
  by (auto simp: mr_simp)

lemma U_nc_par [simp]: "NC \<parallel> U = NC"
  by (metis c_nc_comp1 c_prod_idr nc_par_idem p_prod_distl sup_idem)

lemma uc_par_meet: "(R \<parallel> U) \<inter> (S \<parallel> U) = R \<parallel> U \<parallel> S \<parallel> U"
  using p_prod_assoc up_closed_par_is_meet by blast

lemma uc_unc [simp]: "R \<parallel> U \<parallel> R \<parallel> U = R \<parallel> U"
  using uc_par_meet by auto

lemma uc_interr: "(R \<parallel> S) \<cdot> (T \<parallel> U) = R \<cdot> (T \<parallel> U) \<parallel> S \<cdot> (T \<parallel> U)"
  by (simp add: Orderings.order_eq_iff cl4 seq_conc_subdistr up_closed_par_is_meet)

lemma iso5 [simp]: "(R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi> = R \<cdot> 1\<^sub>\<pi>"
  by (simp add: c3)

lemma iso6 [simp]: "(R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi> \<parallel> U = R \<cdot> 1\<^sub>\<pi> \<parallel> U"
  by simp

lemma sv_hom_par: "(R \<parallel> S) \<cdot> U = R \<cdot> U \<parallel> S \<cdot> U"
  by (metis U_par_idem uc_interr)

lemma vs_hom_meet: "Dom ((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<inter> (S \<cdot> 1\<^sub>\<pi> \<parallel> U)) = Dom (R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<inter> Dom (S \<cdot> 1\<^sub>\<pi> \<parallel> U)"
  by (metis d_conc6 d_conc_inter dc_prop2 iso5 up_closed_par_is_meet)

lemma cv_hom_meet: "(R \<cdot> 1\<^sub>\<pi> \<inter> S \<cdot> 1\<^sub>\<pi>) \<parallel> U = (R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<inter> (S \<cdot> 1\<^sub>\<pi> \<parallel> U)"
  by (metis U_par_idem p_prod_assoc p_prod_comm p_subid_par_eq_meet_var uc_par_meet)

lemma cv_hom_par [simp]: " R \<parallel> U \<parallel> S \<parallel> U = (R \<parallel> S) \<parallel> U"
  by (metis U_par_idem p_prod_assoc p_prod_comm)

lemma vc_hom_meet: "((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<inter> (S \<cdot> 1\<^sub>\<pi> \<parallel> U)) \<cdot> 1\<^sub>\<pi> = ((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi>) \<inter> ((S \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi>)"
  by (metis c4 cl8_var cv_hom_meet iso5 p_subid_par_eq_meet_var)

lemma vc_hom_seq: "((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> (S \<cdot> 1\<^sub>\<pi> \<parallel> U)) \<cdot> 1\<^sub>\<pi> = ((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi>) \<cdot> ((S \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> 1\<^sub>\<pi>)"
proof -
  have "((R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> (S \<cdot> 1\<^sub>\<pi> \<parallel> U)) \<cdot> 1\<^sub>\<pi> = (R \<cdot> 1\<^sub>\<pi> \<parallel> U) \<cdot> (S \<cdot> 1\<^sub>\<pi>)"
    by (metis c4 iso5)
  also have "... = R \<cdot> 1\<^sub>\<pi> \<parallel> U \<cdot> (S \<cdot> 1\<^sub>\<pi>)"
    by (metis cl8_var d_assoc1)
  also have "... = R \<cdot> 1\<^sub>\<pi> \<parallel> (NC \<cdot> (S \<cdot> 1\<^sub>\<pi>) \<union> 1\<^sub>\<pi> \<cdot> (S \<cdot> 1\<^sub>\<pi>))"
    by (metis c_nc_comp1 s_prod_distr sup_commute)
  also have "... = R \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<pi>"
    by (metis Un_absorb1 c4 c6 s_prod_p_idl)
  thus ?thesis
    by (simp add: assoc_p_subid calculation)
qed


subsection \<open>Nonterminal and terminal multirelations\<close>

definition tau :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("\<tau>") where
  "\<tau> R = R \<cdot> {}"

definition nu :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" ("\<nu>") where
  "\<nu> R = R \<inter> NC"

lemma nc_s [simp]: "\<nu> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
  using nu_def s_le_nc by auto

lemma nc_scomp_closed: "\<nu> R \<cdot> \<nu> S \<subseteq> NC"
  by (simp add: nu_def nc_iff1 p_id_zero zero_assoc3)

lemma nc_scomp_closed_alt [simp]: "\<nu> (\<nu> R \<cdot> \<nu> S) = \<nu> R \<cdot> \<nu> S"
  by (metis inf.orderE nc_scomp_closed nu_def)

lemma nc_ccomp_closed: "\<nu> R \<parallel> \<nu> S \<subseteq> NC"
  unfolding nu_def by (clarsimp simp: mr_simp)

lemma nc_ccomp_closed_alt [simp]: "\<nu> (R \<parallel> \<nu> S) = R \<parallel> \<nu> S"
  unfolding nu_def by (clarsimp simp: mr_simp) blast

lemma tarski_prod: "(\<nu> R \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC) = (if \<nu> S = {} then {} else \<nu> R \<cdot> NC)"
proof (cases "\<nu> S = {}")
  case True
  show ?thesis
    by (metis True nc_zero nu_def p_id_NC s_prod_zerol zero_assoc3)
next
  case False
  hence a: "NC \<cdot> (\<nu> S \<cdot> NC) = NC"
    unfolding nu_def by (metis p_id_NC tarski)
  have "(\<nu> R \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC) = (Dom (\<nu> R) \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC)"
    by (simp add: nu_def)
  also have "... = Dom (\<nu> R) \<cdot> (NC \<cdot> (\<nu> S \<cdot> NC))"
    using d_assoc1 by blast
  also have "... = Dom (\<nu> R) \<cdot> NC"
    by (simp add: a)
  also have "... = \<nu> R \<cdot> NC"
    by (simp add: nu_def)
  finally have "(\<nu> R \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC) = \<nu> R \<cdot> NC".
  thus ?thesis
    using False by auto
qed

lemma nc_prod_aux [simp]: "(\<nu> R \<cdot> NC) \<cdot> NC = \<nu> R \<cdot> NC"
  apply (clarsimp simp: mr_simp)
  apply safe
  apply clarsimp
  apply (smt (verit) SUP_bot_conv(1) ex_in_conv)
  apply clarsimp
  by (smt (verit, best) SUP_bot_conv(2) UNIV_I UN_constant)

lemma nc_vec_add_closed: "(\<nu> R \<cdot> NC \<union> \<nu> S \<cdot> NC) \<cdot> NC = \<nu> R \<cdot> NC \<union> \<nu> S \<cdot> NC"
  by (simp add: s_prod_distr)

lemma nc_vec_par_is_meet: "\<nu> R \<cdot> NC \<parallel> \<nu> S \<cdot> NC = \<nu> R \<cdot> NC \<inter> \<nu> S \<cdot> NC"
  by (metis (no_types, lifting) U_nc_par cl11 nu_def p_prod_assoc up_closed_par_is_meet)

lemma nc_vec_meet_closed: "(\<nu> R \<cdot> NC \<inter> \<nu> S \<cdot> NC) \<cdot> NC = \<nu> R \<cdot> NC \<inter> \<nu> S \<cdot> NC"
  apply (clarsimp simp: nu_def mr_simp)
  apply safe
  apply (metis SUP_const UN_I ex_in_conv)
  apply (clarsimp, smt (verit) SUP_bot_conv(2) ex_in_conv)
  by (clarsimp, smt (verit, ccfv_threshold) SUP_bot_conv(1) SUP_const UNIV_I all_not_in_conv)

lemma nc_vec_par_closed: "(\<nu> R \<cdot> NC \<parallel> \<nu> S \<cdot> NC) \<cdot> NC = \<nu> R \<cdot> NC \<parallel> \<nu> S \<cdot> NC"
  by (metis U_nc_par nc_prod_aux uc_interr)

lemma nc_vec_seq_closed: "((\<nu> R \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC)) \<cdot> NC = (\<nu> R \<cdot> NC) \<cdot> (\<nu> S \<cdot> NC)"
proof (cases "\<nu> S = {}")
  case True thus ?thesis
    by simp
next
  case False thus ?thesis
    by (simp add: tarski_prod)
qed

lemma iso5_sharp [simp]: "(\<nu> R \<cdot> 1\<^sub>\<pi> \<parallel> NC) \<cdot> 1\<^sub>\<pi> = \<nu> R \<cdot> 1\<^sub>\<pi>"
  by (simp add: c3)

lemma iso6_sharp [simp]: "(\<nu> R \<cdot> NC \<cdot> 1\<^sub>\<pi>) \<parallel> NC = \<nu> R \<cdot> NC"
  by (simp add: c4 nu_def)

lemma nsv_hom_par: "(R \<parallel> S) \<cdot> NC = R \<cdot> NC \<parallel> S \<cdot> NC"
  by (simp add: cl4 seq_conc_subdistr subset_antisym)

lemma nvs_hom_meet: "Dom (\<nu> R \<cdot> NC \<inter> \<nu> S \<cdot> NC) = Dom (\<nu> R \<cdot> NC) \<inter> Dom (\<nu> S \<cdot> NC)"
  by (rule antisym) (fastforce simp: nu_def mrd_simp)+

lemma ncv_hom_meet: "R \<cdot> 1\<^sub>\<pi> \<inter> S \<cdot> 1\<^sub>\<pi> \<parallel> NC = (R \<cdot> 1\<^sub>\<pi> \<parallel> NC) \<inter> (S \<cdot> 1\<^sub>\<pi> \<parallel> NC)"
  by (metis c4 cl8_var d_exp_ax d_meet d_s_id_inter p_subid_par_eq_meet_var)

lemma ncv_hom_par: "(R \<parallel> S) \<parallel> NC = R \<parallel> NC \<parallel> S \<parallel> NC"
  by (metis nc_par_idem p_prod_assoc p_prod_comm)

lemma nvc_hom_meet: "(\<nu> R \<cdot> NC \<inter> \<nu> S \<cdot> NC) \<cdot> 1\<^sub>\<pi> = (\<nu> R \<cdot> NC) \<cdot> 1\<^sub>\<pi> \<inter> (\<nu> S \<cdot> NC) \<cdot> 1\<^sub>\<pi>"
  by (rule antisym) (fastforce simp: nu_def mr_simp)+

lemma tau_int: "\<tau> R \<le> R"
  using p_id_zero tau_def by auto

lemma nu_int: "\<nu> R \<le> R"
  by (simp add: nu_def)

lemma tau_ret [simp]: "\<tau> (\<tau> R) = \<tau> R"
  by (simp add: tau_def)

lemma nu_ret [simp]: "\<nu> (\<nu> R) = \<nu> R"
  by (simp add: nu_def)

lemma tau_iso: "R \<le> S \<Longrightarrow> \<tau> R \<le> \<tau> S"
  by (simp add: inf.order_iff tau_def x_zero_meet_closed)

lemma nu_iso: "R \<le> S \<Longrightarrow> \<nu> R \<le> \<nu> S"
  by (metis Int_mono nu_def order_refl)

lemma tau_zero [simp]: "\<tau> {} = {}"
  by (simp add: tau_def)

lemma nu_zero [simp]: "\<nu> {} = {}"
  using nu_def by auto

lemma tau_s [simp]: "\<tau> 1\<^sub>\<sigma> = {}"
  by (simp add: tau_def)

lemma tau_c [simp]: "\<tau> 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  by (simp add: tau_def)

lemma nu_c [simp]: "\<nu> 1\<^sub>\<pi> = {}"
  by (simp add: nu_def)

lemma tau_nc [simp]: "\<tau> NC = {}"
  by (metis nc_iff2 order_refl tau_def)

lemma nu_nc [simp]: "\<nu> NC = NC"
  using nu_def by auto

lemma tau_U [simp]: "\<tau> U = 1\<^sub>\<pi>"
  by (simp add: tau_def)

lemma nu_U [simp]: "\<nu> U = NC"
  by (simp add: Diff_eq nu_def)

lemma tau_add [simp]: "\<tau> (R \<union> S) = \<tau> R \<union> \<tau> S"
  by (simp add: tau_def x_zero_add_closed)

lemma nu_add [simp]: "\<nu> (R \<union> S) = \<nu> R \<union> \<nu> S"
  by (simp add: Int_Un_distrib2 nu_def)

lemma tau_meet [simp]: "\<tau> (R \<inter> S) = \<tau> R \<inter> \<tau> S"
  by (simp add: tau_def x_zero_meet_closed)

lemma nu_meet [simp]: "\<nu> (R \<inter> S) = \<nu> R \<inter> \<nu> S"
  by (simp add: inf_commute inf_left_commute nu_def)

lemma tau_seq: "\<tau> (R \<cdot> S) = \<tau> R \<union> \<nu> R \<cdot> \<tau> S"
  unfolding nu_def tau_def
  by (metis sup_commute x_y_split zero_assoc3)

lemma tau_par [simp]: "\<tau> (R \<parallel> S) = \<tau> R \<parallel> \<tau> S"
  by (metis U_par_zero tau_def uc_interr)

lemma nu_par_aux1: "R \<parallel> \<tau> S = Dom (\<tau> S) \<cdot> R"
  by (metis p_prod_comm tau_def x_zero_prop)

lemma nu_par_aux3 [simp]: "\<nu> (\<nu> R \<parallel> \<tau> S) = \<nu> R \<parallel> \<tau> S"
  by (metis nc_ccomp_closed_alt p_prod_comm)

lemma nu_par_aux4 [simp]: "\<nu> (\<tau> R \<parallel> \<tau> S) = {}"
  by (metis nu_def tau_def tau_par zero_nc)

lemma nu_par: "\<nu> (R \<parallel> S) = Dom (\<tau> R) \<cdot> \<nu> S \<union> Dom (\<tau> S) \<cdot> \<nu> R \<union> (\<nu> R \<parallel> \<nu> S)"
  apply (rule antisym)
  apply (fastforce simp: mrd_simp nu_def tau_def)
  by (auto simp: mrd_simp nu_def tau_def)

lemma sprod_tau_nu: "R \<cdot> S = \<tau> R \<union> \<nu> R \<cdot> S"
  by (metis nu_def sup_commute tau_def x_y_split)

lemma pprod_tau_nu: "R \<parallel> S = (\<nu> R \<parallel> \<nu> S) \<union> Dom (\<tau> R) \<cdot> \<nu> S \<union> Dom (\<tau> S) \<cdot> \<nu> R \<union> (\<tau> R \<parallel> \<tau> S)"
  by (smt (verit) nu_def nu_par sup_assoc sup_left_commute tau_def tau_par x_split_var)

lemma tau_idem [simp]: "\<tau> R \<cdot> \<tau> R = \<tau> R"
  by (simp add: tau_def)

lemma tau_interr: "(R \<parallel> S) \<cdot> \<tau> T = R \<cdot> \<tau> T \<parallel> S \<cdot> \<tau> T"
  by (simp add: tau_def cl4 seq_conc_subdistr subset_antisym)

lemma tau_le_c: "\<tau> R \<le> 1\<^sub>\<pi>"
  by (simp add: tau_def x_zero_le_c)

lemma c_le_tauc: "1\<^sub>\<pi> \<le> \<tau> 1\<^sub>\<pi>"
  by simp

lemma x_alpha_tau [simp]: "\<nu> R \<union> \<tau> R = R"
  by (simp add: nu_def tau_def)

lemma alpha_tau_zero [simp]: "\<nu> (\<tau> R) = {}"
  by (simp add: nu_def tau_def)

lemma tau_alpha_zero [simp]: "\<tau> (\<nu> R) = {}"
  by (simp add: nu_def tau_def)

lemma sprod_tau_nu_var [simp]: "\<nu> (\<nu> R \<cdot> S) = \<nu> (R \<cdot> S)"
  by (metis nu_add nu_def nu_ret x_y_split zero_nc)

lemma tau_s_prod [simp]: "\<tau> (R \<cdot> S) = R \<cdot> \<tau> S"
  by (simp add: tau_def zero_assoc3)

lemma alpha_fp: "\<nu> R = R \<longleftrightarrow> R \<cdot> {} = {}"
  by (metis inf.orderE nc_iff2 nc_zero nu_def)

lemma p_prod_tau_alpha: "R \<parallel> S = (R \<parallel> \<nu> S) \<union> (\<nu> R \<parallel> S) \<union> (\<tau> R \<parallel> \<tau> S)"
  by (smt (verit) p_prod_comm p_prod_distl sup.idem sup_assoc sup_commute x_alpha_tau)

lemma p_prod_tau_alpha_var: "R \<parallel> S = (R \<parallel> \<nu> S) \<union> (\<nu> R \<parallel> S) \<union> \<tau> (R \<parallel> S)"
  using p_prod_tau_alpha tau_par by blast

lemma alpha_par: "\<nu> (R \<parallel> S) = (\<nu> R \<parallel> S) \<union> (R \<parallel> \<nu> S)"
  by (metis alpha_tau_zero nc_ccomp_closed_alt nu_add p_prod_comm p_prod_tau_alpha sup_bot_right tau_par)

lemma alpha_tau [simp]: "\<nu> (R \<cdot> \<tau> S) = {}"
  by (metis alpha_tau_zero tau_s_prod)

lemma nu_par_prop: "\<nu> R = R \<Longrightarrow> \<nu> (R \<parallel> S) = R \<parallel> S"
  by (metis nc_ccomp_closed_alt p_prod_comm)

lemma tau_seq_prop: "\<tau> R = R \<Longrightarrow> R \<cdot> S = R"
  by (metis cl6 tau_def)

lemma tau_seq_prop2: "\<tau> R = R \<Longrightarrow> \<tau> (R \<cdot> S) = R \<cdot> S"
  by (metis cl6 tau_def)

lemma d_nu: "\<nu> (Dom R \<cdot> S) = Dom R \<cdot> \<nu> S"
  by (auto simp: nu_def mrd_simp)

lemma nu_ideal1: "\<nu> R = R \<Longrightarrow> S \<le> R \<Longrightarrow> \<nu> S = S"
  unfolding nu_def by blast

lemma tau_ideal1: "\<tau> R = R \<Longrightarrow> S \<le> R \<Longrightarrow> \<tau> S = S"
  by (metis dual_order.trans p_subid_iff_var tau_def)

lemma nu_ideal2: "\<nu> R = R \<Longrightarrow> \<nu> S = S \<Longrightarrow> \<nu> (R \<union> S) = R \<union> S"
  by simp

lemma tau_ideal2: "\<tau> R = R \<Longrightarrow> \<tau> S = S \<Longrightarrow> \<tau> (R \<union> S) = R \<union> S"
  by simp

lemma tau_add_precong: "\<tau> R \<le> \<tau> S \<Longrightarrow> \<tau> (R \<union> T) \<le> \<tau> (S \<union> T)"
  by auto

lemma tau_meet_precong: "\<tau> R \<le> \<tau> S \<Longrightarrow> \<tau> (R \<inter> T) \<le> \<tau> (S \<inter> T)"
  by force

lemma tau_par_precong: "\<tau> R \<le> \<tau> S \<Longrightarrow> \<tau> (R \<parallel> T) \<le> \<tau> (S \<parallel> T)"
  by (simp add: p_prod_isol)

lemma tau_seq_precongl: "\<tau> R \<le> \<tau> S \<Longrightarrow> \<tau> (T \<cdot> R) \<le> \<tau> (T \<cdot> S)"
  by (simp add: s_prod_isor)

lemma nu_add_precong: "\<nu> R \<le> \<nu> S \<Longrightarrow> \<nu> (R \<union> T) \<le> \<nu> (S \<union> T)"
  by auto

lemma nu_meet_precong: "\<nu> R \<le> \<nu> S \<Longrightarrow> \<nu> (R \<inter> T) \<le> \<nu> (S \<inter> T)"
  by force

lemma nu_seq_precongr: "\<nu> R \<le> \<nu> S \<Longrightarrow> \<nu> (R \<cdot> T) \<le> \<nu> (S \<cdot> T)"
  by (metis nu_iso s_prod_isol sprod_tau_nu_var)

definition
  "tcg R S = (\<tau> R \<le> \<tau> S \<and> \<tau> S \<le> \<tau> R)"

definition
  "ncg R S = (\<nu> R \<le> \<nu> S \<and> \<nu> S \<le> \<nu> R)"

lemma tcg_refl: "tcg R R"
  by (simp add: tcg_def)

lemma tcg_trans: "tcg R S \<Longrightarrow> tcg S T \<Longrightarrow> tcg R T"
  by (meson subset_trans tcg_def)

lemma tcg_sym: "tcg R S \<Longrightarrow> tcg S R"
  by (simp add: tcg_def)

lemma ncg_refl: "ncg R R"
  using ncg_def by blast

lemma ncg_trans: "ncg R S \<Longrightarrow> ncg S T \<Longrightarrow> ncg R T"
  by (meson ncg_def order_trans)

lemma ncg_sym: "ncg R S \<Longrightarrow> ncg S R"
  by (simp add: ncg_def)

lemma tcg_alt: "tcg R S = (\<tau> R = \<tau> S)"
  using tcg_def by auto

lemma ncg_alt: "ncg R S = (\<nu> R = \<nu> S)"
  by (simp add: Orderings.order_eq_iff ncg_def)

lemma tcg_add: "\<tau> R = \<tau> S \<Longrightarrow> \<tau> (R \<union> T) = \<tau> (S \<union> T)"
  by simp

lemma tcg_meet: "\<tau> R = \<tau> S \<Longrightarrow> \<tau> (R \<inter> T) = \<tau> (S \<inter> T)"
  by simp

lemma tcg_par: "\<tau> R = \<tau> S \<Longrightarrow> \<tau> (R \<parallel> T) = \<tau> (S \<parallel> T)"
  by simp

lemma tcg_seql: "\<tau> R = \<tau> S \<Longrightarrow> \<tau> (T \<cdot> R) = \<tau> (T \<cdot> S)"
  by simp

lemma ncg_add: "\<nu> R = \<nu> S \<Longrightarrow> \<nu> (R \<union> T) = \<nu> (S \<union> T)"
  by simp

lemma ncg_meet: "\<nu> R = \<nu> S \<Longrightarrow> \<nu> (R \<inter> T) = \<nu> (S \<inter> T)"
  by simp

lemma ncg_seqr: "\<nu> R = \<nu> S \<Longrightarrow> \<nu> (R \<cdot> T) = \<nu> (S \<cdot> T)"
  by (metis sprod_tau_nu_var)


subsection \<open>Powers\<close>

primrec p_power :: "('a,'a) mrel \<Rightarrow> nat \<Rightarrow> ('a,'a) mrel" where
  "p_power R 0       = 1\<^sub>\<sigma>" |
  "p_power R (Suc n) = R \<cdot> p_power R n"

primrec power_rd :: "('a,'a) mrel \<Rightarrow> nat \<Rightarrow> ('a,'a) mrel" where
  "power_rd R 0       = {}" |
  "power_rd R (Suc n) = 1\<^sub>\<sigma> \<union> R \<cdot> power_rd R n"

primrec power_sq :: "('a,'a) mrel \<Rightarrow> nat \<Rightarrow> ('a,'a) mrel" where
  "power_sq R 0       = 1\<^sub>\<sigma>" |
  "power_sq R (Suc n) = 1\<^sub>\<sigma> \<union> R \<cdot> power_sq R n"

lemma power_rd_chain: "power_rd R n \<le> power_rd R (n + 1)"
  apply (induct n)
  apply simp
  by (smt (verit, best) Suc_eq_plus1 Un_subset_iff le_iff_sup power_rd.simps(2) s_prod_subdistl subsetI)

lemma power_sq_chain: "power_sq R n \<le> power_sq R (n + 1)"
  apply (induct n)
  apply clarsimp
  by (smt (verit, ccfv_SIG) UnCI Un_subset_iff add.commute le_iff_sup plus_1_eq_Suc power_sq.simps(2) s_prod_subdistl subsetI)

lemma pow_chain: "p_power (1\<^sub>\<sigma> \<union> R) n \<le> p_power (1\<^sub>\<sigma> \<union> R) (n + 1)"
  apply (induct n)
  apply simp
  by (simp add: s_prod_isor)

lemma pow_prop: "p_power (1\<^sub>\<sigma> \<union> R) (n + 1) = 1\<^sub>\<sigma> \<union> R \<cdot> p_power (1\<^sub>\<sigma> \<union> R) n"
  apply (induct n)
  apply simp
  by (smt (verit, best) add.commute p_power.simps(2) plus_1_eq_Suc s_prod_distr s_prod_idl s_prod_subdistl subset_antisym sup.commute sup.left_commute sup.right_idem sup_ge1)

lemma power_rd_le_sq: "power_rd R n \<le> power_sq R n"
  apply (induct n)
  apply simp
  by (smt (verit, best) UnCI UnE le_iff_sup power_rd.simps(2) power_sq.simps(2) s_prod_subdistl subsetI)

lemma power_sq_le_rd: "power_sq R n \<le> power_rd R (Suc n)"
  apply (induct n)
  apply simp
  by (smt (verit, del_insts) UnCI UnE power_rd.simps(2) power_sq.simps(2) s_prod_subdistl subsetI sup.absorb_iff1)

lemma power_sq_power: "power_sq R n = p_power (1\<^sub>\<sigma> \<union> R) n"
  apply (induct n)
  apply simp
  using pow_prop by auto


subsection \<open>Star\<close>

lemma iso_prop: "mono (\<lambda>X. S \<union> R \<cdot> X)"
  by (rule monoI, (clarsimp simp: mr_simp), blast)

lemma gfp_lfp_prop: "gfp (\<lambda>X. R \<cdot> X) \<union> lfp (\<lambda>X. S \<union> R \<cdot> X) \<subseteq> gfp (\<lambda>X. S \<union> R \<cdot> X)"
  by (simp add: lfp_le_gfp gfp_mono iso_prop)

definition star :: "('a,'a) mrel \<Rightarrow> ('a,'a) mrel" where
  "star R = lfp (\<lambda>X. s_id \<union> R \<cdot> X)"

lemma star_unfold: "1\<^sub>\<sigma> \<union> R \<cdot> star R \<le> star R"
  unfolding star_def using iso_prop lfp_unfold by blast

lemma star_induct: "1\<^sub>\<sigma> \<union> R \<cdot> S \<le> S \<Longrightarrow> star R \<le> S"
  unfolding star_def by (meson lfp_lowerbound)

lemma star_refl: "1\<^sub>\<sigma> \<le> star R"
  using star_unfold by auto

lemma star_unfold_part: "R \<cdot> star R \<le> star R"
  using star_unfold by auto

lemma star_ext_aux: "R \<le> R \<cdot> star R"
  by (metis s_prod_idr s_prod_isor star_refl)

lemma star_ext: "R \<le> star R"
  using star_ext_aux star_unfold_part by blast

lemma star_co_trans: "star R \<le> star R \<cdot> star R"
  by (metis s_prod_idr s_prod_isor star_refl)

lemma star_iso: "R \<le> S \<Longrightarrow> star R \<le> star S"
  by (metis (no_types, lifting) le_sup_iff s_prod_distr star_induct star_refl star_unfold_part subset_Un_eq)

lemma star_unfold_eq [simp]: "1\<^sub>\<sigma> \<union> R \<cdot> star R = star R"
  by (metis iso_prop lfp_unfold star_def)

lemma nu_star1:
  assumes "\<And>(R::('a,'a) mrel) (S::('a,'a) mrel) (T::('a,'a) mrel). R \<cdot> (S \<cdot> T) = (R \<cdot> S) \<cdot> T"
  shows "star (R::('a,'a) mrel) \<le> star (\<nu> R) \<cdot> (1\<^sub>\<sigma> \<union> \<tau> R)"
  by (smt (verit, ccfv_threshold) assms s_prod_distr s_prod_idl sprod_tau_nu star_induct star_unfold_eq subsetI sup_assoc)

lemma nu_star2:
  assumes "\<And>(R::('a,'a) mrel). star R \<cdot> star R \<le> star R"
  shows "star (\<nu> (R::('a,'a) mrel)) \<cdot> (1\<^sub>\<sigma> \<union> \<tau> R) \<le> star R"
  by (smt (verit) assms le_sup_iff nu_int s_prod_isol s_prod_isor star_ext star_refl star_iso subset_trans tau_int)

lemma nu_star:
  assumes "\<And>(R::('a,'a) mrel). star R \<cdot> star R \<le> star R"
  and "\<And>(R::('a,'a) mrel) (S::('a,'a) mrel) (T::('a,'a) mrel). R \<cdot> (S \<cdot> T) = (R \<cdot> S) \<cdot> T"
  shows "star (\<nu> (R::('a,'a) mrel)) \<cdot> (1\<^sub>\<sigma> \<union> \<tau> R) = star R"
  using assms nu_star1 nu_star2 by blast

lemma tau_star: "star (\<tau> R) = 1\<^sub>\<sigma> \<union> \<tau> R"
  by (metis cl6 tau_def star_unfold_eq)

lemma tau_star_var:
  assumes "\<And>(R::('a,'a) mrel) (S::('a,'a) mrel) (T::('a,'a) mrel). R \<cdot> (S \<cdot> T) = (R \<cdot> S) \<cdot> T"
  and "\<And>(R::('a,'a) mrel). star R \<cdot> star R \<le> star R"
  shows "\<tau> (star (R::('a,'a) mrel)) = star (\<nu> R) \<cdot> \<tau> R"
  by (metis (mono_tags, lifting) assms nu_star s_prod_distr s_prod_zerol sup_bot_left tau_def tau_s)

lemma nu_star_sub: "star (\<nu> R) \<le> \<nu> (star R)"
proof -
  have a: "1\<^sub>\<sigma> \<subseteq> star R"
    by (simp add: star_refl)
  have b: "(R \<inter> NC) \<cdot> (star R \<inter> NC) \<subseteq> star R"
    by (metis nu_def nu_int s_prod_isol s_prod_isor star_unfold_part subset_trans)
  have c: "1\<^sub>\<sigma> \<subseteq> NC"
    by (simp add: s_le_nc)
  have "(R \<inter> NC) \<cdot> (star R \<inter> NC) \<subseteq> NC"
    by (metis nc_scomp_closed nu_def)
  thus ?thesis
    by (metis Un_least a b c le_infI nu_def star_induct)
qed

lemma nu_star_nu [simp]: "\<nu> (star (\<nu> R)) = star (\<nu> R)"
  using nu_int nu_star_sub by fastforce

lemma nu_star_tau [simp]: "\<nu> (star (\<tau> R)) = 1\<^sub>\<sigma>"
  using tau_star by (metis alpha_tau_zero nu_add tau_s x_alpha_tau)

lemma tau_star_tau [simp]: "\<tau> (star (\<tau> R)) = \<tau> R"
  by (simp add: tau_star)

lemma tau_star_nu [simp]: "\<tau> (star (\<nu> R)) = {}"
  using alpha_fp tau_def nu_star_nu by metis

lemma d_star_unfold [simp]: "Dom S \<union> Dom (R \<cdot> Dom (star R \<cdot> S)) = Dom (star R \<cdot> S)"
proof -
  have "Dom S \<union> Dom (R \<cdot> Dom (star R \<cdot> S)) = Dom S \<union> Dom (R \<cdot> (star R \<cdot> Dom S))"
    by (metis d_loc_ax)
  also have "... = Dom (1\<^sub>\<sigma> \<cdot> Dom S \<union> (R \<cdot> (star R \<cdot> Dom S)))"
    by (simp add: d_add_ax)
  also have "... = Dom (1\<^sub>\<sigma> \<cdot> Dom S \<union> (R \<cdot> star R) \<cdot> Dom S)"
    by (metis d_comm_ax d_s_id_inter d_s_id_prop s_prod_idl test_assoc3)
  moreover have "... = Dom ((1\<^sub>\<sigma> \<union> R \<cdot> star R) \<cdot> Dom S)"
    using s_prod_distr by metis
  ultimately show ?thesis
    by simp
qed

lemma d_star_sim1:
  assumes "\<And>R S T. Dom (T::('a,'b) mrel) \<union> (R::('a,'a) mrel) \<cdot> (S::('a,'a) mrel) \<le> S \<Longrightarrow> star R \<cdot> Dom T \<le> S"
  shows "(R::('a,'a) mrel) \<cdot> Dom (T::('a,'b) mrel) \<le> Dom T \<cdot> (S::('a,'a) mrel) \<Longrightarrow> star R \<cdot> Dom T \<le> Dom T \<cdot> star S"
proof -
  fix R S::"('a,'a) mrel" and T ::"('a,'b) mrel"
  assume a: "R \<cdot> Dom T \<le> Dom T \<cdot> S"
  hence "(R \<cdot> Dom T) \<cdot> star S \<le> (Dom T \<cdot> S) \<cdot> star S"
    by (simp add: s_prod_isol)
  hence b: "R \<cdot> (Dom T \<cdot> star S) \<le> Dom T \<cdot> (S \<cdot> star S)"
    by (metis d_assoc1 d_s_id_ax inf.order_iff test_assoc1)
  hence "R \<cdot> (Dom T \<cdot> star S) \<le> Dom T \<cdot> star S"
    by (meson order_trans s_prod_isor star_unfold_part)
  hence "Dom T \<union> R \<cdot> (Dom T \<cdot> star S) \<le> Dom T \<cdot> star S"
    by (metis le_supI s_prod_idr s_prod_isor star_refl)
  thus "star R \<cdot> Dom T \<le> Dom T \<cdot> star S"
    using assms by presburger
qed

lemma d_star_induct:
  assumes "\<And>R S T. Dom (T::('a,'b) mrel) \<union> (R::('a,'a) mrel) \<cdot> (S::('a,'a) mrel) \<le> S \<Longrightarrow> star R \<cdot> Dom T \<le> S"
  shows "Dom ((R::('a,'a) mrel) \<cdot> (S::('a,'a) mrel)) \<le> Dom S \<Longrightarrow> Dom (star R \<cdot> S) \<le> Dom S"
  by (metis assms d_star_sim1 dc_prop2 demod1 demod2)


subsection \<open>Omega\<close>

definition omega :: "('a,'a) mrel \<Rightarrow> ('a,'a) mrel" where
  "omega R \<equiv> gfp (\<lambda>X. R \<cdot> X)"

lemma om_unfold: "omega R \<le> R \<cdot> omega R"
  unfolding omega_def
  by (metis (no_types, lifting) gfp_least gfp_upperbound order_trans s_prod_isor)

lemma om_coinduct: "S \<le> R \<cdot> S \<Longrightarrow> S \<le> omega R"
  unfolding omega_def by (simp add: gfp_upperbound omega_def)

lemma om_unfold_eq [simp]: "R \<cdot> omega R = omega R"
  by (rule antisym) (auto simp: om_coinduct om_unfold s_prod_isor)

lemma om_iso: "R \<le> S \<Longrightarrow> omega R \<le> omega S"
  by (metis om_coinduct s_prod_isol om_unfold_eq)

lemma zero_om [simp]: "omega {} = {}"
  using om_unfold_eq s_prod_zerol by blast

lemma s_id_om [simp]: "omega 1\<^sub>\<sigma> = U"
  by (simp add: U_def eq_iff om_coinduct)

lemma p_id_om [simp]: "omega 1\<^sub>\<pi> = 1\<^sub>\<pi>"
  using om_unfold_eq s_prod_p_idl by blast

lemma nc_om [simp]: "omega NC = U"
  by (metis dual_order.refl nc_U om_coinduct s_id_om s_prod_idl subset_antisym)

lemma U_om [simp]: "omega U = U"
  by (metis U_U dual_order.refl om_coinduct s_id_om s_prod_idl subset_antisym)

lemma tau_om1: "\<tau> R \<le> \<tau> (omega R)"
  by (metis om_unfold_eq order_refl sup.boundedE tau_seq)

lemma tau_om2 [simp]: "omega (\<tau> R) = \<tau> R"
  by (metis cl6 om_unfold_eq tau_def)

lemma tau_om3: "omega (\<tau> R) \<le> \<tau> (omega R)"
  by (simp add: tau_om1)

lemma om_nu_tau: "omega (\<nu> R) \<union> star (\<nu> R) \<cdot> \<tau> R \<le> omega R"
proof -
  have "omega (\<nu> R) \<union> star (\<nu> R) \<cdot> \<tau> R = omega (\<nu> R) \<union> (1\<^sub>\<sigma> \<union> \<nu> R \<cdot> star (\<nu> R)) \<cdot> \<tau> R"
    by auto
  also have "... = omega (\<nu> R) \<union> \<tau> R \<union> \<nu> R \<cdot> star (\<nu> R) \<cdot> \<tau> R"
    using s_prod_distr s_prod_idl by blast
  also have "... = \<tau> R \<union> \<nu> R \<cdot> omega (\<nu> R) \<union> \<nu> R \<cdot> (star (\<nu> R) \<cdot> \<tau> R)"
    by (simp add: cl5 sup_commute tau_def)
  also have "... \<le> \<tau> R \<union> \<nu> R \<cdot> (omega (\<nu> R) \<union> star (\<nu> R) \<cdot> \<tau> R)"
    by (smt (verit) Un_subset_iff s_prod_isor sup.cobounded2 sup.coboundedI2 sup_commute)
  also have "... = R \<cdot> (omega (\<nu> R) \<union> star (\<nu> R) \<cdot> \<tau> R)"
    using sprod_tau_nu by blast
  finally show ?thesis
    using om_coinduct by blast
qed

end
