theory MLSSmf_to_MLSS_Complexity
  imports MLSSmf_to_MLSS
begin

definition size\<^sub>m :: "('v, 'f) MLSSmf_clause \<Rightarrow> nat" where
  "size\<^sub>m \<C> \<equiv> card (set \<C>)"

lemma (in normalized_MLSSmf_clause) card_V_upper_bound:
  "card V \<le> 3 * size\<^sub>m \<C>"
  unfolding V_def
  using norm_\<C>
proof (induction \<C>)
  case 1
  then show ?case by simp
next
  case (2 ls l)
  from \<open>norm_literal l\<close> have "card (vars\<^sub>m l) \<le> 3"
    by (cases l rule: norm_literal.cases) (auto simp: card_insert_if)
  with 2 show ?case
  proof (cases "l \<in> set ls")
    case True
    then have "vars\<^sub>m l \<subseteq> vars\<^sub>m ls" by blast
    moreover
    have "vars\<^sub>m (l # ls) = vars\<^sub>m l \<union> vars\<^sub>m ls" by auto
    ultimately
    have "vars\<^sub>m (l # ls) = vars\<^sub>m ls" by blast
    then have "card (vars\<^sub>m (l # ls)) = card (vars\<^sub>m ls)" by argo
    moreover
    from True have "size\<^sub>m (l # ls) = size\<^sub>m ls"
      unfolding size\<^sub>m_def
      by (simp add: insert_absorb)
    ultimately
    show ?thesis using "2.IH" by argo
  next
    case False
    have "vars\<^sub>m (l # ls) = vars\<^sub>m l \<union> vars\<^sub>m ls" by auto
    then have "card (vars\<^sub>m (l # ls)) \<le> card (vars\<^sub>m l) + card (vars\<^sub>m ls)"
      by (simp add: card_Un_le)
    with \<open>card (vars\<^sub>m l) \<le> 3\<close> "2.IH"
    have "card (vars\<^sub>m (l # ls)) \<le> 3 * (Suc (size\<^sub>m ls))"
      by simp
    moreover
    from False have "size\<^sub>m (l # ls) = Suc (size\<^sub>m ls)"
      unfolding size\<^sub>m_def by simp
    ultimately
    show ?thesis by argo
  qed
qed

lemma (in normalized_MLSSmf_clause) card_F_upper_bound:
  "card F \<le> 2 * size\<^sub>m \<C>"
  unfolding F_def
  using norm_\<C>
proof (induction \<C>)
  case 1
  then show ?case by simp
next
  case (2 ls l)
  from \<open>norm_literal l\<close> have "card (funs\<^sub>m l) \<le> 2"
    by (cases l rule: norm_literal.cases) (auto simp: card_insert_if)
  with 2 show ?case
  proof (cases "l \<in> set ls")
    case True
    then have "funs\<^sub>m l \<subseteq> funs\<^sub>m ls" by blast
    moreover
    have "funs\<^sub>m (l # ls) = funs\<^sub>m l \<union> funs\<^sub>m ls" by auto
    ultimately
    have "funs\<^sub>m (l # ls) = funs\<^sub>m ls" by blast
    then have "card (funs\<^sub>m (l # ls)) = card (funs\<^sub>m ls)" by argo
    moreover
    from True have "size\<^sub>m (l # ls) = size\<^sub>m ls"
      unfolding size\<^sub>m_def
      by (simp add: insert_absorb)
    ultimately
    show ?thesis using "2.IH" by argo
  next
    case False
    have "funs\<^sub>m (l # ls) = funs\<^sub>m l \<union> funs\<^sub>m ls" by auto
    then have "card (funs\<^sub>m (l # ls)) \<le> card (funs\<^sub>m l) + card (funs\<^sub>m ls)"
      by (simp add: card_Un_le)
    with \<open>card (funs\<^sub>m l) \<le> 2\<close> "2.IH"
    have "card (funs\<^sub>m (l # ls)) \<le> 2 * (Suc (size\<^sub>m ls))"
      by simp
    moreover
    from False have "size\<^sub>m (l # ls) = Suc (size\<^sub>m ls)"
      unfolding size\<^sub>m_def by simp
    ultimately
    show ?thesis by argo
  qed
qed

lemma (in normalized_MLSSmf_clause) size_restriction_on_InterOfVars:
  "card (restriction_on_InterOfVars vs) \<le> 2 * length vs"
proof (induction vs rule: restriction_on_InterOfVars.induct)
  case (3 x v vs)
  have "length zs > length ys \<Longrightarrow> InterOfVarsAux zs \<notin> \<Union> (vars ` restriction_on_InterOfVars ys)"
    for y ys zs
    by (induction ys rule: restriction_on_InterOfVars.induct) auto
  then have "InterOfVarsAux (x # v # vs) \<notin> \<Union> (vars ` restriction_on_InterOfVars (v # vs))"
    by force
  then have "Var (InterOfVarsAux (x # v # vs)) =\<^sub>s Var (Solo x) -\<^sub>s Var (InterOfVars (v # vs)) \<notin> restriction_on_InterOfVars (v # vs)"
            "Var (InterOfVars (x # v # vs)) =\<^sub>s Var (Solo x) -\<^sub>s Var (InterOfVarsAux (x # v # vs)) \<notin> restriction_on_InterOfVars (v # vs)"
    by auto
  then have "card (restriction_on_InterOfVars (x # v # vs)) = Suc (Suc (card (restriction_on_InterOfVars (v # vs))))"
    using restriction_on_InterOfVar_finite by force
  with "3.IH" show ?case by simp
qed simp+

lemma (in normalized_MLSSmf_clause) size_restriction_on_UnionOfVars:
  "card (restriction_on_UnionOfVars vs) \<le> Suc (length vs)"
  apply (induction vs rule: restriction_on_UnionOfVars.induct)
   apply simp
  by (simp add: card_insert_if restriction_on_UnionOfVar_finite)

theorem (in normalized_MLSSmf_clause) size_introduce_v:
  "card introduce_v \<le> (3 * card V + 2) * (2 ^ card V)"
proof -
  have "card (restriction_on_v ` P\<^sup>+ V) \<le> card (P\<^sup>+ V)"
    using P_plus_finite card_image_le by blast
  then have 1: "card (restriction_on_v ` P\<^sup>+ V) \<le> card (Pow V)"
    by simp

  have "card ((restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>) \<le> 2 * card V" for \<alpha>
  proof -
    have "length (var_set_to_list \<alpha>) \<le> length V_list" by simp
    then have "length (var_set_to_list \<alpha>) \<le> card V"
      unfolding V_list_def
      by (metis V_list_def distinct_V_list distinct_card set_V_list)
    with size_restriction_on_InterOfVars[of "var_set_to_list \<alpha>"]
    have "card (restriction_on_InterOfVars (var_set_to_list \<alpha>)) \<le> 2 * card V"
      by linarith
    then show ?thesis by fastforce
  qed
  then have "(\<Sum>\<alpha>\<in>P\<^sup>+ V. card ((restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>)) \<le> 2 * card V * card (P\<^sup>+ V)"
    by (smt (verit) card_eq_sum nat_mult_1_right sum_distrib_left sum_mono)
  moreover  
  from card_UN_le[where ?I = "P\<^sup>+ V" and ?A = "restriction_on_InterOfVars \<circ> var_set_to_list"]
  have "card (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V)) \<le>
        (\<Sum>\<alpha>\<in>P\<^sup>+ V. card ((restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>))"
    using P_plus_finite finite_V by blast
  ultimately
  have "card (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V)) \<le> 2 * card V * card (P\<^sup>+ V)"
    by linarith
  also have "... \<le> 2 * card V * card (Pow V)" by simp
  finally have 2: "card (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V)) \<le> 2 * card V * card (Pow V)"
    by blast

  have "card ((restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>) \<le> Suc (card V)" for \<alpha>
  proof -
    have "length (var_set_to_list \<alpha>) \<le> length V_list" by simp
    then have "length (var_set_to_list \<alpha>) \<le> card V"
      unfolding V_list_def
      by (metis V_list_def distinct_V_list distinct_card set_V_list)
    with size_restriction_on_UnionOfVars[of "var_set_to_list \<alpha>"]
    have "card (restriction_on_UnionOfVars (var_set_to_list \<alpha>)) \<le> Suc (card V)"
      by linarith
    then show ?thesis by fastforce
  qed
  then have "(\<Sum>\<alpha>\<in>Pow V. card ((restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>)) \<le> Suc (card V) * card (Pow V)"
    by (smt (verit) card_eq_sum nat_mult_1_right sum_distrib_left sum_mono)
  moreover  
  from card_UN_le[where ?I = "Pow V" and ?A = "restriction_on_UnionOfVars \<circ> var_set_to_list"]
  have "card (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V)) \<le>
        (\<Sum>\<alpha>\<in>Pow V. card ((restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>))"
    using finite_V by blast
  ultimately
  have 3: "card (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V)) \<le> Suc (card V) * card (Pow V)"
    by linarith

  let ?atoms = "restriction_on_v ` P\<^sup>+ V \<union>
        \<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V) \<union>
        \<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V)"
  from restriction_on_InterOfVar_finite restriction_on_UnionOfVar_finite
  have "finite ?atoms" using finite_V by auto
  then have "card introduce_v \<le> card ?atoms"
    unfolding introduce_v_def
    using card_image_le by meson
  also have "... \<le> card (restriction_on_v ` P\<^sup>+ V) +
              card (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V)) +
              card (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V))"
    using finite_V by (auto intro!: order.trans[OF card_Un_le])
  also have "... \<le> card (Pow V) +
              card (\<Union> ((restriction_on_InterOfVars \<circ> var_set_to_list) ` P\<^sup>+ V)) +
              card (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V))"
    using 1 by linarith
  also have "... \<le> card (Pow V) + 2 * card V * card (Pow V) +
              card (\<Union> ((restriction_on_UnionOfVars \<circ> var_set_to_list) ` Pow V))"
    using 2 by linarith
  also have "... \<le> card (Pow V) + 2 * card V * card (Pow V) + Suc (card V) * card (Pow V)"
    using 3 by linarith
  also have "... = (1 + 2 * card V + Suc (card V)) * card (Pow V)"
    by algebra
  also have "... = (3 * card V + 2) * card (Pow V)"
    by simp
  also have "... = (3 * card V + 2) * (2 ^ card V)"
    using card_Pow finite_V by fastforce
  finally show ?thesis .
qed

lemma (in normalized_MLSSmf_clause) size_restriction_on_UnionOfVennRegions:
  "card (restriction_on_UnionOfVennRegions \<alpha>s) \<le> Suc (length \<alpha>s)"
  apply (induction \<alpha>s rule: restriction_on_UnionOfVennRegions.induct)
   apply simp+
  by (metis add_mono_thms_linordered_semiring(2) card.infinite card_insert_if finite_insert le_SucI plus_1_eq_Suc)

lemma (in normalized_MLSSmf_clause) length_all_V_set_lists:
  "length all_V_set_lists = 2 ^ card (P\<^sup>+ V)"
  unfolding all_V_set_lists_def
  using length_subseqs set_V_set_list distinct_V_set_list distinct_card
  by force

lemma (in normalized_MLSSmf_clause) length_F_list:
  "length F_list = card F"
  unfolding F_list_def F_def
  by (auto simp add: length_remdups_card_conv)

lemma (in normalized_MLSSmf_clause) size_introduce_UnionOfVennRegions:
  "card introduce_UnionOfVennRegions \<le> Suc (2 ^ card V) * 2 ^ 2 ^ card V"
proof -
  have 1: "card (restriction_on_UnionOfVennRegions \<alpha>s) \<le> Suc (2 ^ card V)"
    if "\<alpha>s \<in> set all_V_set_lists" for \<alpha>s
  proof -
    from that have "length \<alpha>s \<le> length V_set_list"
      unfolding all_V_set_lists_def
      using length_subseq_le by blast
    then have "length \<alpha>s \<le> card (P\<^sup>+ V)"
      by (metis distinct_V_set_list distinct_card set_V_set_list)
    then have "length \<alpha>s \<le> 2 ^ card V"
      using card_Pow finite_V by fastforce
    with size_restriction_on_UnionOfVennRegions[of "\<alpha>s"]
    have "card (restriction_on_UnionOfVennRegions \<alpha>s) \<le> Suc (2 ^ card V)"
      by linarith
    then show ?thesis by fastforce
  qed

  from length_all_V_set_lists have "card (set all_V_set_lists) = 2 ^ card (P\<^sup>+ V)"
    using distinct_card distinct_all_V_set_lists by metis
  also have "... \<le> 2 ^ card (Pow V)" by auto
  also have "... = 2 ^ 2 ^ card V"
    using finite_V by (simp add: card_Pow)
  finally have 2: "card (set all_V_set_lists) \<le> 2 ^ 2 ^ card V".

  let ?atoms = "\<Union> (restriction_on_UnionOfVennRegions ` set all_V_set_lists)"
  from AT_inj have "inj_on AT ?atoms"
    using inj_on_def by force
  from 1 have "(\<Sum>\<alpha>s\<in>set all_V_set_lists. card (restriction_on_UnionOfVennRegions \<alpha>s)) \<le>
    Suc (2 ^ card V) * (card (set all_V_set_lists))"
    using Sum_le_times[where ?s = "set all_V_set_lists"
                         and ?f = "\<lambda>\<alpha>s. card (restriction_on_UnionOfVennRegions \<alpha>s)"]
    by blast
  with 2 have "(\<Sum>\<alpha>s\<in>set all_V_set_lists. card (restriction_on_UnionOfVennRegions \<alpha>s)) \<le>
    Suc (2 ^ card V) * 2 ^ 2 ^ card V"
    by (meson Suc_mult_le_cancel1 le_trans)
  moreover
  from card_UN_le[where ?I = "set all_V_set_lists" and ?A = "restriction_on_UnionOfVennRegions"]
  have "card ?atoms \<le> (\<Sum>\<alpha>s\<in>set all_V_set_lists. card (restriction_on_UnionOfVennRegions \<alpha>s))"
    by blast
  ultimately
  have "card ?atoms \<le> Suc (2 ^ card V) * 2 ^ 2 ^ card V"
    by linarith
  moreover
  from introduce_UnionOfVennRegions_normalized
  have "finite introduce_UnionOfVennRegions"
    unfolding normalized_MLSS_clause_def by blast
  then have "finite ?atoms"
    using finite_image_iff \<open>inj_on AT ?atoms\<close>
    unfolding introduce_UnionOfVennRegions_def by blast
  ultimately
  show ?thesis
    unfolding introduce_UnionOfVennRegions_def
    using card_image[where ?f = "AT" and ?A = ?atoms]
    using \<open>inj_on AT ?atoms\<close>
    by presburger
qed

lemma (in normalized_MLSSmf_clause) length_choices_from_lists:
  "\<forall>choice \<in> set (choices_from_lists xss). length choice = length xss"
  by (induction xss) auto

lemma (in normalized_MLSSmf_clause) size_introduce_w:
  "\<forall>clause \<in> introduce_w. card clause \<le> 2 ^ (2 * 2 ^ card V) * card F"
proof
  let ?xss = "map (\<lambda>(l, m, f). restriction_on_FunOfUnionOfVennRegions l m f)
                  (List.product all_V_set_lists (List.product all_V_set_lists F_list))"
  fix clause assume "clause \<in> introduce_w"
  then obtain choice where choice: "choice \<in> set (choices_from_lists ?xss)" "clause = set choice"
    unfolding introduce_w_def by auto
  then have "card clause \<le> length choice"
    using card_length by blast
  also have "length choice = length ?xss"
    using choice length_choices_from_lists by blast
  also have "... = length (List.product all_V_set_lists (List.product all_V_set_lists F_list))"
    by simp
  also have "... = length all_V_set_lists * length all_V_set_lists * length F_list"
    using length_product by auto
  also have "... = 2 ^ card (P\<^sup>+ V) * 2 ^ card (P\<^sup>+ V) * card F"
    using length_all_V_set_lists length_F_list by presburger
  also have "... = 2 ^ (2 * (card (P\<^sup>+ V))) * card F"
    by (simp add: mult_2 power_add)
  also have "... \<le> 2 ^ (2 * (card (Pow V))) * card F"
    by simp
  also have "... = 2 ^ (2 * 2 ^ card V) * card F"
    using card_Pow by auto
  finally show "card clause \<le> 2 ^ (2 * 2 ^ card V) * card F" .
qed

lemma (in normalized_MLSSmf_clause) card_P_P_V_ge_1:
  "card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) \<ge> 1"
proof -
  have "Pow (P\<^sup>+ V) \<noteq> {}" by blast
  then have "Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V) \<noteq> {}" by blast
  moreover
  from finite_V P_plus_finite have "finite (Pow (P\<^sup>+ V))" by blast
  then have "finite (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" by blast
  ultimately
  have "card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) > 0" by auto
  then show ?thesis by linarith
qed

lemma (in normalized_MLSSmf_clause) size_reduce_norm_literal:
  assumes "norm_literal lt"
    shows "card (reduce_literal lt) \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
  using assms
proof (cases lt rule: norm_literal.cases)
  case (inc f)
  let ?l = "\<lambda>(l, m). AT (Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>)"
  from inc have "reduce_literal lt \<subseteq> ?l ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by force
  then have "card (reduce_literal lt) \<le> card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by (meson finite_SigmaI finite_V pow_of_p_Plus_finite surj_card_le)
  also have "... \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" by linarith
  finally show ?thesis .
next
  case (dec f)
  let ?l = "\<lambda>(l, m). AT (Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)"
  from dec have "reduce_literal lt \<subseteq> ?l ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by force
  then have "card (reduce_literal lt) \<le> card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by (meson finite_SigmaI finite_V pow_of_p_Plus_finite surj_card_le)
  also have "... \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" by linarith
  finally show ?thesis .
next
  case (add f)
  let ?l = "\<lambda>(l, m). AT (Var w\<^bsub>f\<^esub>\<^bsub>l \<union> m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)"
  from add have "reduce_literal lt \<subseteq> ?l ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by force
  then have "card (reduce_literal lt) \<le> card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by (meson finite_SigmaI finite_V pow_of_p_Plus_finite surj_card_le)
  also have "... \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" by linarith
  finally show ?thesis .
next
  case (mul f)
  let ?l1 = "\<lambda>(l, m). AT (Var (InterOfWAux f l m) =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>m\<^esub>)"
  let ?l2 = "\<lambda>(l, m). AT (Var w\<^bsub>f\<^esub>\<^bsub>l\<inter>m\<^esub> =\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub> -\<^sub>s Var (InterOfWAux f l m))"
  from mul have "reduce_literal lt \<subseteq> ?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) \<union> ?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by force
  moreover
  have "?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) \<inter> ?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) = {}"
    by fastforce
  moreover
  from finite_V P_plus_finite have "finite (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by auto
  then have "finite (?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)))" "finite (?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)))"
    by blast+
  ultimately
  have "card (reduce_literal lt) \<le> card (?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))) + card (?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)))"
    using card_Un_disjoint[where ?A = "?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" and ?B = "?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"]
    using card_mono[where ?A = "reduce_literal lt" and ?B = "?l1 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) \<union> ?l2 ` (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"]
    by fastforce
  also have "... \<le> card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) + card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    using card_image_le[where ?A = "Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)"]
    using \<open>finite (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))\<close> add_mono by blast
  also have "... = 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))" by linarith
  finally show ?thesis .
next
  case (le f g)
  let ?l = "\<lambda>l. AT (Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> =\<^sub>s Var w\<^bsub>g\<^esub>\<^bsub>l\<^esub> \<squnion>\<^sub>s Var w\<^bsub>f\<^esub>\<^bsub>l\<^esub>)"
  from le have "reduce_literal lt \<subseteq> ?l ` Pow (P\<^sup>+ V)"
    by force
  then have "card (reduce_literal lt) \<le> card (Pow (P\<^sup>+ V))"
    by (simp add: finite_V surj_card_le)
  also have "... \<le> card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by (simp add: finite_V surj_card_le)
  also have "... \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"
    by linarith
  finally show ?thesis .
next
  case (eq x y)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (eq_empty x n)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (neq x y)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (union x y z)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (diff x y z)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (single x y)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
next
  case (app x f y)
  then have "card (reduce_literal lt) = 1" by simp
  with card_P_P_V_ge_1 show ?thesis by linarith
qed

lemma (in normalized_MLSSmf_clause) size_reduce_clause:
  "card reduce_clause \<le> 2 ^ (Suc (2 * 2 ^ card V)) * size\<^sub>m \<C>"
proof -
  have "card (P\<^sup>+ V) \<le> 2 ^ card V"
    using card_Pow[of V] finite_V by simp
  from card_UN_le
  have "card reduce_clause \<le> (\<Sum>lt\<in>set \<C>. card (reduce_literal lt))"
    using reduce_clause_finite
    unfolding reduce_clause_def
    by blast
  also have "... \<le> 2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V)) * card (set \<C>)"
    using size_reduce_norm_literal norm_\<C> literal_in_norm_clause_is_norm
    using Sum_le_times[where ?s = "set \<C>" and ?f = "\<lambda>lt. card (reduce_literal lt)"
                         and ?n = "2 * card (Pow (P\<^sup>+ V) \<times> Pow (P\<^sup>+ V))"]
    by blast
  also have "... = 2 * card (Pow (P\<^sup>+ V)) * card (Pow (P\<^sup>+ V)) * card (set \<C>)"
    using card_cartesian_product by auto
  also have "... = 2 * 2 ^ (card (P\<^sup>+ V)) * 2 ^ (card (P\<^sup>+ V)) * card (set \<C>)"
    using card_Pow[of "P\<^sup>+ V"] finite_V P_plus_finite by fastforce
  also have "... \<le> 2 * 2 ^ (2 ^ card V) * 2 ^ (2 ^ card V) * card (set \<C>)"
    using \<open>card (P\<^sup>+ V) \<le> 2 ^ card V\<close>
    using power_increasing_iff[where ?b = 2 and ?x = "card (P\<^sup>+ V)" and ?y = "2 ^ card V"]
    by (simp add: mult_le_mono)
  also have "... = 2 ^ (Suc (2 * 2 ^ card V)) * card (set \<C>)"
    by (simp add: power2_eq_square power_even_eq)
  also have "... = 2 ^ (Suc (2 * 2 ^ card V)) * size\<^sub>m \<C>"
    unfolding size\<^sub>m_def by blast
  finally show ?thesis .
qed

theorem (in normalized_MLSSmf_clause) size_reduced_dnf:
  "\<forall>clause \<in> reduced_dnf. card clause \<le>
    2 ^ (2 * 2 ^ (3 * size\<^sub>m \<C>)) * (2 * size\<^sub>m \<C>) +
    (3 * (3 * size\<^sub>m \<C>) + 2) * (2 ^ (3 * size\<^sub>m \<C>)) +
    Suc (2 ^ (3 * size\<^sub>m \<C>)) * 2 ^ 2 ^ (3 * size\<^sub>m \<C>) +
    2 ^ (Suc (2 * 2 ^ (3 * size\<^sub>m \<C>))) * size\<^sub>m \<C>"
proof -
  let ?upper_bound = "2 ^ (2 * 2 ^ (3 * size\<^sub>m \<C>)) * (2 * size\<^sub>m \<C>) +
                      (3 * (3 * size\<^sub>m \<C>) + 2) * (2 ^ (3 * size\<^sub>m \<C>)) +
                      Suc (2 ^ (3 * size\<^sub>m \<C>)) * 2 ^ 2 ^ (3 * size\<^sub>m \<C>) +
                      2 ^ (Suc (2 * 2 ^ (3 * size\<^sub>m \<C>))) * size\<^sub>m \<C>"
  {fix clause assume "clause \<in> reduced_dnf"
    then obtain fms where "fms \<in> introduce_w"
                      and clause: "clause = fms \<union> introduce_v \<union> introduce_UnionOfVennRegions \<union> reduce_clause"
      unfolding reduced_dnf_def by blast    
    then have "card clause \<le> card fms + card introduce_v + card introduce_UnionOfVennRegions + card reduce_clause"
      by (auto intro!: order.trans[OF card_Un_le])
    also have "... \<le> 2 ^ (2 * 2 ^ card V) * card F + card introduce_v + card introduce_UnionOfVennRegions + card reduce_clause"
      using size_introduce_w \<open>fms \<in> introduce_w\<close> by fastforce
    also have "... \<le> 2 ^ (2 * 2 ^ card V) * card F + (3 * card V + 2) * (2 ^ card V) + card introduce_UnionOfVennRegions + card reduce_clause"
      using size_introduce_v by simp
    also have "... \<le> 2 ^ (2 * 2 ^ card V) * card F + (3 * card V + 2) * (2 ^ card V) + Suc (2 ^ card V) * 2 ^ 2 ^ card V + card reduce_clause"
      using size_introduce_UnionOfVennRegions by simp
    also have "... \<le> 2 ^ (2 * 2 ^ card V) * card F + (3 * card V + 2) * (2 ^ card V) + Suc (2 ^ card V) * 2 ^ 2 ^ card V + 2 ^ (Suc (2 * 2 ^ card V)) * size\<^sub>m \<C>"
      using size_reduce_clause by simp
    also have "... \<le> ?upper_bound"
      using card_V_upper_bound card_F_upper_bound
      by (metis Suc_le_mono add_le_mono add_le_mono1 mult_le_mono mult_le_mono1 mult_le_mono2 one_le_numeral power_increasing)
    finally have "card clause \<le> ?upper_bound" .
  }
  then show ?thesis by blast
qed

end
