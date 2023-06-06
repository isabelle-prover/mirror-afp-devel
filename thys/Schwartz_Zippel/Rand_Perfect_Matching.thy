section \<open>A Probabilistic Test for Perfect Matchings\<close>
theory Rand_Perfect_Matching imports
    Schwartz_Zippel
    Jordan_Normal_Form.Determinant
begin

text \<open>
  We use a simple representation of bipartite graphs (with same no. vertices)
  @{term [show_types] \<open>V :: nat\<close>}, @{term [show_types] \<open>E :: (nat \<times> nat) list\<close>}
  where \<open>V\<close> is the number of vertices in each partition and \<open>(x,y) \<in> E\<close> represents an edge
  between vertex \<open>x\<close> in the left partition and vertex \<open>y\<close> in the right partition.
\<close>

definition is_matching::
  "(nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool"
  where "is_matching E match \<longleftrightarrow>
    match \<subseteq> E \<and>
    inj_on fst match \<and>
    inj_on snd match"

definition has_perfect_matching::
  "nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool"
  where "has_perfect_matching V E \<longleftrightarrow>
  (\<exists>match. is_matching E match \<and> card match = V)"

(* The polynomial matrix *)
definition adj_mat::"nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow>
    int mpoly mat"
  where "adj_mat V E =
    mat V V (\<lambda>(i,j).
      if (i,j) \<in> E then Var (i*V+j) else 0)"

lemma adj_mat_square[simp]:
  shows
    "dim_row (adj_mat V E) = V"
    "dim_col (adj_mat V E) = V"
  unfolding adj_mat_def
  by auto

lemma perfect_match_set_map_fst:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "is_matching E match"
  assumes "card match = V"
  shows   "fst ` match = {0..<V}"
proof -
  have "fst ` match \<subseteq> fst ` E"
    using assms(2) unfolding is_matching_def
    by auto
  moreover have "... \<subseteq> {0..<V}"
    using assms(1) by auto
  ultimately have 1: "fst` match \<subseteq> {0..<V}"
    by auto
  then have 2: "{0..<V} \<subseteq> fst ` match"
    by (metis assms(2) assms(3) card_atLeastLessThan card_image card_subset_eq diff_zero finite_atLeastLessThan is_matching_def)
  show ?thesis using 1 2 by auto
qed

lemma perfect_match_set_map_snd:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "is_matching E match"
  assumes "card match = V"
  shows "snd ` match = {0..<V}"
proof -
  have "snd ` match \<subseteq> snd ` E"
    using assms(2) unfolding is_matching_def
    by auto
  moreover have "... \<subseteq> {0..<V}"
    using assms(1) by auto
  ultimately have 1: "snd ` match \<subseteq> {0..<V}"
    by auto
  then have 2: "{0..<V} \<subseteq> snd ` match"
    by (metis assms(2) assms(3) card_atLeastLessThan card_image card_subset_eq diff_zero finite_atLeastLessThan is_matching_def)
  show ?thesis using 1 2 by auto
qed
  
lemma is_matching_permutes:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "is_matching E match"
  assumes "card match = V"
  obtains f where
    "f permutes {0..<V}"
    "\<And>i. i < V \<Longrightarrow> (i, f i) \<in> E"
proof -
  have fV: "fst ` match  = {0..<V}"
    using perfect_match_set_map_fst[OF assms(1-3)] .

  have sV: "snd ` match = {0..<V}"
    using perfect_match_set_map_snd[OF assms(1-3)] .

  define f where "f =
    (\<lambda>i. if i < V then (@j. j < V \<and> (i,j) \<in> match) else i)"

  have exuniq: "i < V \<Longrightarrow>
    (\<exists>!j. j < V \<and> (i,j) \<in> match)" for i
  proof -
    assume "i < V"
    then have "i \<in> fst ` match" using fV
      by auto
    then obtain j where ij: "(i,j) \<in> match" by auto
    then have "j \<in> snd ` match"
      by (auto simp add: rev_image_eqI)
    then have 1: "j < V" using sV by auto  

    thus ?thesis
      using ij 1
      apply auto[1]
      by (metis Pair_inject assms(2) fst_eqD inj_on_def is_matching_def)
  qed

  have 1: "inj_on f {0..<V}"
    unfolding f_def inj_on_def
    apply clarsimp
    apply (drule exuniq)
    apply (drule exuniq)
    by (smt (verit) assms(2) inj_on_def is_matching_def prod.sel(2) prod.simps(1) verit_sko_ex)
  
  have 2: "f \<in> {0..<V} \<rightarrow> {0..<V}"
    unfolding f_def
    apply clarsimp
    apply (drule exuniq)
    by (smt (verit, ccfv_threshold) verit_sko_ex)

  have 1: "f permutes {0..<V}"
    by (intro inj_on_nat_permutes[OF 1 2]) (auto simp: f_def)
  have 2: "i < V \<Longrightarrow> (i, f i) \<in> E" for i
    unfolding f_def
    apply clarsimp
    apply (drule exuniq)
    using assms(2) unfolding is_matching_def subset_iff
    by (smt (verit, ccfv_threshold) verit_sko_ex)
  
  show ?thesis using that 1 2 by auto
qed

lemma Var_not_0:
  shows"Var x \<noteq> (0::'a::idom mpoly)"
  by (simp add: Var_altdef)

(* Copied from Missing_Polynomial.sum_monom_0_iff *)
lemma sum_monom_0_iff:
  assumes fin: "finite S"
  and g: "\<And>i j. i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> g i = g j \<Longrightarrow> i = j"
  shows "sum (\<lambda> i. MPoly_Type.monom (g i) (f i)) S = 0 \<longleftrightarrow> (\<forall> i \<in> S. f i = 0)" (is "?l = ?r")
proof -
  {
    assume "\<not> ?r"
    then obtain i where i: "i \<in> S" and fi: "f i \<noteq> 0" by auto
    let ?g = "\<lambda> i. MPoly_Type.monom (g i) (f i)"
    have "MPoly_Type.coeff (sum ?g S) (g i) =
      f i + sum (\<lambda> j. MPoly_Type.coeff (?g j) (g i)) (S - {i})"
      by (simp add: More_MPoly_Type.coeff_monom sum.remove[OF fin i])
    also have "sum (\<lambda> j. MPoly_Type.coeff (?g j) (g i)) (S - {i}) = 0"
      by (smt (verit, ccfv_threshold) DiffE More_MPoly_Type.coeff_monom assms(2) i insert_iff sum.neutral when_simps(2))
    finally have "MPoly_Type.coeff (sum ?g S) (g i) \<noteq> 0" using fi by auto
    hence "\<not> ?l"
      by fastforce
  }
  thus ?thesis by auto
qed

lemma prod_Var:
  assumes"finite S"
  shows "prod (\<lambda>i. Var(f i)) S =
    MPoly_Type.monom (sum (\<lambda>i. monomial 1 (f i)) S) 1"
  using assms
proof (induction S)
  case empty
  then show ?case
    by auto
next
  case (insert x F)
  then show ?case
    by (auto simp add: Var_altdef MPoly_Type.mult_monom)
qed

lemma det_adj_mat:
  shows "det (adj_mat V E) =
    (\<Sum>p | p permutes {0..<V}.    
    MPoly_Type.monom (
      sum (\<lambda>i.
        monomial 1 (i * V + p i)) {0..<V})
    (if \<forall>i < V. (i,p i) \<in> E then
      of_int (sign p)
    else 0))"
  unfolding det_def
  by (force intro!: sum.cong simp add: adj_mat_def prod_Var monom_uminus sign_def)
  
lemma vars_prod_Var:
  assumes "finite S"
  shows"vars (prod Var S) = S"
  apply (subst prod_Var[OF assms])
  apply (subst vars_monom_keys)
  subgoal
    by simp
  apply (subst keys_sum[OF assms])
  by auto

lemma prod_Var_eq:
  assumes "finite S" "finite T"
  assumes "prod Var S = prod Var T"
  shows "S = T"
  using assms vars_prod_Var
  by metis

lemma pair_enc_eq:
  assumes " a * V + b = c * V + d"
  assumes "b < V" "d < V"
  shows "b = (d::nat)"
  by (metis div_eq_0_iff add_right_cancel assms(1) assms(2) assms(3) diff_add_inverse div_mult_self3 mult_eq_0_iff)

lemma sum_monomial_eq:
  assumes"f permutes {0..<V}"
  assumes"g permutes {0..<V}"
  assumes "
    (\<Sum>i = 0..<V.
      monomial (1::nat) (i * V + (f i::nat))) =
    (\<Sum>i = 0..<V.
      monomial (1::nat) (i * V + g i))"
  shows "f = g"
proof -
  have injf: "inj_on (\<lambda>i. i * V + f i) {0..<V}"
    by (intro inj_onI, unfold atLeastLessThan_iff)
       (metis add_diff_cancel_right' assms(1) div_mult_self_is_m le_less_trans pair_enc_eq permutes_less(1))
    
  have injg:"inj_on (\<lambda>i. i * V + g i) {0..<V}"
    by (intro inj_onI, unfold atLeastLessThan_iff)
       (metis add_diff_cancel_right' assms(2) div_mult_self_is_m le_less_trans pair_enc_eq permutes_less(1))
    
  have "MPoly_Type.monom (sum (\<lambda>i. monomial  (1::nat) (i * V + f i)) {0..<V}) 1 =
        MPoly_Type.monom (sum (\<lambda>i. monomial  (1::nat)(i * V + g i)) {0..<V}) 1"
    using assms(3) by auto

  then have "prod (\<lambda>i. Var(i * V + f i)) {0..<V} =
    prod (\<lambda>i. Var(i * V + g i)) {0..<V}"
    by( auto simp add: prod_Var)

  then have "prod Var ((\<lambda>i. i * V + f i) ` {0..<V}) =
             prod Var ((\<lambda>i. i * V + g i) ` {0..<V})"
    by (simp add: prod.reindex[OF injf] prod.reindex[OF injg])

  then have *: "((\<lambda>i. i * V + f i) ` {0..<V}) =
    ((\<lambda>i. i * V + g i) ` {0..<V})"
    by (intro prod_Var_eq) auto
  have "\<And>i. f i = g i"
  proof -
    fix i
    have " i < V \<or> i \<ge> V" by auto
    moreover {
      assume iV:"i < V"
      then have fiV:"f i < V"
        using iV assms(1) permutes_less(1) by blast
      have "(i * V + f i) \<in> ((\<lambda>i. i * V + g i) ` {0..<V})"
        using iV * by force
      then have "f i = g i"
        apply (safe)
        apply (unfold atLeastLessThan_iff)
        by (metis add_diff_cancel_right' assms(2) basic_trans_rules(21) div_mult_self_is_m fiV pair_enc_eq permutes_less(1))
    }
    moreover {
      assume "i \<ge> V"
      have "f i = g i" using assms(1-2)
        by (metis atLeastLessThan_iff calculation(2) permutes_others)
    }
    ultimately show "f i = g i" by auto
  qed
  thus ?thesis by auto
qed

lemma perfect_matching_det:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "is_matching E match"
  assumes "card match = V"
  shows"det (adj_mat V E) \<noteq> 0"
proof -
  have det: "det (adj_mat V E) =
     (\<Sum>p | p permutes {0..<V}.    
    MPoly_Type.monom (
      sum (\<lambda>i.
        monomial 1 (i * V + p i)) {0..<V})
    (if \<forall>i < V. (i,p i) \<in> E then
      of_int (sign p)
    else 0))"
    unfolding det_adj_mat
    by auto
  from is_matching_permutes[OF assms(1-3)]
  obtain p where p: "p permutes {0..<V}"
      "\<And>i. i < V \<Longrightarrow> (i, p i) \<in> E"  by auto
  then have iV: "i < V \<Longrightarrow>
    adj_mat V E $$ (i, p i) \<noteq> 0" for i
    unfolding adj_mat_def
    by (subst index_mat) (auto simp add: Var_not_0)
  have *: "of_int (sign p) * (\<Prod>i = 0..<V. adj_mat V E $$ (i, p i)) \<noteq> 0"
    by (rule ccontr) (use iV in auto)

  have "det (adj_mat V E) \<noteq> 0"
    unfolding det
    apply (subst sum_monom_0_iff)
    subgoal
      by (auto intro!: finite_permutations)
    subgoal
      by (auto intro!: sum_monomial_eq)
    subgoal
      using p by (auto intro!: sum_monomial_eq)
    done
  thus ?thesis by auto
qed

lemma det_perfect_matching:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "det (adj_mat V E) \<noteq> 0"
  obtains match where
    "is_matching E match"
    "card match = V"
proof -
  have det: "det (adj_mat V E) =
    (\<Sum>p | p permutes {0..<V}.
       of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i)))"
    unfolding det_def
    by auto
  then have "... \<noteq> 0" using assms(2) by auto
  then obtain p where p: "p permutes {0..<V}"
    "of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i)) \<noteq> 0"
    by (metis (no_types, lifting) mem_Collect_eq sum.not_neutral_contains_not_neutral)
  have "\<And>i. i < V \<Longrightarrow>  adj_mat V E $$ (i, p i) \<noteq> 0"
    using p(2)
    by simp
  then have iV: "\<And>i. i < V \<Longrightarrow>  (i, p i) \<in> E"
    unfolding adj_mat_def
    by (smt (verit, del_insts) index_mat(1) p(1) permutes_less(1) prod.simps(2))

  define match where "match = (\<lambda>i. (i,p i)) ` {0..<V}"
  have 1:"card match = V" unfolding match_def
    apply (subst card_image)
    unfolding inj_on_def by auto
  have "inj_on p {0..<V}"
    using p(1) permutes_inj_on
    by blast
  hence 2:"inj_on fst match" "inj_on snd match"
    unfolding match_def
    by (auto simp add: inj_on_def)
  have 3: "match \<subseteq> E"
    using iV unfolding match_def
    by auto
  show ?thesis using that 1 2 3
    unfolding is_matching_def by auto
qed

lemma has_perfect_matching_iff:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  shows"has_perfect_matching V E \<longleftrightarrow> det (adj_mat V E) \<noteq> 0"
  by (metis assms det_perfect_matching has_perfect_matching_def perfect_matching_det)

lemma sum_when_1:
  assumes "finite S" "x \<in> S"
  shows   "(\<Sum>xa\<in>S. 1 when xa = x) = 1"
  by (simp add: assms(1) assms(2) when_def)

lemma total_degree_monom:
  assumes "finite S"
  shows "total_degree (MPoly_Type.monom (sum (\<lambda>i. monomial (Suc 0) i) S) c) =
           (if c = 0 then 0 else card S)"
proof -
  have "(\<Sum>x\<in>keys (sum (monomial (Suc 0)) S). \<Sum>xa\<in>S. Suc 0 when xa = x) = card S"
    using assms by (subst keys_sum) (auto simp add: when_def)
  thus ?thesis
    unfolding MPoly_Type.monom_def by (simp add: total_degree.abs_eq lookup_sum single.rep_eq)
qed

lemma total_degree_geI:
  assumes "m \<in> keys (mapping_of p)" "(\<Sum>v\<in>keys m. lookup m v) \<ge> n"
  shows   "total_degree p \<ge> n"
proof -
  have "n \<le> Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of p)))"
    using assms by (subst Max_ge_iff) auto
  thus ?thesis
    by (simp add: total_degree_def)
qed

lemma total_degree_0_iff: "total_degree p = 0 \<longleftrightarrow> vars p = {}"
proof
  assume "total_degree p = 0"
  show   "vars p = {}"
  proof safe
    fix x assume "x \<in> vars p"
    then obtain m where m: "m \<in> keys (mapping_of p)" "lookup m x > 0"
      unfolding vars_def by blast
    from m have "x \<in> keys m"
      by (simp add: in_keys_iff)
    note m(2)
    also have "lookup m x \<le> (\<Sum>v\<in>keys m. lookup m v)"
      by (rule member_le_sum) (use \<open>x \<in> keys m\<close> in auto)
    also have "\<dots> \<le> total_degree p"
      by (intro total_degree_geI) (use m(1) in auto)
    finally show "x \<in> {}"
      using \<open>total_degree p = 0\<close> by simp
  qed
next
  assume "vars p = {}"
  hence "keys (mapping_of p) \<subseteq> {0}"
    by (simp add: subset_eq vars_def)
  also have "(\<lambda>m. sum (lookup m) (keys m)) ` {0} = {0}"
    by auto
  finally have *: "insert 0 ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of p)) = {0}"
    by fast
  show "total_degree p = 0"
    unfolding total_degree_def map_fun_def id_def o_def * by simp
qed

lemma total_degree_0E: "total_degree p = 0 \<Longrightarrow> (\<And>c. p = Const c \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding total_degree_0_iff using vars_empty_iff[of p] by blast

lemma total_degree_ex:
  assumes "p \<noteq> 0"
  shows   "\<exists>m. m \<in> keys (mapping_of p) \<and> (\<Sum>v\<in>keys m. lookup m v) = total_degree p"
proof (cases "total_degree p = 0")
  case True
  thus ?thesis
    using assms by (auto elim!: total_degree_0E simp: Const.rep_eq keys_Const\<^sub>0)
next
  case False
  have "total_degree p \<in> insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of p))"
    unfolding total_degree_def map_fun_def o_def id_def by (rule Max_in) auto
  with False show ?thesis
    by auto
qed

lemma coeff_times_const_left [simp]: "MPoly_Type.coeff (Const c * p) m = c * MPoly_Type.coeff p m"
  by (metis Symmetric_Polynomials.coeff_smult smult_conv_mult_Const)

lemma total_degree_times_const_left: "total_degree (Const c * p) \<le> total_degree p"
proof (cases "Const c * p = 0")
  case False
  then obtain m where m:
    "m \<in> keys (mapping_of (Const c * p))" "sum (lookup m) (keys m) = total_degree (Const c * p)"
    using total_degree_ex by blast
  have "MPoly_Type.coeff (Const c * p) m \<noteq> 0"
    using m(1) coeff_keys by blast
  hence "MPoly_Type.coeff p m \<noteq> 0"
    by auto
  hence "m \<in> keys (mapping_of p)"
    using coeff_keys by blast
  with m(2) show ?thesis
    by (intro total_degree_geI[of m]) auto
qed auto

lemma total_degree_of_Const [simp]: "total_degree (Const x) = 0"
  by (simp add: total_degree_0_iff)

lemma total_degree_of_int [simp]: "total_degree (of_int x) = 0"
  by (metis monom_of_int mpoly_monom_0_eq_Const total_degree_of_Const)

lemma total_degree_det_adj_mat: "total_degree (det (adj_mat V E)) \<le> V"
proof -
  have fp:"finite {p. p permutes {0..<V}}"
    by (intro finite_permutations) auto
  have det: "det (adj_mat V E) =
    (\<Sum>p | p permutes {0..<V}.    
    MPoly_Type.monom (
      sum (\<lambda>i.
        monomial (Suc 0) (i * V + p i)) {0..<V})
    (if \<forall>i < V. (i,p i) \<in> E then
      of_int (sign p)
    else 0))" (is "_ = (\<Sum>p | p permutes {0..<V}. ?f p)")
    unfolding det_adj_mat
    by auto

  have *: "total_degree (?f p) \<le> V" if p: "p permutes {0..<V}" for p
  proof -
    have inj: "inj_on (\<lambda>i. i * V + p i) {0..<V}"
        apply (intro inj_onI)
        apply (unfold atLeastLessThan_iff)
        using p by (metis pair_enc_eq permutes_less(1) permutes_less(4))
    have "total_degree (?f p) =
          total_degree 
            (MPoly_Type.monom (sum (monomial (Suc 0)) ((\<lambda>i. i * V + p i)`{0..<V}))
            (if \<forall>i<V. (i, p i) \<in> E then sign p else 0))"
      by (subst sum.reindex[OF inj]) auto
    also have "\<dots> \<le> V"
      by (subst total_degree_monom) (simp_all add: card_image[OF inj])
    finally show ?thesis .
  qed
    
  have "total_degree (det(adj_mat V E)) \<le>
    Max ((total_degree \<circ> ?f) `{p. p permutes{0..<V}})"
    unfolding det
    using total_degree_sum[OF fp, of ?f]
    by auto
  moreover have "... \<le> V"
    apply (intro Max.boundedI)
    subgoal
      using fp by blast
    subgoal
      unfolding permutes_def by force
    subgoal
      using * by force
    done
  ultimately show ?thesis
    by auto
qed

lemma arith:
  assumes "i < V"
  assumes "j < (V::nat)"
  shows "i * V + j < V^2"
  by (smt (verit, ccfv_SIG) div_eq_0_iff add.right_neutral assms(1) 
         assms(2) div_less_iff_less_mult div_mult_self3 le_add1 le_add_same_cancel1 
         order_trans_rules(21) power2_eq_square)

lemma vars_det_adj_mat:
  shows"vars (det (adj_mat V E)) \<subseteq> {0..<V^2}"
proof -
  have det: "det (adj_mat V E) =
    (\<Sum>p | p permutes {0..<V}.
       of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i)))"
    unfolding det_def
    by auto
  have *: "\<And>p. p permutes {0..<V} \<Longrightarrow>
    vars (of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i))) \<subseteq> {0..<V^2}"
  proof -
    fix p
    assume "p permutes {0..<V}"
    then have *: "i < V \<Longrightarrow>
      vars (adj_mat V E $$ (i, p i)) \<subseteq> {0..<V^2}" for i
      unfolding adj_mat_def using arith
      by (auto simp add: vars_Var)

    have "vars (of_int (sign p) *
       (\<Prod>i = 0..<V. adj_mat V E $$ (i, p i))) \<subseteq>
      vars (\<Prod>i = 0..<V. adj_mat V E $$ (i, p i))"
      using vars_mult vars_signof by blast
    moreover have "... \<subseteq> (\<Union>i\<in>{0..<V}. vars (adj_mat V E $$ (i, p i)))"
      using vars_prod by auto
    moreover have "... \<subseteq> {0..<V^2}" using *
      by fastforce
    ultimately show " vars (of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i))) \<subseteq> {0..<V^2}" by auto
  qed
  have "vars (det(adj_mat V E)) \<subseteq>
    (\<Union>p \<in> {p. p permutes {0..<V}}.
       vars (of_int (sign p) *
       (\<Prod>i = 0..<V.
           adj_mat V E $$ (i, p i))))
    " unfolding det_def
    by (simp add: vars_sum)
  thus ?thesis using *  
    by auto
qed

definition int_adj_mat::"
  (nat \<Rightarrow> int) \<Rightarrow>
  nat \<Rightarrow>
  (nat \<times> nat) set \<Rightarrow>
  int mat"
  where "int_adj_mat f V E =
    mat V V (\<lambda>(i,j).
      if (i,j) \<in> E then f (i* V + j) else 0)"

lemma map_mat_prod_def:
  shows"map_mat f A \<equiv>
    Matrix.mat (dim_row A) (dim_col A)
     (\<lambda>(i,j). f (A $$ (i,j)))"
  by (smt (verit, best) cong_mat map_mat_def split_conv)
    
lemma int_adj_mat:
  shows"int_adj_mat f V E =
    map_mat (insertion f) (adj_mat V E)"
  unfolding adj_mat_def int_adj_mat_def
    map_mat_prod_def
  by auto

lemma det_int_adj_mat:
  shows"det(int_adj_mat f V E) =
    insertion f (det (adj_mat V E))"
  unfolding int_adj_mat
  by (subst comm_ring_hom.hom_det) (auto simp add:comm_ring_hom_insertion)

definition test_perfect_matching :: "int \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool pmf"
  where "test_perfect_matching n V E =
     do {
       f \<leftarrow> Pi_pmf ({0..<V^2}) 0 (\<lambda>i. pmf_of_set {0::int..<n});
       return_pmf (det (int_adj_mat f V E) \<noteq> 0)
     }"

theorem test_perfect_matching_false_positive:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "\<not>has_perfect_matching V E"
  shows   "pmf (test_perfect_matching n V E) True = 0"
proof -
  have "det (adj_mat V E) = 0"
    using assms(1) assms(2) has_perfect_matching_iff by blast
  thus ?thesis
    unfolding test_perfect_matching_def pmf_eq_0_set_pmf det_int_adj_mat
    by auto
qed

lemma test_perfect_matching_true_negative:
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "\<not>has_perfect_matching V E"
  shows   "pmf (test_perfect_matching n V E) False = 1"
  by (metis assms(1) assms(2) pmf_True_conv_False right_minus_eq test_perfect_matching_false_positive)

theorem test_perfect_matching_false_negative:
  assumes "(n::nat) > 0"
  assumes "E \<subseteq> {0..<V} \<times> {0..<V}"
  assumes "has_perfect_matching V E"
  shows   "pmf (test_perfect_matching n V E) False \<le> V / n"
proof -
  have d: "det (adj_mat V E) \<noteq> 0"
    using assms has_perfect_matching_iff by blast
  have "pmf (test_perfect_matching n V E) False =
          prob_space.prob (test_perfect_matching n V E) {False}"
    by (simp add: pmf.rep_eq)
  moreover have "... =
    prob_space.prob
    (map_pmf (\<lambda>f. det (int_adj_mat f V E) \<noteq> 0)
      (Pi_pmf {0..<V\<^sup>2} 0 (\<lambda>i. pmf_of_set {0..<int n})))
    {False}"
    unfolding test_perfect_matching_def map_pmf_def
    by auto
  moreover have "... =
    prob_space.prob
    (Pi_pmf {0..<V\<^sup>2} 0 (\<lambda>i. pmf_of_set {0..<int n}))
    {f. insertion f (det (adj_mat V E)) = 0}"
    unfolding measure_map_pmf vimage_def
    det_int_adj_mat
    by auto
  moreover have "... \<le> real V / card{0..<int n}"
    by (intro schwartz_zippel[OF _ _ _  total_degree_det_adj_mat d vars_det_adj_mat])
       (auto simp add: assms(1-2))
  moreover have "... \<le> V / n"
    using assms(1) by force
  ultimately show ?thesis by auto
qed

end
