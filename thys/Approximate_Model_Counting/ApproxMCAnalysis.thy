section \<open> ApproxMC definition and analysis \<close>

text \<open>
  This section puts together preceding results to formalize the
  PAC guarantee of ApproxMC.
\<close>

theory ApproxMCAnalysis imports
  ApproxMCCoreAnalysis
  RandomXORHashFamily
  Median_Method.Median
begin

lemma replicate_pmf_Pi_pmf:
  assumes "distinct ls"
  shows "replicate_pmf (length ls) P =
    map_pmf (\<lambda>f. map f ls)
      (Pi_pmf (set ls) def (\<lambda>_. P))"
  using assms
proof (induction ls)
  case Nil
  then show ?case
  by auto
next
  case (Cons x xs)
  then show ?case
    by (auto intro!: bind_pmf_cong simp add: Pi_pmf_insert' map_bind_pmf bind_map_pmf)
qed

lemma replicate_pmf_Pi_pmf':
  assumes "finite V"
  shows "replicate_pmf (card V) P =
    map_pmf (\<lambda>f. map f (sorted_list_of_set V))
      (Pi_pmf V def (\<lambda>_. P))"
proof -
  have *:"card V = length (sorted_list_of_set V)"
    using assms by auto
  show ?thesis
    unfolding *
    apply (subst replicate_pmf_Pi_pmf)
    using assms by auto
qed

definition map_of_default::"('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
where "map_of_default ls def =
  (let m = map_of ls in
  (\<lambda>x. case m x of None \<Rightarrow> def | Some v \<Rightarrow> v))"

lemma Pi_pmf_replicate_pmf:
  assumes "finite V"
  shows
    "(Pi_pmf V def (\<lambda>_. p)) =
    map_pmf (\<lambda>bs.
      map_of_default (zip (sorted_list_of_set V) bs) def)
      (replicate_pmf (card V) p)"
proof -
  show ?thesis
   apply (subst replicate_pmf_Pi_pmf'[OF assms, where def="def"])
  unfolding map_pmf_comp
   apply (intro map_pmf_idI[symmetric])
   unfolding map_of_default_def Let_def fun_eq_iff map_of_zip_map
   by (smt (verit, del_insts) assms option.case(1) option.case(2) pmf_Pi pmf_eq_0_set_pmf sorted_list_of_set.set_sorted_key_list_of_set)
qed

lemma proj_inter_neutral:
  assumes "\<And>w. w \<in> B \<longleftrightarrow> restr S w \<in> C"
  shows "proj S (A \<inter> B) = proj S A \<inter> C"
  unfolding ApproxMCCore.proj_def
  using assms by auto

text \<open>
  An abstract spec of ApproxMC for any Boolean theory.
  This locale must be instantiated with a theory implementing the two
  the functions below (and satisfying the assumption linking them).
\<close>
locale ApproxMC =
  fixes sols :: "'fml \<Rightarrow> ('a \<Rightarrow> bool) set"
  fixes enc_xor :: "'a set \<times> bool \<Rightarrow> 'fml \<Rightarrow> 'fml"
  assumes sols_enc_xor:
    "\<And>F xor. finite (fst xor) \<Longrightarrow>
      sols (enc_xor xor F) =
      sols F \<inter> {\<omega>. satisfies_xor xor {x. \<omega> x}}"
begin

definition compute_thresh :: "real \<Rightarrow> nat"
  where "compute_thresh \<epsilon> =
  nat \<lceil>1 + 9.84 * (1 + \<epsilon> / (1 + \<epsilon>)) * (1 + 1 / \<epsilon>)^2\<rceil>"

definition fix_t :: "real \<Rightarrow> nat"
  where "fix_t \<delta> =
  nat \<lceil>ln (1 / \<delta>) /(2 * (0.5-0.36)^2)\<rceil>"

definition raw_median_bound :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "raw_median_bound \<alpha> t =
  (\<Sum>i = 0..t div 2.
    (t choose i) * (1 / 2 + \<alpha>) ^ i * (1 / 2 - \<alpha>) ^ (t - i))"

definition compute_t :: "real \<Rightarrow> nat \<Rightarrow> nat"
  where "compute_t \<delta> n =
  (if raw_median_bound 0.14 n < \<delta> then n
  else fix_t \<delta>)"

(* The size of the projected solution set after adding i XORs*)
definition size_xor ::"
  'fml \<Rightarrow> 'a set \<Rightarrow>
  (nat \<Rightarrow> ('a set \<times> bool) option) \<Rightarrow>
  nat \<Rightarrow> nat"
  where "size_xor F S xorsf i = (
    let xors = map (the \<circ> xorsf) [0..<i] in
    let Fenc = fold enc_xor xors F in
      card (proj S (sols Fenc))
    )"

definition check_xor ::"
  'fml \<Rightarrow> 'a set \<Rightarrow>
  nat \<Rightarrow>
  (nat \<Rightarrow> ('a set \<times> bool) option) \<Rightarrow>
  nat \<Rightarrow> bool"
  where "check_xor F S thresh xorsf i =
  (size_xor F S xorsf i < thresh)"

definition approxcore_xors :: "
  'fml \<Rightarrow> 'a set \<Rightarrow>
  nat \<Rightarrow>
  (nat \<Rightarrow> ('a set \<times> bool) option) \<Rightarrow>
  nat"
  where "
    approxcore_xors F S thresh xorsf =
    (case List.find
      (check_xor F S thresh xorsf) [1..<card S] of
      None \<Rightarrow> 2 ^ card S
    | Some m \<Rightarrow>
      (2 ^ m * size_xor F S xorsf m))"

definition approxmccore :: "'fml \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> nat pmf"
where "approxmccore F S thresh =
  map_pmf (approxcore_xors F S thresh) (random_xors S (card S - 1))"

definition approxmc :: "'fml \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat pmf"
  where "approxmc F S \<epsilon> \<delta> n = (
    let thresh = compute_thresh \<epsilon> in
    if card (proj S (sols F)) < thresh then
      return_pmf (card (proj S (sols F)))
    else
      let t = compute_t \<delta> n in
      map_pmf (median t)
        (prod_pmf {0..<t::nat} (\<lambda>i. approxmccore F S thresh))
  )"

lemma median_commute:
  assumes "t \<ge> 1"
  shows "(real \<circ> median t) = (\<lambda>w::nat \<Rightarrow> nat. median t (real \<circ> w))"
  unfolding median_def map_map[symmetric]
  apply (subst Median.map_sort[where f = "\<lambda>x. real x"])
  subgoal by (clarsimp simp add:mono_def)
  apply (subst nth_map)
  using assms by auto

lemma median_default:
  shows "median t y = median t (\<lambda>x. if x < t then y x else def)"
  unfolding median_def
  by (auto intro!: arg_cong[where f = "\<lambda>ls. sort ls ! (t div 2)"])

definition default_\<alpha>::"'a set \<Rightarrow> nat assg"
  where "default_\<alpha> S i = (if i < card S - 1 then Some True else None)"

lemma dom_default_\<alpha>:
  "dom (default_\<alpha> S) = {0..<card S -1}"
  by (auto simp add:default_\<alpha>_def split: if_splits)

lemma compute_thresh_bound_4:
  assumes "\<epsilon> > 0"
  shows"4 < compute_thresh \<epsilon>"
proof -
  have 1: "(1 + \<epsilon> / (1 + \<epsilon>)) > 1"
    using assms
    by simp
  have 2: "(1 + 1 / \<epsilon>)^2 > 1"
    using assms by simp

  define a where "a = (1 + \<epsilon> / (1 + \<epsilon>)) * (1 + 1 / \<epsilon>)\<^sup>2"
  have "a > 1" unfolding a_def
    using 1 2
    using less_1_mult by blast
  then have "(984 / 10\<^sup>2) * a \<ge> 4"
    by auto

  thus ?thesis
    unfolding compute_thresh_def
    by (smt (verit) a_def arith_special(2) arithmetic_simps(1) more_arith_simps(11) nat_less_real_le numeral_Bit0 of_nat_numeral real_nat_ceiling_ge)
qed

lemma satisfies_xor_with_domain:
  assumes "fst x \<subseteq> S"
  shows "satisfies_xor x {x. w x} \<longleftrightarrow>
    satisfies_xor x ({x. w x} \<inter> S)"
  using assms
  apply (cases x)
  by (simp add: Int_assoc inf.absorb_iff2)

(* The main step, where we instantiate the ApproxMCCore locale *)
lemma approxcore_xors_eq:
  assumes thresh:
    "thresh = compute_thresh \<epsilon>"
    "thresh \<le> card (proj S (sols F))"
  assumes \<epsilon>: "\<epsilon> > (0::real)" "\<epsilon> \<le> 1"
  assumes S: "finite S"
  shows "measure_pmf.prob (random_xors S (card S - 1))
       {xors. real (approxcore_xors F S thresh xors) \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
        (1 + \<epsilon>) * real (card (proj S (sols F)))}} \<ge> 0.64"
proof -

  have "ApproxMCCore (sols F) S \<epsilon> (default_\<alpha> S) thresh"
    apply unfold_locales
    subgoal using dom_default_\<alpha> by simp
    subgoal using \<epsilon> by simp
    subgoal using thresh assms(3) compute_thresh_bound_4 by blast
    using thresh S by auto
  then interpret amc: ApproxMCCore "sols F" _ _ "(default_\<alpha> S)" .

  have "
    m < card S \<Longrightarrow>
    {0..<m} \<subseteq> dom xors \<Longrightarrow>
    (\<And>i. i < m \<Longrightarrow> fst (the (xors i)) \<subseteq> S) \<Longrightarrow>
    (proj S
       (sols (fold enc_xor (map (the \<circ> xors) [0..<m]) F))) =
     proj S (sols F) \<inter>
        {w. hslice m (\<lambda>\<omega>. xor_hash \<omega> xors) w =
          aslice m (default_\<alpha> S)}" for m xors
  proof (induction m)
    case 0
    then show ?case
      unfolding hslice_def aslice_def
      by auto
  next
    case (Suc m)
    have m: "m \<in> dom xors"
      by (meson Set.basic_monos(7) Suc(3) atLeastLessThan_iff le0 lessI)
    have sp: "fst (the (xors m)) \<subseteq> S"
      by (simp add: Suc(4))

    then obtain xor where x: "xors m = Some xor"
      using m by blast

    have eq: "{w. xor_hash w xors m = Some True} =
        {\<omega>. satisfies_xor xor {x. \<omega> x = Some True}}"
      unfolding xor_hash_def
      by (clarsimp simp add: x)

    have neut: "\<And>w.
      w \<in> {\<omega>. satisfies_xor xor {x. \<omega> x}} \<longleftrightarrow>
      restr S w \<in> {\<omega>. satisfies_xor xor {x. \<omega> x = Some True}}"
      using sp unfolding restr_def
      by (smt (verit, ccfv_SIG) Collect_cong Int_def mem_Collect_eq option.sel satisfies_xor_with_domain x)

    have lhs: "
      proj S
       (sols (fold enc_xor (map (the \<circ> xors) [0..<Suc m]) F)) =
      proj S (sols (fold enc_xor (map (the \<circ> xors) [0..<m]) F)) \<inter>
        {w. xor_hash w xors m = Some True}"
      apply clarsimp
      apply (subst sols_enc_xor)
      subgoal using assms(5) rev_finite_subset sp by blast
      apply (subst proj_inter_neutral)
      using eq neut x by auto

    have rhs1:" hslice (Suc m) (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice (Suc m) (default_\<alpha> S) \<Longrightarrow>
      hslice m (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice m (default_\<alpha> S)" for w
      unfolding hslice_def aslice_def fun_eq_iff
      by (auto simp add:lessThan_Suc restrict_map_def split: if_splits)

    have rhs2:"hslice (Suc m) (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice (Suc m) (default_\<alpha> S) \<Longrightarrow>
      xor_hash w xors m = Some True" for w
      unfolding hslice_def aslice_def fun_eq_iff
      apply (clarsimp simp add:lessThan_Suc restrict_map_def )
      by (metis default_\<alpha>_def domIff m xor_hash_eq_dom)

    have rhs3: "hslice m (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice m (default_\<alpha> S) \<Longrightarrow>
      xor_hash w xors m = Some True \<Longrightarrow>
      hslice (Suc m) (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice (Suc m) (default_\<alpha> S)" for w
      unfolding hslice_def aslice_def fun_eq_iff
      apply (clarsimp simp add:lessThan_Suc restrict_map_def )
      by (metis One_nat_def Suc.prems(1) Suc_lessD Suc_less_eq Suc_pred default_\<alpha>_def gr_zeroI zero_less_diff)

    have rhs: "{w. hslice (Suc m) (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice (Suc m) (default_\<alpha> S)} =
      {w. hslice m (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice m (default_\<alpha> S)} \<inter>
      {w. xor_hash w xors m = Some True}"
      by (auto simp add: rhs1 rhs2 rhs3)

    have ih: "proj S (sols (fold enc_xor (map (the \<circ> xors) [0..<m]) F)) =
      proj S (sols F) \<inter>
      {w. hslice m (\<lambda>\<omega>. xor_hash \<omega> xors) w = aslice m (default_\<alpha> S)}"
      apply (intro Suc(1))
      using Suc(2) Suc_lessD apply blast
      using Suc(3) atLeast0_lessThan_Suc apply blast
      using Suc(4) less_SucI by blast

    show ?case
      unfolding lhs rhs
      by (simp add: Int_ac(1) ih)
  qed
  then have *: "
    m < card S \<Longrightarrow>
    {0..<m} \<subseteq> dom xors \<Longrightarrow>
    (\<And>i. i < m \<Longrightarrow> fst (the (xors i)) \<subseteq> S) \<Longrightarrow>
     size_xor F S xors m =
     amc.card_slice (\<lambda>\<omega>. xor_hash \<omega> xors) m" for m xors
    unfolding size_xor_def amc.card_slice_def
    by auto

  have **: "
   {0..<card S - 1} \<subseteq> dom xors \<Longrightarrow>
   (\<And>i. i < card S - 1 \<Longrightarrow> fst (the (xors i)) \<subseteq> S) \<Longrightarrow>
   find (check_xor F S thresh xors) [1..<card S] =
   find (\<lambda>i. (\<lambda>\<omega>. xor_hash \<omega> xors) \<in> amc.T i) [1..<card S]" for xors
    apply (intro find_cong)
    unfolding check_xor_def amc.T_def
    subgoal by simp
    apply (subst *)
      subgoal by clarsimp
      subgoal by (clarsimp simp add: domIff subset_iff)
    by auto

  have rw: "
    {0..<card S - 1} \<subseteq> dom xors \<Longrightarrow>
    (\<And>i. i < card S - 1 \<Longrightarrow> fst (the (xors i)) \<subseteq> S) \<Longrightarrow>
    approxcore_xors F S thresh xors =
      (\<lambda>(a,b). a*b) (amc.approxcore (\<lambda>\<omega>. xor_hash \<omega> xors))" for  xors
    apply (subst amc.approxcore_def)
    unfolding approxcore_xors_def
    apply (subst **)
      subgoal by clarsimp
      subgoal by clarsimp
    apply (clarsimp split: option.split)
    apply (subst *)
    subgoal by (auto simp add: find_Some_iff domIff subset_iff)
    subgoal by (auto simp add: find_Some_iff domIff subset_iff)
    subgoal
      using \<open>\<And>x2. \<lbrakk>{0..<card S - Suc 0} \<subseteq> dom xors; \<And>i. i < card S - Suc 0 \<Longrightarrow> fst (the (xors i)) \<subseteq> S; find (\<lambda>i. (\<lambda>\<omega>. xor_hash \<omega> xors) \<in> amc.T i) [Suc 0..<card S] = Some x2\<rbrakk> \<Longrightarrow> x2 < card S\<close> by auto 
    by auto

  from xor_hash_family_2_universal[OF S]
  have univ:"prob_space.k_universal (measure_pmf (random_xors S (card S - 1))) 2
   xor_hash {\<alpha>. dom \<alpha> = S} {\<alpha>. dom \<alpha> = {0..<card S - 1}}" .

  have "measure_pmf.prob
   (map_pmf (\<lambda>s w. xor_hash w s) (random_xors S (card S - 1)))
   amc.approxcore_fail \<le> 0.36"
    apply (intro amc.analysis_3[OF _ _ univ])
    apply (smt (verit, ccfv_SIG) Groups.mult_ac(3) amc.pivot_def assms(1) compute_thresh_def more_arith_simps(11) real_nat_ceiling_ge)
    using S finite_random_xors_set_pmf apply blast
    using \<epsilon> by auto

  then have b: "measure_pmf.prob
    (random_xors S (card S - 1))
    {xors.
      (real ((\<lambda>(a,b). a*b) (amc.approxcore (\<lambda>\<omega>. xor_hash \<omega> xors))))
      \<notin>
      {real (card (proj S (sols F))) / (1 + \<epsilon>)..
        (1 + \<epsilon>) * real (card (proj S (sols F)))}} \<le> 0.36"
    unfolding amc.approxcore_fail_def
    by (auto simp add: case_prod_unfold Let_def)

  have 1: "x \<in> set_pmf (random_xors S (card S - Suc 0)) \<Longrightarrow>
    {0..<card S - 1} \<subseteq> dom x" for x
    by (auto simp add:random_xors_set_pmf[OF S])
  have 2: "x \<in> set_pmf (random_xors S (card S - Suc 0)) \<Longrightarrow>
    (\<forall>i. i < card S - 1 \<longrightarrow> fst (the (x i)) \<subseteq> S)" for x
  proof -
    assume x: "x \<in> set_pmf (random_xors S (card S - Suc 0))"
    moreover {
      fix i
      assume i: "i < card S - 1"
      from random_xors_set_pmf[OF S]
      have xx: "dom x = {..<(card S - Suc 0)}" "ran x \<subseteq> Pow S \<times> UNIV"
        using x by auto
      obtain xi where xi: "x i = Some xi"
        using xx i apply clarsimp
        by (metis atLeast0LessThan atLeastLessThan_iff bot_nat_0.extremum domIff option.exhaust surj_pair)
      then have "fst xi \<subseteq> S" using xx(2)
        unfolding ran_def apply (clarsimp simp add: subset_iff)
        by (metis prod.collapse)
      then have "fst (the (x i)) \<subseteq> S" by (simp add: xi)
    }
    thus "(\<forall>i. i < card S - 1 \<longrightarrow> fst (the (x i)) \<subseteq> S)" by auto
  qed

  have "measure_pmf.prob (random_xors S (card S - 1))
       {xors. real (approxcore_xors F S thresh xors) \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
        (1 + \<epsilon>) * real (card (proj S (sols F)))}} =
    measure_pmf.prob
    (random_xors S (card S - 1))
    {xors.
      (real ((\<lambda>(a,b). a*b) (amc.approxcore (\<lambda>\<omega>. xor_hash \<omega> xors))))
      \<in>
      {real (card (proj S (sols F))) / (1 + \<epsilon>)..
        (1 + \<epsilon>) * real (card (proj S (sols F)))}}"
    apply (intro measure_pmf.measure_pmf_eq[where p = "(random_xors S (card S - 1))"])
    subgoal by auto
    apply clarsimp
    apply (frule 1)
    apply (drule 2)
    apply (frule rw)
    by auto

  moreover have "... =
     1 - measure_pmf.prob
      (random_xors S (card S - 1))
      {xors.
        (real ((\<lambda>(a,b). a*b) (amc.approxcore (\<lambda>\<omega>. xor_hash \<omega> xors))))
        \<notin>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj S (sols F)))}}"
    apply (subst measure_pmf.prob_compl[symmetric])
    by (auto intro!: measure_pmf.measure_pmf_eq)
  moreover have "... \<ge> 0.64"
    using b
    by auto
  ultimately show ?thesis by auto
qed

lemma compute_t_ge1:
  assumes "0 < \<delta>" "\<delta> < 1"
  shows"compute_t \<delta> n \<ge> 1"
proof -
  have "ln (1 / \<delta>) > 0"
    by (simp add: assms)
  then have fix_t: "1 \<le> fix_t \<delta>"
    unfolding fix_t_def
    by (simp add: Suc_leI)

  show ?thesis
  unfolding compute_t_def
  using fix_t
  apply (cases n)
  unfolding raw_median_bound_def
  using assms by auto
qed

lemma success_arith_bound:
  assumes "s \<le> (f ::nat)"
  assumes "p \<le> (1::real)" "q \<le> p" "1 /2 \<le> q"
  shows "p ^ s * (1 - p) ^ f \<le> q ^ s * (1 - q) ^ f"
proof -
  have ple: "p * (1-p) \<le> q * (1-q)"
    using assms(2-4)
    by (sos "(((A<0 * R<1) + ((R<1 * (R<1 * [p + ~1*q]^2)) + ((A<=1 * (A<=2 * R<1)) * (R<2 * [1]^2)))))")

  have feq:"f = (f-s)+s"
    using Nat.le_imp_diff_is_add assms(1) by blast
  then have "(1-p)^f = (1-p)^s * (1-p)^(f-s)"
    by (metis add.commute power_add)
  then have "p ^ s * (1 - p) ^ f =
    (p * (1-p)) ^ s * (1 - p) ^ (f-s)"
    by (simp add: power_mult_distrib)
  moreover have "... \<le>
    (q * (1-q)) ^ s * (1 - p) ^ (f-s)"
    by (smt (verit) assms(1) assms(2) assms(3) assms(4) diff_self_eq_0 divide_nonneg_nonneg mult_nonneg_nonneg mult_right_mono order_le_less ple power_0 power_eq_0_iff power_mono zero_less_diff zero_less_power)
  moreover have "... \<le>
    (q * (1-q)) ^ s * (1 - q) ^ (f-s)"
    by (smt (verit, ccfv_SIG) assms(2) assms(3) assms(4) divide_eq_0_iff divide_nonneg_nonneg mult_left_mono mult_pos_pos power_mono zero_less_power)
  moreover have "... = q ^ s * (1 - q) ^ f"
    by (smt (verit) feq mult.assoc mult.commute power_add power_mult_distrib)
  ultimately show ?thesis by auto
qed

lemma prob_binomial_pmf_upto_mono:
  assumes "1/2 \<le> q" "q \<le> p" "p \<le> 1"
  shows "
  measure_pmf.prob (binomial_pmf n p) {..n div 2} \<le>
  measure_pmf.prob (binomial_pmf n q) {..n div 2}"
proof -
  have i: "i \<le> n div 2 \<Longrightarrow>
    p ^ i * (1 - p) ^ (n - i) \<le> q ^ i * (1 - q) ^ (n - i)" for i
    using assms by(auto intro!: success_arith_bound)

  show ?thesis
    apply (subst prob_binomial_pmf_upto)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (subst prob_binomial_pmf_upto)
    subgoal using assms by auto
    subgoal using assms by auto
    by (auto intro!: sum_mono simp add: i ab_semigroup_mult_class.mult_ac(1) mult_left_mono)
qed

(* The main result *)
theorem approxmc_sound:
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0" "\<epsilon> \<le> 1"
  assumes S: "finite S"
  shows "measure_pmf.prob (approxmc F S \<epsilon> \<delta> n)
      {c. real c \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj S (sols F)))}}
      \<ge> 1 - \<delta>"
proof -
  define thresh where "thresh = compute_thresh \<epsilon>"
  define t where "t = compute_t \<delta> n"
  then have t1: "1 \<le> t"
    using compute_t_ge1[OF \<delta>] by auto

  have "card (proj S (sols F)) < thresh \<or>
      card (proj S (sols F)) \<ge> thresh" by auto
  moreover {
    assume "card (proj S (sols F)) < thresh"
    then have "approxmc F S \<epsilon> \<delta> n =
      return_pmf (card (proj S (sols F)))"
      unfolding approxmc_def Let_def thresh_def
      by auto
    then have "?thesis"
      unfolding indicator_def of_bool_def
      using assms \<epsilon>
      by (auto simp add: mult_le_cancel_left1 mult_le_cancel_right1 divide_le_eq)
  }
  moreover {
    assume a: "card (proj S (sols F)) \<ge> thresh"
    define Xf where "Xf = (\<lambda>(i::nat) xs.
      approxcore_xors F S thresh (xs i))"

    then have *: "approxmc F S \<epsilon> \<delta> n =
      map_pmf (median t)
      (prod_pmf {0..<t} (\<lambda>i. approxmccore F S thresh))"
      using a
      unfolding approxmc_def Let_def thresh_def t_def
      by auto

    have **: "map_pmf (real \<circ> median t)
      (Pi_pmf {0..<t} (approxcore_xors F S thresh undefined)
       (\<lambda>i. approxmccore F S thresh)) =
       map_pmf (\<lambda>\<omega>. median t (\<lambda>i. real (Xf i \<omega>)))
      (prod_pmf {0..<t} (\<lambda>i. random_xors S (card S - 1)))"
      apply (subst median_commute)
      subgoal using t1 by simp
      unfolding approxmccore_def
       apply (subst Pi_pmf_map)
      unfolding Xf_def by (auto simp add: pmf.map_comp o_def)

    define \<alpha> where "\<alpha> = (0.14 ::real)"
    then have \<alpha>: "\<alpha> > 0" by auto

    have indep:"prob_space.indep_vars
     (measure_pmf
       (prod_pmf {0..<t} (\<lambda>i. random_xors S (card S - 1))))
      (\<lambda>_. borel) (\<lambda>x xa. real (Xf x xa)) {0..<t}"
      unfolding Xf_def
      apply (intro indep_vars_restrict_intro')
      by (auto simp add: restrict_dfl_def)

    have d: "\<delta> \<in> {0<..<1}" using \<delta> by auto

    from approxcore_xors_eq[OF thresh_def a \<epsilon> S]
    have b1: "1 / 2 + \<alpha> \<le>
     measure_pmf.prob (random_xors S (card S - 1))
      {xors.
       real (approxcore_xors F S thresh xors)
       \<in> {real (card (proj S (sols F))) /
           (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
      unfolding \<alpha>_def by auto
    then have b2: "i < t \<Longrightarrow>
      1 / 2 + \<alpha> \<le>
      measure_pmf.prob
         (prod_pmf {0..<t}
           (\<lambda>i. random_xors S (card S - 1)))
         {\<omega> \<in> space
                (measure_pmf
                  (prod_pmf {0..<t}
                    (\<lambda>i. random_xors S (card S - 1)))).
          real (Xf i \<omega>)
          \<in> {real (card (proj S (sols F))) /(1 + \<epsilon>)..
              (1 + \<epsilon>) *real (card (proj S (sols F)))}}" for i
    unfolding Xf_def apply clarsimp
    apply (subst prob_prod_pmf_slice)
    by auto

    have ***: "1 - \<delta>
      \<le> measure_pmf.prob (prod_pmf {0..<t} (\<lambda>i. random_xors S (card S - 1)))
      {\<omega>.
       median t (\<lambda>i. real (Xf i \<omega>))
       \<in> {real (card (proj S (sols F))) /
           (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
    proof -
      have "t = fix_t \<delta> \<or> t = n \<and> raw_median_bound \<alpha> n < \<delta>"
      unfolding t_def compute_t_def \<alpha>_def by auto
      moreover {
        assume "t = fix_t \<delta>"
        then have tb:"- ln \<delta> / (2 * \<alpha>\<^sup>2) \<le> real t"
        unfolding fix_t_def \<alpha>_def
        apply clarsimp
        by (metis assms(1) divide_minus_left inverse_eq_divide ln_inverse real_nat_ceiling_ge)

        from measure_pmf.median_bound_1[OF \<alpha> d indep tb]
        have ?thesis using b2 by auto
      }
      moreover {
        assume *: "t = n" "raw_median_bound \<alpha> n < \<delta>"
        have s: "1 / 2 - \<alpha> = 1 - (1 /2 + \<alpha>)"
          by auto

        have d1: "0 < t" using t1 by linarith
        have d2: "1 / 2 + \<alpha> \<ge> 0" using \<alpha> by auto
        have d3: "interval{x..y::real}" for x y
          unfolding interval_def by auto

        from prob_space.median_bound_raw[OF _ d1 d2 d3 indep b2]
        have "1 -
          measure_pmf.prob (binomial_pmf t (1 / 2 + \<alpha>)) {..t div 2}
          \<le> measure_pmf.prob
              (prod_pmf {0..<t}
                (\<lambda>i. random_xors S (card S - 1)))
              {\<omega>.
               median t (\<lambda>i. real (Xf i \<omega>))
               \<in> {real (card (proj S (sols F))) /
                   (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
          by (auto simp add: prob_space_measure_pmf)

        moreover have "measure_pmf.prob (binomial_pmf t (1 / 2 + \<alpha>)) {..t div 2} \<le> \<delta>"
          by (smt (verit, ccfv_SIG) * b1 d2 measure_pmf.prob_le_1 prob_binomial_pmf_upto raw_median_bound_def s sum.cong)

        ultimately have ?thesis by auto
      }
      ultimately show ?thesis by auto
    qed

    have "measure_pmf.prob (approxmc F S \<epsilon> \<delta> n)
        {c. real c
            \<in> {real (card (proj S (sols F))) /
                (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}} =
      measure_pmf.prob (map_pmf (real \<circ> median t)
        (prod_pmf {0..<t}
         (\<lambda>i. approxmccore F S thresh)))
          {c. c \<in> {real (card (proj S (sols F))) /
                  (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
      using * by auto
    moreover have "... =
      measure_pmf.prob (map_pmf (real \<circ> median t)
      (map_pmf (\<lambda>f x. if x \<in> {0..<t} then f x else undefined) (Pi_pmf {0..<t} (approxcore_xors F S thresh undefined)
       (\<lambda>i. approxmccore F S thresh))))
      {c. c \<in> {real (card (proj S (sols F))) /
                (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
      apply (subst Pi_pmf_default_swap)
      by auto
    moreover have "... =
      measure_pmf.prob (map_pmf (real \<circ> median t)
      (Pi_pmf {0..<t} (approxcore_xors F S thresh undefined)
       (\<lambda>i. approxmccore F S thresh)))
      {c. c \<in> {real (card (proj S (sols F))) /
                (1 + \<epsilon>)..(1 + \<epsilon>) * real (card (proj S (sols F)))}}"
      by (clarsimp simp add: median_default[symmetric])
    moreover have "... \<ge> 1 - \<delta>"
      unfolding **
      using ***
      by auto
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

text \<open> To simplify further analyses, we can remove the (required) upper bound on epsilon. \<close>

definition mk_eps :: "real \<Rightarrow> real"
  where "mk_eps \<epsilon> = (if \<epsilon> > 1 then 1 else \<epsilon>)"

definition approxmc'::"
  'fml \<Rightarrow> 'a set \<Rightarrow>
  real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat pmf"
  where "approxmc' F S \<epsilon> \<delta> n =
    approxmc F S (mk_eps \<epsilon>) \<delta> n"

corollary approxmc'_sound:
  assumes \<delta>: "\<delta> > 0" "\<delta> < 1"
  assumes \<epsilon>: "\<epsilon> > 0"
  assumes S: "finite S"
  shows "prob_space.prob (approxmc' F S \<epsilon> \<delta> n)
      {c. real c \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj S (sols F)))}}
      \<ge> 1 - \<delta>"
proof -
  define \<epsilon>' where "\<epsilon>' = (if \<epsilon> > 1 then 1 else \<epsilon>)"
  have \<epsilon>': "0 < \<epsilon>'" "\<epsilon>' \<le> 1"
    unfolding \<epsilon>'_def using \<epsilon> by auto

  from approxmc_sound[OF \<delta> \<epsilon>' S]
  have *: "prob_space.prob (approxmc F S \<epsilon>' \<delta> n)
      {c. real c \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>')..
          (1 + \<epsilon>') * real (card (proj S (sols F)))}}
      \<ge> 1 - \<delta>" .

  have **: "
    {c. real c \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>')..
          (1 + \<epsilon>') * real (card (proj S (sols F)))}}
    \<subseteq>
    {c. real c \<in>
        {real (card (proj S (sols F))) / (1 + \<epsilon>)..
          (1 + \<epsilon>) * real (card (proj S (sols F)))}}"
    unfolding \<epsilon>'_def
    apply clarsimp
    apply (rule conjI)
    apply (smt (verit) field_sum_of_halves frac_less2 zero_less_divide_iff)
    by (metis (no_types, opaque_lifting) add_le_cancel_left arith_special(3) dual_order.trans less_eq_real_def mult_right_mono of_nat_0_le_iff)

  show ?thesis
    apply (intro order.trans[OF *])
    unfolding approxmc'_def \<epsilon>'_def mk_eps_def
    apply (intro measure_pmf.finite_measure_mono)
    using **[unfolded  \<epsilon>'_def]
    by auto
qed

text \<open> This shows we can lift all randomness to the top-level (i.e., eagerly sample it). \<close>

definition approxmc_map::"
  'fml \<Rightarrow> 'a set \<Rightarrow>
  real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat \<Rightarrow> ('a set \<times> bool) option) \<Rightarrow>
  nat"
  where "approxmc_map F S \<epsilon> \<delta> n xorsFs = (
    let \<epsilon> = mk_eps \<epsilon> in
    let thresh = compute_thresh \<epsilon> in
    if card (proj S (sols F)) < thresh then
      card (proj S (sols F))
    else
      let t = compute_t \<delta> n in
      median t (approxcore_xors F S thresh \<circ> xorsFs))"

lemma approxmc_map_eq:
  shows "
    map_pmf (approxmc_map F S \<epsilon> \<delta> n)
      (Pi_pmf {0..<compute_t \<delta> n} def
         (\<lambda>i. random_xors S (card S - 1))) =
    approxmc' F S \<epsilon> \<delta> n"
proof -
  define def' where "def' = approxcore_xors F S (compute_thresh (mk_eps \<epsilon>)) def"

  have *: "
     map_pmf (median (compute_t \<delta> n))
     (prod_pmf {0..<compute_t \<delta> n}
       (\<lambda>i. map_pmf
              (approxcore_xors F S
                (compute_thresh (mk_eps \<epsilon>)))
              (random_xors S (card S - Suc 0)))) =
     map_pmf (median (compute_t \<delta> n))
     (Pi_pmf {0..<compute_t \<delta> n} def'
       (\<lambda>i. map_pmf
              (approxcore_xors F S
                (compute_thresh (mk_eps \<epsilon>)))
              (random_xors S (card S - Suc 0))))"
    apply (subst Pi_pmf_default_swap[symmetric, where dflt ="undefined", where dflt'="def'"])
    by (auto simp add: map_pmf_comp median_default[symmetric])

  show ?thesis
  unfolding approxmc'_def approxmc_map_def approxmc_def Let_def approxmccore_def
  using def'_def
  by (auto simp add: map_pmf_comp  Pi_pmf_map[of _ _ def] *)
qed

end

end
