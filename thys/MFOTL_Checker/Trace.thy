(*<*)
theory Trace
  imports "MFOTL_Monitor.Interval" "HOL-Library.Stream"
begin
(*>*)

section \<open>Traces and Trace Prefixes\<close>

subsection \<open>Infinite Traces\<close>

coinductive ssorted :: "'a :: linorder stream \<Rightarrow> bool" where
  "shd s \<le> shd (stl s) \<Longrightarrow> ssorted (stl s) \<Longrightarrow> ssorted s"

lemma ssorted_siterate[simp]: "(\<And>n. n \<le> f n) \<Longrightarrow> ssorted (siterate f n)"
  by (coinduction arbitrary: n) auto

lemma ssortedD: "ssorted s \<Longrightarrow> s !! i \<le> stl s !! i"
  by (induct i arbitrary: s) (auto elim: ssorted.cases)

lemma ssorted_sdrop: "ssorted s \<Longrightarrow> ssorted (sdrop i s)"
  by (coinduction arbitrary: i s) (auto elim: ssorted.cases ssortedD)

lemma ssorted_monoD: "ssorted s \<Longrightarrow> i \<le> j \<Longrightarrow> s !! i \<le> s !! j"
proof (induct "j - i" arbitrary: j)
  case (Suc x)
  from Suc(1)[of "j - 1"] Suc(2-4) ssortedD[of s "j - 1"]
    show ?case by (cases j) (auto simp: le_Suc_eq Suc_diff_le)
qed simp

lemma sorted_stake: "ssorted s \<Longrightarrow> sorted (stake i s)"
  by (induct i arbitrary: s)
    (auto elim: ssorted.cases simp: in_set_conv_nth
      intro!: ssorted_monoD[of _ 0, simplified, THEN order_trans, OF _ ssortedD])

lemma ssorted_monoI: "\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j \<Longrightarrow> ssorted s"
  by (coinduction arbitrary: s)
    (auto dest: spec2[of _ "Suc _" "Suc _"] spec2[of _ 0 "Suc 0"])

lemma ssorted_iff_mono: "ssorted s \<longleftrightarrow> (\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j)"
  using ssorted_monoI ssorted_monoD by metis

lemma ssorted_iff_le_Suc: "ssorted s \<longleftrightarrow> (\<forall>i. s !! i \<le> s !! Suc i)"
  using mono_iff_le_Suc[of "snth s"] by (simp add: mono_def ssorted_iff_mono)

definition "sincreasing s = (\<forall>x. \<exists>i. x < s !! i)"

lemma sincreasingI: "(\<And>x. \<exists>i. x < s !! i) \<Longrightarrow> sincreasing s"
  by (simp add: sincreasing_def)

lemma sincreasing_grD:
  fixes x :: "'a :: semilattice_sup"
  assumes "sincreasing s"
  shows "\<exists>j>i. x < s !! j"
proof -
  let ?A = "insert x {s !! n | n. n \<le> i}"
  from assms obtain j where *: "Sup_fin ?A < s !! j"
    by (auto simp: sincreasing_def)
  then have "x < s !! j"
    by (rule order.strict_trans1[rotated]) (auto intro: Sup_fin.coboundedI)
  moreover have "i < j"
  proof (rule ccontr)
    assume "\<not> i < j"
    then have "s !! j \<in> ?A" by (auto simp: not_less)
    then have "s !! j \<le> Sup_fin ?A"
      by (auto intro: Sup_fin.coboundedI)
    with * show False by simp
  qed
  ultimately show ?thesis by blast
qed

lemma sincreasing_siterate_nat[simp]:
  fixes n :: nat
  assumes "(\<And>n. n < f n)"
  shows "sincreasing (siterate f n)"
unfolding sincreasing_def proof
  fix x
  show "\<exists>i. x < siterate f n !! i"
  proof (induction x)
    case 0
    have "0 < siterate f n !! 1"
      using order.strict_trans1[OF le0 assms] by simp
    then show ?case ..
  next
    case (Suc x)
    then obtain i where "x < siterate f n !! i" ..
    then have "Suc x < siterate f n !! Suc i"
      using order.strict_trans1[OF _ assms] by (simp del: snth.simps)
    then show ?case ..
  qed
qed

lemma sincreasing_stl: "sincreasing s \<Longrightarrow> sincreasing (stl s)" for s :: "'a :: semilattice_sup stream"
  by (auto 0 4 simp: gr0_conv_Suc intro!: sincreasingI dest: sincreasing_grD[of s 0])

definition "sfinite s = (\<forall>i. finite (s !! i))"

lemma sfiniteI: "(\<And>i. finite (s !! i)) \<Longrightarrow> sfinite s"
  by (simp add: sfinite_def)

typedef 'a trace = "{s :: ('a set \<times> nat) stream. ssorted (smap snd s) \<and> sincreasing (smap snd s) \<and> sfinite (smap fst s)}"
  by (intro exI[of _ "smap (\<lambda>i. ({}, i)) nats"])
    (auto simp: stream.map_comp stream.map_ident sfinite_def cong: stream.map_cong)

setup_lifting type_definition_trace

lift_definition \<Gamma> :: "'a trace \<Rightarrow> nat \<Rightarrow> 'a set" is
  "\<lambda>s i. fst (s !! i)" .
lift_definition \<tau> :: "'a trace \<Rightarrow> nat \<Rightarrow> nat" is
  "\<lambda>s i. snd (s !! i)" .

lemma stream_eq_iff: "s = s' \<longleftrightarrow> (\<forall>n. s !! n = s' !! n)"
  by (metis stream.map_cong0 stream_smap_nats)

lemma trace_eqI: "(\<And>i. \<Gamma> \<sigma> i = \<Gamma> \<sigma>' i) \<Longrightarrow> (\<And>i. \<tau> \<sigma> i = \<tau> \<sigma>' i) \<Longrightarrow> \<sigma> = \<sigma>'"
  by transfer (auto simp: stream_eq_iff intro!: prod_eqI)

lemma \<tau>_mono[simp]: "i \<le> j \<Longrightarrow> \<tau> s i \<le> \<tau> s j"
  by transfer (auto simp: ssorted_iff_mono)

lemma ex_le_\<tau>: "\<exists>j\<ge>i. x \<le> \<tau> s j"
  by (transfer fixing: i x) (auto dest!: sincreasing_grD[of _ i x] less_imp_le)

lemma le_\<tau>_less: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j \<Longrightarrow> j < i \<Longrightarrow> \<tau> \<sigma> i = \<tau> \<sigma> j"
  by (simp add: antisym)

lemma less_\<tau>D: "\<tau> \<sigma> i < \<tau> \<sigma> j \<Longrightarrow> i < j"
  by (meson \<tau>_mono less_le_not_le not_le_imp_less)

abbreviation "\<Delta> s i \<equiv> \<tau> s i - \<tau> s (i - 1)"

subsection \<open>Finite Trace Prefixes\<close>

typedef 'a prefix = "{p :: ('a set \<times> nat) list. sorted (map snd p)}"
  by (auto intro!: exI[of _ "[]"])

setup_lifting type_definition_prefix

lift_definition pmap_\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a prefix \<Rightarrow> 'b prefix" is
  "\<lambda>f. map (\<lambda>(x, i). (f x, i))"
  by (simp add: split_beta comp_def)

lift_definition last_ts :: "'a prefix \<Rightarrow> nat" is
  "\<lambda>p. (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p))" .

lift_definition first_ts :: "nat \<Rightarrow> 'a prefix \<Rightarrow> nat" is
  "\<lambda>n p. (case p of [] \<Rightarrow> n | _ \<Rightarrow> snd (hd p))" .

lift_definition pnil :: "'a prefix" is "[]" by simp

lift_definition plen :: "'a prefix \<Rightarrow> nat" is "length" .

lift_definition psnoc :: "'a prefix \<Rightarrow> 'a set \<times> nat \<Rightarrow> 'a prefix" is
  "\<lambda>p x. if (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p)) \<le> snd x then p @ [x] else []"
proof (goal_cases sorted_psnoc)
  case (sorted_psnoc p x)
  then show ?case
    by (induction p) (auto split: if_splits list.splits)
qed

instantiation prefix :: (type) order begin

lift_definition less_eq_prefix :: "'a prefix \<Rightarrow> 'a prefix \<Rightarrow> bool" is
  "\<lambda>p q. \<exists>r. q = p @ r" .

definition less_prefix :: "'a prefix \<Rightarrow> 'a prefix \<Rightarrow> bool" where
  "less_prefix x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof (standard, goal_cases less refl trans antisym)
  case (less x y)
  then show ?case unfolding less_prefix_def ..
next
  case (refl x)
  then show ?case by transfer auto
next
  case (trans x y z)
  then show ?case by transfer auto
next
  case (antisym x y)
  then show ?case by transfer auto
qed

end

lemma psnoc_inject[simp]:
  "last_ts p \<le> snd x \<Longrightarrow> last_ts q \<le> snd y \<Longrightarrow> psnoc p x = psnoc q y \<longleftrightarrow> (p = q \<and> x = y)"
  by transfer auto

lift_definition prefix_of :: "'a prefix \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>p s. stake (length p) s = p" .

lemma prefix_of_pnil[simp]: "prefix_of pnil \<sigma>"
  by transfer auto

lemma plen_pnil[simp]: "plen pnil = 0"
  by transfer auto

lemma plen_mono: "\<pi> \<le> \<pi>' \<Longrightarrow> plen \<pi> \<le> plen \<pi>'"
  by transfer auto

lemma prefix_of_psnocE: "prefix_of (psnoc p x) s \<Longrightarrow> last_ts p \<le> snd x \<Longrightarrow>
  (prefix_of p s \<Longrightarrow> \<Gamma> s (plen p) = fst x \<Longrightarrow> \<tau> s (plen p) = snd x \<Longrightarrow> P) \<Longrightarrow> P"
  by transfer (simp del: stake.simps add: stake_Suc)

lemma le_pnil[simp]: "pnil \<le> \<pi>"
  by transfer auto

lift_definition take_prefix :: "nat \<Rightarrow> 'a trace \<Rightarrow> 'a prefix" is stake
  by (auto dest: sorted_stake)

lemma plen_take_prefix[simp]: "plen (take_prefix i \<sigma>) = i"
  by transfer auto

lemma plen_psnoc[simp]: "last_ts \<pi> \<le> snd x \<Longrightarrow> plen (psnoc \<pi> x) = plen \<pi> + 1"
  by transfer auto

lemma prefix_of_take_prefix[simp]: "prefix_of (take_prefix i \<sigma>) \<sigma>"
  by transfer auto

lift_definition pdrop :: "nat \<Rightarrow> 'a prefix \<Rightarrow> 'a prefix" is drop
  by (auto simp: drop_map[symmetric] sorted_wrt_drop)

lemma pdrop_0[simp]: "pdrop 0 \<pi> = \<pi>"
  by transfer auto

lemma prefix_of_antimono: "\<pi> \<le> \<pi>' \<Longrightarrow> prefix_of \<pi>' s \<Longrightarrow> prefix_of \<pi> s"
  by transfer (auto simp del: stake_add simp add: stake_add[symmetric])

lemma prefix_of_imp_linear: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi>' \<sigma> \<Longrightarrow> \<pi> \<le> \<pi>' \<or> \<pi>' \<le> \<pi>"
proof transfer
  fix \<pi> \<pi>' and \<sigma> :: "('a set \<times> nat) stream"
  assume assms: "stake (length \<pi>) \<sigma> = \<pi>" "stake (length \<pi>') \<sigma> = \<pi>'"
  show "(\<exists>r. \<pi>' = \<pi> @ r) \<or> (\<exists>r. \<pi> = \<pi>' @ r)"
  proof (cases "length \<pi>" "length \<pi>'" rule: le_cases)
    case le
    then have "\<pi>' = take (length \<pi>) \<pi>' @ drop (length \<pi>) \<pi>'"
      by simp
    moreover have "take (length \<pi>) \<pi>' = \<pi>"
      using assms le by (metis min.absorb1 take_stake)
    ultimately show ?thesis by auto
  next
    case ge
    then have "\<pi> = take (length \<pi>') \<pi> @ drop (length \<pi>') \<pi>"
      by simp
    moreover have "take (length \<pi>') \<pi> = \<pi>'"
      using assms ge by (metis min.absorb1 take_stake)
    ultimately show ?thesis by auto
  qed
qed

lemma \<tau>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<tau> s i = \<tau> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma \<Gamma>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<Gamma> s i = \<Gamma> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma sincreasing_sdrop:
  fixes s :: "('a :: semilattice_sup) stream"
  assumes "sincreasing s"
  shows "sincreasing (sdrop n s)"
proof (rule sincreasingI)
  fix x
  obtain i where "n < i" and "x < s !! i"
    using sincreasing_grD[OF assms] by blast
  then have "x < sdrop n s !! (i - n)"
    by (simp add: sdrop_snth)
  then show "\<exists>i. x < sdrop n s !! i" ..
qed

lemma ssorted_shift:
  "ssorted (xs @- s) = (sorted xs \<and> ssorted s \<and> (\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y))"
proof safe
  assume *: "ssorted (xs @- s)"
  then show "sorted xs"
    by (auto simp: ssorted_iff_mono shift_snth sorted_iff_nth_mono split: if_splits)
  from ssorted_sdrop[OF *, of "length xs"] show "ssorted s"
    by (auto simp: sdrop_shift)
  fix x y assume "x \<in> set xs" "y \<in> sset s"
  then obtain i j where "i < length xs" "xs ! i = x" "s !! j = y"
    by (auto simp: set_conv_nth sset_range)
  with ssorted_monoD[OF *, of i "j + length xs"] show "x \<le> y" by auto
next
  assume "sorted xs" "ssorted s" "\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y"
  then show "ssorted (xs @- s)"
  proof (coinduction arbitrary: xs s)
    case (ssorted xs s)
    with \<open>ssorted s\<close> show ?case
      by (subst (asm) ssorted.simps) (auto 0 4 simp: neq_Nil_conv shd_sset intro: exI[of _ "_ # _"])
  qed
qed

lemma sincreasing_shift:
  assumes "sincreasing s"
  shows "sincreasing (xs @- s)"
proof (rule sincreasingI)
  fix x
  from assms obtain i where "x < s !! i"
    unfolding sincreasing_def by blast
  then have "x < (xs @- s) !! (length xs + i)"
    by simp
  then show "\<exists>i. x < (xs @- s) !! i" ..
qed

lift_definition pts :: "'a prefix \<Rightarrow> nat list" is "map snd" .

lemma pts_pmap_\<Gamma>[simp]: "pts (pmap_\<Gamma> f \<pi>) = pts \<pi>"
  by (transfer fixing: f) (simp add: split_beta)

subsection \<open>Earliest and Latest Time-Points\<close>

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"  where
  "ETP \<sigma> t = (LEAST i. \<tau> \<sigma> i \<ge> t)"

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat" where
  "LTP \<sigma> t = Max {i. (\<tau> \<sigma> i) \<le> t}"

abbreviation "\<delta> \<sigma> i j \<equiv> (\<tau> \<sigma> i - \<tau> \<sigma> j)"

abbreviation "ETP_p \<sigma> i b \<equiv> ETP \<sigma> ((\<tau> \<sigma> i) - b)"
abbreviation "LTP_p \<sigma> i I \<equiv> min i (LTP \<sigma> ((\<tau> \<sigma> i) - left I))"
abbreviation "ETP_f \<sigma> i I \<equiv> max i (ETP \<sigma> ((\<tau> \<sigma> i) + left I))"
abbreviation "LTP_f \<sigma> i b \<equiv> LTP \<sigma> ((\<tau> \<sigma> i) + b)"

definition max_opt where
  "max_opt a b = (case (a,b) of (Some x, Some y) \<Rightarrow> Some (max x y) | _ \<Rightarrow> None)"

definition "LTP_p_safe \<sigma> i I = (if \<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0 then LTP_p \<sigma> i I else 0)"

lemma i_ETP_tau: "i \<ge> ETP \<sigma> n \<longleftrightarrow> \<tau> \<sigma> i \<ge> n"
proof
  assume P: "i \<ge> ETP \<sigma> n"
  define j where j_def: "j \<equiv> ETP \<sigma> n"
  then have i_j: "\<tau> \<sigma> i \<ge> \<tau> \<sigma> j" using P by auto
  from j_def have "\<tau> \<sigma> j \<ge> n"
    unfolding ETP_def using LeastI_ex ex_le_\<tau> by force
  then show "\<tau> \<sigma> i \<ge> n" using i_j by auto
next
  assume Q: "\<tau> \<sigma> i \<ge> n"
  then show "ETP \<sigma> n \<le> i" unfolding ETP_def
    by (auto simp add: Least_le)
qed

lemma tau_LTP_k: 
  assumes "\<tau> \<sigma> 0 \<le> n" "LTP \<sigma> n < k"
  shows "\<tau> \<sigma> k > n"
proof -
  have "finite {i. \<tau> \<sigma> i \<le> n}"
    by (rule ccontr, unfold infinite_nat_iff_unbounded_le mem_Collect_eq)
      (metis Suc_le_eq i_ETP_tau  leD)
  then show ?thesis
    using assms(2) Max.coboundedI linorder_not_less
    unfolding LTP_def by auto
qed

lemma i_LTP_tau:
  assumes n_asm: "n \<ge> \<tau> \<sigma> 0"
  shows "(i \<le> LTP \<sigma> n \<longleftrightarrow> \<tau> \<sigma> i \<le> n)"
proof
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume P: "i \<le> LTP \<sigma> n"
  from n_asm A_def have A_ne: "A \<noteq> {}" by auto
  from j_def have i_j: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j" using P by auto
  have not_in: "k \<notin> A" if "j < k" for k
    using n_asm that tau_LTP_k leD
    unfolding A_def j_def by blast
  then have "A \<subseteq> {0..<Suc j}"
    using assms not_less_eq
    unfolding A_def j_def 
    by fastforce
  then have fin_A: "finite A"
    using subset_eq_atLeast0_lessThan_finite[of A "Suc j"]
    by simp
  from A_ne j_def have "\<tau> \<sigma> j \<le> n"
    using Max_in[of A] A_def fin_A 
    unfolding LTP_def 
    by simp
  then show "\<tau> \<sigma> i \<le> n" using i_j by auto
next
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume Q: "\<tau> \<sigma> i \<le> n" 
  have not_in: "k \<notin> A" if "j < k" for k
    using n_asm that tau_LTP_k leD
    unfolding A_def j_def by blast
  then have "A \<subseteq> {0..<Suc j}"
    using assms not_less_eq
    unfolding A_def j_def 
    by fastforce
  then have fin_A: "finite A"
    using subset_eq_atLeast0_lessThan_finite[of A "Suc j"]
    by simp
  moreover have "i \<in> A" using Q A_def by auto
  ultimately show "i \<le> LTP \<sigma> n" 
    using Max_ge[of A] A_def 
    unfolding LTP_def
    by auto
qed

lemma ETP_\<delta>: "i \<ge> ETP \<sigma> (\<tau> \<sigma> l + n) \<Longrightarrow> \<delta> \<sigma> i l \<ge> n"
proof -
  assume P: "i \<ge> ETP \<sigma> (\<tau> \<sigma> l + n)"
  then have "\<tau> \<sigma> i \<ge> \<tau> \<sigma> l + n" by (auto simp add: i_ETP_tau)
  then show ?thesis by auto
qed

lemma ETP_ge: "ETP \<sigma> (\<tau> \<sigma> l + n + 1) > l"
proof -
  define j where j_def: "j \<equiv> \<tau> \<sigma> l + n + 1"
  then have etp_j: "\<tau> \<sigma> (ETP \<sigma> j) \<ge> j" unfolding ETP_def
    using LeastI_ex ex_le_\<tau> by force
  then have "\<tau> \<sigma> (ETP \<sigma> j) > \<tau> \<sigma> l" using j_def by auto
  then show ?thesis using j_def less_\<tau>D by blast
qed

lemma i_le_LTPi: "i \<le> LTP \<sigma> (\<tau> \<sigma> i)"
  using \<tau>_mono i_LTP_tau[of \<sigma> "\<tau> \<sigma> i" i]
  by auto

lemma i_le_LTPi_add: "i \<le> LTP \<sigma> (\<tau> \<sigma> i + n)"
  using i_le_LTPi
  by (simp add: add_increasing2 i_LTP_tau)

lemma i_le_LTPi_minus:
  assumes "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i" "i > 0" "n > 0"
  shows "LTP \<sigma> (\<tau> \<sigma> i - n) < i"
  unfolding LTP_def
proof (subst Max_less_iff; (intro ballI; elim CollectE)?)
  show "finite {j. \<tau> \<sigma> j \<le> \<tau> \<sigma> i - n}"
    unfolding finite_nat_set_iff_bounded_le
  proof (intro exI[of _ i], safe)
    fix j
    assume "\<tau> \<sigma> j \<le> \<tau> \<sigma> i - n"
    with assms(1,3) show "j \<le> i"
      by (metis add_leD2 add_strict_increasing le_add_diff_inverse less_\<tau>D less_or_eq_imp_le)
  qed
next
  from assms(1) show "{j. \<tau> \<sigma> j \<le> \<tau> \<sigma> i - n} \<noteq> {}"
    by (auto simp: le_diff_conv2)
next
  fix j
  assume "\<tau> \<sigma> j \<le> \<tau> \<sigma> i - n"
  with assms(1,3) show "j < i"
    by (metis add_leD2 add_strict_increasing le_add_diff_inverse less_\<tau>D)
qed

lemma i_ge_etpi: "ETP \<sigma> (\<tau> \<sigma> i) \<le> i"
  using i_ETP_tau by auto

(*<*)
end
(*>*)
