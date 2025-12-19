(* License: LGPL *)

section \<open>Expressiveness Prices\<close>

theory Energy
  imports "HOL-Library.Extended_Nat"
begin

text \<open>
  We intend to work on eight-dimensional vectors in an energy game.
  The dimensions will encode expressiveness prices to HML$_\text{SRBB}$ formulas.
  This price is supposed to capture syntactic features needed to describe a certain property and will later be used to select sublogics of specific expressiveness to characterize behavioural equivalences.

  The eight dimensions are intended to measure the following properties of formulas:

   \<^enum> Modal depth (of observations $\langle\alpha\rangle$, $(\alpha)$),
   \<^enum> Depth of branching conjunctions (with one observation clause not starting with $\langle\varepsilon\rangle$),
   \<^enum> Depth of stable conjunctions (that do enforce stability by a $\neg\langle\tau\rangle\top$-conjunct),
   \<^enum> Depth of unstable conjunctions (that do not enforce stability by a $\neg\langle\tau\rangle\top$-conjunct),
   \<^enum> Depth of immediate conjunctions (that are not preceded by $\langle\varepsilon\rangle$),
   \<^enum> Maximal modal depth of positive clauses in conjunctions,
   \<^enum> Maximal modal depth of negative clauses in conjunctions,
   \<^enum> Depth of negations
\<close>

datatype energy =
  E (modal_depth: \<open>enat\<close>) (br_conj_depth: \<open>enat\<close>) (conj_depth: \<open>enat\<close>)
    (st_conj_depth: \<open>enat\<close>) (imm_conj_depth: \<open>enat\<close>)
    (pos_conjuncts: \<open>enat\<close>) (neg_conjuncts: \<open>enat\<close>) (neg_depth: \<open>enat\<close>)

subsection \<open>Comparing and Subtracting Energies\<close>

text \<open>In order to define subtraction on energies, we first lift the orderings
      \<open>\<le>\<close> and \<open><\<close> from \<^type>\<open>enat\<close> to \<^type>\<open>energy\<close>.\<close>
instantiation energy :: order begin

definition \<open>e1 \<le> e2 \<equiv>
  (case e1 of E a1 b1 c1 d1 e1 f1 g1 h1 \<Rightarrow> (
    case e2 of E a2 b2 c2 d2 e2 f2 g2 h2 \<Rightarrow>
      (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2 \<and> g1 \<le> g2 \<and> h1 \<le> h2)
    ))\<close>

definition \<open>(x::energy) < y = (x \<le> y \<and> \<not> y \<le> x)\<close>

instance proof
  fix e1 e2 e3 :: energy
  show \<open>e1 \<le> e1\<close> unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show \<open>e1 \<le> e2 \<Longrightarrow> e2 \<le> e3 \<Longrightarrow> e1 \<le> e3\<close> unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if order_trans)
  show \<open>e1 < e2 = (e1 \<le> e2 \<and> \<not> e2 \<le> e1)\<close> using less_energy_def .
  show \<open>e1 \<le> e2 \<Longrightarrow> e2 \<le> e1 \<Longrightarrow> e1 = e2\<close> unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
qed

lemma leq_components[simp]:
  shows \<open>e1 \<le> e2 \<equiv>
      (modal_depth e1 \<le> modal_depth e2 \<and> br_conj_depth e1 \<le> br_conj_depth e2
      \<and> conj_depth e1 \<le> conj_depth e2 \<and> st_conj_depth e1 \<le> st_conj_depth e2
      \<and> imm_conj_depth e1 \<le> imm_conj_depth e2 \<and> pos_conjuncts e1 \<le> pos_conjuncts e2
      \<and> neg_conjuncts e1 \<le> neg_conjuncts e2 \<and> neg_depth e1 \<le> neg_depth e2)\<close>
  unfolding less_eq_energy_def by (simp add: energy.case_eq_if)

lemma energy_leq_cases:
  assumes
    \<open>modal_depth e1 \<le> modal_depth e2\<close> \<open>br_conj_depth e1 \<le> br_conj_depth e2\<close>
    \<open>conj_depth e1 \<le> conj_depth e2\<close> \<open>st_conj_depth e1 \<le> st_conj_depth e2\<close>
    \<open>imm_conj_depth e1 \<le> imm_conj_depth e2\<close> \<open>pos_conjuncts e1 \<le> pos_conjuncts e2\<close>
    \<open>neg_conjuncts e1 \<le> neg_conjuncts e2\<close> \<open>neg_depth e1 \<le> neg_depth e2\<close>
  shows
    \<open>e1 \<le> e2\<close>
  using assms unfolding leq_components by blast

end

abbreviation somewhere_larger where \<open>somewhere_larger e1 e2 \<equiv> \<not>(e1 \<ge> e2)\<close>

lemma somewhere_larger_eq:
  assumes
    \<open>somewhere_larger e1 e2\<close>
  shows
    \<open>modal_depth e1 < modal_depth e2 \<or> br_conj_depth e1 < br_conj_depth e2
    \<or> conj_depth e1 < conj_depth e2 \<or> st_conj_depth e1 < st_conj_depth e2
    \<or> imm_conj_depth e1 < imm_conj_depth e2 \<or> pos_conjuncts e1 < pos_conjuncts e2
    \<or> neg_conjuncts e1 < neg_conjuncts e2 \<or> neg_depth e1 < neg_depth e2\<close>
  by (smt (z3) assms energy.case_eq_if less_eq_energy_def linorder_le_less_linear)

instantiation energy :: minus
begin

definition minus_energy_def[simp]: \<open>e1 - e2 \<equiv> E
  ((modal_depth e1) - (modal_depth e2))
  ((br_conj_depth e1) - (br_conj_depth e2))
  ((conj_depth e1) - (conj_depth e2))
  ((st_conj_depth e1) - (st_conj_depth e2))
  ((imm_conj_depth e1) - (imm_conj_depth e2))
  ((pos_conjuncts e1) - (pos_conjuncts e2))
  ((neg_conjuncts e1) - (neg_conjuncts e2))
  ((neg_depth e1) - (neg_depth e2))\<close>

instance ..

end

text \<open>Some lemmas to ease the manipulation of expressions using subtraction on energies.\<close>
lemma energy_minus[simp]:
  shows \<open>E a1 b1 c1 d1 e1 f1 g1 h1 - E a2 b2 c2 d2 e2 f2 g2 h2
         = E (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2)
             (e1 - e2) (f1 - f2) (g1 - g2) (h1 - h2)\<close>
  unfolding minus_energy_def somewhere_larger_eq by simp

lemma minus_component_leq:
  assumes
    \<open>s \<le> x\<close>
    \<open>x \<le> y\<close>
  shows
    \<open>modal_depth (x - s) \<le> modal_depth (y - s)\<close>
    \<open>br_conj_depth (x - s) \<le> br_conj_depth (y - s)\<close>
    \<open>conj_depth (x - s) \<le> conj_depth (y - s)\<close>
    \<open>st_conj_depth (x - s) \<le> st_conj_depth (y - s)\<close>
    \<open>imm_conj_depth (x - s) \<le> imm_conj_depth (y - s)\<close>
    \<open>pos_conjuncts (x - s) \<le> pos_conjuncts (y - s)\<close>
    \<open>neg_conjuncts (x - s) \<le> neg_conjuncts (y - s)\<close>
    \<open>neg_depth (x - s) \<le> neg_depth (y - s)\<close>
  using assms by (simp_all) (metis add.commute add_diff_assoc_enat le_iff_add)+

lemma enat_diff_mono:
  assumes \<open>(i::enat) \<le> j\<close>
  shows \<open>i - k \<le> j - k\<close>
proof (cases i)
  case (enat iN)
  show ?thesis
  proof (cases j)
    case (enat jN)
    then show ?thesis
      using assms enat_ile by (cases k, fastforce+)
  next
    case infinity
    then show ?thesis using assms by auto
  qed
next
  case infinity
  hence \<open>j = \<infinity>\<close>
    using assms by auto
  then show ?thesis by auto
qed

text \<open>We further show that the subtraction of energies is decreasing.\<close>
lemma energy_diff_mono:
  fixes s :: energy
  shows \<open>mono_on UNIV (\<lambda>x. x - s)\<close>
  unfolding mono_on_def
  by (auto simp add: enat_diff_mono)

lemma gets_smaller:
  fixes s :: energy
  shows \<open>(\<lambda>x. x - s) x \<le> x\<close>
  by (auto)
     (metis add.commute add_diff_cancel_enat enat_diff_mono idiff_infinity idiff_infinity_right
      le_iff_add not_infinity_eq zero_le)+

lemma mono_subtract:
  assumes \<open>x \<le> x'\<close>
  shows \<open>(\<lambda>x. x - (E a b c d e f g h)) x \<le> (\<lambda>x. x - (E a b c d e f g h)) x'\<close>
  using assms enat_diff_mono by force

text \<open>Abbreviations for performing subtraction in the energy games.\<close>
abbreviation \<open>subtract_fn a b c d e f g h \<equiv>
  (\<lambda>x. if somewhere_larger x (E a b c d e f g h) then None else Some (x - (E a b c d e f g h)))\<close>

abbreviation \<open>subtract a b c d e f g h \<equiv> Some (subtract_fn a b c d e f g h)\<close>

subsection \<open>Minimum Updates\<close>
text \<open>Two energy updates that replace the first component with the minimum of two other components.\<close>
definition \<open>min1_6 e \<equiv> case e of E a b c d e f g h \<Rightarrow> Some (E (min a f) b c d e f g h)\<close>
definition \<open>min1_7 e \<equiv> case e of E a b c d e f g h \<Rightarrow> Some (E (min a g) b c d e f g h)\<close>

text \<open>Abbreviations for identity update.\<close>
abbreviation \<open>id_up \<equiv> Some Some\<close>

text \<open>lift order to options\<close>
instantiation option :: (order) order
begin

definition less_eq_option_def[simp]:
  \<open>less_eq_option (optA :: 'a option) optB \<equiv>
    case optA of
      (Some a) \<Rightarrow>
        (case optB of
          (Some b) \<Rightarrow> a \<le> b |
          None \<Rightarrow> False) |
      None \<Rightarrow> True\<close>

definition less_option_def[simp]:
  \<open>less_option (optA :: 'a option) optB \<equiv> (optA \<le> optB \<and> \<not> optB \<le> optA)\<close>

instance proof standard
  fix x y::\<open>'a option\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> by simp
next
  fix x::\<open>'a option\<close>
  show \<open>x \<le> x\<close>
    by (simp add: option.case_eq_if)
next
  fix x y z::\<open>'a option\<close>
  assume \<open>x \<le> y\<close> \<open>y \<le> z\<close>
  thus \<open>x \<le> z\<close>
    unfolding less_eq_option_def
    by (metis option.case_eq_if order_trans)
next
  fix x y::\<open>'a option\<close>
  assume \<open> x \<le> y\<close> \<open>y \<le> x\<close>
  thus \<open>x = y\<close>
    unfolding less_eq_option_def
    by (smt (z3) inf.absorb_iff2 le_boolD option.case_eq_if option.split_sel order_antisym)
qed

end

text \<open>Again, we prove some lemmas to ease the manipulation of expressions using mininum updates.\<close>

lemma min_1_6_simps[simp]:
  shows \<open>modal_depth (the (min1_6 e)) = min (modal_depth e) (pos_conjuncts e)\<close>
        \<open>br_conj_depth (the (min1_6 e)) = br_conj_depth e\<close>
        \<open>conj_depth (the (min1_6 e)) = conj_depth e\<close>
        \<open>st_conj_depth (the (min1_6 e)) = st_conj_depth e\<close>
        \<open>imm_conj_depth (the (min1_6 e)) = imm_conj_depth e\<close>
        \<open>pos_conjuncts (the (min1_6 e)) = pos_conjuncts e\<close>
        \<open>neg_conjuncts (the (min1_6 e)) = neg_conjuncts e\<close>
        \<open>neg_depth (the (min1_6 e)) = neg_depth e\<close>
  unfolding min1_6_def by (simp_all add: energy.case_eq_if)

lemma min_1_7_simps[simp]:
  shows \<open>modal_depth (the (min1_7 e)) = min (modal_depth e) (neg_conjuncts e)\<close>
        \<open>br_conj_depth (the (min1_7 e)) = br_conj_depth e\<close>
        \<open>conj_depth (the (min1_7 e)) = conj_depth e\<close>
        \<open>st_conj_depth (the (min1_7 e)) = st_conj_depth e\<close>
        \<open>imm_conj_depth (the (min1_7 e)) = imm_conj_depth e\<close>
        \<open>pos_conjuncts (the (min1_7 e)) = pos_conjuncts e\<close>
        \<open>neg_conjuncts (the (min1_7 e)) = neg_conjuncts e\<close>
        \<open>neg_depth (the (min1_7 e)) = neg_depth e\<close>
  unfolding min1_7_def by (simp_all add: energy.case_eq_if)

lemma min_1_6_some:
  shows \<open>min1_6 e \<noteq> None\<close>
  unfolding min1_6_def
  using energy.case_eq_if by blast

lemma min_1_7_some:
  shows \<open>min1_7 e \<noteq> None\<close>
  unfolding min1_7_def
  using energy.case_eq_if by blast

lemma min_1_7_lower_end:
  assumes \<open>(Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) = None\<close>
  shows \<open>neg_depth e = 0\<close>
  using assms
  by (smt (verit, ccfv_threshold) bind.bind_lunit energy.sel ileI1
      leq_components min_1_7_some not_gr_zero one_eSuc zero_le)

lemma min_1_7_subtr_simp:
  shows \<open>(Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)
    = (if neg_depth e = 0 then None
        else Some (E (min (modal_depth e) (neg_conjuncts e)) (br_conj_depth e) (conj_depth e)
                     (st_conj_depth e) (imm_conj_depth e) (pos_conjuncts e)
                     (neg_conjuncts e) (neg_depth e - 1)))\<close>
  using min_1_7_lower_end
  by (auto simp add: min1_7_def)

lemma min_1_7_subtr_mono:
  shows \<open>mono (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
proof
  fix e1 e2 :: energy
  assume \<open>e1 \<le> e2\<close>
  thus \<open>(\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) e1
    \<le>  (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) e2\<close>
    unfolding min_1_7_subtr_simp
    by (auto simp add: min.coboundedI1  min.coboundedI2 enat_diff_mono)
qed

lemma min_1_6_subtr_simp:
  shows \<open>(Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)
    = (if br_conj_depth e = 0 \<or> conj_depth e = 0 then None
        else Some (E (min (modal_depth e) (pos_conjuncts e)) (br_conj_depth e - 1)
                     (conj_depth e - 1) (st_conj_depth e) (imm_conj_depth e)
                     (pos_conjuncts e) (neg_conjuncts e) (neg_depth e)))\<close>
  by (auto simp add: min1_6_def ileI1 one_eSuc)

instantiation energy :: Sup
begin

definition \<open>Sup ee \<equiv> E
  (Sup (modal_depth ` ee)) (Sup (br_conj_depth ` ee )) (Sup (conj_depth ` ee))
  (Sup (st_conj_depth ` ee)) (Sup (imm_conj_depth ` ee)) (Sup (pos_conjuncts ` ee))
  (Sup (neg_conjuncts ` ee)) (Sup (neg_depth ` ee))\<close>

instance ..
end


end