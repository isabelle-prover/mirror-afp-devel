section \<open>Ackermann's Function and the PR Functions\<close>

text \<open>
  This proof has been adopted from a development by Nora Szasz \<^cite>\<open>"szasz93"\<close>.
  \medskip
\<close>


theory Primrec imports Main begin


subsection\<open>Ackermann's Function\<close>

fun ack :: "[nat,nat] \<Rightarrow> nat" where
  "ack 0 n =  Suc n"
| "ack (Suc m) 0 = ack m 1"
| "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"


text \<open>PROPERTY A 4\<close>

lemma less_ack2 [iff]: "j < ack i j"
  by (induct i j rule: ack.induct) simp_all


text \<open>PROPERTY A 5-, the single-step lemma\<close>

lemma ack_less_ack_Suc2 [iff]: "ack i j < ack i (Suc j)"
  by (induct i j rule: ack.induct) simp_all


text \<open>PROPERTY A 5, monotonicity for \<open><\<close>\<close>

lemma ack_less_mono2: "j < k \<Longrightarrow> ack i j < ack i k"
  by (simp add: lift_Suc_mono_less)


text \<open>PROPERTY A 5', monotonicity for \<open>\<le>\<close>\<close>

lemma ack_le_mono2: "j \<le> k \<Longrightarrow> ack i j \<le> ack i k"
  by (simp add: ack_less_mono2 less_mono_imp_le_mono)


text \<open>PROPERTY A 6\<close>

lemma ack2_le_ack1 [iff]: "ack i (Suc j) \<le> ack (Suc i) j"
proof (induct j)
  case 0 show ?case by simp
next
  case (Suc j) show ?case
    by (metis Suc ack.simps(3) ack_le_mono2 le_trans less_ack2 less_eq_Suc_le)
qed


text \<open>PROPERTY A 4'? Extra lemma needed for \<^term>\<open>CONSTANT\<close> case, constant functions\<close>

lemma ack_less_ack_Suc1 [iff]: "ack i j < ack (Suc i) j"
  by (blast intro: ack_less_mono2 less_le_trans)

lemma less_ack1 [iff]: "i < ack i j"
  by (induct i) (auto intro: less_trans_Suc)


text \<open>PROPERTY A 8\<close>

lemma ack_1 [simp]: "ack (Suc 0) j = j + 2"
  by (induct j) simp_all


text \<open>PROPERTY A 9.  The unary \<open>1\<close> and \<open>2\<close> in \<^term>\<open>ack\<close> is essential for the rewriting.\<close>

lemma ack_2 [simp]: "ack (Suc (Suc 0)) j = 2 * j + 3"
  by (induct j) simp_all

text \<open>Added in 2022 just for fun\<close>
lemma ack_3: "ack (Suc (Suc (Suc 0))) j = 2 ^ (j+3) - 3"
proof (induct j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  with less_le_trans show ?case
    by (fastforce simp add: power_add algebra_simps)
qed

text \<open>PROPERTY A 7, monotonicity for \<open><\<close> [not clear why
  @{thm [source] ack_1} is now needed first!]\<close>

lemma ack_less_mono1_aux: "ack i k < ack (Suc (i+j)) k"
proof (induct i k rule: ack.induct)
  case (1 n) show ?case
    using less_le_trans by auto
next
  case (2 m) thus ?case by simp
next
  case (3 m n) thus ?case
    using ack_less_mono2 less_trans by fastforce
qed

lemma ack_less_mono1: "i < j \<Longrightarrow> ack i k < ack j k"
  using ack_less_mono1_aux less_iff_Suc_add by auto


text \<open>PROPERTY A 7', monotonicity for \<open>\<le>\<close>\<close>

lemma ack_le_mono1: "i \<le> j \<Longrightarrow> ack i k \<le> ack j k"
  using ack_less_mono1 le_eq_less_or_eq by auto


text \<open>PROPERTY A 10\<close>

lemma ack_nest_bound: "ack i1 (ack i2 j) < ack (2 + (i1 + i2)) j"
proof -
  have "ack i1 (ack i2 j) < ack (i1 + i2) (ack (Suc (i1 + i2)) j)"
    by (meson ack_le_mono1 ack_less_mono1 ack_less_mono2 le_add1 le_trans less_add_Suc2 not_less)
  also have "\<dots> = ack (Suc (i1 + i2)) (Suc j)"
    by simp
  also have "\<dots> \<le> ack (2 + (i1 + i2)) j"
    using ack2_le_ack1 add_2_eq_Suc by presburger
  finally show ?thesis .
qed



text \<open>PROPERTY A 11\<close>

lemma ack_add_bound: "ack i1 j + ack i2 j < ack (4 + (i1 + i2)) j"
proof -
  have "ack i1 j \<le> ack (i1 + i2) j" "ack i2 j \<le> ack (i1 + i2) j"
    by (simp_all add: ack_le_mono1)
  then have "ack i1 j + ack i2 j < ack (Suc (Suc 0)) (ack (i1 + i2) j)"
    by simp
  also have "\<dots> < ack (4 + (i1 + i2)) j"
    by (metis ack_nest_bound add.assoc numeral_2_eq_2 numeral_Bit0)
  finally show ?thesis .
qed


text \<open>PROPERTY A 12.  Article uses existential quantifier but the ALF proof
  used \<open>k + 4\<close>.  Quantified version must be nested \<open>\<exists>k'. \<forall>i j. \<dots>\<close>\<close>

lemma ack_add_bound2:
  assumes "i < ack k j" shows "i + j < ack (4 + k) j"
proof -
  have "i + j < ack k j + ack 0 j"
    using assms by auto
  also have "\<dots> < ack (4 + k) j"
    by (metis ack_add_bound add.right_neutral)
  finally show ?thesis .
qed


subsection\<open>Primitive Recursive Functions\<close>

primrec hd0 :: "nat list \<Rightarrow> nat" where
  "hd0 [] = 0"
| "hd0 (m # ms) = m"


text \<open>Inductive definition of the set of primitive recursive functions of type \<^typ>\<open>nat list \<Rightarrow> nat\<close>.\<close>

definition SC :: "nat list \<Rightarrow> nat"
  where "SC l = Suc (hd0 l)"

definition CONSTANT :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  where "CONSTANT n l = n"

definition PROJ :: "nat \<Rightarrow> nat list \<Rightarrow> nat"
  where "PROJ i l = hd0 (drop i l)"

definition COMP :: "[nat list \<Rightarrow> nat, (nat list \<Rightarrow> nat) list, nat list] \<Rightarrow> nat"
  where "COMP g fs l = g (map (\<lambda>f. f l) fs)"

fun PREC :: "[nat list \<Rightarrow> nat, nat list \<Rightarrow> nat, nat list] \<Rightarrow> nat"
  where
    "PREC f g [] = 0"
  | "PREC f g (x # l) = rec_nat (f l) (\<lambda>y r. g (r # y # l)) x"
    \<comment> \<open>Note that \<^term>\<open>g\<close> is applied first to \<^term>\<open>PREC f g y\<close> and then to \<^term>\<open>y\<close>!\<close>

inductive PRIMREC :: "(nat list \<Rightarrow> nat) \<Rightarrow> bool" where
  SC: "PRIMREC SC"
| CONSTANT: "PRIMREC (CONSTANT k)"
| PROJ: "PRIMREC (PROJ i)"
| COMP: "PRIMREC g \<Longrightarrow> listsp PRIMREC fs \<Longrightarrow> PRIMREC (COMP g fs)"
| PREC: "PRIMREC f \<Longrightarrow> PRIMREC g \<Longrightarrow> PRIMREC (PREC f g)"
  monos listsp_mono


subsection \<open>Main Result: Ackermann's Function is not Primitive Recursive\<close>

lemma SC_case: "SC l < ack 1 (sum_list l)"
  unfolding SC_def
  by (induct l) (simp_all add: le_add1 le_imp_less_Suc)

lemma CONSTANT_case: "CONSTANT n l < ack n (sum_list l)"
  by (simp add: CONSTANT_def)

lemma PROJ_case: "PROJ i l < ack 0 (sum_list l)"
proof -
  have "hd0 (drop i l) \<le> sum_list l"
    by (induct l arbitrary: i) (auto simp: drop_Cons' trans_le_add2)
  then show ?thesis
    by (simp add: PROJ_def)
qed

text \<open>\<^term>\<open>COMP\<close> case\<close>

lemma COMP_map_aux: "\<forall>f \<in> set fs. \<exists>kf. \<forall>l. f l < ack kf (sum_list l)
        \<Longrightarrow> \<exists>k. \<forall>l. sum_list (map (\<lambda>f. f l) fs) < ack k (sum_list l)"
proof (induct fs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a fs)
  then show ?case
    by simp (blast intro: add_less_mono ack_add_bound less_trans)
qed

lemma COMP_case:
  assumes 1: "\<forall>l. g l < ack kg (sum_list l)"
      and 2: "\<forall>f \<in> set fs. \<exists>kf. \<forall>l. f l < ack kf (sum_list l)"
  shows "\<exists>k. \<forall>l. COMP g fs  l < ack k (sum_list l)"
  unfolding COMP_def
  using 1 COMP_map_aux [OF 2] by (meson ack_less_mono2 ack_nest_bound less_trans)

text \<open>\<^term>\<open>PREC\<close> case\<close>

lemma PREC_case_aux:
  assumes f: "\<And>l. f l + sum_list l < ack kf (sum_list l)"
    and g: "\<And>l. g l + sum_list l < ack kg (sum_list l)"
  shows "PREC f g (m#l) + sum_list (m#l) < ack (Suc (kf + kg)) (sum_list (m#l))"
proof (induct m)
  case 0
  then show ?case
    using ack_less_mono1_aux f less_trans by fastforce
next
  case (Suc m)
  let ?r = "PREC f g (m#l)"
  have "\<not> g (?r # m # l) + sum_list (?r # m # l) < g (?r # m # l) + (m + sum_list l)"
    by force
  then have "g (?r # m # l) + (m + sum_list l) < ack kg (sum_list (?r # m # l))"
    by (meson g leI less_le_trans)
  moreover
    have "\<dots> < ack (kf + kg) (ack (Suc (kf + kg)) (m + sum_list l))"
    using Suc.hyps by simp (meson ack_le_mono1 ack_less_mono2 le_add2 le_less_trans)
  ultimately show ?case
    by auto
qed

lemma PREC_case_aux':
  assumes f: "\<And>l. f l + sum_list l < ack kf (sum_list l)"
    and g: "\<And>l. g l + sum_list l < ack kg (sum_list l)"
  shows "PREC f g l + sum_list l < ack (Suc (kf + kg)) (sum_list l)"
  by (smt (verit, best) PREC.elims PREC_case_aux add.commute add.right_neutral f g less_ack2)

proposition PREC_case:
  "\<lbrakk>\<And>l. f l < ack kf (sum_list l); \<And>l. g l < ack kg (sum_list l)\<rbrakk>
  \<Longrightarrow> \<exists>k. \<forall>l. PREC f g l < ack k (sum_list l)"
  by (metis le_less_trans [OF le_add1 PREC_case_aux'] ack_add_bound2)

lemma ack_bounds_PRIMREC: "PRIMREC f \<Longrightarrow> \<exists>k. \<forall>l. f l < ack k (sum_list l)"
  by (erule PRIMREC.induct) (blast intro: SC_case CONSTANT_case PROJ_case COMP_case PREC_case)+

theorem ack_not_PRIMREC:
  "\<not> PRIMREC (\<lambda>l. ack (hd0 l) (hd0 l))"
proof
  assume *: "PRIMREC (\<lambda>l. ack (hd0 l) (hd0 l))"
  then obtain m where m: "\<And>l. ack (hd0 l) (hd0 l) < ack m (sum_list l)"
    using ack_bounds_PRIMREC by blast
  show False
    using m [of "[m]"] by simp
qed

end
