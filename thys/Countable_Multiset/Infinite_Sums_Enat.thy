section \<open>Infinite Sums over Extended Natural Numbers\<close>


text \<open>This is a theory of infinite sums of extended natural numbers defined as limits of finite sums. 
The goal is to make reasoning about these infinite sums almost as easy as that about finite sums. 
\<close>


theory Infinite_Sums_Enat
  imports "HOL-Library.Countable_Set" "HOL-Library.Extended_Nat"
begin

subsection \<open>Preliminaries\<close>

lemma enat_pm_iff:
  "\<And>a b c. b \<le> c \<Longrightarrow> (a::enat) + b \<le> c \<longleftrightarrow> a \<le> c - b"
  "\<And>a b c. a \<le> c \<Longrightarrow> (a::enat) + b \<le> c \<longleftrightarrow> b \<le> c - a"
  "\<And>a b c. a \<le> b \<Longrightarrow> c \<le> b \<Longrightarrow> (a::enat) \<le> b - c \<longleftrightarrow> c \<le> b - a"
  by (smt (verit) add.commute add_diff_cancel_enat add_left_mono idiff_infinity le_iff_add nle_le plus_eq_infty_iff_enat)+


lemma disjoint_finite_aux: 
  "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {} \<Longrightarrow> B \<subseteq> \<Union> (A ` I) \<Longrightarrow> finite B \<Longrightarrow> finite {i \<in> I. B \<inter> A i \<noteq> {}}"
proof -
  assume disj: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
    and hB: "B \<subseteq> \<Union> (A ` I)"
    and hfin: "finite B"
  show "finite {i \<in> I. B \<inter> A i \<noteq> {}}"
  proof (rule inj_on_finite[of "\<lambda>i. SOME b. b \<in> B \<inter> A i" _ B])
    show "inj_on (\<lambda>i. SOME b. b \<in> B \<inter> A i) {i \<in> I. B \<inter> A i \<noteq> {}}"
      unfolding inj_on_def
    proof (intro ballI impI)
      fix x y
      assume xI: "x \<in> {i \<in> I. B \<inter> A i \<noteq> {}}" and yI: "y \<in> {i \<in> I. B \<inter> A i \<noteq> {}}"
      assume eq: "(SOME b. b \<in> B \<inter> A x) = (SOME b. b \<in> B \<inter> A y)"
      have hx: "(SOME b. b \<in> B \<inter> A x) \<in> B \<inter> A x"
      proof -
        from xI have "B \<inter> A x \<noteq> {}" by simp
        then obtain c where "c \<in> B \<inter> A x" by blast
        then show ?thesis by (rule someI[of "\<lambda>b. b \<in> B \<inter> A x"])
      qed
      have hy: "(SOME b. b \<in> B \<inter> A y) \<in> B \<inter> A y"
      proof -
        from yI have "B \<inter> A y \<noteq> {}" by simp
        then obtain c where "c \<in> B \<inter> A y" by blast
        then show ?thesis by (rule someI[of "\<lambda>b. b \<in> B \<inter> A y"])
      qed
      show "x = y"
      proof (rule ccontr)
        assume "x \<noteq> y"
        with xI yI disj have "A x \<inter> A y = {}" by auto
        with hx hy eq show False by auto
      qed
    qed
    show "(\<lambda>i. SOME b. b \<in> B \<inter> A i) ` {i \<in> I. B \<inter> A i \<noteq> {}} \<subseteq> B"
    proof (intro subsetI)
      fix d assume "d \<in> (\<lambda>i. SOME b. b \<in> B \<inter> A i) ` {i \<in> I. B \<inter> A i \<noteq> {}}"
      then obtain i where iI: "i \<in> {i \<in> I. B \<inter> A i \<noteq> {}}" and deq: "d = (SOME b. b \<in> B \<inter> A i)" by blast
      from iI have "B \<inter> A i \<noteq> {}" by simp
      then obtain c where "c \<in> B \<inter> A i" by blast
      then have "(SOME b. b \<in> B \<inter> A i) \<in> B \<inter> A i" by (rule someI[of "\<lambda>b. b \<in> B \<inter> A i"])
      with deq show "d \<in> B" by auto
    qed
    show "finite B" using hfin .
  qed
qed


lemma incl_UNION_aux: "B \<subseteq> \<Union> (A ` I) \<Longrightarrow> B = \<Union> ((\<lambda>i. (B \<inter> A i)) ` {i \<in> I. B \<inter> A i \<noteq> {}})"
  by fastforce

lemma incl_UNION_aux2: "B \<subseteq> \<Union> (A ` I) \<longleftrightarrow> B = \<Union> ((\<lambda>i. (B \<inter> A i)) ` I)"
  by fastforce

lemma sum_singl[simp]: "sum f {a} = f a"  
  by simp

lemma sum_two[simp]: "a1 \<noteq> a2 \<Longrightarrow> sum f {a1,a2} = f a1 + f a2"  
  by simp

lemma sum_three[simp]: "a1 \<noteq> a2 \<Longrightarrow> a1 \<noteq> a3 \<Longrightarrow> a2 \<noteq> a3 \<Longrightarrow> 
 sum f {a1,a2,a3} = f a1 + f a2 + f a3"  
  by (simp add: add.assoc)

lemma Sup_leq: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (a::enat) \<le> b \<Longrightarrow> Sup A \<le> Sup B"
  by (simp add: cSup_mono)


lemma Sup_image_leq: 
  "A \<noteq> {} \<Longrightarrow>  \<forall>a\<in>A. \<exists>b\<in>B. (f a::enat) \<le> g b \<Longrightarrow>
 Sup (f ` A) \<le> Sup (g ` B)"
  by (rule Sup_leq) auto

lemma Sup_cong: 
  assumes "A \<noteq> {} \<or> B \<noteq> {}" "\<forall>a\<in>A. \<exists>b\<in>B. (a::enat) \<le> b" "\<forall>b\<in>B. \<exists>a\<in>A. (b::enat) \<le> a"
  shows "Sup A = Sup B" 
proof-
  have "A \<noteq> {} \<and> B \<noteq> {}"
    using assms unfolding bdd_above_def using order.trans by blast+
  thus ?thesis using assms
    by (meson Sup_mono order_antisym)
qed

lemma Sup_image_cong: 
  "A \<noteq> {} \<or> B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (f a::enat) \<le> g b \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (g b::enat) \<le> f a \<Longrightarrow>
 Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_cong) auto

lemma Sup_congL: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (a::enat) \<le> b \<Longrightarrow> \<forall>b\<in>B. b \<le> Sup A \<Longrightarrow> Sup A = Sup B"
  by (metis Collect_empty_eq Collect_mem_eq Sup_leq cSup_least dual_order.antisym)

lemma Sup_image_congL: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (f a::enat) \<le> g b \<Longrightarrow> \<forall>b\<in>B. g b \<le> Sup (f ` A) \<Longrightarrow> Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_congL) auto

lemma Sup_congR: 
  "B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. a \<le> Sup B \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (b::enat) \<le> a \<Longrightarrow> Sup A = Sup B"
  by (metis Collect_empty_eq Collect_mem_eq Sup_leq cSup_least dual_order.antisym)

lemma Sup_image_congR: 
  "B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. f a \<le> Sup (g ` B) \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (g b::enat) \<le> f a \<Longrightarrow> Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_congR) auto

lemma Sup_eq_0_iff: "Sup (A :: enat set) = 0 \<longleftrightarrow> (\<forall>a\<in>A. a = 0)"
  using Sup_bot_conv(1)[of A] unfolding bot_enat_def by auto


lemma plus_Sup_commute:
  assumes f1: "{f1 b1 | b1. \<phi>1 b1} \<noteq> {}" and 
          f2: "{f2 b2 | b2. \<phi>2 b2} \<noteq> {}"
  shows 
    "Sup {(f1 b1::enat) | b1 . \<phi>1 b1} + Sup {f2 b2 | b2 . \<phi>2 b2} = 
     Sup {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}" (is "?L1 + ?L2 = ?R")
proof-
  have f: 
    "{f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2} \<noteq> {}"
    using f1 f2 by auto
  show ?thesis proof (rule order.antisym)
    show "?L1 + ?L2 \<le> ?R"
    proof -
      obtain b1_wit where hb1_wit: "\<phi>1 b1_wit" using f1 by auto
      have hL2_le_R: "?L2 \<le> ?R"
      proof (intro cSup_le_iff[OF f2 bdd_above_top, THEN iffD2] ballI)
        fix x assume "x \<in> {f2 b2 | b2. \<phi>2 b2}"
        then obtain b2 where hb: "x = f2 b2" "\<phi>2 b2" by auto
        have mem: "f1 b1_wit + f2 b2 \<in> {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}"
          using hb1_wit hb(2) by blast
        have "f2 b2 \<le> f1 b1_wit + f2 b2" by (simp add: le_add2)
        also have "... \<le> ?R" using cSup_upper[OF mem bdd_above_top] by simp
        finally show "x \<le> ?R" using hb(1) by simp
      qed
      have hL1_le_R: "\<And>b1. \<phi>1 b1 \<Longrightarrow> f1 b1 \<le> ?R"
      proof -
        fix b1 assume h\<phi>1: "\<phi>1 b1"
        obtain b2 where hb2: "\<phi>2 b2" using f2 by auto
        have mem: "f1 b1 + f2 b2 \<in> {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}"
          using h\<phi>1 hb2 by blast
        have "f1 b1 \<le> f1 b1 + f2 b2" by (simp add: le_add1)
        also have "... \<le> ?R" using cSup_upper[OF mem bdd_above_top] by simp
        finally show "f1 b1 \<le> ?R" .
      qed
      have hL1_le: "?L1 \<le> ?R - ?L2"
      proof (intro cSup_le_iff[OF f1 bdd_above_top, THEN iffD2] ballI)
        fix x assume "x \<in> {f1 b1 | b1. \<phi>1 b1}"
        then obtain b1 where hb: "x = f1 b1" "\<phi>1 b1" by auto
        have hfb1_le_R: "f1 b1 \<le> ?R" using hL1_le_R hb(2) by blast
        have hL2_le_Rm: "?L2 \<le> ?R - f1 b1"
        proof (intro cSup_le_iff[OF f2 bdd_above_top, THEN iffD2] ballI)
          fix y assume "y \<in> {f2 b2 | b2. \<phi>2 b2}"
          then obtain b2 where hy: "y = f2 b2" "\<phi>2 b2" by auto
          have mem: "f1 b1 + f2 b2 \<in> {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}"
            using hb(2) hy(2) by blast
          have hle: "f1 b1 + f2 b2 \<le> ?R" using cSup_upper[OF mem bdd_above_top] by simp
          show "y \<le> ?R - f1 b1"
            using enat_pm_iff(2)[OF hfb1_le_R] hle hy(1) by simp
        qed
        show "x \<le> ?R - ?L2"
          using enat_pm_iff(3)[OF hfb1_le_R hL2_le_R] hL2_le_Rm hb(1) by simp
      qed
      show "?L1 + ?L2 \<le> ?R"
        using enat_pm_iff(1)[OF hL2_le_R] hL1_le by simp
    qed
  next
    show "?R \<le> ?L1 + ?L2"
    proof (intro cSup_le_iff[OF f bdd_above_top, THEN iffD2] ballI)
      fix x assume "x \<in> {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}"
      then obtain b1 b2 where hx: "x = f1 b1 + f2 b2" "\<phi>1 b1" "\<phi>2 b2" by auto
      have mem1: "f1 b1 \<in> {f1 b1 | b1. \<phi>1 b1}" using hx(2) by blast
      have mem2: "f2 b2 \<in> {f2 b2 | b2. \<phi>2 b2}" using hx(3) by blast
      have h1: "f1 b1 \<le> ?L1" using cSup_upper[OF mem1 bdd_above_top] by simp
      have h2: "f2 b2 \<le> ?L2" using cSup_upper[OF mem2 bdd_above_top] by simp
      show "x \<le> ?L1 + ?L2" using h1 h2 hx(1) by (simp add: add_mono)
    qed
  qed
qed

lemma plus_Sup_commute':
  assumes f1: "A1 \<noteq> {}" and f2: "A2 \<noteq> {}"
  shows "Sup A1 + Sup A2 = Sup {(a1::enat) + a2 | a1 a2. a1 \<in> A1 \<and> a2 \<in> A2}"  
  using plus_Sup_commute[of id "\<lambda>a1. a1 \<in> A1" id "\<lambda>a2. a2 \<in> A2"] assms 
  by auto

lemma plus_SupR: "A \<noteq> {} \<Longrightarrow> Sup A + (b::enat) = Sup {a + b | a. a \<in> A}"
proof -
  assume hA: "A \<noteq> {}"
  have "Sup A + b = Sup A + Sup {b}" by simp
  also have "... = Sup {a1 + a2 | a1 a2. a1 \<in> A \<and> a2 \<in> {b}}"
    using plus_Sup_commute'[of A "{b}"] hA by auto
  also have "... = Sup {a + b | a. a \<in> A}" by auto
  finally show ?thesis .
qed

lemma plus_SupL: "A \<noteq> {} \<Longrightarrow> (b::enat) + Sup A = Sup {b + a | a. a \<in> A}"
proof -
  assume hA: "A \<noteq> {}"
  have "b + Sup A = Sup {b} + Sup A" by simp
  also have "... = Sup {a1 + a2 | a1 a2. a1 \<in> {b} \<and> a2 \<in> A}"
    using plus_Sup_commute'[of "{b}" A] hA by auto
  also have "... = Sup {b + a | a. a \<in> A}" by auto
  finally show ?thesis .
qed



lemma sum_mono3: 
  "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (f a::enat) \<le> g a) \<Longrightarrow> 
 sum f A \<le> sum g B"
  by (metis order_trans sum_mono sum_mono2 zero_le)

lemma sum_Sup_commute: 
  fixes h :: "'a \<Rightarrow> enat"
  assumes "finite J" and "\<forall>i\<in>J. {h b | b. \<phi> i b} \<noteq> {}"
  shows "sum (\<lambda>i. Sup {h b | b. \<phi> i b}) J = 
       Sup {sum (\<lambda>i. h (b i)) J | b . \<forall>i\<in>J. \<phi> i (b i)}"
  using assms proof (induction J)
  case empty then show ?case by simp
next
  case (insert j J)
  have note1: "{\<Sum>i\<in>J. h (b i) | b. \<forall>i\<in>J. \<phi> i (b i)} \<noteq> {}"
    if hyp: "\<forall>i\<in>J. {h b | b. \<phi> i b} \<noteq> {}"
  proof -
    from hyp have "\<forall>i\<in>J. \<exists>b. \<phi> i b" by auto
    then have "\<exists>b. \<forall>i\<in>J. \<phi> i (b i)"
      by (intro exI[of _ "\<lambda>i. SOME b. \<phi> i b"]) (simp add: some_eq_ex)
    then show ?thesis by blast
  qed
  have hJ_ne: "\<forall>i\<in>J. {h b | b. \<phi> i b} \<noteq> {}" using insert.prems by auto
  have hIH: "sum (\<lambda>i. Sup {h b | b. \<phi> i b}) J = Sup {sum (\<lambda>i. h (b i)) J | b. \<forall>i\<in>J. \<phi> i (b i)}"
    using insert.IH[OF hJ_ne] by simp
  have hpsc: "Sup {h b | b. \<phi> j b} + Sup {sum (\<lambda>i. h (b i)) J | b. \<forall>i\<in>J. \<phi> i (b i)} =
              Sup {h b1 + sum (\<lambda>i. h (b2 i)) J | b1 b2. \<phi> j b1 \<and> (\<forall>i\<in>J. \<phi> i (b2 i))}"
    using plus_Sup_commute[of h "\<phi> j" "\<lambda>b. sum (\<lambda>i. h (b i)) J" "\<lambda>b2. \<forall>i\<in>J. \<phi> i (b2 i)"]
          insert.prems note1[OF hJ_ne]
    by auto
  have hset: "{h b1 + sum (\<lambda>i. h (b2 i)) J | b1 b2. \<phi> j b1 \<and> (\<forall>i\<in>J. \<phi> i (b2 i))} =
              {sum (\<lambda>i. h (b i)) (insert j J) | b. \<forall>i\<in>insert j J. \<phi> i (b i)}"
    using insert.hyps
  proof (intro set_eqI iffI)
    fix x
    assume "x \<in> {h b1 + sum (\<lambda>i. h (b2 i)) J | b1 b2. \<phi> j b1 \<and> (\<forall>i\<in>J. \<phi> i (b2 i))}"
    then obtain b1 b2 where hx: "x = h b1 + sum (\<lambda>i. h (b2 i)) J" "\<phi> j b1" "\<forall>i\<in>J. \<phi> i (b2 i)"
      by auto
    let ?b = "\<lambda>j'. if j' = j then b1 else b2 j'"
    have hb_J: "\<forall>i\<in>J. ?b i = b2 i" using insert.hyps by simp
    have hsum_eq: "sum (\<lambda>i. h (?b i)) J = sum (\<lambda>i. h (b2 i)) J"
      by (rule sum.cong) (auto simp: hb_J)
    have "x = sum (\<lambda>i. h (?b i)) (insert j J)"
      using hx insert.hyps by (simp add: hsum_eq)
    moreover have "\<forall>i\<in>insert j J. \<phi> i (?b i)"
      using hx insert.hyps by (auto simp: insertE)
    ultimately show "x \<in> {sum (\<lambda>i. h (b i)) (insert j J) | b. \<forall>i\<in>insert j J. \<phi> i (b i)}"
      by auto
  next
    fix x
    assume "x \<in> {sum (\<lambda>i. h (b i)) (insert j J) | b. \<forall>i\<in>insert j J. \<phi> i (b i)}"
    then obtain b where hx: "x = sum (\<lambda>i. h (b i)) (insert j J)" "\<forall>i\<in>insert j J. \<phi> i (b i)"
      by auto
    have "x = h (b j) + sum (\<lambda>i. h (b i)) J"
      using insert.hyps hx(1) by simp
    then show "x \<in> {h b1 + sum (\<lambda>i. h (b2 i)) J | b1 b2. \<phi> j b1 \<and> (\<forall>i\<in>J. \<phi> i (b2 i))}"
      using hx(2) by auto
  qed
  show ?case
    using insert.hyps
    by (simp add: hIH hpsc hset)
qed


subsection \<open>Infinite Summation\<close>

(* Infinite sums *)
definition isum :: "('a \<Rightarrow> enat) \<Rightarrow> 'a set \<Rightarrow> enat" where 
  "isum f A \<equiv> Sup (sum f  ` {B | B . B \<subseteq> A \<and> finite B})"

lemma isum_subset_mono: "A \<subseteq> B \<Longrightarrow> isum f A \<le> isum f B"
  unfolding isum_def image_def
  by(auto intro: Sup_subset_mono)

(* isum versus sum *)
lemma isum_eq_sum:
  "finite A \<Longrightarrow> isum f A = sum f A"
proof -
  assume hA: "finite A"
  show "isum f A = sum f A"
    unfolding isum_def
  proof (rule cSup_eq_maximum)
    show "sum f A \<in> sum f ` {B | B. B \<subseteq> A \<and> finite B}" using hA by blast
    show "\<And>x. x \<in> sum f ` {B | B. B \<subseteq> A \<and> finite B} \<Longrightarrow> x \<le> sum f A"
      using hA by (auto intro: sum_mono2)
  qed
qed







(* Congruence and monotonicity *)
(* thm sum.cong *)
lemma isum_cong: 
  assumes "A = B" and "\<And>x. x \<in> B \<Longrightarrow> g x = h x" 
  shows "isum g A = isum h B"
  using assms unfolding isum_def 
  by (auto intro!: SUP_cong comm_monoid_add_class.sum.cong)

(* thm sum_mono *)
lemma isum_mono: 
  assumes "\<And>x. x \<in> A \<Longrightarrow> g x \<le> h x" 
  shows "isum g A \<le> isum h A"
  unfolding isum_def
proof (intro cSup_mono)
  show "sum g ` {B | B. B \<subseteq> A \<and> finite B} \<noteq> {}" by auto
  show "bdd_above (sum h ` {B | B. B \<subseteq> A \<and> finite B})"
    unfolding bdd_above_def using bdd_above.unfold by blast
  fix r assume "r \<in> sum g ` {B | B. B \<subseteq> A \<and> finite B}"
  then obtain B where hB: "B \<subseteq> A" "finite B" and hr: "r = sum g B" by blast
  show "\<exists>b \<in> sum h ` {B | B. B \<subseteq> A \<and> finite B}. r \<le> b"
  proof (intro bexI[of _ "sum h B"])
    show "r \<le> sum h B" using hr assms hB by (auto intro: sum_mono)
    show "sum h B \<in> sum h ` {B | B. B \<subseteq> A \<and> finite B}" using hB by blast
  qed
qed

lemma isum_mono': 
  assumes "A \<subseteq> B" 
  shows "isum g A \<le> isum g B"
  using assms unfolding isum_def
  by (intro cSup_subset_mono) (auto intro!: exI[of _ "\<infinity>"])

(* isum vs. 0 *)
(* thm comm_monoid_add_class.sum.empty *)
lemma isum_empty[simp]: "isum g {} = 0"
  unfolding isum_def by auto

(* thm comm_monoid_add_class.sum.neutral_const *)
lemma isum_const_zero[simp]: "isum (\<lambda>x. 0) A = 0"
  unfolding isum_def 
  by simp (metis cSUP_const empty_iff empty_subsetI finite.emptyI mem_Collect_eq)

(* thm sum.neutral  *)
lemma isum_const_zero': "\<forall>x\<in>A. g x = 0 \<Longrightarrow> isum g A = 0"
  by (simp add: isum_cong)

(* thm sum_eq_0_iff  *)
lemma isum_eq_0_iff: "isum f A = 0 \<longleftrightarrow> (\<forall>a\<in>A. f a = 0)"
  unfolding isum_def by (subst Sup_eq_0_iff) auto

(* Reindexing: *)
(* thm sum.reindex *)
lemma isum_reindex: "inj_on h A \<Longrightarrow> isum g (h ` A) = isum (g \<circ> h) A"
  unfolding isum_def
proof (intro arg_cong[of _ _ Sup])
  assume "inj_on h A"
  then have "sum (g \<circ> h) B = sum g (image h B)" if "B \<subseteq> A" for B
    by (simp add: inj_on_subset sum.reindex that)
  then show "sum g ` {B |B. B \<subseteq> h ` A \<and> finite B} =
    sum (g \<circ> h) ` {B |B. B \<subseteq> A \<and> finite B}"
    by (auto simp: image_iff dest: finite_subset_image)
qed

(* thm sum.reindex_cong *)
lemma isum_reindex_cong: "inj_on l B \<Longrightarrow> A = l ` B \<Longrightarrow> 
 (\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x) \<Longrightarrow> isum g A = isum h B"
  by (metis isum_cong comp_def isum_reindex)

(* thm sum.reindex_nontrivial *)
lemma isum_reindex_cong': 
  assumes "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> h x = h y \<Longrightarrow> g (h x) = 0)"
  shows "isum g (h ` A) = isum (g \<circ> h) A"
  unfolding isum_def
proof (safe intro!: arg_cong[of _ _ Sup])
  fix B
  assume "B \<subseteq> h ` A" "finite B"
  with assms show "sum g B \<in> sum (g \<circ> h) ` {B |B. B \<subseteq> A \<and> finite B}"
    by (smt (verit) finite_subset_image image_iff in_mono mem_Collect_eq
        sum.reindex_nontrivial)
next
  fix B
  assume "B \<subseteq> A" "finite B"
  with assms show "sum (g \<circ> h) B \<in> sum g ` {B |B. B \<subseteq> h ` A \<and> finite B}"
    by (smt (verit, ccfv_SIG) finite_imageI image_iff mem_Collect_eq subset_iff
        sum.reindex_nontrivial)
qed

(* thm sum.mono_neutral_cong *)
lemma isum_zeros_cong:
  assumes "\<And>i. i \<in> T - S \<Longrightarrow> h i = 0" and "\<And>i. i \<in> S - T \<Longrightarrow> g i = 0"
    and "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x = h x"
  shows "isum g S = isum h T"
  unfolding isum_def
proof (rule Sup_image_cong)
  show "{B |B. B \<subseteq> S \<and> finite B} \<noteq> {} \<or> {B |B. B \<subseteq> T \<and> finite B} \<noteq> {}"
    by auto
next
  show "\<forall>a \<in> {B |B. B \<subseteq> S \<and> finite B}. \<exists>b \<in> {B |B. B \<subseteq> T \<and> finite B}. sum g a \<le> sum h b"
  proof (intro ballI)
    fix a assume "a \<in> {B |B. B \<subseteq> S \<and> finite B}"
    then have hA: "a \<subseteq> S" "finite a" by blast+
    show "\<exists>b \<in> {B |B. B \<subseteq> T \<and> finite B}. sum g a \<le> sum h b"
    proof (intro bexI[of _ "a \<inter> T"])
      show "sum g a \<le> sum h (a \<inter> T)"
        by (rule order_eq_refl, rule sum.mono_neutral_cong) (use assms hA in auto)
      show "a \<inter> T \<in> {B |B. B \<subseteq> T \<and> finite B}"
        using hA by blast
    qed
  qed
next
  show "\<forall>b \<in> {B |B. B \<subseteq> T \<and> finite B}. \<exists>a \<in> {B |B. B \<subseteq> S \<and> finite B}. sum h b \<le> sum g a"
  proof (intro ballI)
    fix b assume "b \<in> {B |B. B \<subseteq> T \<and> finite B}"
    then have hB: "b \<subseteq> T" "finite b" by blast+
    show "\<exists>a \<in> {B |B. B \<subseteq> S \<and> finite B}. sum h b \<le> sum g a"
    proof (intro bexI[of _ "b \<inter> S"])
      show "sum h b \<le> sum g (b \<inter> S)"
        by (rule order_eq_refl, rule sum.mono_neutral_cong) (use assms hB in auto)
      show "b \<inter> S \<in> {B |B. B \<subseteq> S \<and> finite B}"
        using hB by blast
    qed
  qed
qed


(* thm sum.mono_neutral_left *)
lemma isum_zeros_congL: 
  "S \<subseteq> T \<Longrightarrow> \<forall>i\<in>T - S. g i = 0 \<Longrightarrow> isum g S = isum g T"
  by (metis Diff_eq_empty_iff emptyE isum_zeros_cong)

(* thm sum.mono_neutral_right *)
lemma isum_zeros_congR:
  "S \<subseteq> T \<Longrightarrow> \<forall>i\<in>T - S. g i = 0 \<Longrightarrow> isum g T = isum g S"
  by (simp add: isum_zeros_congL)

lemma isum_singl[simp]: "isum f {a} = f a"  
  by (simp add: isum_eq_sum)

lemma isum_two[simp]: "a1 \<noteq> a2 \<Longrightarrow> isum f {a1,a2} = f a1 + f a2"  
  by (simp add: isum_eq_sum)

lemma isum_three[simp]: "a1 \<noteq> a2 \<Longrightarrow> a1 \<noteq> a3 \<Longrightarrow> a2 \<noteq> a3 \<Longrightarrow>
 isum f {a1,a2,a3} = f a1 + f a2 + f a3"  
  by (simp add: isum_eq_sum)

lemma in_le_isum: "a \<in> A \<Longrightarrow> f a \<le> isum f A"
  by (metis isum_mono' isum_singl singletonD subsetI)

lemma isum_eq_singl: 
  assumes fx: "f a = x" and f: "\<forall>a'. a' \<noteq> a \<longrightarrow> f a' = 0" and a: "a \<in> A"
  shows "isum f A = x"
proof -
  have "isum f A = isum f {a}"
    by (rule isum_zeros_cong) (use assms in auto)
  then show ?thesis by (simp add: fx)
qed

lemma isum_le_singl: 
  assumes fx: "f a \<le> x" and f: "\<forall>a'. a' \<noteq> a \<longrightarrow> f a' = 0" and a: "a \<in> A"
  shows "isum f A \<le> x"
  by (metis a f fx isum_eq_singl)

lemma isum_insert[simp]: "a \<notin> A \<Longrightarrow> isum f (insert a A) = isum f A + f a"
proof -
  assume ha: "a \<notin> A"
  have hA: "sum f ` {B |B. B \<subseteq> A \<and> finite B} \<noteq> {}" by auto
  show ?thesis
    unfolding isum_def
  proof (subst plus_SupR[OF hA], rule Sup_cong)
    show "sum f ` {B |B. B \<subseteq> insert a A \<and> finite B} \<noteq> {} \<or>
          {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}} \<noteq> {}" by auto
  next
    show "\<forall>v \<in> sum f ` {B |B. B \<subseteq> insert a A \<and> finite B}.
          \<exists>w \<in> {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}}. v \<le> w"
    proof (intro ballI)
      fix v assume "v \<in> sum f ` {B |B. B \<subseteq> insert a A \<and> finite B}"
      then obtain B where hB: "B \<subseteq> insert a A" "finite B" and hv: "v = sum f B" by blast
      show "\<exists>w \<in> {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}}. v \<le> w"
      proof (intro bexI[of _ "sum f (B - {a}) + f a"])
        show "v \<le> sum f (B - {a}) + f a"
        proof (cases "a \<in> B")
          case True
          then have "sum f B = f a + sum f (B - {a})" using hB by (simp add: sum.remove)
          then show ?thesis unfolding hv by (simp add: add.commute)
        next
          case False
          then show ?thesis unfolding hv by simp
        qed
        show "sum f (B - {a}) + f a \<in> {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}}"
          using hB ha by blast
      qed
    qed
  next
    show "\<forall>w \<in> {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}}.
          \<exists>v \<in> sum f ` {B |B. B \<subseteq> insert a A \<and> finite B}. w \<le> v"
    proof (intro ballI)
      fix w assume "w \<in> {x + f a |x. x \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}}"
      then obtain B where hB: "B \<subseteq> A" "finite B" and hw: "w = sum f B + f a" by blast
      show "\<exists>v \<in> sum f ` {B |B. B \<subseteq> insert a A \<and> finite B}. w \<le> v"
      proof (intro bexI[of _ "sum f (insert a B)"])
        show "w \<le> sum f (insert a B)"
          unfolding hw using ha hB by force
        show "sum f (insert a B) \<in> sum f ` {B |B. B \<subseteq> insert a A \<and> finite B}"
          using hB by blast
      qed
    qed
  qed
qed



(* thm sum.UNION_disjoint *)
lemma isum_UNION: 
  assumes dsj: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "isum g (\<Union> (A ` I)) = isum (\<lambda>i. isum g (A i)) I"
proof -
  have step1: "\<And>J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow>
      (\<Sum>i\<in>J. Sup {y. \<exists>B\<subseteq>A i. finite B \<and> y = sum g B}) \<le>
      Sup {y. \<exists>B\<subseteq>\<Union> (A ` I). finite B \<and> y = sum g B}"
  proof -
    fix J assume J1: "J \<subseteq> I" "finite J"
    have hsets_ne: "\<forall>i\<in>J. {sum g B | B. B \<subseteq> A i \<and> finite B} \<noteq> {}"
      by auto
    have step1a:
      "sum (\<lambda>i. Sup {sum g B | B. B \<subseteq> A i \<and> finite B}) J =
       Sup {sum (\<lambda>i. sum g (B i)) J | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
      using sum_Sup_commute[OF J1(2) hsets_ne] by simp
    have step1b:
      "Sup {sum (\<lambda>i. sum g (B i)) J | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)} =
       Sup {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
    proof (rule arg_cong[of _ _ Sup], intro set_eqI iffI)
      fix x
      assume "x \<in> {sum (\<lambda>i. sum g (B i)) J | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
      then obtain B where hB: "\<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)"
        and hx: "x = sum (\<lambda>i. sum g (B i)) J" by auto
      have hdisj: "\<forall>i\<in>J. \<forall>j\<in>J. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}"
      proof (intro ballI impI)
        fix i j assume "i \<in> J" "j \<in> J" "i \<noteq> j"
        have "A i \<inter> A j = {}" using dsj \<open>i \<in> J\<close> \<open>j \<in> J\<close> \<open>i \<noteq> j\<close> J1(1) by auto
        moreover have "B i \<subseteq> A i" "B j \<subseteq> A j" using hB \<open>i \<in> J\<close> \<open>j \<in> J\<close> by auto
        ultimately show "B i \<inter> B j = {}" by auto
      qed
      have "x = sum g (\<Union> (B ` J))"
        unfolding hx
        by (rule sum.UNION_disjoint[symmetric]) (use J1(2) hB hdisj in auto)
      then show "x \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
        using hB by auto
    next
      fix x
      assume "x \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
      then obtain B where hB: "\<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)"
        and hx: "x = sum g (\<Union> (B ` J))" by auto
      have hdisj: "\<forall>i\<in>J. \<forall>j\<in>J. i \<noteq> j \<longrightarrow> B i \<inter> B j = {}"
      proof (intro ballI impI)
        fix i j assume "i \<in> J" "j \<in> J" "i \<noteq> j"
        have "A i \<inter> A j = {}" using dsj \<open>i \<in> J\<close> \<open>j \<in> J\<close> \<open>i \<noteq> j\<close> J1(1) by auto
        moreover have "B i \<subseteq> A i" "B j \<subseteq> A j" using hB \<open>i \<in> J\<close> \<open>j \<in> J\<close> by auto
        ultimately show "B i \<inter> B j = {}" by auto
      qed
      have "x = sum (\<lambda>i. sum g (B i)) J"
        unfolding hx
        by (rule sum.UNION_disjoint) (use J1(2) hB hdisj in auto)
      then show "x \<in> {sum (\<lambda>i. sum g (B i)) J | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
        using hB by auto
    qed
    have step1c:
      "Sup {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)} =
       Sup {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}"
    proof (rule Sup_cong)
      show "{sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)} \<noteq> {} \<or>
            {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B} \<noteq> {}" by auto
    next
      show "\<forall>a \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}.
            \<exists>b \<in> {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}. a \<le> b"
      proof (intro ballI)
        fix a assume "a \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
        then obtain B where hB: "\<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)"
          and ha: "a = sum g (\<Union> (B ` J))" by auto
        show "\<exists>b \<in> {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}. a \<le> b"
        proof (intro bexI[of _ "sum g (\<Union> (B ` J))"])
          show "sum g (\<Union> (B ` J)) \<in> {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}"
            using J1 hB by force
          show "a \<le> sum g (\<Union> (B ` J))" using ha by simp
        qed
      qed
    next
      show "\<forall>b \<in> {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}.
            \<exists>a \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}. b \<le> a"
      proof (intro ballI)
        fix b assume "b \<in> {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B}"
        then obtain C where hCsub: "C \<subseteq> \<Union> (A ` J)" "finite C"
          and hb: "b = sum g C" by auto
        show "\<exists>a \<in> {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}. b \<le> a"
        proof (intro bexI[of _ "sum g (\<Union> ((\<lambda>i. C \<inter> A i) ` J))"])
          show "b \<le> sum g (\<Union> ((\<lambda>i. C \<inter> A i) ` J))"
            using hCsub unfolding incl_UNION_aux2 by (auto simp: hb)
          show "sum g (\<Union> ((\<lambda>i. C \<inter> A i) ` J)) \<in>
                {sum g (\<Union> (B ` J)) | B. \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
            using J1 hCsub by blast
        qed
      qed
    qed
    have step1d:
      "Sup {sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B} \<le>
       Sup {sum g B | B. B \<subseteq> \<Union> (A ` I) \<and> finite B}"
    proof (rule cSup_subset_mono)
      show "{sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B} \<noteq> {}" by auto
      show "{sum g B | B. B \<subseteq> \<Union> (A ` J) \<and> finite B} \<subseteq>
            {sum g B | B. B \<subseteq> \<Union> (A ` I) \<and> finite B}"
        using J1 by (force intro: Union_mono)
    qed simp
    show "(\<Sum>i\<in>J. Sup {y. \<exists>B\<subseteq>A i. finite B \<and> y = sum g B}) \<le>
          Sup {y. \<exists>B\<subseteq>\<Union> (A ` I). finite B \<and> y = sum g B}"
      using step1a step1b step1c step1d
      by (smt (verit, best) Collect_eqI order.trans order.refl sum_mono)
  qed
  show ?thesis
    unfolding isum_def
  proof (intro Sup_image_congL ballI)
    show "{B |B. B \<subseteq> \<Union> (A ` I) \<and> finite B} \<noteq> {}" by auto
  next
    fix B assume hB: "B \<in> {B |B. B \<subseteq> \<Union> (A ` I) \<and> finite B}"
    then have hBsub: "B \<subseteq> \<Union> (A ` I)" and hBfin: "finite B" by blast+
    let ?J = "{i. i \<in> I \<and> B \<inter> A i \<noteq> {}}"
    show "\<exists>b \<in> {B |B. B \<subseteq> I \<and> finite B}.
          sum g B \<le> (\<Sum>i\<in>b. Sup (sum g ` {B |B. B \<subseteq> A i \<and> finite B}))"
    proof (intro bexI[of _ ?J])
      have "sum g B \<le> sum (\<lambda>i. Sup {y. \<exists>x\<in>{B |B. B \<subseteq> A i \<and> finite B}. y = sum g x}) ?J"
      proof -
        have hJfin: "finite ?J" using dsj hBsub hBfin disjoint_finite_aux by blast
        have hJsub: "?J \<subseteq> I" by auto
        have hdecomp: "B = \<Union> ((\<lambda>i. B \<inter> A i) ` ?J)"
          using incl_UNION_aux[OF hBsub] by simp
        have hdisj_J: "\<forall>i\<in>?J. \<forall>j\<in>?J. i \<noteq> j \<longrightarrow> (B \<inter> A i) \<inter> (B \<inter> A j) = {}"
          using dsj hJsub by auto
        have hfin_J: "\<forall>i\<in>?J. finite (B \<inter> A i)"
          using hBfin by auto
        have hsum_eq: "sum g B = sum (\<lambda>i. sum g (B \<inter> A i)) ?J"
          by (subst hdecomp, rule comm_monoid_add_class.sum.UNION_disjoint)
            (use hJfin hdisj_J hfin_J in auto)
        show ?thesis
          unfolding hsum_eq
        proof (rule sum_mono)
          fix i assume "i \<in> ?J"
          then have "B \<inter> A i \<subseteq> A i" "finite (B \<inter> A i)" using hBfin by auto
          with hBsub show "sum g (B \<inter> A i) \<le> Sup {y. \<exists>x\<in>{B |B. B \<subseteq> A i \<and> finite B}. y = sum g x}"
            by (intro cSup_upper) auto
        qed
      qed
      then show "sum g B \<le> (\<Sum>i | i \<in> I \<and> B \<inter> A i \<noteq> {}. Sup (sum g ` {B |B. B \<subseteq> A i \<and> finite B}))"
        by (rule order_trans) (auto intro!: Sup_mono sum_mono)
      show "?J \<in> {B |B. B \<subseteq> I \<and> finite B}"
        using dsj hBsub hBfin disjoint_finite_aux by force
    qed
  next
    fix J assume hB: "J \<in> {B |B. B \<subseteq> I \<and> finite B}"
    then have J1: "J \<subseteq> I" "finite J" by blast+
    show "(\<Sum>i\<in>J. Sup (sum g ` {B |B. B \<subseteq> A i \<and> finite B}))
         \<le> Sup (sum g ` {B |B. B \<subseteq> \<Union> (A ` I) \<and> finite B})"
      using step1[OF J1] by (auto simp: image_def)
  qed
qed

lemma isum_Un[simp]: 
  assumes "A1 \<inter> A2 = {}"
  shows "isum f (A1 \<union> A2) = isum f A1 + isum f A2"
proof-
  have [simp]: "isum (\<lambda>i. isum f (case i of 0 \<Rightarrow> A1 | Suc _ \<Rightarrow> A2)) {0, Suc 0} = isum f A1 + isum f A2"
    by (subst isum_two) auto
  show ?thesis using assms isum_UNION[of "{0,1::nat}" "\<lambda>i. case i of 0 \<Rightarrow> A1 |_ \<Rightarrow> A2" f] by auto
qed

(* thm sum.Sigma *)
lemma isum_Sigma: 
  "isum (\<lambda>(a,b). f a b) (Sigma A Bs) = isum (\<lambda>a. isum (f a) (Bs a)) A"
proof-
  define g where "g \<equiv> \<lambda>(a,b). f a b"
  define Cs where "Cs \<equiv> \<lambda>a. {a} \<times> Bs a"
  have 1: "\<And>a. {a} \<times> Bs a = Pair a ` (Bs a)" by auto
  have 0: "Sigma A Bs = (\<Union>a\<in>A. Cs a)" unfolding Cs_def by auto
  show ?thesis unfolding 0
  proof (subst isum_UNION)
    show "\<forall>i\<in>A. \<forall>j\<in>A. i \<noteq> j \<longrightarrow> Cs i \<inter> Cs j = {}" unfolding Cs_def by auto
  next
    show "isum (\<lambda>i. isum (\<lambda>(x, y). f x y) (Cs i)) A = isum (\<lambda>a. isum (f a) (Bs a)) A"
      unfolding Cs_def
    proof (rule isum_cong)
      show "A = A" ..
    next
      fix a assume "a \<in> A"
      show "isum (\<lambda>(x, y). f x y) ({a} \<times> Bs a) = isum (f a) (Bs a)"
      proof -
        have "isum (\<lambda>(x, y). f x y) ({a} \<times> Bs a) = isum (\<lambda>(x, y). f x y) (Pair a ` Bs a)"
          by (simp add: 1)
        also have "\<dots> = isum (f a) (Bs a)"
          by (subst isum_reindex_cong') (auto simp: o_def)
        finally show ?thesis .
      qed
    qed
  qed
qed

(* Redundant but visually useful: *)
(* thm sum.cartesian_product *)
lemma isum_Times: "isum (\<lambda>(a,b). f a b) (A \<times> B) = isum (\<lambda>a. isum (f a) B) A"
  using isum_Sigma .

(* thm sum.swap *)
lemma isum_swap: "isum (\<lambda>a. isum (f a) B) A = isum (\<lambda>b. isum (\<lambda>a. f a b) A) B" (is "?L = ?R")
proof-
  have 0: "A \<times> B = (\<lambda>(a,b). (b,a)) ` (B \<times> A)" by auto
  have "?L = isum (\<lambda>(a,b). f a b) (A \<times> B)" using isum_Times ..
  also have "\<dots> = isum (\<lambda>(b,a). f a b) (B \<times> A)" unfolding 0 by (subst isum_reindex_cong') (auto simp: o_def intro!: arg_cong2[of _ _ _ _ isum])
  also have "\<dots> = ?R" by (subst isum_Times) auto
  finally show ?thesis .
qed

lemma isum_plus:
  shows "isum (\<lambda>a. f1 a + f2 a) A = isum f1 A + isum f2 A"
proof -
  let ?S = "sum f1 ` {B |B. B \<subseteq> A \<and> finite B}"
  let ?T = "sum f2 ` {B |B. B \<subseteq> A \<and> finite B}"
  have hS: "?S \<noteq> {}" by auto
  have hT: "?T \<noteq> {}" by auto
  have "isum (\<lambda>a. f1 a + f2 a) A =
    Sup {a1 + a2 | a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T}"
  proof (unfold isum_def, rule Sup_cong)
    show "sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B} \<noteq> {} \<or>
      {a1 + a2 |a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T} \<noteq> {}" by auto
    show "\<forall>a \<in> sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B}.
      \<exists>b \<in> {a1 + a2 |a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T}. a \<le> b"
    proof (intro ballI)
      fix a assume "a \<in> sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B}"
      then obtain B where hB: "B \<subseteq> A" "finite B" and ha: "a = sum (\<lambda>a. f1 a + f2 a) B" by auto
      show "\<exists>b \<in> {a1 + a2 |a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T}. a \<le> b"
        using ha sum.distrib[of f1 f2 B] hB
        by (intro bexI[of _ "sum f1 B + sum f2 B"]) auto
    qed
    show "\<forall>b \<in> {a1 + a2 |a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T}.
      \<exists>a \<in> sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B}. b \<le> a"
    proof (intro ballI)
      fix b assume "b \<in> {a1 + a2 |a1 a2. a1 \<in> ?S \<and> a2 \<in> ?T}"
      then obtain B1 B2 where hB1: "B1 \<subseteq> A" "finite B1" and hB2: "B2 \<subseteq> A" "finite B2"
        and hb: "b = sum f1 B1 + sum f2 B2" by auto
      show "\<exists>a \<in> sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B}. b \<le> a"
      proof (intro bexI[of _ "sum (\<lambda>a. f1 a + f2 a) (B1 \<union> B2)"])
        have h1: "sum f1 B1 \<le> sum f1 (B1 \<union> B2)" using hB1 hB2 by (intro sum_mono2) auto
        have h2: "sum f2 B2 \<le> sum f2 (B1 \<union> B2)" using hB1 hB2 by (intro sum_mono2) auto
        show "b \<le> sum (\<lambda>a. f1 a + f2 a) (B1 \<union> B2)"
          using hb h1 h2 sum.distrib[of f1 f2 "B1 \<union> B2"] by (simp add: add_mono)
        show "sum (\<lambda>a. f1 a + f2 a) (B1 \<union> B2) \<in> sum (\<lambda>a. f1 a + f2 a) ` {B |B. B \<subseteq> A \<and> finite B}"
          using hB1 hB2 by auto
      qed
    qed
  qed
  also have "... = Sup ?S + Sup ?T"
    by (subst plus_Sup_commute'[symmetric, OF hS hT]) simp
  finally show ?thesis unfolding isum_def .
qed

end