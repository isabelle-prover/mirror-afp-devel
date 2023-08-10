(* Title:      Matrix Peano Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Matrix Peano Algebras\<close>

text \<open>
We define a Boolean matrix representation of natural numbers up to \<open>n\<close>, where \<open>n\<close> the size of an enumeration type \<open>'a::enum\<close>.
Numbers (obtained by \<open>Z_matrix\<close> for \<open>0\<close> and \<open>N_matrix n\<close> for \<open>n\<close>) are represented as relational vectors.
The total successor function (\<open>S_matrix\<close>, modulo \<open>n\<close>) and the partial successor function (\<open>S'_matrix\<close>, for numbers up to \<open>n-1\<close>) are relations that are (partial) functions.

We give an order-embedding of \<open>nat\<close> into this representation.
We show that this representation satisfies a relational version of the Peano axioms.
We also implement a function \<open>CP_matrix\<close> that chooses a number in a non-empty set.
\<close>

theory Matrix_Peano_Algebras

imports Aggregation_Algebras.M_Choose_Component Relational_Disjoint_Set_Forests.More_Disjoint_Set_Forests

begin

no_notation
  uminus ("- _" [81] 80) and
  minus_class.minus (infixl "-" 65)

definition Z_matrix :: "('a::enum,'b::{bot,top}) square" ("mZero") where "mZero = (\<lambda>(i,j) . if i = hd enum_class.enum then top else bot)"
definition S_matrix :: "('a::enum,'b::{bot,top}) square" ("msuccmod") where "msuccmod = (\<lambda>(i,j) . let e = (enum_class.enum :: 'a list) in if (\<exists>k . Suc k<length e \<and> i = e ! k \<and> j = e ! Suc k) \<or> (i = e ! minus_class.minus (length e) 1 \<and> j = hd e) then top else bot)"
definition S'_matrix :: "('a::enum,'b::{bot,top}) square" ("msucc") where "msucc = (\<lambda>(i,j) . let e = (enum_class.enum :: 'a list) in if \<exists>k . Suc k<length e \<and> i = e ! k \<and> j = e ! Suc k then top else bot)"
definition N_matrix :: "nat \<Rightarrow> ('a::enum,'b::{bot,top}) square" ("mnat") where "mnat n = (\<lambda>(i,j) . if i = enum_class.enum ! n then top else bot)"
definition CP_matrix  :: "('a::enum,'b::{bot,uminus}) square \<Rightarrow> ('a,'b) square" ("mcp") where "mcp f = (\<lambda>(i,j) . if Some i = find (\<lambda>x . f (x,x) \<noteq> bot) enum_class.enum then uminus_class.uminus (uminus_class.uminus (f (i,j))) else bot)"

lemma S'_matrix_S_matrix:
  "(msucc :: ('a::enum,'b::stone_relation_algebra) square) = msuccmod \<ominus> mZero\<^sup>t"
proof (rule ext, rule prod_cases)
  let ?e = "enum_class.enum :: 'a list"
  let ?h = "hd ?e"
  let ?s = "msuccmod :: ('a,'b) square"
  let ?s' = "msucc :: ('a,'b) square"
  let ?z = "mZero :: ('a,'b) square"
  fix i j
  have "?s' (i,j) = ?s (i,j) - ?z (j,i)"
  proof (cases "j = ?h")
    case True
    have "?s' (i,j) = bot"
    proof (unfold S'_matrix_def, clarsimp)
      fix k
      assume 1: "Suc k < length ?e" "j = ?e ! Suc k"
      have "(UNIV :: 'a set) \<noteq> {}"
        by simp
      hence "?e ! Suc k = ?e ! 0"
        using 1 by (simp add: hd_conv_nth UNIV_enum True)
      hence "Suc k = 0"
        apply (subst nth_eq_iff_index_eq[THEN sym, of ?e])
        using 1 enum_distinct by auto
      thus "top = bot"
        by simp
    qed
    thus ?thesis
      by (simp add: Z_matrix_def True)
  next
    case False
    thus ?thesis
      by (simp add: Z_matrix_def S_matrix_def S'_matrix_def)
  qed
  thus "?s' (i,j) = (?s \<ominus> ?z\<^sup>t) (i,j)"
    by (simp add: minus_matrix_def conv_matrix_def Z_matrix_def)
qed

lemma N_matrix_power_S:
  "n < length (enum_class.enum :: 'a list) \<longrightarrow> mnat n = matrix_monoid.power (msuccmod\<^sup>t) n \<odot> (mZero :: ('a::enum,'b::stone_relation_algebra) square)"
proof (induct n)
  let ?z = "mZero :: ('a,'b) square"
  let ?s = "msuccmod :: ('a,'b) square"
  let ?e = "enum_class.enum :: 'a list"
  let ?h = "hd ?e"
  let ?l = "length ?e"
  let ?g = "?e ! minus_class.minus ?l 1"
  let ?p = "matrix_monoid.power (?s\<^sup>t)"
  case 0
  have "(UNIV :: 'a set) \<noteq> {}"
    by simp
  hence "?h = ?e ! 0"
    by (simp add: hd_conv_nth UNIV_enum)
  thus ?case
    by (simp add: N_matrix_def Z_matrix_def)
  case (Suc n)
  assume 1: "n < ?l \<longrightarrow> mnat n = ?p n \<odot> ?z"
  show "Suc n < ?l \<longrightarrow> mnat (Suc n) = ?p (Suc n) \<odot> ?z"
  proof
    assume 2: "Suc n < ?l"
    hence "n < ?l"
      by simp
    hence "\<forall>l<?l . (?e ! l = ?e ! n \<longrightarrow> l = n)"
      using nth_eq_iff_index_eq enum_distinct by auto
    hence 3: "\<And>i . (\<exists>l<?l . ?e ! n = ?e ! l \<and> i = ?e ! Suc l) \<longrightarrow> (i = ?e ! Suc n)"
      by auto
    have 4: "\<And>i . (\<exists>l . Suc l<?l \<and> ?e ! n = ?e ! l \<and> i = ?e ! Suc l) \<longleftrightarrow> (i = ?e ! Suc n)"
      apply (rule iffI)
      using 3 apply (metis Suc_lessD)
      using 2 by auto
    show "mnat (Suc n) = ?p (Suc n) \<odot> ?z"
    proof (rule ext, rule prod_cases)
      fix i j :: 'a
      have "(?p (Suc n) \<odot> ?z) (i,j) = (?s\<^sup>t \<odot> mnat n) (i,j)"
        using 1 2 by (simp add: matrix_monoid.mult_assoc)
      also have "... = (\<Squnion>\<^sub>k ((?s (k,i))\<^sup>T * mnat n (k,j)))"
        by (simp add: times_matrix_def conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>k ((if (\<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l) \<or> (k = ?g \<and> i = ?h) then top else bot)\<^sup>T * (if k = ?e ! n then top else bot)))"
        by (simp add: S_matrix_def N_matrix_def)
      also have "... = (\<Squnion>\<^sub>k ((if (\<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l) \<or> (k = ?g \<and> i = ?h) then top else bot) * (if k = ?e ! n then top else bot)))"
        by (smt (verit, best) sup_monoid.sum.cong symmetric_bot_closed symmetric_top_closed)
      also have "... = (\<Squnion>\<^sub>k (if (\<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! n) \<or> (k = ?g \<and> i = ?h \<and> k = ?e ! n) then top else bot))"
        by (smt (verit, best) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
      also have "... = (if \<exists>l . Suc l<length ?e \<and> ?e ! n = ?e ! l \<and> i = ?e ! Suc l then top else bot)"
      proof -
        have "\<And>k . \<not>(k = ?g \<and> i = ?h \<and> k = ?e ! n)"
          using 2 distinct_conv_nth[of ?e] enum_distinct by auto
        thus ?thesis
          by (smt (verit, del_insts) comp_inf.ub_sum sup.order_iff sup_monoid.sum.neutral sup_top_right)
      qed
      also have "... = (if i = ?e ! Suc n then top else bot)"
        using 4 by simp
      also have "... = mnat (Suc n) (i,j)"
        by (simp add: N_matrix_def)
      finally show "mnat (Suc n) (i,j) = (?p (Suc n) \<odot> ?z) (i,j)"
        by simp
    qed
  qed
qed

lemma N_matrix_power_S':
  "n < length (enum_class.enum :: 'a list) \<longrightarrow> mnat n = matrix_monoid.power (msucc\<^sup>t) n \<odot> (mZero :: ('a::enum,'b::stone_relation_algebra) square)"
proof (induct n)
  let ?z = "mZero :: ('a,'b) square"
  let ?s = "msucc :: ('a,'b) square"
  let ?e = "enum_class.enum :: 'a list"
  let ?h = "hd ?e"
  let ?l = "length ?e"
  let ?p = "matrix_monoid.power (?s\<^sup>t)"
  case 0
  have "(UNIV :: 'a set) \<noteq> {}"
    by simp
  hence "?h = ?e ! 0"
    by (simp add: hd_conv_nth UNIV_enum)
  thus ?case
    by (simp add: N_matrix_def Z_matrix_def)
  case (Suc n)
  assume 1: "n < ?l \<longrightarrow> mnat n = ?p n \<odot> ?z"
  show "Suc n < ?l \<longrightarrow> mnat (Suc n) = ?p (Suc n) \<odot> ?z"
  proof
    assume 2: "Suc n < ?l"
    hence "n < ?l"
      by simp
    hence "\<forall>l<?l . (?e ! l = ?e ! n \<longrightarrow> l = n)"
      using nth_eq_iff_index_eq enum_distinct by auto
    hence 3: "\<And>i . (\<exists>l<?l . ?e ! n = ?e ! l \<and> i = ?e ! Suc l) \<longrightarrow> (i = ?e ! Suc n)"
      by auto
    have 4: "\<And>i . (\<exists>l . Suc l<?l \<and> ?e ! n = ?e ! l \<and> i = ?e ! Suc l) \<longleftrightarrow> (i = ?e ! Suc n)"
      apply (rule iffI)
      using 3 apply (metis Suc_lessD)
      using 2 by auto
    show "mnat (Suc n) = ?p (Suc n) \<odot> ?z"
    proof (rule ext, rule prod_cases)
      fix i j :: 'a
      have "(?p (Suc n) \<odot> ?z) (i,j) = (?s\<^sup>t \<odot> mnat n) (i,j)"
        using 1 2 by (simp add: matrix_monoid.mult_assoc)
      also have "... = (\<Squnion>\<^sub>k ((?s (k,i))\<^sup>T * mnat n (k,j)))"
        by (simp add: times_matrix_def conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>k ((if \<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l then top else bot)\<^sup>T * (if k = ?e ! n then top else bot)))"
        by (simp add: S'_matrix_def N_matrix_def)
      also have "... = (\<Squnion>\<^sub>k ((if \<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l then top else bot) * (if k = ?e ! n then top else bot)))"
        by (smt (verit, best) sup_monoid.sum.cong symmetric_bot_closed symmetric_top_closed)
      also have "... = (\<Squnion>\<^sub>k (if \<exists>l . Suc l<length ?e \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! n then top else bot))"
        by (smt (verit, best) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
      also have "... = (if \<exists>l . Suc l<length ?e \<and> ?e ! n = ?e ! l \<and> i = ?e ! Suc l then top else bot)"
        by (smt (verit, del_insts) comp_inf.ub_sum sup.order_iff sup_monoid.sum.neutral sup_top_right)
      also have "... = (if i = ?e ! Suc n then top else bot)"
        using 4 by simp
      also have "... = mnat (Suc n) (i,j)"
        by (simp add: N_matrix_def)
      finally show "mnat (Suc n) (i,j) = (?p (Suc n) \<odot> ?z) (i,j)"
        by simp
    qed
  qed
qed

lemma N_matrix_power_S'_hom_zero:
  "mnat 0 = (mZero :: ('a::enum,'b::stone_relation_algebra) square)"
proof -
  let ?e = "enum_class.enum :: 'a list"
  have "(UNIV :: 'a set) = set ?e"
    using UNIV_enum by simp
  hence "0 < length ?e"
    by auto
  thus ?thesis
    using N_matrix_power_S' by force
qed

lemma N_matrix_power_S'_hom_succ:
  assumes "Suc n < length (enum_class.enum :: 'a list)"
    shows "mnat (Suc n) = msucc\<^sup>t \<odot> (mnat n :: ('a::enum,'b::stone_relation_algebra) square)"
proof -
  let ?e = "enum_class.enum :: 'a list"
  let ?z = "mZero :: ('a,'b) square"
  have 1: "n < length ?e"
    using assms by simp
  have "mnat (Suc n) = matrix_monoid.power (msucc\<^sup>t) (Suc n) \<odot> ?z"
    using assms N_matrix_power_S' by blast
  also have "... = msucc\<^sup>t \<odot> matrix_monoid.power (msucc\<^sup>t) n \<odot> ?z"
    by simp
  also have "... = msucc\<^sup>t \<odot> (matrix_monoid.power (msucc\<^sup>t) n \<odot> ?z)"
    by (simp add: matrix_monoid.mult_assoc)
  also have "... = msucc\<^sup>t \<odot> mnat n"
    using 1 by (metis N_matrix_power_S')
  finally show ?thesis
    .
qed

lemma N_matrix_power_S'_hom_inj:
  assumes "m < length (enum_class.enum :: 'a list)"
      and "n < length (enum_class.enum :: 'a list)"
      and "m \<noteq> n"
    shows "mnat m \<noteq> (mnat n :: ('a::enum,'b::stone_relation_algebra_consistent) square)"
proof -
  let ?e = "enum_class.enum :: 'a list"
  let ?m = "?e ! m"
  have 1: "mnat m (?m,?m) = top"
    by (simp add: N_matrix_def)
  have "mnat n (?m,?m) = bot"
    apply (unfold N_matrix_def)
    using assms enum_distinct nth_eq_iff_index_eq by auto
  thus ?thesis
    using 1 by (metis consistent)
qed

syntax
  "_sum_sup_monoid" :: "idt \<Rightarrow> nat \<Rightarrow> 'a::bounded_semilattice_sup_bot \<Rightarrow> 'a" ("(\<Squnion>_<_ . _)" [0,51,10] 10)
translations
  "\<Squnion>x<y . t" => "XCONST sup_monoid.sum (\<lambda>x . t) { x . x < y }"

context bounded_semilattice_sup_bot
begin

lemma ub_sum_nat:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "i < l"
    shows "f i \<le> (\<Squnion>k<l . f k)"
  by (metis (no_types, lifting) assms finite_Collect_less_nat sup_ge1 sup_monoid.sum.remove mem_Collect_eq)

lemma lub_sum_nat:
  fixes f :: "nat \<Rightarrow> 'a"
  assumes "\<forall>k<l . f k \<le> x"
    shows "(\<Squnion>k<l . f k) \<le> x"
  apply (rule finite_subset_induct[where A="{k . k < l}"])
  by (simp_all add: assms)

end

lemma ext_sum_nat:
  fixes l :: nat
  shows "(\<Squnion>k<l . f k x) = (\<Squnion>k<l . f k) x"
  apply (rule finite_subset_induct[where A="{k . k < l}"])
  apply simp
  apply simp
  apply (metis (no_types, lifting) bot_apply sup_monoid.sum.empty)
  by (metis (mono_tags, lifting) sup_apply sup_monoid.sum.insert)

interpretation matrix_skra_peano_1: skra_peano_1 where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and Z = Z_matrix and S = S_matrix
proof
  let ?z = "mZero :: ('a,'b) square"
  let ?s = "msuccmod :: ('a,'b) square"
  let ?e = "enum_class.enum :: 'a list"
  let ?h = "hd ?e"
  let ?l = "length ?e"
  let ?g = "?e ! minus_class.minus ?l 1"
  let ?p = "matrix_monoid.power (?s\<^sup>t)"
  have 1: "?z \<odot> mtop = ?z"
  proof (rule ext, rule prod_cases)
    fix i j :: 'a
    have "(?z \<odot> mtop) (i,j) = (\<Squnion>\<^sub>k (?z (i,k) * top))"
      by (simp add: times_matrix_def top_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if i = ?h then top else bot) * top)"
      by (simp add: Z_matrix_def)
    also have "... = (if i = ?h then top else bot) * (top :: 'b)"
      using sum_const by blast
    also have "... = ?z (i,j)"
      by (simp add: Z_matrix_def)
    finally show "(?z \<odot> mtop) (i,j) = ?z (i,j)"
      .
  qed
  have 2: "?z \<odot> ?z\<^sup>t \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(?z \<odot> ?z\<^sup>t) (i,j) = (\<Squnion>\<^sub>k (?z (i,k) * (?z (j,k))\<^sup>T))"
      by (simp add: times_matrix_def conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if i = ?h then top else bot) * (if j = ?h then top else bot))"
      by (simp add: Z_matrix_def)
    also have "... = (if i = ?h then top else bot) * (if j = ?h then top else bot)"
      using sum_const by blast
    also have "... \<le> mone (i,j)"
      by (simp add: one_matrix_def)
    finally show "(?z \<odot> ?z\<^sup>t) (i,j) \<le> mone (i,j)"
      .
  qed
  have 3: "mtop \<odot> ?z = mtop"
  proof (rule ext, rule prod_cases)
    fix i j :: 'a
    have "mtop (i,j) = (top::'b) * (if ?h = ?h then top else bot)"
      by (simp add: top_matrix_def)
    also have "... \<le> (\<Squnion>\<^sub>k::'a (top * (if k = ?h then top else bot)))"
      by (rule ub_sum)
    also have "... = (\<Squnion>\<^sub>k (top * ?z (k,j)))"
      by (simp add: Z_matrix_def)
    also have "... = (mtop \<odot> ?z) (i,j)"
      by (simp add: times_matrix_def top_matrix_def)
    finally show "(mtop \<odot> ?z) (i,j) = mtop (i,j)"
      by (simp add: inf.le_bot top_matrix_def)
  qed
  show "matrix_stone_relation_algebra.point ?z"
    using 1 2 3 by simp
  have "\<forall>i (j::'a) (k::'a) . (\<exists>l<?l . \<exists>m<?l . k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<longrightarrow> i = j"
    using distinct_conv_nth enum_distinct by auto
  hence 4: "\<forall>i (j::'a) (k::'a) . (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<longrightarrow> i = j"
    by (metis Suc_lessD)
  show "?s\<^sup>t \<odot> ?s \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(?s\<^sup>t \<odot> ?s) (i,j) = (\<Squnion>\<^sub>k (?s (k,i) * ?s (k,j)))"
      by (simp add: times_matrix_def conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a ((if (\<exists>l . Suc l<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l) \<or> (k = ?g \<and> i = ?h) then top else bot) * (if (\<exists>m . Suc m<?l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<or> (k = ?g \<and> j = ?h) then top else bot)))"
      by (simp add: S_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<or> (k = ?g \<and> i = ?h \<and> j = ?h) then top else bot))"
    proof -
      have 5: "\<And>k . \<not>((\<exists>l . Suc l<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l) \<and> (k = ?g \<and> j = ?h))"
        using distinct_conv_nth[of ?e] enum_distinct by auto
      have "\<And>k . \<not>((k = ?g \<and> i = ?h) \<and> (\<exists>m . Suc m<?l \<and> k = ?e ! m \<and> j = ?e ! Suc m))"
        using distinct_conv_nth[of ?e] enum_distinct by auto
      thus ?thesis
        using 5 by (smt (verit) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
    qed
    also have "... \<le> (\<Squnion>\<^sub>k::'a (if i = j then top else bot))"
      using 4 by (smt (verit, best) comp_inf.ub_sum order_top_class.top_greatest sup_monoid.sum.not_neutral_contains_not_neutral top.extremum_uniqueI)
    also have "... \<le> (if i = j then top else bot)"
      by (simp add: sum_const)
    also have "... = mone (i,j)"
      by (simp add: one_matrix_def)
    finally show "(?s\<^sup>t \<odot> ?s) (i,j) \<le> mone (i,j)"
      .
  qed
  have 6: "\<forall>i (j::'a) (k::'a) . (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l \<and> j = ?e ! m \<and> k = ?e ! Suc m) \<longrightarrow> i = j"
    using distinct_conv_nth enum_distinct by auto
  show "?s \<odot> ?s\<^sup>t \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(?s \<odot> ?s\<^sup>t) (i,j) = (\<Squnion>\<^sub>k (?s (i,k) * ?s (j,k)))"
      by (simp add: times_matrix_def conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a ((if (\<exists>l . Suc l<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l) \<or> (i = ?g \<and> k = ?h) then top else bot) * (if (\<exists>m . Suc m<?l \<and> j = ?e ! m \<and> k = ?e ! Suc m) \<or> (j = ?g \<and> k = ?h) then top else bot)))"
      by (simp add: S_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l \<and> j = ?e ! m \<and> k = ?e ! Suc m) \<or> (i = ?g \<and> k = ?h \<and> j = ?g) then top else bot))"
    proof -
      have 7: "\<And>l . Suc l<?l \<longrightarrow> 0<?l"
        by auto
      have 8: "?h = ?e ! 0"
      proof (rule hd_conv_nth, rule)
        assume "?e = []"
        hence "(UNIV::'a set) = {}"
          by (auto simp add: UNIV_enum)
        thus "False"
          by simp
      qed
      have 9: "\<And>k . \<not>((\<exists>l . Suc l<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l) \<and> (j = ?g \<and> k = ?h))"
        using 7 8 distinct_conv_nth[of ?e] enum_distinct by auto
      have "\<And>k . \<not>((i = ?g \<and> k = ?h) \<and> (\<exists>m . Suc m<?l \<and> j = ?e ! m \<and> k = ?e ! Suc m))"
        using 7 8 distinct_conv_nth[of ?e] enum_distinct by auto
      thus ?thesis
        using 9 by (smt (verit) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
    qed
    also have "... \<le> (\<Squnion>\<^sub>k::'a (if i = j then top else bot))"
      using 6 by (smt (verit, best) comp_inf.ub_sum order_top_class.top_greatest sup_monoid.sum.not_neutral_contains_not_neutral top.extremum_uniqueI)
    also have "... \<le> (if i = j then top else bot)"
      by simp
    also have "... = mone (i,j)"
      by (simp add: one_matrix_def)
    finally show "(?s \<odot> ?s\<^sup>t) (i,j) \<le> mone (i,j)"
      .
  qed
  have "(mtop :: ('a,'b) square) = (\<Squnion>k<?l . mnat k)"
  proof (rule ext, rule prod_cases)
    fix i j :: 'a
    have "mtop (i,j) = (top :: 'b)"
      by (simp add: top_matrix_def)
    also have "... = (\<Squnion>k<?l . (if i = ?e ! k then top else bot))"
    proof -
      have "i \<in> set ?e"
        using UNIV_enum by auto
      from this obtain k where 6: "k < ?l \<and> i = ?e ! k"
        by (metis in_set_conv_nth)
      hence "(\<lambda>k . if i = ?e ! k then top else bot) k \<le> (\<Squnion>k<?l . (if i = ?e ! k then top else bot :: 'b))"
        by (metis ub_sum_nat)
      hence "top \<le> (\<Squnion>k<?l . (if i = ?e ! k then top else bot :: 'b))"
        using 6 by simp
      thus ?thesis
        using top.extremum_uniqueI by force
    qed
    also have "... = (\<Squnion>k<?l . mnat k (i,j))"
      by (simp add: N_matrix_def)
    also have "... = (\<Squnion>k<?l . mnat k) (i,j)"
      by (simp add: ext_sum_nat)
    finally show "(mtop (i,j) :: 'b) = (\<Squnion>k<?l . mnat k) (i,j)"
      .
  qed
  also have "... = (\<Squnion>k<?l . ?p k \<odot> ?z)"
  proof -
    have "\<And>k . k<?l \<longrightarrow> mnat k = ?p k \<odot> ?z"
      using N_matrix_power_S by auto
    thus ?thesis
      by (metis (no_types, lifting) mem_Collect_eq sup_monoid.sum.cong)
  qed
  also have "... \<preceq> ?s\<^sup>t\<^sup>\<odot> \<odot> ?z"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(\<Squnion>k<?l . ?p k \<odot> ?z) (i,j) = (\<Squnion>k<?l . (?p k \<odot> ?z) (i,j))"
      by (metis ext_sum_nat)
    also have "... \<le> (?s\<^sup>t\<^sup>\<odot> \<odot> ?z) (i,j)"
      apply (rule lub_sum_nat)
      by (metis less_eq_matrix_def matrix_idempotent_semiring.mult_left_isotone matrix_kleene_algebra.star.power_below_circ)
    finally show "(\<Squnion>k<?l . ?p k \<odot> ?z) (i,j) \<le> (?s\<^sup>t\<^sup>\<odot> \<odot> ?z) (i,j)"
      .
  qed
  finally show "?s\<^sup>t\<^sup>\<odot> \<odot> ?z = mtop"
    by (simp add: matrix_order.antisym_conv)
qed

interpretation matrix_skra_peano_2: skra_peano_2 where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and Z = Z_matrix and S = S_matrix
proof
  let ?s = "msuccmod :: ('a,'b) square"
  let ?e = "enum_class.enum :: 'a list"
  let ?h = "hd ?e"
  let ?l = "length ?e"
  let ?g = "?e ! minus_class.minus ?l 1"
  show "matrix_bounded_idempotent_semiring.total ?s"
  proof (rule ext, rule prod_cases)
    fix i j :: 'a
    have "(?s \<odot> mtop) (i,j) = (\<Squnion>\<^sub>k (?s (i,k) * top))"
      by (simp add: times_matrix_def top_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a if (\<exists>l . Suc l<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l) \<or> (i = ?g \<and> k = ?h) then top else bot)"
      by (simp add: S_matrix_def)
    also have "... = top"
    proof -
      have "\<And>i . (\<exists>l . Suc l<?l \<and> i = ?e ! l) \<or> i = ?g"
        by (metis in_set_conv_nth in_enum Suc_lessI diff_Suc_1)
      hence "\<And>i . \<exists>k . (\<exists>l . Suc l<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l) \<or> (i = ?g \<and> k = ?h)"
        by blast
      thus ?thesis
        by (smt (verit, ccfv_threshold) comp_inf.ub_sum top.extremum_uniqueI)
    qed
    finally show "(?s \<odot> mtop) (i,j) = mtop (i,j)"
      by (simp add: top_matrix_def)
  qed
qed

interpretation matrix_skra_peano_3: skra_peano_3 where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and Z = Z_matrix and S = S_matrix
proof (unfold_locales, rule finite_surj)
  show "finite (UNIV :: 'a rel set)"
    by simp
  let ?f = "\<lambda>R p . if p \<in> R then top else bot"
  show "{ f :: ('a,'b) square . matrix_p_algebra.regular f } \<subseteq> range ?f"
  proof
    fix f :: "('a,'b) square"
    let ?R = "{ (x,y) . f (x,y) = top }"
    assume "f \<in> { f . matrix_p_algebra.regular f }"
    hence "matrix_p_algebra.regular f"
      by simp
    hence "\<And>p . f p \<noteq> top \<longrightarrow> f p = bot"
      by (metis linorder_stone_algebra_expansion_class.uminus_def uminus_matrix_def)
    hence "f = ?f ?R"
      by fastforce
    thus "f \<in> range ?f"
      by blast
  qed
qed

interpretation matrix_skra_peano_4: skra_peano_4 where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_plus_expansion) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and Z = Z_matrix and S = S_matrix and choose_point = agg_square_m_kleene_algebra_2.m_choose_component_algebra_tarski.choose_component_point
  apply unfold_locales
  apply (simp add: agg_square_m_kleene_algebra_2.m_choose_component_algebra_tarski.choose_component_point_point)
  by (simp add: agg_square_m_kleene_algebra_2.m_choose_component_algebra_tarski.choose_component_point_decreasing)

interpretation matrix'_skra_peano_1: skra_peano_1 where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and Z = Z_matrix and S = S'_matrix
proof
  let ?z = "mZero :: ('a,'b) square"
  let ?s = "msucc :: ('a,'b) square"
  let ?e = "enum_class.enum :: 'a list"
  let ?l = "length ?e"
  let ?p = "matrix_monoid.power (?s\<^sup>t)"
  show "matrix_stone_relation_algebra.point ?z"
    using matrix_skra_peano_1.Z_point by auto
  have "\<forall>i (j::'a) (k::'a) . (\<exists>l<?l . \<exists>m<?l . k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<longrightarrow> i = j"
    using distinct_conv_nth enum_distinct by auto
  hence 4: "\<forall>i (j::'a) (k::'a) . (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) \<longrightarrow> i = j"
    by (metis Suc_lessD)
  show "?s\<^sup>t \<odot> ?s \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(?s\<^sup>t \<odot> ?s) (i,j) = (\<Squnion>\<^sub>k (?s (k,i) * ?s (k,j)))"
      by (simp add: times_matrix_def conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a ((if \<exists>l . Suc l<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l then top else bot) * (if \<exists>m . Suc m<?l \<and> k = ?e ! m \<and> j = ?e ! Suc m then top else bot)))"
      by (simp add: S'_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> k = ?e ! l \<and> i = ?e ! Suc l \<and> k = ?e ! m \<and> j = ?e ! Suc m) then top else bot))"
      by (smt (verit) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
    also have "... \<le> (\<Squnion>\<^sub>k::'a (if i = j then top else bot))"
      using 4 by (smt (verit, best) comp_inf.ub_sum order_top_class.top_greatest sup_monoid.sum.not_neutral_contains_not_neutral top.extremum_uniqueI)
    also have "... \<le> (if i = j then top else bot)"
      by (simp add: sum_const)
    also have "... = mone (i,j)"
      by (simp add: one_matrix_def)
    finally show "(?s\<^sup>t \<odot> ?s) (i,j) \<le> mone (i,j)"
      .
  qed
  have 5: "\<forall>i (j::'a) (k::'a) . (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l \<and> j = ?e ! m \<and> k = ?e ! Suc m) \<longrightarrow> i = j"
    using distinct_conv_nth enum_distinct by auto
  show "?s \<odot> ?s\<^sup>t \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(?s \<odot> ?s\<^sup>t) (i,j) = (\<Squnion>\<^sub>k (?s (i,k) * ?s (j,k)))"
      by (simp add: times_matrix_def conv_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a ((if \<exists>l . Suc l<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l then top else bot) * (if \<exists>m . Suc m<?l \<and> j = ?e ! m \<and> k = ?e ! Suc m then top else bot)))"
      by (simp add: S'_matrix_def)
    also have "... = (\<Squnion>\<^sub>k::'a (if (\<exists>l m . Suc l<?l \<and> Suc m<?l \<and> i = ?e ! l \<and> k = ?e ! Suc l \<and> j = ?e ! m \<and> k = ?e ! Suc m) then top else bot))"
      by (smt (verit) covector_bot_closed idempotent_bot_closed sup_monoid.sum.cong surjective_top_closed vector_bot_closed)
    also have "... \<le> (\<Squnion>\<^sub>k::'a (if i = j then top else bot))"
      using 5 by (smt (verit, best) comp_inf.ub_sum order_top_class.top_greatest sup_monoid.sum.not_neutral_contains_not_neutral top.extremum_uniqueI)
    also have "... \<le> (if i = j then top else bot)"
      by simp
    also have "... = mone (i,j)"
      by (simp add: one_matrix_def)
    finally show "(?s \<odot> ?s\<^sup>t) (i,j) \<le> mone (i,j)"
      .
  qed
  have "(mtop :: ('a,'b) square) = (\<Squnion>k<?l . mnat k)"
  proof (rule ext, rule prod_cases)
    fix i j :: 'a
    have "mtop (i,j) = (top :: 'b)"
      by (simp add: top_matrix_def)
    also have "... = (\<Squnion>k<?l . (if i = ?e ! k then top else bot))"
    proof -
      have "i \<in> set ?e"
        using UNIV_enum by auto
      from this obtain k where 6: "k < ?l \<and> i = ?e ! k"
        by (metis in_set_conv_nth)
      hence "(\<lambda>k . if i = ?e ! k then top else bot) k \<le> (\<Squnion>k<?l . (if i = ?e ! k then top else bot :: 'b))"
        by (metis ub_sum_nat)
      hence "top \<le> (\<Squnion>k<?l . (if i = ?e ! k then top else bot :: 'b))"
        using 6 by simp
      thus ?thesis
        using top.extremum_uniqueI by force
    qed
    also have "... = (\<Squnion>k<?l . mnat k (i,j))"
      by (simp add: N_matrix_def)
    also have "... = (\<Squnion>k<?l . mnat k) (i,j)"
      by (simp add: ext_sum_nat)
    finally show "(mtop (i,j) :: 'b) = (\<Squnion>k<?l . mnat k) (i,j)"
      .
  qed
  also have "... = (\<Squnion>k<?l . ?p k \<odot> ?z)"
  proof -
    have "\<And>k . k<?l \<longrightarrow> mnat k = ?p k \<odot> ?z"
      using N_matrix_power_S' by auto
    thus ?thesis
      by (metis (no_types, lifting) mem_Collect_eq sup_monoid.sum.cong)
  qed
  also have "... \<preceq> ?s\<^sup>t\<^sup>\<odot> \<odot> ?z"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j :: 'a
    have "(\<Squnion>k<?l . ?p k \<odot> ?z) (i,j) = (\<Squnion>k<?l . (?p k \<odot> ?z) (i,j))"
      by (metis ext_sum_nat)
    also have "... \<le> (?s\<^sup>t\<^sup>\<odot> \<odot> ?z) (i,j)"
      apply (rule lub_sum_nat)
      by (metis less_eq_matrix_def matrix_idempotent_semiring.mult_left_isotone matrix_kleene_algebra.star.power_below_circ)
    finally show "(\<Squnion>k<?l . ?p k \<odot> ?z) (i,j) \<le> (?s\<^sup>t\<^sup>\<odot> \<odot> ?z) (i,j)"
      .
  qed
  finally show "?s\<^sup>t\<^sup>\<odot> \<odot> ?z = mtop"
    by (simp add: matrix_order.antisym_conv)
qed

lemma nat_less_lesseq_pred:
  "(m :: nat) < n \<Longrightarrow> m \<le> minus_class.minus n 1"
  by simp

lemma S'_matrix_acyclic:
  "matrix_stone_kleene_relation_algebra.acyclic (msucc :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square)"
proof (rule ccontr)
  let ?e = "enum_class.enum :: 'a list"
  let ?l = "length ?e"
  let ?l1 = "minus_class.minus ?l 1"
  let ?s = "msucc :: ('a,'b) square"
  have "(UNIV :: 'a set) \<noteq> {}"
    by simp
  hence 1: "?e \<noteq> []"
    by (simp add: UNIV_enum)
  hence 2: "?l \<noteq> 0"
    by simp
  assume "\<not> matrix_stone_kleene_relation_algebra.acyclic ?s"
  hence "?s \<odot> ?s\<^sup>\<odot> \<otimes> mone \<noteq> mbot"
    by (simp add: matrix_p_algebra.pseudo_complement)
  from this obtain i1 i2 where "(?s \<odot> ?s\<^sup>\<odot> \<otimes> mone) (i1,i2) \<noteq> bot"
    by (metis bot_matrix_def ext surj_pair)
  hence 3: "(?s \<odot> ?s\<^sup>\<odot>) (i1,i2) \<sqinter> mone (i1,i2) \<noteq> bot"
    by (simp add: inf_matrix_def)
  hence "mone (i1,i2) \<noteq> (bot :: 'b)"
    by force
  hence "i1 = i2"
    by (metis (mono_tags, lifting) prod.simps(2) one_matrix_def)
  hence "(?s \<odot> ?s\<^sup>\<odot>) (i1,i1) \<noteq> bot"
    using 3 by force
  hence "(\<Squnion>\<^sub>k ?s (i1,k) * (?s\<^sup>\<odot>) (k,i1)) \<noteq> bot"
    by (smt (verit, best) times_matrix_def case_prod_conv sup_monoid.sum.cong)
  from this obtain i3 where 4: "?s (i1,i3) * (?s\<^sup>\<odot>) (i3,i1) \<noteq> bot"
    by force
  hence "?s (i1,i3) \<noteq> bot"
    by force
  hence "(if \<exists>j1 . Suc j1<?l \<and> i1 = ?e ! j1 \<and> i3 = ?e ! Suc j1 then top else bot :: 'b) \<noteq> bot"
    by (simp add: S'_matrix_def)
  from this obtain j1 where 5: "Suc j1 < ?l \<and> i1 = ?e ! j1 \<and> i3 = ?e ! Suc j1"
    by meson
  have "j1 \<noteq> ?l1"
    using 5 enum_distinct by auto
  hence "i1 \<noteq> last ?e"
    apply (subst last_conv_nth)
    using 1 apply simp
    apply (subst 5)
    apply (subst nth_eq_iff_index_eq[of ?e])
    using 1 5 enum_distinct by auto
  hence 6: "mone (last ?e,i1) = (bot :: 'b)"
    by (simp add: one_matrix_def)
  have 7: "(?s\<^sup>\<odot>) (i3,i1) \<noteq> bot"
    using 4 by force
  have "\<And>j2 . Suc j1 + j2 < ?l \<longrightarrow> (?s\<^sup>\<odot>) (?e ! (Suc j1 + j2),i1) \<noteq> bot"
  proof -
    fix j2
    show "Suc j1 + j2 < ?l \<longrightarrow> (?s\<^sup>\<odot>) (?e ! (Suc j1 + j2),i1) \<noteq> bot"
    proof (induct j2)
      case 0
      show ?case
        using 5 7 by simp
    next
      case (Suc j3)
      show ?case
      proof
        assume 8: "Suc j1 + Suc j3 < ?l"
        hence "(?s\<^sup>\<odot>) (?e ! (Suc j1 + j3),i1) \<noteq> bot"
          using Suc by simp
        hence "(mone \<oplus> ?s \<odot> ?s\<^sup>\<odot>) (?e ! (Suc j1 + j3),i1) \<noteq> bot"
          by (metis matrix_kleene_algebra.star_left_unfold_equal)
        hence 9: "mone (?e ! (Suc j1 + j3),i1) \<squnion> (?s \<odot> ?s\<^sup>\<odot>) (?e ! (Suc j1 + j3),i1) \<noteq> bot"
          by (simp add: sup_matrix_def)
        have "?e ! (Suc j1 + j3) \<noteq> i1"
          using 5 8 distinct_conv_nth[of ?e] enum_distinct by auto
        hence "mone (?e ! (Suc j1 + j3),i1) = (bot :: 'b)"
          by (simp add: one_matrix_def)
        hence "(?s \<odot> ?s\<^sup>\<odot>) (?e ! (Suc j1 + j3),i1) \<noteq> bot"
          using 9 by simp
        hence "(\<Squnion>\<^sub>k ?s (?e ! (Suc j1 + j3),k) * (?s\<^sup>\<odot>) (k,i1)) \<noteq> bot"
          by (smt (verit, best) times_matrix_def case_prod_conv sup_monoid.sum.cong)
        from this obtain i4 where 10: "?s (?e ! (Suc j1 + j3),i4) * (?s\<^sup>\<odot>) (i4,i1) \<noteq> bot"
          by force
        hence "?s (?e ! (Suc j1 + j3),i4) \<noteq> bot"
          by force
        hence "(if \<exists>j4 . Suc j4<?l \<and> ?e ! (Suc j1 + j3) = ?e ! j4 \<and> i4 = ?e ! Suc j4 then top else bot :: 'b) \<noteq> bot"
          by (simp add: S'_matrix_def)
        from this obtain j4 where 11: "Suc j4<?l \<and> ?e ! (Suc j1 + j3) = ?e ! j4 \<and> i4 = ?e ! Suc j4"
          by meson
        hence "Suc j1 + j3 = j4"
          apply (subst nth_eq_iff_index_eq[of ?e, THEN sym])
          using 8 enum_distinct by auto
        hence "i4 = ?e ! (Suc j1 + Suc j3)"
          using 11 by simp
        thus "(?s\<^sup>\<odot>) (?e ! (Suc j1 + Suc j3),i1) \<noteq> bot"
          using 10 by force
      qed
    qed
  qed
  hence "\<And>j5 . Suc j1 \<le> j5 \<and> j5 < ?l \<longrightarrow> (?s\<^sup>\<odot>) (?e ! j5,i1) \<noteq> bot"
    using le_Suc_ex by blast
  hence "(?s\<^sup>\<odot>) (last ?e,i1) \<noteq> bot"
    apply (subst last_conv_nth)
    using 1 2 5 nat_less_lesseq_pred by auto
  hence "(mone \<oplus> ?s \<odot> ?s\<^sup>\<odot>) (last ?e,i1) \<noteq> bot"
    by (metis matrix_kleene_algebra.star_left_unfold_equal)
  hence "mone (last ?e,i1) \<squnion> (?s \<odot> ?s\<^sup>\<odot>) (last ?e,i1) \<noteq> bot"
    by (simp add: sup_matrix_def)
  hence "(?s \<odot> ?s\<^sup>\<odot>) (last ?e,i1) \<noteq> bot"
    using 6 by simp
  hence "(\<Squnion>\<^sub>k ?s (last ?e,k) * (?s\<^sup>\<odot>) (k,i1)) \<noteq> bot"
    by (smt (verit, best) times_matrix_def case_prod_conv sup_monoid.sum.cong)
  from this obtain i5 where "?s (last ?e,i5) * (?s\<^sup>\<odot>) (i5,i1) \<noteq> bot"
    by force
  hence "?s (last ?e,i5) \<noteq> bot"
    by force
  hence "(if \<exists>j6 . Suc j6<?l \<and> last ?e = ?e ! j6 \<and> i5 = ?e ! Suc j6 then top else bot :: 'b) \<noteq> bot"
    by (simp add: S'_matrix_def)
  from this obtain j6 where 12: "Suc j6<?l \<and> last ?e = ?e ! j6 \<and> i5 = ?e ! Suc j6"
    by force
  hence "?e ! ?l1 = ?e ! j6"
    using 1 5 by (metis last_conv_nth)
  hence "?l1 = j6"
    apply (subst nth_eq_iff_index_eq[of ?e, THEN sym])
    using 2 12 enum_distinct by auto
  thus False
    using 12 by auto
qed

lemma N_matrix_point:
  assumes "n < length (enum_class.enum :: 'a list)"
    shows "matrix_stone_relation_algebra.point (mnat n :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square)"
proof -
  let ?e = "enum_class.enum :: 'a list"
  let ?n = "mnat n :: ('a,'b) square"
  let ?s = "msucc :: ('a,'b) square"
  let ?z = "mZero :: ('a,'b) square"
  have 1: "?n = matrix_monoid.power (?s\<^sup>t) n \<odot> ?z"
    using assms N_matrix_power_S' by blast
  have "?s = matrix_skra_peano_1.S'"
    by (simp add: S'_matrix_S_matrix inf_matrix_def minus_matrix_def uminus_matrix_def)
  hence 2: "matrix_p_algebra.regular ?s"
    by (metis matrix_skra_peano_2.S'_regular)
  have "?n \<noteq> mbot"
  proof
    assume "?n = mbot"
    hence "?n (?e ! n,?e ! n) = mbot (?e ! n,?e ! n)"
      by simp
    hence "top = (bot :: 'b)"
      by (simp add: N_matrix_def bot_matrix_def)
    thus False
      by (metis bot_not_top)
  qed
  thus "matrix_stone_relation_algebra.point ?n"
    using 1 2 by (metis (no_types, lifting) matrix'_skra_peano_1.S_univalent matrix'_skra_peano_1.Z_point matrix_stone_relation_algebra.injective_power_closed matrix_stone_relation_algebra_tarski_consistent.regular_injective_vector_point_xor_bot matrix_stone_relation_algebra.regular_power_closed matrix_stone_relation_algebra.bijective_regular matrix_stone_relation_algebra.comp_associative matrix_stone_relation_algebra.injective_mult_closed matrix_stone_relation_algebra.regular_conv_closed matrix_stone_relation_algebra.regular_mult_closed matrix_stone_relation_algebra.univalent_conv_injective)
qed

lemma N_matrix_power_S'_hom_lesseq:
  assumes "m < length (enum_class.enum :: 'a list)"
      and "n < length (enum_class.enum :: 'a list)"
    shows "m < n \<longleftrightarrow> mnat m \<preceq> msucc \<odot> msucc\<^sup>\<odot> \<odot> (mnat n :: ('a::enum,'b::linorder_stone_kleene_relation_algebra_tarski_consistent_expansion) square)"
proof -
  let ?m = "mnat m :: ('a,'b) square"
  let ?n = "mnat n :: ('a,'b) square"
  let ?s = "msucc :: ('a,'b) square"
  let ?z = "mZero :: ('a,'b) square"
  have 1: "?m = matrix_monoid.power (?s\<^sup>t) m \<odot> ?z"
    using assms(1) N_matrix_power_S' by blast
  have 2: "?n = matrix_monoid.power (?s\<^sup>t) n \<odot> ?z"
    using assms(2) N_matrix_power_S' by blast
  have 3: "matrix_stone_relation_algebra.point ?m"
    by (simp add: assms(1) N_matrix_point)
  have 4: "matrix_stone_relation_algebra.point ?n"
    by (simp add: assms(2) N_matrix_point)
  show "m < n \<longleftrightarrow> ?m \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?n"
  proof
    assume "m < n"
    from this obtain k where "n = Suc k + m"
      using less_iff_Suc_add by auto
    hence "?n = matrix_monoid.power (?s\<^sup>t) (Suc k) \<odot> matrix_monoid.power (?s\<^sup>t) m \<odot> ?z"
      using 2 by (metis matrix_monoid.power_add)
    also have "... = matrix_monoid.power (?s\<^sup>t) (Suc k) \<odot> ?m"
      using 1 by (simp add: matrix_monoid.mult_assoc)
    also have "... = (matrix_monoid.power ?s (Suc k))\<^sup>t \<odot> ?m"
      by (metis matrix_stone_relation_algebra.power_conv_commute)
    finally have "?m \<preceq> matrix_monoid.power ?s (Suc k) \<odot> ?n"
      using 3 4 by (simp add: matrix_stone_relation_algebra.bijective_reverse)
    also have "... = ?s \<odot> matrix_monoid.power ?s k \<odot> ?n"
      by simp
    also have "... \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?n"
      using matrix_idempotent_semiring.mult_left_isotone matrix_idempotent_semiring.mult_right_isotone matrix_kleene_algebra.star.power_below_circ by blast
    finally show "?m \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?n"
      .
  next
    assume 5: "?m \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?n"
    show "m < n"
    proof (rule ccontr)
      assume "\<not> m < n"
      from this obtain k where "m = k + n"
        by (metis add.commute add_diff_inverse_nat)
      hence "?m = matrix_monoid.power (?s\<^sup>t) k \<odot> matrix_monoid.power (?s\<^sup>t) n \<odot> ?z"
        using 1 by (metis matrix_monoid.power_add)
      also have "... = matrix_monoid.power (?s\<^sup>t) k \<odot> ?n"
        using 2 by (simp add: matrix_monoid.mult_assoc)
      also have "... = (matrix_monoid.power ?s k)\<^sup>t \<odot> ?n"
        by (metis matrix_stone_relation_algebra.power_conv_commute)
      finally have "?n \<preceq> matrix_monoid.power ?s k \<odot> ?m"
        using 3 4 by (simp add: matrix_stone_relation_algebra.bijective_reverse)
      also have "... \<preceq> ?s\<^sup>\<odot> \<odot> ?m"
        using matrix_kleene_algebra.star.power_below_circ matrix_stone_relation_algebra.comp_left_isotone by blast
      finally have "?n \<preceq> ?s\<^sup>\<odot> \<odot> ?m"
        .
      hence "?m \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?s\<^sup>\<odot> \<odot> ?m"
        using 5 by (metis (no_types, opaque_lifting) matrix_monoid.mult_assoc matrix_order.dual_order.trans matrix_stone_relation_algebra.comp_right_isotone)
      hence "?m \<preceq> ?s \<odot> ?s\<^sup>\<odot> \<odot> ?m"
        by (metis matrix_kleene_algebra.star.circ_transitive_equal matrix_monoid.mult_assoc)
      thus False
        using 3 S'_matrix_acyclic matrix_stone_kleene_relation_algebra_consistent.acyclic_reachable_different by blast
    qed
  qed
qed

end

