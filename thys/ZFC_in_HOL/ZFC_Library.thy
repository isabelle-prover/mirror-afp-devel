theory ZFC_Library
  imports "HOL-Library.Countable_Set" "HOL-Library.Equipollence" "HOL-Cardinals.Cardinals"

begin

text\<open>These are a mixture of results that mostly deserve to be installed in the main Isabelle/HOL libraries.\<close>

(*REPLACE*)
notation Sup ("\<Squnion>")
context conditionally_complete_lattice
begin
lemma cSUP_subset_mono: "A \<noteq> {} \<Longrightarrow> bdd_above (g ` B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> \<Squnion>(f ` A) \<le> \<Squnion>(g ` B)"
  by (rule cSUP_mono) auto
end

lemma lepoll_refl [iff]: "A \<lesssim> A"
  by (simp add: subset_imp_lepoll)

lemma empty_lepoll [iff]: "{} \<lesssim> A"
  by (simp add: lepoll_iff)

lemma lepoll_Pow_self: "A \<lesssim> Pow A"
  unfolding lepoll_def inj_def
  proof (intro exI conjI)
    show "inj_on (\<lambda>x. {x}) A"
      by (auto simp: inj_on_def)
qed auto

lemma lesspoll_Pow_self: "A \<prec> Pow A"
  unfolding lesspoll_def
  by (meson lepoll_Pow_self Cantors_paradox bij_betw_def eqpoll_def)

lemma eqpoll_refl [iff]: "A \<approx> A"
  by (simp add: lepoll_antisym subset_imp_lepoll)

lemma inj_on_image_eqpoll_self: "inj_on f A \<Longrightarrow> f ` A \<approx> A"
  by (meson bij_betw_def eqpoll_def eqpoll_sym)

lemma inj_on_image_lepoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<lesssim> B \<longleftrightarrow> A \<lesssim> B"
  by (meson assms image_lepoll lepoll_def lepoll_trans order_refl)

lemma inj_on_image_lepoll_2 [simp]:
  assumes "inj_on f B" shows "A \<lesssim> f ` B \<longleftrightarrow> A \<lesssim> B"
  by (meson assms eq_iff image_lepoll lepoll_def lepoll_trans)

lemma inj_on_image_lesspoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<prec> B \<longleftrightarrow> A \<prec> B"
  by (meson assms image_lepoll le_less lepoll_def lesspoll_trans1)

lemma inj_on_image_lesspoll_2 [simp]:
  assumes "inj_on f B" shows "A \<prec> f ` B \<longleftrightarrow> A \<prec> B"
  by (meson assms eqpoll_sym inj_on_image_eqpoll_self lesspoll_eq_trans)

lemma inj_on_image_eqpoll_1 [simp]:
  assumes "inj_on f A" shows "f ` A \<approx> B \<longleftrightarrow> A \<approx> B"
  by (metis assms eqpoll_trans inj_on_image_eqpoll_self eqpoll_sym)

lemma inj_on_image_eqpoll_2 [simp]:
  assumes "inj_on f B" shows "A \<approx> f ` B \<longleftrightarrow> A \<approx> B"
  by (metis assms inj_on_image_eqpoll_1 eqpoll_sym)

lemma times_square_lepoll: "A \<lesssim> A \<times> A"
  unfolding lepoll_def inj_def
proof (intro exI conjI)
  show "inj_on (\<lambda>x. (x,x)) A"
    by (auto simp: inj_on_def)
qed auto

lemma times_commute_eqpoll: "A \<times> B \<approx> B \<times> A"
  unfolding eqpoll_def
  by (force intro: bij_betw_byWitness [where f = "\<lambda>(x,y). (y,x)" and f' = "\<lambda>(x,y). (y,x)"])

lemma times_assoc_eqpoll: "(A \<times> B) \<times> C \<approx> A \<times> (B \<times> C)"
  unfolding eqpoll_def
  by (force intro: bij_betw_byWitness [where f = "\<lambda>((x,y),z). (x,(y,z))" and f' = "\<lambda>(x,(y,z)). ((x,y),z)"])

lemma times_singleton_eqpoll: "{a} \<times> A \<approx> A"
proof -
  have "{a} \<times> A = (\<lambda>x. (a,x)) ` A"
    by auto
  also have "\<dots>  \<approx> A"
    proof (rule inj_on_image_eqpoll_self)
      show "inj_on (Pair a) A"
        by (auto simp: inj_on_def)
    qed
    finally show ?thesis .
qed


lemma Union_eqpoll_Times:
  assumes B: "\<And>x. x \<in> A \<Longrightarrow> F x \<approx> B" and disj: "pairwise (\<lambda>x y. disjnt (F x) (F y)) A"
  shows "(\<Union>x\<in>A. F x) \<approx> A \<times> B"
proof (rule lepoll_antisym)
  obtain b where b: "\<And>x. x \<in> A \<Longrightarrow> bij_betw (b x) (F x) B"
    using B unfolding eqpoll_def by metis
  show "\<Union>(F ` A) \<lesssim> A \<times> B"
    unfolding lepoll_def
  proof (intro exI conjI)
    define \<chi> where "\<chi> \<equiv> \<lambda>z. THE x. x \<in> A \<and> z \<in> F x"
    have \<chi>: "\<chi> z = x" if "x \<in> A" "z \<in> F x" for x z
      unfolding \<chi>_def
      apply (rule the_equality)
      apply (simp add: that)
      by (metis disj disjnt_iff pairwiseD that)
    let ?f = "\<lambda>z. (\<chi> z, b (\<chi> z) z)"
    show "inj_on ?f (\<Union>(F ` A))"
      unfolding inj_on_def
      by clarify (metis \<chi> b bij_betw_inv_into_left)
    show "?f ` \<Union>(F ` A) \<subseteq> A \<times> B"
      using \<chi> b bij_betwE by blast
  qed
  show "A \<times> B \<lesssim> \<Union>(F ` A)"
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?f = "\<lambda>(x,y). inv_into (F x) (b x) y"
    have *: "inv_into (F x) (b x) y \<in> F x" if "x \<in> A" "y \<in> B" for x y
      by (metis b bij_betw_imp_surj_on inv_into_into that)
    then show "inj_on ?f (A \<times> B)"
      unfolding inj_on_def
      by clarsimp (metis (mono_tags, lifting) b bij_betw_inv_into_right disj disjnt_iff pairwiseD)
    show "?f ` (A \<times> B) \<subseteq> \<Union> (F ` A)"
      by clarsimp (metis b bij_betw_imp_surj_on inv_into_into)
  qed
qed


lemma countable_iff_lepoll: "countable A \<longleftrightarrow> A \<lesssim> (UNIV :: nat set)"
  by (auto simp: countable_def lepoll_def)

lemma infinite_times_eqpoll_self:
  assumes "infinite A" shows "A \<times> A \<approx> A"
  by (simp add: Times_same_infinite_bij_betw assms eqpoll_def)

lemma finite_lepoll_infinite:
  assumes "infinite A" "finite B" shows "B \<lesssim> A"
proof -
  have "B \<lesssim> (UNIV::nat set)"
    unfolding lepoll_def
    using finite_imp_inj_to_nat_seg [OF \<open>finite B\<close>] by blast
  then show ?thesis
    using \<open>infinite A\<close> infinite_le_lepoll lepoll_trans by auto
qed

lemma finite_lesspoll_infinite:
  assumes "infinite A" "finite B" shows "B \<prec> A"
  by (meson assms eqpoll_finite_iff finite_lepoll_infinite lesspoll_def)


lemma infinite_insert_lepoll:
  assumes "infinite A" shows "insert a A \<lesssim> A"
proof -
  obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "range f \<subseteq> A"
    using assms infinite_countable_subset by blast
  let ?g = "(\<lambda>z. if z=a then f 0 else if z \<in> range f then f (Suc (inv f z)) else z)"
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on ?g (insert a A)"
      using inj_on_eq_iff [OF \<open>inj f\<close>]
      by (auto simp: inj_on_def)
    show "?g ` insert a A \<subseteq> A"
      using f by auto
  qed
qed

lemma infinite_insert_eqpoll: "infinite A \<Longrightarrow> insert a A \<approx> A"
  by (simp add: lepoll_antisym infinite_insert_lepoll subset_imp_lepoll subset_insertI)


lemma Un_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" "disjnt C D" shows "A \<union> B \<lesssim> C \<union> D"
proof -
  obtain f g where inj: "inj_on f A" "inj_on g B" and fg: "f ` A \<subseteq> C" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  have "inj_on (\<lambda>x. if x \<in> A then f x else g x) (A \<union> B)"
    using inj \<open>disjnt C D\<close> fg unfolding disjnt_iff
    by (fastforce intro: inj_onI dest: inj_on_contraD split: if_split_asm)
  with fg show ?thesis
    unfolding lepoll_def
    by (rule_tac x="\<lambda>x. if x \<in> A then f x else g x" in exI) auto
qed

lemma Un_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D; disjnt A B; disjnt C D\<rbrakk> \<Longrightarrow> A \<union> B \<approx> C \<union> D"
  by (meson Un_lepoll_mono eqpoll_imp_lepoll eqpoll_sym lepoll_antisym)

lemma sum_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" shows "A <+> B \<lesssim> C <+> D"
proof -
  obtain f g where "inj_on f A" "f ` A \<subseteq> C" "inj_on g B" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  then show ?thesis
    unfolding lepoll_def
    by (rule_tac x="case_sum (Inl \<circ> f) (Inr \<circ> g)" in exI) (force simp: inj_on_def)
qed

lemma sum_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D\<rbrakk> \<Longrightarrow> A <+> B \<approx> C <+> D"
  by (meson eqpoll_imp_lepoll eqpoll_sym lepoll_antisym sum_lepoll_mono)

lemma Sigma_lepoll_mono:
  assumes "A \<subseteq> C" "\<And>x. x \<in> A \<Longrightarrow> B x \<lesssim> D x" shows "Sigma A B \<lesssim> Sigma C D"
proof -
  have "\<And>x. x \<in> A \<Longrightarrow> \<exists>f. inj_on f (B x) \<and> f ` (B x) \<subseteq> D x"
    by (meson assms lepoll_def)
  then obtain f where  "\<And>x. x \<in> A \<Longrightarrow> inj_on (f x) (B x) \<and> f x ` B x \<subseteq> D x"
    by metis
  with \<open>A \<subseteq> C\<close> show ?thesis
    unfolding lepoll_def inj_on_def
    by (rule_tac x="\<lambda>(x,y). (x, f x y)" in exI) force
qed

lemma times_lepoll_mono:
  assumes "A \<lesssim> C" "B \<lesssim> D" shows "A \<times> B \<lesssim> C \<times> D"
proof -
  obtain f g where "inj_on f A" "f ` A \<subseteq> C" "inj_on g B" "g ` B \<subseteq> D"
    by (meson assms lepoll_def)
  then show ?thesis
    unfolding lepoll_def
    by (rule_tac x="\<lambda>(x,y). (f x, g y)" in exI) (auto simp: inj_on_def)
qed

lemma times_eqpoll_cong: "\<lbrakk>A \<approx> C; B \<approx> D\<rbrakk> \<Longrightarrow> A \<times> B \<approx> C \<times> D"
  by (metis eqpoll_imp_lepoll eqpoll_sym lepoll_antisym times_lepoll_mono)

lemma
  assumes "B \<noteq> {}" shows lepoll_times1: "A \<lesssim> A \<times> B" and lepoll_times2:  "A \<lesssim> B \<times> A"
  using assms lepoll_iff by fastforce+


lemma times_0_eqpoll: "{} \<times> A \<approx> {}"
  by (simp add: eqpoll_iff_bijections)

lemma sum_times_distrib_eqpoll: "(A <+> B) \<times> C \<approx> (A \<times> C) <+> (B \<times> C)"
  unfolding eqpoll_def
proof
  show "bij_betw (\<lambda>(x,z). case_sum(\<lambda>y. Inl(y,z)) (\<lambda>y. Inr(y,z)) x) ((A <+> B) \<times> C) (A \<times> C <+> B \<times> C)"
    by (rule bij_betw_byWitness [where f' = "case_sum (\<lambda>(x,z). (Inl x, z)) (\<lambda>(y,z). (Inr y, z))"]) auto
qed

lemma prod_insert_eqpoll:
  assumes "a \<notin> A" shows "insert a A \<times> B \<approx> B <+> A \<times> B"
  unfolding eqpoll_def
  proof
  show "bij_betw (\<lambda>(x,y). if x=a then Inl y else Inr (x,y)) (insert a A \<times> B) (B <+> A \<times> B)"
    by (rule bij_betw_byWitness [where f' = "case_sum (\<lambda>y. (a,y)) id"]) (auto simp: assms)
qed

lemma insert_lepoll_insertD:
  assumes "insert u A \<lesssim> insert v B" "u \<notin> A" "v \<notin> B" shows "A \<lesssim> B"
proof -
  obtain f where inj: "inj_on f (insert u A)" and fim: "f ` (insert u A) \<subseteq> insert v B"
    by (meson assms lepoll_def)
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?g = "\<lambda>x\<in>A. if f x = v then f u else f x"
    show "inj_on ?g A"
      using inj \<open>u \<notin> A\<close> by (auto simp: inj_on_def)
    show "?g ` A \<subseteq> B"
      using fim \<open>u \<notin> A\<close> image_subset_iff inj inj_on_image_mem_iff by fastforce
  qed
qed

lemma insert_eqpoll_insertD: "\<lbrakk>insert u A \<approx> insert v B; u \<notin> A; v \<notin> B\<rbrakk> \<Longrightarrow> A \<approx> B"
  by (meson insert_lepoll_insertD eqpoll_imp_lepoll eqpoll_sym lepoll_antisym)

lemma insert_lepoll_cong:
  assumes "A \<lesssim> B" "b \<notin> B" shows "insert a A \<lesssim> insert b B"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  let ?f = "\<lambda>u \<in> insert a A. if u=a then b else f u"
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on ?f (insert a A)"
      using f \<open>b \<notin> B\<close> by (auto simp: inj_on_def)
    show "?f ` insert a A \<subseteq> insert b B"
      using f \<open>b \<notin> B\<close> by auto
  qed
qed

lemma insert_eqpoll_cong:
     "\<lbrakk>A \<approx> B; a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> insert a A \<approx> insert b B"
  apply (rule lepoll_antisym)
  apply (simp add: eqpoll_imp_lepoll insert_lepoll_cong)+
  by (meson eqpoll_imp_lepoll eqpoll_sym insert_lepoll_cong)

lemma insert_eqpoll_insert_iff:
     "\<lbrakk>a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> insert a A \<approx> insert b B  \<longleftrightarrow>  A \<approx> B"
  by (meson insert_eqpoll_insertD insert_eqpoll_cong)

lemma insert_lepoll_insert_iff:
     " \<lbrakk>a \<notin> A; b \<notin> B\<rbrakk> \<Longrightarrow> (insert a A \<lesssim> insert b B) \<longleftrightarrow> (A \<lesssim> B)"
  by (meson insert_lepoll_insertD insert_lepoll_cong)

lemma less_imp_insert_lepoll:
  assumes "A \<prec> B" shows "insert a A \<lesssim> B"
proof -
  obtain f where "inj_on f A" "f ` A \<subset> B"
    using assms by (metis bij_betw_def eqpoll_def lepoll_def lesspoll_def psubset_eq)
  then obtain b where b: "b \<in> B" "b \<notin> f ` A"
    by auto
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on (f(a:=b)) (insert a A)"
      using b \<open>inj_on f A\<close> by (auto simp: inj_on_def)
    show "(f(a:=b)) ` insert a A \<subseteq> B"
      using \<open>f ` A \<subset> B\<close>  by (auto simp: b)
  qed
qed

lemma finite_insert_lepoll: "finite A \<Longrightarrow> (insert a A \<lesssim> A) \<longleftrightarrow> (a \<in> A)"
proof (induction A rule: finite_induct)
  case (insert x A)
  then show ?case
    apply (auto simp: insert_absorb)
    by (metis insert_commute insert_iff insert_lepoll_insertD)
qed auto


lemma lists_lepoll_mono:
  assumes "A \<lesssim> B" shows "lists A \<lesssim> lists B"
proof -
  obtain f where "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  then show ?thesis
    unfolding lepoll_def
    by (rule_tac x="map f" in exI) (simp add: inj_on_map_lists map_lists_mono)
qed

lemma infinite_finite_times_lepoll_self:
  assumes "infinite A" "finite B" shows "A \<times> B \<lesssim> A"
proof -
  have "B \<lesssim> A"
    by (simp add: assms finite_lepoll_infinite)
  then have "A \<times> B \<lesssim> A \<times> A"
    by (simp add: subset_imp_lepoll times_lepoll_mono)
  also have "\<dots> \<approx> A"
    by (simp add: \<open>infinite A\<close> infinite_times_eqpoll_self)
  finally show ?thesis .
qed


lemma lists_n_lepoll_self:
  assumes "infinite A" shows "{l \<in> lists A. length l = n} \<lesssim> A"
proof (induction n)
  case 0
  have "{l \<in> lists A. length l = 0} = {[]}"
    by auto
  then show ?case
    by (metis Set.set_insert assms ex_in_conv finite.emptyI singleton_lepoll)
next
  case (Suc n)
  have "{l \<in> lists A. length l = Suc n} = (\<Union>x\<in>A. \<Union>l \<in> {l \<in> lists A. length l = n}. {x#l})"
    by (auto simp: length_Suc_conv)
  also have "\<dots> \<lesssim> A \<times> {l \<in> lists A. length l = n}"
    unfolding lepoll_iff
    by (rule_tac x="\<lambda>(x,l). Cons x l" in exI) auto
  also have "\<dots> \<lesssim> A"
  proof (cases "finite {l \<in> lists A. length l = n}")
    case True
    then show ?thesis
      using assms infinite_finite_times_lepoll_self by blast
  next
    case False
    have "A \<times> {l \<in> lists A. length l = n} \<lesssim> A \<times> A"
      by (simp add: Suc.IH subset_imp_lepoll times_lepoll_mono)
    also have "\<dots> \<approx> A"
      by (simp add: assms infinite_times_eqpoll_self)
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma lepoll_lists: "A \<lesssim> lists A"
  unfolding lepoll_def inj_on_def by(rule_tac x="\<lambda>x. [x]" in exI) auto

lemma infinite_eqpoll_lists:
    assumes "infinite A" shows "lists A \<approx> A"
proof -
  have "lists A \<lesssim> Sigma UNIV (\<lambda>n. {l \<in> lists A. length l = n})"
    unfolding lepoll_iff
    by (rule_tac x=snd in exI) (auto simp: in_listsI snd_image_Sigma)
  also have "\<dots> \<lesssim> (UNIV::nat set) \<times> A"
    by (rule Sigma_lepoll_mono) (auto simp: lists_n_lepoll_self assms)
  also have "\<dots> \<lesssim> A \<times> A"
    by (metis assms infinite_le_lepoll order_refl subset_imp_lepoll times_lepoll_mono)
  also have "\<dots> \<approx> A"
    by (simp add: assms infinite_times_eqpoll_self)
  finally show ?thesis
    by (simp add: lepoll_antisym lepoll_lists)
qed


lemma UN_lepoll_UN:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> B x \<lesssim> C x"
    and disj: "pairwise (\<lambda>x y. disjnt (C x) (C y)) A"
  shows "\<Union> (B`A) \<lesssim> \<Union> (C`A)"
proof -
  obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> inj_on (f x) (B x) \<and> f x ` (B x) \<subseteq> (C x)"
    using A unfolding lepoll_def by metis
  show ?thesis
    unfolding lepoll_def
  proof (intro exI conjI)
    define \<chi> where "\<chi> \<equiv> \<lambda>z. @x. x \<in> A \<and> z \<in> B x"
    have \<chi>: "\<chi> z \<in> A \<and> z \<in> B (\<chi> z)" if "x \<in> A" "z \<in> B x" for x z
      unfolding \<chi>_def by (metis (mono_tags, lifting) someI_ex that)
    let ?f = "\<lambda>z. (f (\<chi> z) z)"
    show "inj_on ?f (\<Union>(B ` A))"
      using disj f unfolding inj_on_def disjnt_iff pairwise_def image_subset_iff
      by (metis UN_iff \<chi>)
    show "?f ` \<Union> (B ` A) \<subseteq> \<Union> (C ` A)"
      using \<chi> f unfolding image_subset_iff by blast
  qed
qed

lemma UN_eqpoll_UN:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> B x \<approx> C x"
    and B: "pairwise (\<lambda>x y. disjnt (B x) (B y)) A"
    and C: "pairwise (\<lambda>x y. disjnt (C x) (C y)) A"
  shows "(\<Union>x\<in>A. B x) \<approx> (\<Union>x\<in>A. C x)"
proof (rule lepoll_antisym)
  show "\<Union> (B ` A) \<lesssim> \<Union> (C ` A)"
    by (meson A C UN_lepoll_UN eqpoll_imp_lepoll)
  show "\<Union> (C ` A) \<lesssim> \<Union> (B ` A)"
    by (simp add: A B UN_lepoll_UN eqpoll_imp_lepoll eqpoll_sym)
qed

end
