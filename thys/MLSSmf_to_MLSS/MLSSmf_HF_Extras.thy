theory MLSSmf_HF_Extras
  imports HereditarilyFinite.HF
begin

lemma union_hunion: "finite a \<Longrightarrow> finite b \<Longrightarrow> HF (a \<union> b) = HF a \<squnion> HF b"
  by (standard, standard, standard) auto

lemma inter_hinter: "finite a \<Longrightarrow> finite b \<Longrightarrow> HF (a \<inter> b) = HF a \<sqinter> HF b"
  by (standard, standard, standard) auto

lemma hdisjoint_iff[iff]: "A \<sqinter> B = 0 \<longleftrightarrow> (\<forall>x. x \<^bold>\<in> A \<longrightarrow> x \<^bold>\<notin> B)"
  apply standard
   apply (metis hinter_iff hmem_hempty)
  apply blast
  done

lemma hcard_0E: "hcard s = 0 \<Longrightarrow> s = 0"
proof (rule ccontr)
  assume "s \<noteq> 0" "hcard s = 0"
  then have "hcard s > 0"
    using hcard_hinsert_if hcard_hdiff1_less by fastforce
  with \<open>hcard s = 0\<close> show False by simp
qed

lemma hcard_1E: "hcard s = 1 \<Longrightarrow> \<exists>c. s = 0 \<triangleleft> c"
proof (rule ccontr)
  assume "hcard s = 1" "\<nexists>c. s = 0 \<triangleleft> c"
  then obtain s' c where "s = s' \<triangleleft> c" "s' \<noteq> 0" "c \<^bold>\<notin> s'"
    by (metis hcard_0 hf_cases zero_neq_one) 
  then have "hcard s = Suc (hcard s')"
    using hcard_hinsert_if by auto
  moreover
  from \<open>s' \<noteq> 0\<close> have "hcard s' > 0"
    using hcard_0E by blast
  ultimately
  have "hcard s > 1" by simp
  with \<open>hcard s = 1\<close> show False by presburger
qed

lemma singleton_nonempty_subset:
  assumes "s = HF {c}"
      and "t \<le> s"
      and "t \<noteq> 0"
    shows "t = HF {c}"
proof -
  from \<open>t \<le> s\<close> \<open>s = HF {c}\<close> have "c' = c" if "c' \<^bold>\<in> t" for c'
    using that by force
  with \<open>t \<noteq> 0\<close> show ?thesis by force
qed

lemma hsubset_hunion:
  "s \<le> t \<or> s \<le> u \<Longrightarrow> s \<le> t \<squnion> u"
  by (cases "s \<le> t") auto

lemma mem_hsubset_HUnion:
  "finite S \<Longrightarrow> s \<in> S \<Longrightarrow> s \<le> \<Squnion>HF S"
  by auto

lemma hinter_hdiff_hempty: "s \<le> B \<Longrightarrow> s \<sqinter> (A - B) = 0"
  by blast

lemma Hunion_nonempty: "finite S \<Longrightarrow> \<Squnion>HF S = \<Squnion>HF {s \<in> S. s \<noteq> 0}"
  by force

lemma hcard_Hunion_singletons:
  assumes "finite s"
      and f_s_singletons: "\<forall>x \<in> s. hcard (f x) = 1"
    shows "hcard (\<Squnion>HF (f ` s)) \<le> card s"
  using assms
proof (induction s)
  case empty
  then show ?case using Zero_hf_def by auto
next
  case (insert x F)
  then have IH': "hcard (\<Squnion>HF (f ` F)) \<le> card F" by blast
  from \<open>\<forall>x\<in>insert x F. hcard (f x) = 1\<close> obtain a where "f x = HF {a}"
    using hcard_1E by fastforce
  then have Hunion_insert_a: "\<Squnion>HF (f ` insert x F) = \<Squnion>HF (insert (HF {a}) (f ` F))"
    by simp
  have "HF (insert (HF {a}) (f ` F)) = (HF (f ` F)) \<triangleleft> (HF {a})"
    by (simp add: hinsert_def insert.hyps(1))
  also have "\<Squnion>... = HF {a} \<squnion> (\<Squnion>HF (f ` F))" by blast
  also have "... = (\<Squnion>HF (f ` F)) \<triangleleft> a" by force
  finally have "\<Squnion>HF (insert (HF {a}) (f ` F)) = \<Squnion>HF (f ` F) \<triangleleft> a" .
  with Hunion_insert_a have insert_hinsert:
    "\<Squnion>HF (f ` insert x F) = \<Squnion>HF (f ` F) \<triangleleft> a"
    by argo
  
  have Suc_hcard_le: "hcard (\<Squnion>HF (f ` F) \<triangleleft> a) \<le> Suc (hcard (\<Squnion>HF (f ` F)))"
    apply (cases "a \<^bold>\<in> \<Squnion>HF (f ` F)")
    by (simp add: hcard_hinsert_if)+

  from \<open>x \<notin> F\<close> have Suc_card: "card (insert x F) = Suc (card F)"
    by (simp add: insert.hyps(1))

  from insert_hinsert Suc_hcard_le Suc_card IH'
  show ?case by presburger
qed

lemma hcard_Hunion_distinct_singletons:
  assumes "finite s"
      and f_distinct: "\<forall>x \<in> s. \<forall>y \<in> s. x \<noteq> y \<longrightarrow> f x \<noteq> f y"
      and f_s_singletons: "\<forall>x \<in> s. hcard (f x) = 1"
    shows "hcard (\<Squnion>HF (f ` s)) = card s"
  using assms
proof (induction s)
  case empty
  then show ?case using Zero_hf_def by auto
next
  case (insert x F)
  then have IH': "hcard (\<Squnion>HF (f ` F)) = card F" by blast
  from \<open>\<forall>x\<in>insert x F. hcard (f x) = 1\<close> obtain a where "f x = HF {a}"
    using hcard_1E by fastforce
  then have Hunion_insert_a: "\<Squnion>HF (f ` insert x F) = \<Squnion>HF (insert (HF {a}) (f ` F))"
    by simp
  have "HF (insert (HF {a}) (f ` F)) = (HF (f ` F)) \<triangleleft> (HF {a})"
    by (simp add: hinsert_def insert.hyps(1))
  also have "\<Squnion>... = HF {a} \<squnion> (\<Squnion>HF (f ` F))" by blast
  also have "... = (\<Squnion>HF (f ` F)) \<triangleleft> a" by force
  finally have "\<Squnion>HF (insert (HF {a}) (f ` F)) = \<Squnion>HF (f ` F) \<triangleleft> a" .
  with Hunion_insert_a have insert_hinsert:
    "\<Squnion>HF (f ` insert x F) = \<Squnion>HF (f ` F) \<triangleleft> a"
    by argo
  
  have "b \<noteq> a" if "b \<^bold>\<in> \<Squnion>HF (f ` F)" for b
  proof -
    from that obtain y where "y \<in> F" "b \<^bold>\<in> f y" by auto
    with insert.prems(2) have "f y = HF {b}"
      using hcard_1E by force
    from \<open>y \<in> F\<close> \<open>x \<notin> F\<close> insert.prems(1) have "f x \<noteq> f y" by auto
    with \<open>f x = HF {a}\<close> \<open>f y = HF {b}\<close>
    show "b \<noteq> a" by auto
  qed
  then have Suc_hcard: "hcard (\<Squnion>HF (f ` F) \<triangleleft> a) = Suc (hcard (\<Squnion>HF (f ` F)))"
    by (metis hcard_hinsert_if)

  from \<open>x \<notin> F\<close> have Suc_card: "card (insert x F) = Suc (card F)"
    by (simp add: insert.hyps(1))

  from insert_hinsert Suc_hcard Suc_card IH'
  show ?case by presburger
qed

lemma singleton_mem_eq:
  assumes "HF {a} = HF {b}"
    shows "a = b"
  using assms
  by (metis HF_hfset hfset_0 hfset_hinsert singleton_insert_inj_eq') 

lemma hinter_HUnion_if_image_pairwise_disjoint:
  assumes "finite U"
      and "S \<subseteq> U"
      and "T \<subseteq> U"
      and image_pairwise_disjoint: "\<forall>x \<in> U. \<forall>y \<in> U. x \<noteq> y \<longrightarrow> f x \<sqinter> f y = 0"
    shows "\<Squnion>HF (f ` S) \<sqinter> \<Squnion>HF (f ` T) = \<Squnion>HF (f ` (S \<inter> T))"
proof (standard; standard)
  fix c assume "c \<^bold>\<in> \<Squnion>HF (f ` S) \<sqinter> \<Squnion>HF (f ` T)"
  from assms have "finite S" "finite T"
    using finite_subset by blast+
  from \<open>c \<^bold>\<in> \<Squnion>HF (f ` S) \<sqinter> \<Squnion>HF (f ` T)\<close>
  have "c \<^bold>\<in> \<Squnion>HF (f ` S)" "c \<^bold>\<in> \<Squnion>HF (f ` T)" by blast+
  then obtain x y where "x \<in> S" "c \<^bold>\<in> f x" "y \<in> T" "c \<^bold>\<in> f y"
    using \<open>finite S\<close> \<open>finite T\<close> by fastforce+
  with image_pairwise_disjoint have "x = y"
    using \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> by blast
  with \<open>x \<in> S\<close> \<open>y \<in> T\<close> have "x \<in> S \<inter> T" by blast
  with \<open>c \<^bold>\<in> f x\<close> show "c \<^bold>\<in> \<Squnion>HF (f ` (S \<inter> T))"
    using \<open>finite S\<close> by auto
next
  fix c assume "c \<^bold>\<in> \<Squnion>HF (f ` (S \<inter> T))"
  then obtain x where "x \<in> S \<inter> T" "c \<^bold>\<in> f x"
    by auto
  then have "x \<in> S" "x \<in> T" by blast+
  from assms have "finite S" "finite T"
    using finite_subset by blast+
  from \<open>x \<in> S\<close> \<open>c \<^bold>\<in> f x\<close> have "c \<^bold>\<in> \<Squnion>HF (f ` S)" 
    using \<open>finite S\<close> by auto
  moreover
  from \<open>x \<in> T\<close> \<open>c \<^bold>\<in> f x\<close> have "c \<^bold>\<in> \<Squnion>HF (f ` T)" 
    using \<open>finite T\<close> by auto
  ultimately
  show "c \<^bold>\<in> \<Squnion>HF (f ` S) \<sqinter> \<Squnion>HF (f ` T)" by blast
qed

lemma HUnion_hdiff_if_image_pairwise_disjoint:
  assumes "finite U"
      and "S \<subseteq> U"
      and "T \<subseteq> U"
      and image_pairwise_disjoint: "\<forall>x \<in> U. \<forall>y \<in> U. x \<noteq> y \<longrightarrow> f x \<sqinter> f y = 0"
    shows "\<Squnion>HF (f ` (S - T)) = \<Squnion>HF (f ` S) - \<Squnion>HF (f ` T)"
proof (standard; standard)
  fix c assume "c \<^bold>\<in> \<Squnion>HF (f ` (S - T))"
  then obtain x where "x \<in> S - T" "c \<^bold>\<in> f x"
    by auto
  then have "x \<in> S" "x \<notin> T" by blast+
  from assms have "finite S" "finite T"
    using finite_subset by blast+
  from \<open>x \<in> S\<close> \<open>c \<^bold>\<in> f x\<close> have "c \<^bold>\<in> \<Squnion>HF (f ` S)" 
    using \<open>finite S\<close> by auto
  from image_pairwise_disjoint \<open>c \<^bold>\<in> f x\<close>
  have "\<forall>y \<in> U. y \<noteq> x \<longrightarrow> c \<^bold>\<notin> f y"
    using \<open>x \<in> S\<close> \<open>S \<subseteq> U\<close> by auto
  with \<open>x \<notin> T\<close> have "\<forall>y \<in> T. c \<^bold>\<notin> f y"
    using \<open>T \<subseteq> U\<close> by fast
  then have "c \<^bold>\<notin> \<Squnion>HF (f ` T)"
    using \<open>finite T\<close> by simp
  with \<open>c \<^bold>\<in> \<Squnion>HF (f ` S)\<close> show "c \<^bold>\<in> \<Squnion>HF (f ` S) - \<Squnion>HF (f ` T)"
    by blast
next
  fix c assume "c \<^bold>\<in> \<Squnion>HF (f ` S) - \<Squnion>HF (f ` T)"
  from assms have "finite S" "finite T"
    using finite_subset by blast+
  from \<open>c \<^bold>\<in> \<Squnion>HF (f ` S) - \<Squnion>HF (f ` T)\<close>
  have "c \<^bold>\<in> \<Squnion>HF (f ` S)" "c \<^bold>\<notin> \<Squnion>HF (f ` T)" by blast+
  then obtain x where "x \<in> S" "x \<notin> T" "c \<^bold>\<in> f x"
    using \<open>finite T\<close> by fastforce
  then show "c \<^bold>\<in> \<Squnion>HF (f ` (S - T))"
    using \<open>finite S\<close> by auto
qed

lemma hsubset_hcard:
  assumes "S \<le> T"
  shows "hcard S \<le> hcard T"
  using assms
  apply (induction T arbitrary: S)
   apply simp
  apply (smt (verit) hcard_hinsert_if less_eq_insert2_iff linorder_le_cases not_less_eq_eq)
  done

lemma HInter_singleton: "\<Sqinter>HF {x} = x"
  unfolding HInter_def by auto

lemma HF_nonempty: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> HF S \<noteq> 0"
  using hfset_HF by fastforce

lemma HF_insert_hinsert: "finite S \<Longrightarrow> HF (insert x S) = HF S \<triangleleft> x"
  unfolding hinsert_def by simp

lemma HUnion_empty: "\<forall>s \<in> S. f s = 0 \<Longrightarrow> \<Squnion>HF (f ` S) = 0"
  by fastforce

lemma HUnion_eq: "\<forall>x \<in> S. f x = g x \<Longrightarrow> \<Squnion>HF (f ` S) = \<Squnion>HF (g ` S)"
  by auto

end