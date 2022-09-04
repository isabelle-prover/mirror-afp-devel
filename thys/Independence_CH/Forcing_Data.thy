section\<open>Transitive set models of ZF\<close>
text\<open>This theory defines locales for countable transitive models of $\ZF$,
and on top of that, one that includes a forcing notion. Weakened versions
of both locales are included, that only assume finitely many replacement
instances.\<close>

theory Forcing_Data
  imports
    Forcing_Notions
    Cohen_Posets_Relative
    ZF_Trans_Interpretations
begin

no_notation Aleph (\<open>\<aleph>_\<close> [90] 90)

subsection\<open>A forcing locale and generic filters\<close>

text\<open>Ideally, countability should be separated from the assumption of this locale.
The fact is that our present proofs of the “definition of forces” (and many
consequences) and of the lemma for “forcing a value” of function
unnecessarily depend on the countability of the ground model. \<close>

locale forcing_data1 = forcing_notion + M_ctm1 +
  assumes P_in_M:           "\<bbbP> \<in> M"
    and leq_in_M:         "leq \<in> M"

locale forcing_data2 = forcing_data1 + M_ctm2_AC

locale forcing_data3 = forcing_data2 + M_ctm3_AC

context forcing_data1
begin

lemma P_sub_M : "\<bbbP> \<subseteq> M"
  using transitivity P_in_M by auto

definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) \<equiv> filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>\<bbbP> \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

declare iff_trans [trans]

lemma M_generic_imp_filter[dest]: "M_generic(G) \<Longrightarrow> filter(G)"
  unfolding M_generic_def by blast

lemma generic_filter_existence:
  "p\<in>\<bbbP> \<Longrightarrow> \<exists>G. p\<in>G \<and> M_generic(G)"
proof -
  assume "p\<in>\<bbbP>"
  let ?D="\<lambda>n\<in>nat. (if (enum`n\<subseteq>\<bbbP> \<and> dense(enum`n))  then enum`n else \<bbbP>)"
  have "\<forall>n\<in>nat. ?D`n \<in> Pow(\<bbbP>)"
    by auto
  then
  have "?D:nat\<rightarrow>Pow(\<bbbP>)"
    using lam_type by auto
  have "\<forall>n\<in>nat. dense(?D`n)"
  proof(intro ballI)
    fix n
    assume "n\<in>nat"
    then
    have "dense(?D`n) \<longleftrightarrow> dense(if enum`n \<subseteq> \<bbbP> \<and> dense(enum`n) then enum`n else \<bbbP>)"
      by simp
    also
    have "... \<longleftrightarrow>  (\<not>(enum`n \<subseteq> \<bbbP> \<and> dense(enum`n)) \<longrightarrow> dense(\<bbbP>)) "
      using split_if by simp
    finally
    show "dense(?D`n)"
      using P_dense \<open>n\<in>nat\<close> by auto
  qed
  with \<open>?D\<in>_\<close>
  interpret cg: countable_generic \<bbbP> leq \<one> ?D
    by (unfold_locales, auto)
  from \<open>p\<in>\<bbbP>\<close>
  obtain G where 1: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    using cg.countable_rasiowa_sikorski[where M="\<lambda>_. M"]  P_sub_M
      M_countable[THEN bij_is_fun] M_countable[THEN bij_is_surj, THEN surj_range]
    unfolding cg.D_generic_def by blast
  then
  have "(\<forall>D\<in>M. D\<subseteq>\<bbbP> \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  proof (intro ballI impI)
    fix D
    assume "D\<in>M" and 2: "D \<subseteq> \<bbbP> \<and> dense(D) "
    moreover
    have "\<forall>y\<in>M. \<exists>x\<in>nat. enum`x= y"
      using M_countable and  bij_is_surj unfolding surj_def by (simp)
    moreover from calculation
    obtain n where Eq10: "n\<in>nat \<and> enum`n = D"
      by auto
    moreover from calculation if_P
    have "?D`n = D"
      by simp
    moreover
    note 1
    ultimately
    show "D\<inter>G\<noteq>0"
      by auto
  qed
  with 1
  show ?thesis
    unfolding M_generic_def by auto
qed

lemma one_in_M: "\<one> \<in> M"
  using one_in_P P_in_M transitivity
  by simp

declare P_in_M [simp,intro]
declare one_in_M [simp,intro]
declare leq_in_M [simp,intro]
declare one_in_P [intro]

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

locale G_generic1 = forcing_data1 +
  fixes G :: "i"
  assumes generic : "M_generic(G)"
begin

lemma G_nonempty: "G\<noteq>0"
  using generic subset_refl[of \<bbbP>] P_dense
  unfolding M_generic_def
  by auto

lemma M_genericD [dest]: "x\<in>G \<Longrightarrow> x\<in>\<bbbP>"
  using generic
  by (blast dest:filterD)

lemma M_generic_leqD [dest]: "p\<in>G \<Longrightarrow> q\<in>\<bbbP> \<Longrightarrow> p\<preceq>q \<Longrightarrow> q\<in>G"
  using generic
  by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. q\<preceq>p \<and> q\<preceq>r"
  using generic
  by (blast dest:low_bound_filter)

lemma M_generic_denseD [dest]: "dense(D) \<Longrightarrow> D\<subseteq>\<bbbP> \<Longrightarrow> D\<in>M \<Longrightarrow> \<exists>q\<in>G. q\<in>D"
  using generic
  unfolding M_generic_def by blast

lemma G_subset_P: "G\<subseteq>\<bbbP>"
  using generic by auto

lemma one_in_G : "\<one> \<in> G"
proof -
  have "increasing(G)"
    using generic
    unfolding M_generic_def filter_def by simp
  then
  show ?thesis
    using G_nonempty one_max
    unfolding increasing_def by blast
qed

lemma G_subset_M: "G \<subseteq> M"
  using generic transitivity[OF _ P_in_M] by auto

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

locale G_generic1_AC = G_generic1 + M_ctm1_AC

end