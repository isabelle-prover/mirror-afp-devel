section\<open>Transitive set models of ZF\<close>
text\<open>This theory defines locales for countable transitive models of $\ZF$,
and on top of that, one that includes a forcing notion. Weakened versions
of both locales are included, that only assume finitely many replacement
instances.\<close>

theory Forcing_Data
  imports
    Forcing_Notions
    Cohen_Posets_Relative
    Interface
begin

locale M_ctm1 = M_ZF1_trans +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"

locale M_ctm1_AC = M_ctm1 + M_ZFC1_trans

subsection\<open>A forcing locale and generic filters\<close>

txt\<open>Ideally, countability should be separated from the assumption of this locale.
The fact is that our present proofs of the "definition of forces" (and many
consequences) and of the lemma for “forcing a value” of function
unnecessarily depend on the countability of the ground model. \<close>

locale forcing_data1 = forcing_notion + M_ctm1 +
  assumes P_in_M:           "P \<in> M"
    and leq_in_M:         "leq \<in> M"

context forcing_data1
begin

(* P \<subseteq> M *)
lemma P_sub_M : "P\<subseteq>M"
  using transitivity P_in_M by auto

definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) \<equiv> filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

lemma M_genericD [dest]: "M_generic(G) \<Longrightarrow> x\<in>G \<Longrightarrow> x\<in>P"
  unfolding M_generic_def by (blast dest:filterD)

lemma M_generic_leqD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>P \<Longrightarrow> p\<preceq>q \<Longrightarrow> q\<in>G"
  unfolding M_generic_def by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. q\<preceq>p \<and> q\<preceq>r"
  unfolding M_generic_def by (blast dest:low_bound_filter)

lemma M_generic_denseD [dest]: "M_generic(G) \<Longrightarrow> dense(D) \<Longrightarrow> D\<subseteq>P \<Longrightarrow> D\<in>M \<Longrightarrow> \<exists>q\<in>G. q\<in>D"
  unfolding M_generic_def by blast

lemma G_nonempty: "M_generic(G) \<Longrightarrow> G\<noteq>0"
  using P_in_M P_dense subset_refl[of P]
  unfolding M_generic_def
  by auto

lemma one_in_G :
  assumes "M_generic(G)"
  shows  "\<one> \<in> G"
proof -
  from assms
  have "G\<subseteq>P"
    unfolding M_generic_def filter_def by simp
  from \<open>M_generic(G)\<close>
  have "increasing(G)"
    unfolding M_generic_def filter_def by simp
  with \<open>G\<subseteq>P\<close> \<open>M_generic(G)\<close>
  show ?thesis
    using G_nonempty one_in_P one_max
    unfolding increasing_def by blast
qed

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M"
  using transitivity[OF _ P_in_M] by auto

declare iff_trans [trans]

lemma generic_filter_existence:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> M_generic(G)"
proof -
  assume "p\<in>P"
  let ?D="\<lambda>n\<in>nat. (if (enum`n\<subseteq>P \<and> dense(enum`n))  then enum`n else P)"
  have "\<forall>n\<in>nat. ?D`n \<in> Pow(P)"
    by auto
  then
  have "?D:nat\<rightarrow>Pow(P)"
    using lam_type by auto
  have "\<forall>n\<in>nat. dense(?D`n)"
  proof(intro ballI)
    fix n
    assume "n\<in>nat"
    then
    have "dense(?D`n) \<longleftrightarrow> dense(if enum`n \<subseteq> P \<and> dense(enum`n) then enum`n else P)"
      by simp
    also
    have "... \<longleftrightarrow>  (\<not>(enum`n \<subseteq> P \<and> dense(enum`n)) \<longrightarrow> dense(P)) "
      using split_if by simp
    finally
    show "dense(?D`n)"
      using P_dense \<open>n\<in>nat\<close> by auto
  qed
  with \<open>?D\<in>_\<close>
  interpret cg: countable_generic P leq \<one> ?D
    by (unfold_locales, auto)
  from \<open>p\<in>P\<close>
  obtain G where 1: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    using cg.countable_rasiowa_sikorski[where M="\<lambda>_. M"]  P_sub_M
      M_countable[THEN bij_is_fun] M_countable[THEN bij_is_surj, THEN surj_range]
    unfolding cg.D_generic_def by blast
  then
  have "(\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  proof (intro ballI impI)
    fix D
    assume "D\<in>M" and 2: "D \<subseteq> P \<and> dense(D) "
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

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end