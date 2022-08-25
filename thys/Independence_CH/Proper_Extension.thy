section\<open>Separative notions and proper extensions\<close>
theory Proper_Extension
  imports
    Names

begin

text\<open>The key ingredient to obtain a proper extension is to have
a \<^emph>\<open>separative preorder\<close>:\<close>

locale separative_notion = forcing_notion +
  assumes separative: "p\<in>\<bbbP> \<Longrightarrow> \<exists>q\<in>\<bbbP>. \<exists>r\<in>\<bbbP>. q \<preceq> p \<and> r \<preceq> p \<and> q \<bottom> r"
begin

text\<open>For separative preorders, the complement of every filter is
dense. Hence an $M$-generic filter cannot belong to the ground model.\<close>

lemma filter_complement_dense:
  assumes "filter(G)"
  shows "dense(\<bbbP> - G)"
proof
  fix p
  assume "p\<in>\<bbbP>"
  show "\<exists>d\<in>\<bbbP> - G. d \<preceq> p"
  proof (cases "p\<in>G")
    case True
    note \<open>p\<in>\<bbbP>\<close> assms
    moreover
    obtain q r where "q \<preceq> p" "r \<preceq> p" "q \<bottom> r" "q\<in>\<bbbP>" "r\<in>\<bbbP>"
      using separative[OF \<open>p\<in>\<bbbP>\<close>]
      by force
    with \<open>filter(G)\<close>
    obtain s where "s \<preceq> p" "s \<notin> G" "s \<in> \<bbbP>"
      using filter_imp_compat[of G q r]
      by auto
    then
    show ?thesis
      by blast
  next
    case False
    with \<open>p\<in>\<bbbP>\<close>
    show ?thesis
      using refl_leq unfolding Diff_def by auto
  qed
qed

end \<comment> \<open>\<^locale>\<open>separative_notion\<close>\<close>

locale ctm_separative = forcing_data1 + separative_notion
begin

context
  fixes G
  assumes generic: "M_generic(G)"
begin

interpretation G_generic1 \<bbbP> leq \<one> M enum G
  by unfold_locales (simp add:generic)

lemma generic_not_in_M:
  shows "G \<notin> M"
proof
  assume "G\<in>M"
  then
  have "\<bbbP> - G \<in> M"
    using Diff_closed by simp
  moreover
  have "\<not>(\<exists>q\<in>G. q \<in> \<bbbP> - G)" "(\<bbbP> - G) \<subseteq> \<bbbP>"
    unfolding Diff_def by auto
  moreover
  note generic
  ultimately
  show "False"
    using filter_complement_dense[of G] M_generic_denseD[of "\<bbbP>-G"]
    by auto
qed

theorem proper_extension: "M \<noteq> M[G]"
  using generic G_in_Gen_Ext one_in_G generic_not_in_M
  by force
end
end \<comment> \<open>\<^locale>\<open>ctm_separative\<close>\<close>

end