section\<open>The Axiom of Unions in $M[G]$\<close>
theory Union_Axiom
  imports Names
begin

definition Union_name_body :: "[i,i,i,i] \<Rightarrow> o" where
  "Union_name_body(P,leq,\<tau>,x) \<equiv> \<exists> \<sigma> . \<exists>q\<in>P . \<exists>r\<in>P .
      \<langle>\<sigma>,q\<rangle> \<in> \<tau> \<and> \<langle>fst(x),r\<rangle> \<in> \<sigma> \<and> \<langle>snd(x),r\<rangle> \<in> leq \<and> \<langle>snd(x),q\<rangle> \<in> leq"

relativize relational "Union_name_body" "is_Union_name_body"
reldb_add functional "Union_name_body" "is_Union_name_body"
synthesize "is_Union_name_body" from_definition assuming "nonempty"
arity_theorem for "is_Union_name_body_fm"

definition Union_name :: "[i,i,i] \<Rightarrow> i" where
  "Union_name(P,leq,\<tau>) \<equiv> {u \<in> domain(\<Union>(domain(\<tau>))) \<times> P . Union_name_body(P,leq,\<tau>,u)}"

relativize functional "Union_name" "Union_name_rel"
relativize relational "Union_name" "is_Union_name"
synthesize "is_Union_name" from_definition assuming "nonempty"
arity_theorem for "is_Union_name_fm"

context M_basic
begin

is_iff_rel for "Union_name"
  using transM[OF _ cartprod_closed] domain_closed Union_closed
  unfolding is_Union_name_def Union_name_rel_def
  by simp

lemma Union_name_body_iff:
  assumes "M(x)" "M(leq)" "M(P)" "M(\<tau>)"
  shows "is_Union_name_body(M, P, leq, \<tau>, x) \<longleftrightarrow> Union_name_body(P, leq, \<tau>, x)"
proof -
  from \<open>M(\<tau>)\<close>
  have "M(\<sigma>)" if "\<langle>\<sigma>,q\<rangle>\<in>\<tau>" for \<sigma> q
    using transM[of _ \<tau>] transM[of _ "\<langle>\<sigma>,q\<rangle>"] that
    unfolding Pair_def
    by auto
  then
  show ?thesis
    using assms transM[OF _ cartprod_closed] pair_abs fst_abs snd_abs
    unfolding is_Union_name_body_def Union_name_body_def
    by auto
qed

lemma Union_name_abs :
  assumes "M(P)" "M(leq)" "M(\<tau>)"
  shows "Union_name_rel(M,P,leq,\<tau>) = Union_name(P,leq,\<tau>)"
  using assms transM[OF _ cartprod_closed] Union_name_body_iff
  unfolding Union_name_rel_def Union_name_def
  by auto

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

context forcing_data1
begin

lemma Union_name_closed :
  assumes "\<tau> \<in> M"
  shows "Union_name(P,leq,\<tau>) \<in> M"
proof -
  let ?\<phi>="is_Union_name_body_fm(3,2,1,0)"
  let ?P="\<lambda> x . M,[x,\<tau>,leq,P] \<Turnstile> ?\<phi>"
  let ?Q="Union_name_body(P,leq,\<tau>)"
  from \<open>\<tau>\<in>M\<close>
  have "domain(\<Union>(domain(\<tau>)))\<in>M" (is "?d \<in> _")
    using domain_closed Union_closed by simp
  then
  have "?d \<times> P \<in> M"
    using cartprod_closed P_in_M by simp
  note types = leq_in_M P_in_M assms \<open>?d\<times>P \<in> M\<close> \<open>?d\<in>M\<close>
  moreover
  have "arity(?\<phi>)\<le>4"
    using arity_is_Union_name_body_fm ord_simp_union by simp
  moreover from calculation
  have "separation(##M,?P)"
    using separation_ax by simp
  moreover from calculation
  have closed:"{ u \<in> ?d \<times> P . ?P(u) } \<in> M"
    using separation_iff by force
  moreover from calculation
  have "?P(x)\<longleftrightarrow> x\<in>M \<and> ?Q(x)" if "x\<in>?d\<times>P" for x
  proof -
    note calculation that
    moreover from this
    have "x = \<langle>fst(x),snd(x)\<rangle>" "x\<in>M"  "fst(x) \<in> M" "snd(x) \<in> M"
      using Pair_fst_snd_eq transitivity[of x "?d\<times>P"] fst_snd_closed
      by simp_all
    ultimately
    show "?P(x) \<longleftrightarrow> x\<in>M \<and> ?Q(x)"
      using types zero_in_M is_Union_name_body_iff_sats Union_name_body_iff
      by simp
  qed
  with \<open>?d \<times> P \<in> M\<close> types
  have "Union_name_rel(##M,P,leq,\<tau>) \<in> M"
    unfolding Union_name_rel_def
    using transitivity[OF _ \<open>?d\<times>P\<in>_\<close>] Collect_cong closed Union_name_body_iff
    by simp
  ultimately
  show ?thesis
    using Union_name_abs
    by simp
qed

lemma Union_MG_Eq :
  assumes "a \<in> M[G]" and "a = val(P,G,\<tau>)" and "filter(G)" and "\<tau> \<in> M"
  shows "\<Union> a = val(P,G,Union_name(P,leq,\<tau>))"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> \<Union> a"
  with \<open>a=_\<close>
  have "x\<in> \<Union> (val(P,G,\<tau>))"
    by simp
  then
  obtain i where "i \<in> val(P,G,\<tau>)" "x \<in> i"
    by blast
  with \<open>\<tau> \<in> M\<close>
  obtain \<sigma> q where "q \<in> G" "\<langle>\<sigma>,q\<rangle> \<in> \<tau>" "val(P,G,\<sigma>) = i" "\<sigma> \<in> M"
    using elem_of_val_pair domain_trans[OF trans_M]
    by blast
  moreover from this \<open>x \<in> i\<close>
  obtain \<theta> r where "r \<in> G" "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "val(P,G,\<theta>) = x" "\<theta> \<in> M"
    using elem_of_val_pair domain_trans[OF trans_M] by blast
  moreover from calculation
  have "\<theta> \<in> domain(\<Union>(domain(\<tau>)))"
    by auto
  moreover from calculation \<open>filter(G)\<close>
  obtain p where "p \<in> G" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq" "p \<in> P" "r \<in> P" "q \<in> P"
    using low_bound_filter filterD by blast
  moreover from this
  have "p \<in> M" "q\<in>M" "r\<in>M"
    using P_in_M by (auto dest:transM)
  moreover from calculation
  have "\<langle>\<theta>,p\<rangle> \<in> Union_name(P,leq,\<tau>)"
    unfolding Union_name_def Union_name_body_def
    by auto
  moreover from this \<open>p\<in>P\<close> \<open>p\<in>G\<close>
  have "val(P,G,\<theta>) \<in> val(P,G,Union_name(P,leq,\<tau>))"
    using val_of_elem by simp
  ultimately
  show "x \<in> val(P,G,Union_name(P,leq,\<tau>))"
    by simp
next
  fix x
  assume "x \<in> (val(P,G,Union_name(P,leq,\<tau>)))"
  moreover
  note \<open>filter(G)\<close> \<open>a=val(P,G,\<tau>)\<close>
  moreover from calculation
  obtain \<theta> p where "p \<in> G" "\<langle>\<theta>,p\<rangle> \<in> Union_name(P,leq,\<tau>)" "val(P,G,\<theta>) = x"
    using elem_of_val_pair by blast
  moreover from calculation
  have "p\<in>P"
    using filterD by simp
  moreover from calculation
  obtain \<sigma> q r where "\<langle>\<sigma>,q\<rangle> \<in> \<tau>" "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq" "r\<in>P" "q\<in>P"
    unfolding Union_name_def Union_name_body_def
    by force
  moreover from calculation
  have "r \<in> G" "q \<in> G"
    using filter_leqD by auto
  moreover from this \<open>\<langle>\<theta>,r\<rangle> \<in> \<sigma>\<close> \<open>\<langle>\<sigma>,q\<rangle>\<in>\<tau>\<close> \<open>q\<in>P\<close> \<open>r\<in>P\<close>
  have "val(P,G,\<sigma>) \<in> val(P,G,\<tau>)" "val(P,G,\<theta>) \<in> val(P,G,\<sigma>)"
    using val_of_elem by simp+
  moreover from this
  have "val(P,G,\<theta>) \<in> \<Union> val(P,G,\<tau>)"
    by blast
  ultimately
  show "x \<in> \<Union> a"
    by simp
qed

lemma union_in_MG :
  assumes "filter(G)"
  shows "Union_ax(##M[G])"
  unfolding Union_ax_def
proof(clarsimp)
  fix a
  assume "a \<in> M[G]"
  moreover
  note \<open>filter(G)\<close>
  moreover from calculation
  interpret mgtrans : M_trans "##M[G]"
    using transitivity_MG by (unfold_locales; auto)
  from calculation
  obtain \<tau> where "\<tau> \<in> M" "a=val(P,G,\<tau>)"
    using GenExtD by blast
  moreover from this
  have "val(P,G,Union_name(P,leq,\<tau>)) \<in> M[G]"
    using GenExtI Union_name_closed P_in_M leq_in_M by simp
  ultimately
  show "\<exists>z\<in>M[G] . big_union(##M[G],a,z)"
    using Union_MG_Eq by auto
qed

theorem Union_MG : "M_generic(G) \<Longrightarrow> Union_ax(##M[G])"
  by (simp add:M_generic_def union_in_MG)

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end