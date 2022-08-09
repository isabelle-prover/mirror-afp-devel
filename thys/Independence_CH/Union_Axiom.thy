section\<open>The Axiom of Unions in $M[G]$\<close>
theory Union_Axiom
  imports Names
begin

definition Union_name_body :: "[i,i,i,i] \<Rightarrow> o" where
  "Union_name_body(P,leq,\<tau>,x) \<equiv> \<exists> \<sigma>\<in>domain(\<tau>) . \<exists>q\<in>P . \<exists>r\<in>P .
      \<langle>\<sigma>,q\<rangle> \<in> \<tau> \<and> \<langle>fst(x),r\<rangle> \<in> \<sigma> \<and> \<langle>snd(x),r\<rangle> \<in> leq \<and> \<langle>snd(x),q\<rangle> \<in> leq"

definition Union_name :: "[i,i,i] \<Rightarrow> i" where
  "Union_name(P,leq,\<tau>) \<equiv> {u \<in> domain(\<Union>(domain(\<tau>))) \<times> P . Union_name_body(P,leq,\<tau>,u)}"

context forcing_data1
begin

lemma Union_name_closed :
  assumes "\<tau> \<in> M"
  shows "Union_name(P,leq,\<tau>) \<in> M"
proof -
  let ?Q="Union_name_body(P,leq,\<tau>)"
  note lr_fst2 = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]
    and lr_fst3 = lam_replacement_hcomp[OF lr_fst2] lam_replacement_hcomp[OF lr_fst2 lr_fst2]
  note \<open>\<tau>\<in>M\<close>
  moreover from this
  have "domain(\<Union>(domain(\<tau>)))\<in>M" (is "?d \<in> _")
    using domain_closed Union_closed by simp
  moreover from this
  have "?d \<times> P \<in> M"
    using cartprod_closed by simp
  note types = assms \<open>?d\<times>P \<in> M\<close> \<open>?d\<in>M\<close>
  ultimately
  show ?thesis
    using domain_closed pair_in_M_iff fst_closed snd_closed separation_closed
      lam_replacement_constant lam_replacement_hcomp
      lam_replacement_fst lam_replacement_snd lam_replacement_product
      separation_bex separation_conj separation_in lr_fst2 lr_fst3
      lam_replacement_hcomp[OF lr_fst3(1) lam_replacement_snd]
    unfolding Union_name_body_def Union_name_def
    by simp
qed

lemma Union_MG_Eq :
  assumes "a \<in> M[G]" and "a = val(G,\<tau>)" and "filter(G)" and "\<tau> \<in> M"
  shows "\<Union> a = val(G,Union_name(P,leq,\<tau>))"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> \<Union> a"
  with \<open>a=_\<close>
  have "x \<in> \<Union> (val(G,\<tau>))"
    by simp
  then
  obtain i where "i \<in> val(G,\<tau>)" "x \<in> i"
    by blast
  with \<open>\<tau> \<in> M\<close>
  obtain \<sigma> q where "q \<in> G" "\<langle>\<sigma>,q\<rangle> \<in> \<tau>" "val(G,\<sigma>) = i" "\<sigma> \<in> M"
    using elem_of_val_pair domain_trans[OF trans_M] by blast
  moreover from this \<open>x \<in> i\<close>
  obtain \<theta> r where "r \<in> G" "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "val(G,\<theta>) = x" "\<theta> \<in> M"
    using elem_of_val_pair domain_trans[OF trans_M] by blast
  moreover from calculation
  have "\<theta> \<in> domain(\<Union>(domain(\<tau>)))"
    by auto
  moreover from calculation \<open>filter(G)\<close>
  obtain p where "p \<in> G" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq" "p \<in> P" "r \<in> P" "q \<in> P"
    using low_bound_filter filterD by blast
  moreover from this
  have "p \<in> M" "q\<in>M" "r\<in>M"
    by (auto dest:transitivity)
  moreover from calculation
  have "\<langle>\<theta>,p\<rangle> \<in> Union_name(P,leq,\<tau>)"
    unfolding Union_name_def Union_name_body_def
    by auto
  moreover from this \<open>p\<in>P\<close> \<open>p\<in>G\<close>
  have "val(G,\<theta>) \<in> val(G,Union_name(P,leq,\<tau>))"
    using val_of_elem by simp
  ultimately
  show "x \<in> val(G,Union_name(P,leq,\<tau>))"
    by simp
next
  fix x
  assume "x \<in> (val(G,Union_name(P,leq,\<tau>)))"
  moreover
  note \<open>filter(G)\<close> \<open>a=val(G,\<tau>)\<close>
  moreover from calculation
  obtain \<theta> p where "p \<in> G" "\<langle>\<theta>,p\<rangle> \<in> Union_name(P,leq,\<tau>)" "val(G,\<theta>) = x"
    using elem_of_val_pair by blast
  moreover from calculation
  have "p\<in>P"
    using filterD by simp
  moreover from calculation
  obtain \<sigma> q r where "\<langle>\<sigma>,q\<rangle> \<in> \<tau>" "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq" "r\<in>P" "q\<in>P"
    unfolding Union_name_def Union_name_body_def
    by auto
  moreover from calculation
  have "r \<in> G" "q \<in> G"
    using filter_leqD by auto
  moreover from this \<open>\<langle>\<theta>,r\<rangle> \<in> \<sigma>\<close> \<open>\<langle>\<sigma>,q\<rangle>\<in>\<tau>\<close> \<open>q\<in>P\<close> \<open>r\<in>P\<close>
  have "val(G,\<sigma>) \<in> val(G,\<tau>)" "val(G,\<theta>) \<in> val(G,\<sigma>)"
    using val_of_elem by simp+
  ultimately
  show "x \<in> \<Union> a"
    by blast
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
  obtain \<tau> where "\<tau> \<in> M" "a=val(G,\<tau>)"
    using GenExtD by blast
  moreover from this
  have "val(G,Union_name(P,leq,\<tau>)) \<in> M[G]"
    using GenExtI Union_name_closed by simp
  ultimately
  show "\<exists>z\<in>M[G] . big_union(##M[G],a,z)"
    using Union_MG_Eq by auto
qed

theorem Union_MG : "M_generic(G) \<Longrightarrow> Union_ax(##M[G])"
  by (auto simp:union_in_MG)

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end