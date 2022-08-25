section\<open>The Axiom of Choice in $M[G]$\<close>

theory Choice_Axiom
  imports
    Powerset_Axiom
    Extensionality_Axiom
    Foundation_Axiom
    Replacement_Axiom
    Infinity_Axiom
begin

definition
  upair_name :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "upair_name(\<tau>,\<rho>,on) \<equiv> Upair(\<langle>\<tau>,on\<rangle>,\<langle>\<rho>,on\<rangle>)"

definition
  opair_name :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "opair_name(\<tau>,\<rho>,on) \<equiv> upair_name(upair_name(\<tau>,\<tau>,on),upair_name(\<tau>,\<rho>,on),on)"

definition
  induced_surj :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "induced_surj(f,a,e) \<equiv> f-``(range(f)-a)\<times>{e} \<union> restrict(f,f-``a)"

lemma domain_induced_surj: "domain(induced_surj(f,a,e)) = domain(f)"
  unfolding induced_surj_def using domain_restrict domain_of_prod by auto

lemma range_restrict_vimage:
  assumes "function(f)"
  shows "range(restrict(f,f-``a)) \<subseteq> a"
proof
  from assms
  have "function(restrict(f,f-``a))"
    using function_restrictI by simp
  fix y
  assume "y \<in> range(restrict(f,f-``a))"
  then
  obtain x where "\<langle>x,y\<rangle> \<in> restrict(f,f-``a)"  "x \<in> f-``a" "x\<in>domain(f)"
    using domain_restrict domainI[of _ _ "restrict(f,f-``a)"] by auto
  moreover
  note \<open>function(restrict(f,f-``a))\<close>
  ultimately
  have "y = restrict(f,f-``a)`x"
    using function_apply_equality by blast
  also from \<open>x \<in> f-``a\<close>
  have "restrict(f,f-``a)`x = f`x"
    by simp
  finally
  have "y = f`x" .
  moreover from assms \<open>x\<in>domain(f)\<close>
  have "\<langle>x,f`x\<rangle> \<in> f"
    using function_apply_Pair by auto
  moreover
  note assms \<open>x \<in> f-``a\<close>
  ultimately
  show "y\<in>a"
    using function_image_vimage[of f a] by auto
qed

lemma induced_surj_type:
  assumes "function(f)" (* "relation(f)" (* a function can contain non-pairs *) *)
  shows
    "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    and
    "x \<in> f-``a \<Longrightarrow> induced_surj(f,a,e)`x = f`x"
proof -
  let ?f1="f-``(range(f)-a) \<times> {e}" and ?f2="restrict(f, f-``a)"
  have "domain(?f2) = domain(f) \<inter> f-``a"
    using domain_restrict by simp
  moreover from assms
  have "domain(?f1) = f-``(range(f))-f-``a"
    using domain_of_prod function_vimage_Diff by simp
  ultimately
  have "domain(?f1) \<inter> domain(?f2) = 0"
    by auto
  moreover
  have "function(?f1)" "relation(?f1)" "range(?f1) \<subseteq> {e}"
    unfolding function_def relation_def range_def by auto
  moreover from this and assms
  have "?f1: domain(?f1) \<rightarrow> range(?f1)"
    using function_imp_Pi by simp
  moreover from assms
  have "?f2: domain(?f2) \<rightarrow> range(?f2)"
    using function_imp_Pi[of "restrict(f, f -`` a)"] function_restrictI by simp
  moreover from assms
  have "range(?f2) \<subseteq> a"
    using range_restrict_vimage by simp
  ultimately
  have "induced_surj(f,a,e): domain(?f1) \<union> domain(?f2) \<rightarrow> {e} \<union> a"
    unfolding induced_surj_def using fun_is_function fun_disjoint_Un fun_weaken_type by simp
  moreover
  have "domain(?f1) \<union> domain(?f2) = domain(f)"
    using domain_restrict domain_of_prod by auto
  ultimately
  show "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    by simp
  assume "x \<in> f-``a"
  then
  have "?f2`x = f`x"
    using restrict by simp
  moreover from \<open>x \<in> f-``a\<close> \<open>domain(?f1) = _\<close>
  have "x \<notin> domain(?f1)"
    by simp
  ultimately
  show "induced_surj(f,a,e)`x = f`x"
    unfolding induced_surj_def using fun_disjoint_apply2[of x ?f1 ?f2] by simp
qed

lemma induced_surj_is_surj :
  assumes
    "e\<in>a" "function(f)" "domain(f) = \<alpha>" "\<And>y. y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y"
  shows "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
  unfolding surj_def
proof (intro CollectI ballI)
  from assms
  show "induced_surj(f,a,e): \<alpha> \<rightarrow> a"
    using induced_surj_type[of f a e] cons_eq cons_absorb by simp
  fix y
  assume "y \<in> a"
  with assms
  have "\<exists>x\<in>\<alpha>. f ` x = y"
    by simp
  then
  obtain x where "x\<in>\<alpha>" "f ` x = y" by auto
  with \<open>y\<in>a\<close> assms
  have "x\<in>f-``a"
    using vimage_iff function_apply_Pair[of f x] by auto
  with \<open>f ` x = y\<close> assms
  have "induced_surj(f, a, e) ` x = y"
    using induced_surj_type by simp
  with \<open>x\<in>\<alpha>\<close> show
    "\<exists>x\<in>\<alpha>. induced_surj(f, a, e) ` x = y" by auto
qed

lemma (in M_ZF1_trans) upair_name_closed :
  "\<lbrakk> x\<in>M; y\<in>M ; o\<in>M\<rbrakk> \<Longrightarrow> upair_name(x,y,o)\<in>M"
  unfolding upair_name_def
  using upair_in_M_iff pair_in_M_iff Upair_eq_cons
  by simp

context G_generic1
begin

lemma val_upair_name : "val(G,upair_name(\<tau>,\<rho>,\<one>)) = {val(G,\<tau>),val(G,\<rho>)}"
  unfolding upair_name_def
  using val_Upair Upair_eq_cons generic one_in_G
  by simp

lemma val_opair_name : "val(G,opair_name(\<tau>,\<rho>,\<one>)) = \<langle>val(G,\<tau>),val(G,\<rho>)\<rangle>"
  unfolding opair_name_def Pair_def
  using val_upair_name by simp

lemma val_RepFun_one: "val(G,{\<langle>f(x),\<one>\<rangle> . x\<in>a}) = {val(G,f(x)) . x\<in>a}"
proof -
  let ?A = "{f(x) . x \<in> a}"
  let ?Q = "\<lambda>\<langle>x,p\<rangle> . p = \<one>"
  have "\<one> \<in> \<bbbP>\<inter>G" using generic one_in_G one_in_P by simp
  have "{\<langle>f(x),\<one>\<rangle> . x \<in> a} = {t \<in> ?A \<times> \<bbbP> . ?Q(t)}"
    using one_in_P by force
  then
  have "val(G,{\<langle>f(x),\<one>\<rangle>  . x \<in> a}) = val(G,{t \<in> ?A \<times> \<bbbP> . ?Q(t)})"
    by simp
  also
  have "... = {z . t \<in> ?A , (\<exists>p\<in>\<bbbP>\<inter>G . ?Q(\<langle>t,p\<rangle>)) \<and> z= val(G,t)}"
    using val_of_name_alt by simp
  also from \<open>\<one>\<in>\<bbbP>\<inter>G\<close>
  have "... = {val(G,t) . t \<in> ?A }"
    by force
  also
  have "... = {val(G,f(x)) . x \<in> a}"
    by auto
  finally
  show ?thesis
    by simp
qed

end\<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

subsection\<open>$M[G]$ is a transitive model of ZF\<close>

sublocale G_generic1 \<subseteq> ext:M_Z_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    replacement_assm_MG separation_in_MG infinity_in_MG
    replacement_ax1
  by unfold_locales

lemma (in M_replacement) upair_name_lam_replacement :
  "M(z) \<Longrightarrow> lam_replacement(M,\<lambda>x . upair_name(fst(x),snd(x),z))"
  using lam_replacement_Upair[THEN [5] lam_replacement_hcomp2]
    lam_replacement_product
    lam_replacement_fst lam_replacement_snd lam_replacement_constant
  unfolding upair_name_def
  by simp

lemma (in forcing_data1) repl_opname_check :
  assumes "A\<in>M" "f\<in>M"
  shows "{opair_name(check(x),f`x,\<one>). x\<in>A}\<in>M"
    using assms lam_replacement_constant check_lam_replacement lam_replacement_identity
      upair_name_lam_replacement[THEN [5] lam_replacement_hcomp2]
      lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
      lam_replacement_imp_strong_replacement_aux
      transitivity RepFun_closed upair_name_closed apply_closed
    unfolding opair_name_def
    by simp

theorem (in G_generic1) choice_in_MG:
  assumes "choice_ax(##M)"
  shows "choice_ax(##M[G])"
proof -
  {
    fix a
    assume "a\<in>M[G]"
    then
    obtain \<tau> where "\<tau>\<in>M" "val(G,\<tau>) = a"
      using GenExt_def by auto
    with \<open>\<tau>\<in>M\<close>
    have "domain(\<tau>)\<in>M"
      using domain_closed by simp
    then
    obtain s \<alpha> where "s\<in>surj(\<alpha>,domain(\<tau>))" "Ord(\<alpha>)" "s\<in>M" "\<alpha>\<in>M"
      using assms choice_ax_abs
      by auto
    then
    have "\<alpha>\<in>M[G]"
      using M_subset_MG generic one_in_G subsetD
      by blast
    let ?A="domain(\<tau>)\<times>\<bbbP>"
    let ?g = "{opair_name(check(\<beta>),s`\<beta>,\<one>). \<beta>\<in>\<alpha>}"
    have "?g \<in> M"
      using \<open>s\<in>M\<close> \<open>\<alpha>\<in>M\<close> repl_opname_check
      by simp
    let ?f_dot="{\<langle>opair_name(check(\<beta>),s`\<beta>,\<one>),\<one>\<rangle>. \<beta>\<in>\<alpha>}"
    have "?f_dot = ?g \<times> {\<one>}" by blast
    define f where
      "f \<equiv> val(G,?f_dot)"
    from \<open>?g\<in>M\<close> \<open>?f_dot = ?g\<times>{\<one>}\<close>
    have "?f_dot\<in>M"
      using cartprod_closed singleton_closed
      by simp
    then
    have "f \<in> M[G]"
      unfolding f_def
      by (blast intro:GenExtI)
    have "f = {val(G,opair_name(check(\<beta>),s`\<beta>,\<one>)) . \<beta>\<in>\<alpha>}"
      unfolding f_def
      using val_RepFun_one
      by simp
    also
    have "... = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}"
      using val_opair_name val_check generic one_in_G one_in_P
      by simp
    finally
    have "f = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}" .
    then
    have 1: "domain(f) = \<alpha>" "function(f)"
      unfolding function_def by auto
    have 2: "y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" for y
    proof -
      fix y
      assume
        "y \<in> a"
      with \<open>val(G,\<tau>) = a\<close>
      obtain \<sigma> where  "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) = y"
        using elem_of_val[of y _ \<tau>]
        by blast
      with \<open>s\<in>surj(\<alpha>,domain(\<tau>))\<close>
      obtain \<beta> where "\<beta>\<in>\<alpha>" "s`\<beta> = \<sigma>"
        unfolding surj_def
        by auto
      with \<open>val(G,\<sigma>) = y\<close>
      have "val(G,s`\<beta>) = y"
        by simp
      with \<open>f = {\<langle>\<beta>,val(G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}\<close> \<open>\<beta>\<in>\<alpha>\<close>
      have "\<langle>\<beta>,y\<rangle>\<in>f"
        by auto
      with \<open>function(f)\<close>
      have "f`\<beta> = y"
        using function_apply_equality by simp
      with \<open>\<beta>\<in>\<alpha>\<close> show
        "\<exists>\<beta>\<in>\<alpha>. f ` \<beta> = y"
        by auto
    qed
    then
    have "\<exists>\<alpha>\<in>(M[G]). \<exists>f'\<in>(M[G]). Ord(\<alpha>) \<and> f' \<in> surj(\<alpha>,a)"
    proof (cases "a=0")
      case True
      then
      show ?thesis
        unfolding surj_def
        using zero_in_MG
        by auto
    next
      case False
      with \<open>a\<in>M[G]\<close>
      obtain e where "e\<in>a" "e\<in>M[G]"
        using transitivity_MG
        by blast
      with 1 and 2
      have "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
        using induced_surj_is_surj by simp
      moreover from \<open>f\<in>M[G]\<close> \<open>a\<in>M[G]\<close> \<open>e\<in>M[G]\<close>
      have "induced_surj(f,a,e) \<in> M[G]"
        unfolding induced_surj_def
        by (simp flip: setclass_iff)
      moreover
      note \<open>\<alpha>\<in>M[G]\<close> \<open>Ord(\<alpha>)\<close>
      ultimately
      show ?thesis
        by auto
    qed
  }
  then
  show ?thesis
    using ext.choice_ax_abs
    by simp
qed

sublocale G_generic1_AC \<subseteq> ext:M_ZC_basic "M[G]"
  using choice_ax choice_in_MG
  by unfold_locales

end