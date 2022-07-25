section\<open>A poset of successions\<close>

theory Succession_Poset
  imports
    ZF_Trans_Interpretations
    Proper_Extension
begin

text\<open>In this theory we define a separative poset. Its underlying set is the
set of finite binary sequences (that is, with codomain $2={0,1}$);
of course, one can see that set as
the set \<^term>\<open>\<omega>-||>2\<close> or equivalently as the set of partial functions
\<^term>\<open>Fn(\<omega>,\<omega>,2)\<close>, i.e. the set of partial functions bounded by \<^term>\<open>\<omega>\<close>.

The order relation of the poset is that of being less defined as functions
(cf. \<^term>\<open>Fnlerel(A\<^bsup><\<omega>\<^esup>)\<close>), so it could be surprising that we have not used
\<^term>\<open>Fn(\<omega>,\<omega>,2)\<close> for the set. The only reason why we keep this alternative
definition is because we can prove \<^term>\<open>A\<^bsup><\<omega>\<^esup> \<in> M\<close> (and therefore
\<^term>\<open>Fnlerel(A\<^bsup><\<omega>\<^esup>) \<in> M\<close>) using only one instance of separation.\<close>

definition seq_upd :: "i \<Rightarrow> i \<Rightarrow> i" where
  "seq_upd(f,a) \<equiv> \<lambda> j \<in> succ(domain(f)) . if j < domain(f) then f`j else a"

lemma seq_upd_succ_type :
  assumes "n\<in>nat" "f\<in>n\<rightarrow>A" "a\<in>A"
  shows "seq_upd(f,a)\<in> succ(n) \<rightarrow> A"
proof -
  from assms
  have equ: "domain(f) = n"
    using domain_of_fun by simp
  {
    fix j
    assume "j\<in>succ(domain(f))"
    with equ \<open>n\<in>_\<close>
    have "j\<le>n"
      using ltI by auto
    with \<open>n\<in>_\<close>
    consider (lt) "j<n" | (eq) "j=n"
      using leD by auto
    then
    have "(if j < n then f`j else a) \<in> A"
    proof cases
      case lt
      with \<open>f\<in>_\<close>
      show ?thesis
        using apply_type ltD[OF lt] by simp
    next
      case eq
      with \<open>a\<in>_\<close>
      show ?thesis
        by auto
    qed
  }
  with equ
  show ?thesis
    unfolding seq_upd_def
    using lam_type[of "succ(domain(f))"]
    by auto
qed

lemma seq_upd_type :
  assumes "f\<in>A\<^bsup><\<omega>\<^esup>" "a\<in>A"
  shows "seq_upd(f,a) \<in> A\<^bsup><\<omega>\<^esup>"
proof -
  from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f\<in>y\<rightarrow>A"
    unfolding seqspace_def by blast
  with \<open>a\<in>A\<close>
  have "seq_upd(f,a)\<in>succ(y)\<rightarrow>A"
    using seq_upd_succ_type by simp
  with \<open>y\<in>_\<close>
  show ?thesis
    unfolding seqspace_def by auto
qed

lemma seq_upd_apply_domain [simp]:
  assumes "f:n\<rightarrow>A" "n\<in>nat"
  shows "seq_upd(f,a)`n = a"
  unfolding seq_upd_def using assms domain_of_fun by auto

lemma zero_in_seqspace :
  shows "0 \<in> A\<^bsup><\<omega>\<^esup>"
  unfolding seqspace_def
  by force

definition
  seqlerel :: "i \<Rightarrow> i" where
  "seqlerel(A) \<equiv> Fnlerel(A\<^bsup><\<omega>\<^esup>)"

definition
  seqle :: "i" where
  "seqle \<equiv> seqlerel(2)"

lemma seqleI[intro!]:
  "\<langle>f,g\<rangle> \<in> 2\<^bsup><\<omega>\<^esup>\<times>2\<^bsup><\<omega>\<^esup> \<Longrightarrow> g \<subseteq> f  \<Longrightarrow> \<langle>f,g\<rangle> \<in> seqle"
  unfolding seqle_def seqlerel_def seqspace_def Rrel_def Fnlerel_def
  by blast

lemma seqleD[dest!]:
  "z \<in> seqle \<Longrightarrow> \<exists>x y. \<langle>x,y\<rangle> \<in> 2\<^bsup><\<omega>\<^esup>\<times>2\<^bsup><\<omega>\<^esup> \<and> y \<subseteq> x \<and> z = \<langle>x,y\<rangle>"
  unfolding Rrel_def seqle_def seqlerel_def Fnlerel_def
  by blast

lemma upd_leI :
  assumes "f\<in>2\<^bsup><\<omega>\<^esup>" "a\<in>2"
  shows "\<langle>seq_upd(f,a),f\<rangle>\<in>seqle"  (is "\<langle>?f,_\<rangle>\<in>_")
proof
  show " \<langle>?f, f\<rangle> \<in> 2\<^bsup><\<omega>\<^esup> \<times> 2\<^bsup><\<omega>\<^esup>"
    using assms seq_upd_type by auto
next
  show  "f \<subseteq> seq_upd(f,a)"
  proof
    fix x
    assume "x \<in> f"
    moreover from \<open>f \<in> 2\<^bsup><\<omega>\<^esup>\<close>
    obtain n where "n\<in>nat" "f : n \<rightarrow> 2"
      by blast
    moreover from calculation
    obtain y where "y\<in>n" "x=\<langle>y,f`y\<rangle>"
      using Pi_memberD[of f n "\<lambda>_ . 2"]
      by blast
    moreover from \<open>f:n\<rightarrow>2\<close>
    have "domain(f) = n"
      using domain_of_fun by simp
    ultimately
    show "x \<in> seq_upd(f,a)"
      unfolding seq_upd_def lam_def
      by (auto intro:ltI)
  qed
qed

lemma preorder_on_seqle: "preorder_on(2\<^bsup><\<omega>\<^esup>,seqle)"
  unfolding preorder_on_def refl_def trans_on_def by blast

lemma zero_seqle_max: "x\<in>2\<^bsup><\<omega>\<^esup> \<Longrightarrow> \<langle>x,0\<rangle> \<in> seqle"
  using zero_in_seqspace
  by auto

interpretation sp:forcing_notion "2\<^bsup><\<omega>\<^esup>" "seqle" "0"
  using preorder_on_seqle zero_seqle_max zero_in_seqspace
  by unfold_locales simp_all

notation sp.Leq (infixl "\<preceq>s" 50)
notation sp.Incompatible (infixl "\<bottom>s" 50)

lemma seqspace_separative:
  assumes "f\<in>2\<^bsup><\<omega>\<^esup>"
  shows "seq_upd(f,0) \<bottom>s seq_upd(f,1)" (is "?f \<bottom>s ?g")
proof
  assume "sp.compat(?f, ?g)"
  then
  obtain h where "h \<in> 2\<^bsup><\<omega>\<^esup>" "?f \<subseteq> h" "?g \<subseteq> h"
    by blast
  moreover from \<open>f\<in>_\<close>
  obtain y where "y\<in>nat" "f:y\<rightarrow>2"
    by blast
  moreover from this
  have "?f: succ(y) \<rightarrow> 2" "?g: succ(y) \<rightarrow> 2"
    using seq_upd_succ_type by blast+
  moreover from this
  have "\<langle>y,?f`y\<rangle> \<in> ?f" "\<langle>y,?g`y\<rangle> \<in> ?g"
    using apply_Pair by auto
  ultimately
  have "\<langle>y,0\<rangle> \<in> h" "\<langle>y,1\<rangle> \<in> h"
    by auto
  moreover from \<open>h \<in> 2\<^bsup><\<omega>\<^esup>\<close>
  obtain n where "n\<in>nat" "h:n\<rightarrow>2"
    by blast
  ultimately
  show "False"
    using fun_is_function[of h n "\<lambda>_. 2"]
    unfolding seqspace_def function_def by auto
qed

definition seqleR_fm :: "i \<Rightarrow> i" where
  "seqleR_fm(fg) \<equiv> Exists(Exists(And(pair_fm(0,1,fg+\<^sub>\<omega>2),subset_fm(1,0))))"

lemma type_seqleR_fm : "fg \<in> nat \<Longrightarrow> seqleR_fm(fg) \<in> formula"
  unfolding seqleR_fm_def
  by simp

arity_theorem for "seqleR_fm"

lemma (in M_ctm1) seqleR_fm_sats :
  assumes "fg\<in>nat" "env\<in>list(M)"
  shows "(M, env \<Turnstile> seqleR_fm(fg)) \<longleftrightarrow> (\<exists>f[##M]. \<exists>g[##M]. pair(##M,f,g,nth(fg,env)) \<and> f \<supseteq> g)"
  unfolding seqleR_fm_def
  using assms trans_M sats_subset_fm pair_iff_sats
  by auto

context M_ctm2
begin

lemma seqle_in_M: "seqle \<in> M"
  using arity_seqleR_fm seqleR_fm_sats type_seqleR_fm
    cartprod_closed seqspace_closed nat_into_M nat_in_M pair_in_M_iff
  unfolding seqle_def seqlerel_def Rrel_def Fnlerel_def
  by (rule_tac Collect_in_M[of "seqleR_fm(0)" "[]"],auto)

subsection\<open>Cohen extension is proper\<close>

interpretation ctm_separative "2\<^bsup><\<omega>\<^esup>" seqle 0
proof (unfold_locales)
  fix f
  let ?q="seq_upd(f,0)" and ?r="seq_upd(f,1)"
  assume "f \<in> 2\<^bsup><\<omega>\<^esup>"
  then
  have "?q \<preceq>s f \<and> ?r \<preceq>s f \<and> ?q \<bottom>s ?r"
    using upd_leI seqspace_separative by auto
  moreover from calculation
  have "?q \<in> 2\<^bsup><\<omega>\<^esup>"  "?r \<in> 2\<^bsup><\<omega>\<^esup>"
    using seq_upd_type[of f 2] by auto
  ultimately
  show "\<exists>q\<in>2\<^bsup><\<omega>\<^esup>. \<exists>r\<in>2\<^bsup><\<omega>\<^esup>. q \<preceq>s f \<and> r \<preceq>s f \<and> q \<bottom>s r"
    by (rule_tac bexI)+ \<comment> \<open>why the heck auto-tools don't solve this?\<close>
next
  show "2\<^bsup><\<omega>\<^esup> \<in> M"
    using nat_into_M seqspace_closed by simp
next
  show "seqle \<in> M"
    using seqle_in_M .
qed

lemma cohen_extension_is_proper: "\<exists>G. M_generic(G) \<and> M \<noteq> M[G]"
  using proper_extension generic_filter_existence zero_in_seqspace
  by force

end \<comment> \<open>\<^locale>\<open>M_ctm2\<close>\<close>

end