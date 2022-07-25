section\<open>Cohen forcing notions\<close>

theory Cohen_Posets_Relative
  imports
    Forcing_Notions
    Transitive_Models.Delta_System_Relative
    Transitive_Models.Partial_Functions_Relative
begin

locale cohen_data =
  fixes \<kappa> I J::i
  assumes zero_lt_kappa: "0<\<kappa>"
begin

lemmas zero_lesspoll_kappa = zero_lesspoll[OF zero_lt_kappa]

end \<comment> \<open>\<^locale>\<open>cohen_data\<close>\<close>

abbreviation
  inj_dense :: "[i,i,i,i]\<Rightarrow>i" where
  "inj_dense(I,J,w,x) \<equiv>
    { p\<in>Fn(\<omega>,I\<times>\<omega>,J) . (\<exists>n\<in>\<omega>. \<langle>\<langle>w,n\<rangle>,1\<rangle> \<in> p \<and> \<langle>\<langle>x,n\<rangle>,0\<rangle> \<in> p) }"

(* TODO write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close> *)
lemma dense_inj_dense:
  assumes "w \<in> I" "x \<in> I" "w \<noteq> x" "p\<in>Fn(\<omega>,I\<times>\<omega>,J)" "0\<in>J" "1\<in>J"
  shows "\<exists>d\<in>inj_dense(I,J,w,x). \<langle>d ,p\<rangle> \<in> Fnle(\<omega>,I\<times>\<omega>,J)"
proof -
  obtain n where "\<langle>w,n\<rangle> \<notin> domain(p)" "\<langle>x,n\<rangle> \<notin> domain(p)" "n \<in> \<omega>"
  proof -
    {
      assume "\<langle>w,n\<rangle> \<in> domain(p) \<or> \<langle>x,n\<rangle> \<in> domain(p)" if "n \<in> \<omega>" for n
      then
      have "\<omega> \<subseteq> range(domain(p))" by blast
      then
      have "\<not> Finite(p)"
        using Finite_range Finite_domain subset_Finite nat_not_Finite
        by auto
      with \<open>p \<in> _\<close>
      have False
        using Fn_nat_eq_FiniteFun FiniteFun.dom_subset[of "I\<times>\<omega>" J]
          Fin_into_Finite by auto
    }
    with that\<comment> \<open>the shape of the goal puts assumptions in this variable\<close>
    show ?thesis by auto
  qed
  moreover
  note \<open>p \<in> _\<close> assms
  moreover from calculation
  have "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) \<in> Fn(\<omega>,I\<times>\<omega>,J)"
    using FiniteFun.consI[of "\<langle>x,n\<rangle>" "I\<times>\<omega>" 0 J p]
      Fn_nat_eq_FiniteFun by auto
  ultimately
  have "cons(\<langle>\<langle>w,n\<rangle>,1\<rangle>, cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) ) \<in> Fn(\<omega>,I\<times>\<omega>,J)"
    using FiniteFun.consI[of "\<langle>w,n\<rangle>" "I \<times> \<omega>" 1 J "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p)"]
      Fn_nat_eq_FiniteFun by auto
  with \<open>n \<in> \<omega>\<close>
  show ?thesis
    using \<open>p \<in> _\<close> by (intro bexI) auto
qed

locale add_reals = cohen_data nat _ 2

subsection\<open>Combinatorial results on Cohen posets\<close>

sublocale cohen_data \<subseteq> forcing_notion "Fn(\<kappa>,I,J)" "Fnle(\<kappa>,I,J)" 0
proof
  show "0 \<in> Fn(\<kappa>, I, J)"
    using zero_lt_kappa zero_in_Fn by simp
  then
  show "\<forall>p\<in>Fn(\<kappa>, I, J). \<langle>p, 0\<rangle> \<in> Fnle(\<kappa>, I, J)"
    unfolding preorder_on_def refl_def trans_on_def
    by auto
next
  show "preorder_on(Fn(\<kappa>, I, J), Fnle(\<kappa>, I, J))"
    unfolding preorder_on_def refl_def trans_on_def
    by blast
qed


context cohen_data
begin


lemma compat_imp_Un_is_function:
  assumes "G \<subseteq> Fn(\<kappa>, I, J)" "\<And>p q. p \<in> G \<Longrightarrow> q \<in> G \<Longrightarrow> compat(p,q)"
  shows "function(\<Union>G)"
  unfolding function_def
proof (intro allI ballI impI)
  fix x y y'
  assume "\<langle>x, y\<rangle> \<in> \<Union>G" "\<langle>x, y'\<rangle> \<in> \<Union>G"
  then
  obtain p q where "\<langle>x, y\<rangle> \<in> p" "\<langle>x, y'\<rangle> \<in> q" "p \<in> G" "q \<in> G"
    by auto
  moreover from this and assms
  obtain r where "r \<in> Fn(\<kappa>, I, J)" "r \<supseteq> p" "r \<supseteq> q"
    using compatD[of p q] by force
  moreover from this
  have "function(r)"
    using Fn_is_function by simp
  ultimately
  show "y = y'"
    unfolding function_def by fastforce
qed

(* MOVE THIS to an appropriate place *)
lemma filter_subset_notion: "filter(G) \<Longrightarrow> G \<subseteq> Fn(\<kappa>, I, J)"
  unfolding filter_def by simp

lemma Un_filter_is_function: "filter(G) \<Longrightarrow> function(\<Union>G)"
  using compat_imp_Un_is_function filter_imp_compat[of G]
    filter_subset_notion
  by simp

end \<comment> \<open>\<^locale>\<open>cohen_data\<close>\<close>

locale M_cohen = M_delta +
  assumes
    countable_lepoll_assms2:
    "M(A') \<Longrightarrow> M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. {p \<in> A . domain(p) = a}, b, f, i)\<rangle>)"
    and
    countable_lepoll_assms3:
    "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(b) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> M(A')\<Longrightarrow>
        separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(r', D, A), b, f, i)\<rangle>)"

lemma (in M_library) Fnle_rel_Aleph_rel1_closed[intro,simp]:
  "M(Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))"
  by simp

locale M_add_reals = M_cohen + add_reals
begin

lemmas zero_lesspoll_rel_kappa = zero_lesspoll_rel[OF zero_lt_kappa]

end \<comment> \<open>\<^locale>\<open>M_add_reals\<close>\<close>

(* MOVE THIS to some appropriate place. Notice that in Forcing_Notions
we don't import anything relative. *)
relativize relational "compat_in" "is_compat_in" external
synthesize "compat_in" from_definition "is_compat_in" assuming "nonempty"
context
  notes Un_assoc[simp] Un_trasposition_aux2[simp]
begin
arity_theorem for "compat_in_fm"
end

lemma (in M_trivial) compat_in_abs[absolut]:
  assumes
    "M(A)" "M(r)" "M(p)" "M(q)"
  shows
    "is_compat_in(M,A,r,p,q) \<longleftrightarrow> compat_in(A,r,p,q)"
  using assms unfolding is_compat_in_def compat_in_def by simp

definition
  antichain :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "antichain(P,leq,A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A. \<forall>q\<in>A. p\<noteq>q \<longrightarrow> \<not>compat_in(P,leq,p,q))"

relativize relational  "antichain" "antichain_rel"

definition
  ccc :: "i \<Rightarrow> i \<Rightarrow> o" where
  "ccc(P,leq) \<equiv> \<forall>A. antichain(P,leq,A) \<longrightarrow> |A| \<le> nat"

abbreviation
  antichain_rel_abbr :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" (\<open>antichain\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "antichain\<^bsup>M\<^esup>(P,leq,A) \<equiv> antichain_rel(M,P,leq,A)"

abbreviation
  antichain_r_set :: "[i,i,i,i] \<Rightarrow> o" (\<open>antichain\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "antichain\<^bsup>M\<^esup>(P,leq,A) \<equiv> antichain_rel(##M,P,leq,A)"

context M_trivial
begin

lemma antichain_abs [absolut]:
  "\<lbrakk> M(A); M(P); M(leq) \<rbrakk> \<Longrightarrow> antichain\<^bsup>M\<^esup>(P,leq,A) \<longleftrightarrow> antichain(P,leq,A)"
  unfolding antichain_rel_def antichain_def by (simp add:absolut)

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

relativize relational "ccc" "ccc_rel"

abbreviation
  ccc_rel_abbr :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" (\<open>ccc\<^bsup>_\<^esup>'(_,_')\<close>) where
  "ccc_rel_abbr(M) \<equiv> ccc_rel(M)"

abbreviation
  ccc_r_set :: "[i,i,i]\<Rightarrow>o" (\<open>ccc\<^bsup>_\<^esup>'(_,_')\<close>) where
  "ccc_r_set(M) \<equiv> ccc_rel(##M)"

context M_cardinals
begin

lemma def_ccc_rel:
  shows
    "ccc\<^bsup>M\<^esup>(P,leq) \<longleftrightarrow> (\<forall>A[M]. antichain\<^bsup>M\<^esup>(P,leq,A) \<longrightarrow> |A|\<^bsup>M\<^esup> \<le> \<omega>)"
  using is_cardinal_iff
  unfolding ccc_rel_def by (simp add:absolut)

end \<comment> \<open>\<^locale>\<open>M_cardinals\<close>\<close>

context M_FiniteFun
begin

lemma Fnle_nat_closed[intro,simp]:
  assumes "M(I)" "M(J)"
  shows "M(Fnle(\<omega>,I,J))"
  unfolding Fnle_def Fnlerel_def Rrel_def
  using supset_separation FiniteFun_closed Fn_nat_eq_FiniteFun assms by simp

lemma Fn_nat_closed:
  assumes "M(A)" "M(B)" shows "M(Fn(\<omega>,A,B))"
  using assms Fn_nat_eq_FiniteFun
  by simp

end \<comment> \<open>\<^locale>\<open>M_FiniteFun\<close>\<close>

context M_add_reals
begin

lemma lam_replacement_drSR_Y: "M(A) \<Longrightarrow> M(D) \<Longrightarrow> M(r') \<Longrightarrow> lam_replacement(M, drSR_Y(r',D,A))"
  using lam_replacement_drSR_Y
  by simp

lemma (in M_trans) mem_F_bound3:
  fixes F A
  defines "F \<equiv> dC_F"
  shows "x\<in>F(A,c) \<Longrightarrow> c \<in> (range(f) \<union> {domain(x). x\<in>A})"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def drSR_Y_def dC_F_def)

lemma ccc_rel_Fn_nat:
  assumes "M(I)"
  shows "ccc\<^bsup>M\<^esup>(Fn(nat,I,2), Fnle(nat,I,2))"
proof -
  have repFun_dom_closed:"M({domain(p) . p \<in> A})" if "M(A)" for A
    using RepFun_closed domain_replacement_simp transM[OF _ \<open>M(A)\<close>] that
    by auto
  from assms
  have "M(Fn(nat,I,2))" using Fn_nat_eq_FiniteFun by simp
  {
    fix A
    assume "\<not> |A|\<^bsup>M\<^esup> \<le> nat" "M(A)" "A \<subseteq> Fn(nat, I, 2)"
    moreover from this
    have "countable_rel(M,{p\<in>A. domain(p) = d})" if "M(d)" for d
    proof (cases "d\<prec>\<^bsup>M\<^esup>nat \<and> d \<subseteq> I")
      case True
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
      have "{p \<in> A . domain(p) = d} \<subseteq> d \<rightarrow>\<^bsup>M\<^esup> 2"
        using domain_of_fun function_space_rel_char[of _ 2]
        by (auto,subgoal_tac "M(domain(x))",simp_all add:transM[of _ A],force)
      moreover from True \<open>M(d)\<close>
      have "Finite(d \<rightarrow>\<^bsup>M\<^esup> 2)"
        using Finite_Pi[THEN [2] subset_Finite, of _ d "\<lambda>_. 2"]
          lesspoll_rel_nat_is_Finite_rel function_space_rel_char[of _ 2]
        by auto
      moreover from \<open>M(d)\<close>
      have "M(d \<rightarrow>\<^bsup>M\<^esup> 2)"
        by simp
      moreover from \<open>M(A)\<close>
      have "M({p \<in> A . domain(p) = d})"
        using separation_closed domain_eq_separation[OF \<open>M(d)\<close>] by simp
      ultimately
      show ?thesis using subset_Finite[of _ "d\<rightarrow>\<^bsup>M\<^esup>2" ]
        by (auto intro!:Finite_imp_countable_rel)
    next
      case False
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
      have "domain(p) \<noteq> d" if "p\<in>A" for p
      proof -
        note False that \<open>M(A)\<close>
        moreover from this
        obtain d' where "d' \<subseteq> I" "p\<in>d' \<rightarrow> 2" "d' \<prec> \<omega>"
          using FnD[OF subsetD[OF \<open>A\<subseteq>_\<close> \<open>p\<in>A\<close>]]
          by auto
        moreover from this
        have "p \<approx> d'" "domain(p) = d'"
          using function_eqpoll Pi_iff
          by auto
        ultimately
        show ?thesis
          using lesspoll_nat_imp_lesspoll_rel transM[of p]
          by auto
      qed
      then
      show ?thesis
        using empty_lepoll_relI by auto
    qed
    have 2:"M(x) \<Longrightarrow> x \<in> dC_F(X, i) \<Longrightarrow> M(i)" for x X i
      unfolding dC_F_def
      by auto
    moreover
    have "uncountable_rel(M,{domain(p) . p \<in> A})"
    proof
      interpret M_replacement_lepoll M dC_F
        using lam_replacement_dC_F domain_eq_separation lam_replacement_inj_rel lam_replacement_minimum
        unfolding dC_F_def
      proof(unfold_locales,simp_all)
        fix X b f
        assume "M(X)" "M(b)" "M(f)"
        with 2[of X]
        show "lam_replacement(M, \<lambda>x. \<mu> i. x \<in> if_range_F_else_F(\<lambda>d. {p \<in> X . domain(p) = d}, b, f, i))"
          using lam_replacement_dC_F domain_eq_separation
            mem_F_bound3 countable_lepoll_assms2 repFun_dom_closed
          by (rule_tac lam_Least_assumption_general[where U="\<lambda>_. {domain(x). x\<in>X}"],auto)
      qed (auto)
      have "\<exists>a\<in>A. x = domain(a) \<Longrightarrow> M(dC_F(A,x))" for x
        using \<open>M(A)\<close> transM[OF _ \<open>M(A)\<close>] by (auto)
      moreover
      have "w \<in> A \<and> domain(w) = x \<Longrightarrow> M(x)" for w x
        using transM[OF _ \<open>M(A)\<close>] by auto
      ultimately
      interpret M_cardinal_UN_lepoll _ "dC_F(A)" "{domain(p). p\<in>A}"
        using lam_replacement_dC_F lam_replacement_inj_rel \<open>M(A)\<close>
          lepoll_assumptions domain_eq_separation lam_replacement_minimum
          countable_lepoll_assms2 repFun_dom_closed
          lepoll_assumptions1[OF \<open>M(A)\<close> repFun_dom_closed[OF \<open>M(A)\<close>]]
        apply(unfold_locales)
        by(simp_all del:if_range_F_else_F_def,
            rule_tac lam_Least_assumption_general[where U="\<lambda>_. {domain(x). x\<in>A}"])
          (auto simp del:if_range_F_else_F_def simp add:dC_F_def)
      from \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have x:"(\<Union>d\<in>{domain(p) . p \<in> A}. {p\<in>A. domain(p) = d}) = A"
        by auto
      moreover
      assume "countable_rel(M,{domain(p) . p \<in> A})"
      moreover
      note \<open>\<And>d. M(d) \<Longrightarrow> countable_rel(M,{p\<in>A. domain(p) = d})\<close>
      moreover from \<open>M(A)\<close>
      have "p\<in>A \<Longrightarrow> M(domain(p))" for p
        by (auto dest: transM)
      ultimately
      have "countable_rel(M,A)"
        using countable_rel_imp_countable_rel_UN
        unfolding dC_F_def
        by auto
      with \<open>\<not> |A|\<^bsup>M\<^esup> \<le> nat\<close> \<open>M(A)\<close>
      show False
        using countable_rel_iff_cardinal_rel_le_nat by simp
    qed
    moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(A)\<close>
    have "p \<in> A \<Longrightarrow> Finite(domain(p))" for p
      using lesspoll_rel_nat_is_Finite_rel[of "domain(p)"]
        lesspoll_nat_imp_lesspoll_rel[of "domain(p)"]
        domain_of_fun[of p _ "\<lambda>_. 2"] by (auto dest:transM)
    moreover
    note repFun_dom_closed[OF \<open>M(A)\<close>]
    ultimately
    obtain D where "delta_system(D)" "D \<subseteq> {domain(p) . p \<in> A}" "D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "M(D)"
      using delta_system_uncountable_rel[of "{domain(p) . p \<in> A}"] by auto
    then
    have delta:"\<forall>d1\<in>D. \<forall>d2\<in>D. d1 \<noteq> d2 \<longrightarrow> d1 \<inter> d2 = \<Inter>D"
      using delta_system_root_eq_Inter
      by simp
    moreover from \<open>D \<approx>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>M(D)\<close>
    have "uncountable_rel(M,D)"
      using uncountable_rel_iff_subset_eqpoll_rel_Aleph_rel1 by auto
    moreover from this and \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
    obtain p1 where "p1 \<in> A" "domain(p1) \<in> D"
      using uncountable_rel_not_empty[of D] by blast
    moreover from this and \<open>p1 \<in> A \<Longrightarrow> Finite(domain(p1))\<close>
    have "Finite(domain(p1))"
      using Finite_domain by simp
    moreover
    define r where "r \<equiv> \<Inter>D"
    moreover from \<open>M(D)\<close>
    have "M(r)" "M(r\<times>2)"
      unfolding r_def by simp_all
    ultimately
    have "Finite(r)" using subset_Finite[of "r" "domain(p1)"]
      by auto
    have "countable_rel(M,{restrict(p,r) . p\<in>A})"
    proof -
      note \<open>M(Fn(nat, I, 2))\<close> \<open>M(r)\<close>
      moreover from this
      have "f\<in>Fn(nat, I, 2) \<Longrightarrow> M(restrict(f,r))" for f
        by (blast dest: transM)
      ultimately
      have "f\<in>Fn(nat, I, 2) \<Longrightarrow> restrict(f,r) \<in> Pow_rel(M,r \<times> 2)" for f
        using restrict_subset_Sigma[of f _ "\<lambda>_. 2" r] Pow_rel_char
        by (auto del:FnD dest!:FnD simp: Pi_def) (auto dest:transM)
      with \<open>A \<subseteq> Fn(nat, I, 2)\<close>
      have "{restrict(f,r) . f \<in> A } \<subseteq> Pow_rel(M,r \<times> 2)"
        by fast
      moreover from \<open>M(A)\<close> \<open>M(r)\<close>
      have "M({restrict(f,r) . f \<in> A })"
        using RepFun_closed restrict_strong_replacement transM[OF _ \<open>M(A)\<close>] by auto
      moreover
      note \<open>Finite(r)\<close> \<open>M(r)\<close>
      ultimately
      show ?thesis
        using Finite_Sigma[THEN Finite_Pow_rel, of r "\<lambda>_. 2"]
        by (intro Finite_imp_countable_rel) (auto intro:subset_Finite)
    qed
    moreover from \<open>M(A)\<close> \<open>M(D)\<close>
    have "M({p\<in>A. domain(p) \<in> D})"
      using domain_mem_separation by simp
    have "uncountable_rel(M,{p\<in>A. domain(p) \<in> D})" (is "uncountable_rel(M,?X)")
    proof
      from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
      have "(\<lambda>p\<in>?X. domain(p)) \<in> surj(?X, D)"
        using lam_type unfolding surj_def by auto
      moreover from \<open>M(A)\<close> \<open>M(?X)\<close>
      have "M(\<lambda>p\<in>?X. domain(p))"
        using lam_closed[OF domain_replacement \<open>M(?X)\<close>] transM[OF _ \<open>M(?X)\<close>] by simp
      moreover
      note \<open>M(?X)\<close> \<open>M(D)\<close>
      moreover from calculation
      have surjection:"(\<lambda>p\<in>?X. domain(p)) \<in> surj\<^bsup>M\<^esup>(?X, D)"
        using surj_rel_char by simp
      moreover
      assume "countable_rel(M,?X)"
      moreover
      note \<open>uncountable_rel(M,D)\<close>
      ultimately
      show False
        using surj_rel_countable_rel[OF _ surjection] by auto
    qed
    moreover
    have "D = (\<Union>f\<in>Pow_rel(M,r\<times>2) . {y . p\<in>A, restrict(p,r) = f \<and> y=domain(p) \<and> domain(p) \<in> D})"
    proof -
      {
        fix z
        assume "z \<in> D"
        with \<open>M(D)\<close>
        have \<open>M(z)\<close> by (auto dest:transM)
        from \<open>z\<in>D\<close> \<open>D \<subseteq> _\<close> \<open>M(A)\<close>
        obtain p  where "domain(p) = z" "p \<in> A" "M(p)"
          by (auto dest:transM)
        moreover from \<open>A \<subseteq> Fn(nat, I, 2)\<close> \<open>M(z)\<close> and this
        have "p \<in> z \<rightarrow>\<^bsup>M\<^esup> 2"
          using domain_of_fun function_space_rel_char by (auto del:FnD dest!:FnD)
        moreover from this \<open>M(z)\<close>
        have "p \<in> z \<rightarrow> 2"
          using domain_of_fun function_space_rel_char by (auto)
        moreover from this \<open>M(r)\<close>
        have "restrict(p,r) \<subseteq> r \<times> 2"
          using function_restrictI[of p r] fun_is_function[of p z "\<lambda>_. 2"]
            restrict_subset_Sigma[of p z "\<lambda>_. 2" r] function_space_rel_char
          by (auto simp:Pi_def)
        moreover from \<open>M(p)\<close> \<open>M(r)\<close>
        have "M(restrict(p,r))" by simp
        moreover
        note \<open>M(r)\<close>
        ultimately
        have "\<exists>p\<in>A.  restrict(p,r) \<in> Pow_rel(M,r\<times>2) \<and> domain(p) = z"
          using Pow_rel_char by auto
      }
      then
      show ?thesis
        by (intro equalityI) (force)+
    qed
    from \<open>M(D)\<close>\<open>M(r)\<close>
    have "M({y . p\<in>A, restrict(p,r) = f \<and> y=domain(p) \<and> domain(p) \<in> D})" (is "M(?Y(A,f))")
      if "M(f)" "M(A)" for f A
      using drSR_Y_closed[unfolded drSR_Y_def] that
      by simp
    then
    obtain f where "uncountable_rel(M,?Y(A,f))" "M(f)"
    proof -
      have 1:"M(i)"
        if "M(B)" "M(x)"
          "x \<in> {y . x \<in> B, restrict(x, r) = i \<and> y = domain(x) \<and> domain(x) \<in> D}"
        for B x i
        using that \<open>M(r)\<close>
        by (auto dest:transM)
      note \<open>M(r)\<close>
      moreover from this
      have "M(Pow\<^bsup>M\<^esup>(r \<times> 2))" by simp
      moreover
      note \<open>M(A)\<close> \<open>\<And>f A. M(f) \<Longrightarrow> M(A) \<Longrightarrow> M(?Y(A,f))\<close> \<open>M(D)\<close>
      moreover from calculation
      interpret M_replacement_lepoll M "drSR_Y(r,D)"
        using countable_lepoll_assms3 lam_replacement_inj_rel lam_replacement_drSR_Y
          drSR_Y_closed lam_Least_assumption_drSR_Y lam_replacement_minimum
        by (unfold_locales,simp_all add:drSR_Y_def,rule_tac 1,simp_all)
      from calculation
      have "x \<in> Pow\<^bsup>M\<^esup>(r \<times> 2) \<Longrightarrow> M(drSR_Y(r, D, A, x))" for x
        unfolding drSR_Y_def by (auto dest:transM)
      ultimately
      interpret M_cardinal_UN_lepoll _ "?Y(A)" "Pow_rel(M,r\<times>2)"
        using countable_lepoll_assms3 lam_replacement_drSR_Y
          lepoll_assumptions[where S="Pow_rel(M,r\<times>2)", unfolded lepoll_assumptions_defs]
          lam_Least_assumption_drSR_Y[unfolded drSR_Y_def] lam_replacement_minimum
        unfolding drSR_Y_def
        apply unfold_locales
             apply (simp_all add:lam_replacement_inj_rel del: if_range_F_else_F_def,rule_tac 1,simp_all)
        by ((fastforce dest:transM[OF _ \<open>M(A)\<close>])+)
      {
        from \<open>Finite(r)\<close> \<open>M(r)\<close>
        have "countable_rel(M,Pow_rel(M,r\<times>2))"
          using Finite_Sigma[THEN Finite_Pow_rel] Finite_imp_countable_rel
          by simp
        moreover
        assume "M(f) \<Longrightarrow> countable_rel(M,?Y(A,f))" for f
        moreover
        note \<open>D = (\<Union>f\<in>Pow_rel(M,r\<times>2) .?Y(A,f))\<close> \<open>M(r)\<close>
        moreover
        note \<open>uncountable_rel(M,D)\<close>
        ultimately
        have "False"
          using countable_rel_imp_countable_rel_UN by (auto dest: transM)
      }
      with that
      show ?thesis
        by auto
    qed
    moreover from this \<open>M(A)\<close> and \<open>M(f) \<Longrightarrow> M(A) \<Longrightarrow> M(?Y(A,f))\<close>
    have "M(?Y(A,f))"
      by blast
    ultimately
    obtain j where "j \<in> inj_rel(M,nat, ?Y(A,f))" "M(j)"
      using uncountable_rel_iff_nat_lt_cardinal_rel[THEN iffD1, THEN leI,
          THEN cardinal_rel_le_imp_lepoll_rel, THEN lepoll_relD]
      by auto
    with \<open>M(?Y(A,f))\<close>
    have "j`0 \<noteq> j`1" "j`0 \<in> ?Y(A,f)" "j`1 \<in> ?Y(A,f)"
      using inj_is_fun[THEN apply_type, of j nat "?Y(A,f)"]
        inj_rel_char
      unfolding inj_def by auto
    then
    obtain p q where "domain(p) \<noteq> domain(q)" "p \<in> A" "q \<in> A"
      "domain(p) \<in> D" "domain(q) \<in> D"
      "restrict(p,r) = restrict(q,r)" by auto
    moreover from this and delta
    have "domain(p) \<inter> domain(q) = r"
      unfolding r_def by simp
    moreover
    note \<open>A \<subseteq> Fn(nat, I, 2)\<close> Fn_nat_abs[OF \<open>M(I)\<close> nat_into_M[of 2],simplified]
    moreover from calculation
    have "p \<in> Fn\<^bsup>M\<^esup>(nat, I, 2)" "q \<in> Fn\<^bsup>M\<^esup>(nat, I, 2)"
      by auto
    moreover from calculation
    have "p \<union> q \<in> Fn(nat, I, 2)"
      using restrict_eq_imp_compat_rel InfCard_rel_nat
      by simp
    ultimately
    have "\<exists>p\<in>A. \<exists>q\<in>A. p \<noteq> q \<and> compat_in(Fn(nat, I, 2), Fnle(nat, I, 2), p, q)"
      unfolding compat_in_def
      by (rule_tac bexI[of _ p], rule_tac bexI[of _ q]) blast
  }
  moreover from assms
  have "M(Fnle(\<omega>,I,2))"
    by simp
  moreover note \<open>M(Fn(\<omega>,I,2))\<close>
  ultimately
  show ?thesis using def_ccc_rel by (auto simp:absolut antichain_def) fastforce
qed

end \<comment> \<open>\<^locale>\<open>M_add_reals\<close>\<close>

end