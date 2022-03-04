section\<open>Replacements using Lambdas\<close>

theory Lambda_Replacement
  imports
    Discipline_Function
begin

text\<open>In this theory we prove several instances of separation and replacement
in @{locale M_basic}. Moreover we introduce a new locale assuming two instances
of separation and twelve instances of lambda replacements (ie, replacement of
the form $\lambda x y. y=\langle x, f(x) \rangle$) we prove a bunch of other
instances.\<close>


definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

lemma separation_univ :
  shows "separation(M,M)"
  unfolding separation_def by auto

context M_basic
begin

lemma separation_iff':
  assumes "separation(M,\<lambda>x . P(x))" "separation(M,\<lambda>x . Q(x))"
  shows "separation(M,\<lambda>x . P(x) \<longleftrightarrow> Q(x))"
  using assms separation_conj separation_imp iff_def
  by auto

lemma separation_in_constant :
  assumes "M(a)"
  shows "separation(M,\<lambda>x . x\<in>a)"
proof -
  have "{x\<in>A . x\<in>a} = A \<inter> a" for A by auto
  with \<open>M(a)\<close>
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma separation_equal :
  shows "separation(M,\<lambda>x . x=a)"
proof -
  have "{x\<in>A . x=a} = (if a\<in>A then {a} else 0)" for A
    by auto
  then
  have "M({x\<in>A . x=a})" if "M(A)" for A
    using transM[OF _ \<open>M(A)\<close>] by simp
  then
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma (in M_basic) separation_in_rev:
  assumes "(M)(a)"
  shows "separation(M,\<lambda>x . a\<in>x)"
proof -
  have eq: "{x\<in>A. a\<in>x} = Memrel(A\<union>{a}) `` {a}" for A
    unfolding ZF_Base.image_def
    by(intro equalityI,auto simp:mem_not_refl)
  moreover from assms
  have "M(Memrel(A\<union>{a}) `` {a})" if "M(A)" for A
    using that by simp
  ultimately
  show ?thesis
    using separation_iff Collect_abs
    by simp
qed

lemma lam_replacement_iff_lam_closed:
  assumes "\<forall>x[M]. M(b(x))"
  shows "lam_replacement(M, b) \<longleftrightarrow>  (\<forall>A[M]. M(\<lambda>x\<in>A. b(x)))"
  using assms lam_closed lam_funtype[of _ b, THEN Pi_memberD]
  unfolding lam_replacement_def strong_replacement_def
  by (auto intro:lamI dest:transM)
    (rule lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_imp_lam_closed:
  assumes "lam_replacement(M, b)" "M(A)" "\<forall>x\<in>A. M(b(x))"
  shows "M(\<lambda>x\<in>A. b(x))"
  using assms unfolding lam_replacement_def
  by (rule_tac lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_cong:
  assumes "lam_replacement(M,f)" "\<forall>x[M]. f(x) = g(x)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M,g)"
proof -
  note assms
  moreover from this
  have "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
    using lam_replacement_iff_lam_closed
    by simp
  moreover from calculation
  have "(\<lambda>x\<in>A . f(x)) = (\<lambda>x\<in>A . g(x))" if "M(A)" for A
    using lam_cong[OF refl,of A f g] transM[OF _ that]
    by simp
  ultimately
  show ?thesis
    using lam_replacement_iff_lam_closed
    by simp
qed

lemma converse_subset : "converse(r) \<subseteq> {\<langle>snd(x),fst(x)\<rangle> . x\<in>r}"
  unfolding converse_def
proof(intro  subsetI, auto)
  fix u v
  assume "\<langle>u,v\<rangle>\<in>r" (is "?z\<in>r")
  moreover
  have "v=snd(?z)" "u=fst(?z)" by simp_all
  ultimately
  show "\<exists>z\<in>r. v=snd(z) \<and> u = fst(z)"
    using rexI[where x="\<langle>u,v\<rangle>"] by force
qed

lemma converse_eq_aux :
  assumes "<0,0>\<in>r"
  shows "converse(r) = {\<langle>snd(x),fst(x)\<rangle> . x\<in>r}"
  using converse_subset
proof(intro equalityI subsetI,auto)
  fix z
  assume "z\<in>r"
  then show "\<langle>fst(z),snd(z)\<rangle> \<in> r"
  proof(cases "\<exists> a b . z =\<langle>a,b\<rangle>")
    case True
    with \<open>z\<in>r\<close>
    show ?thesis by auto
  next
    case False
    then
    have "fst(z) = 0" "snd(z)=0"
      unfolding fst_def snd_def by auto
    with \<open>z\<in>r\<close> assms
    show ?thesis by auto
  qed
qed

lemma converse_eq_aux' :
  assumes "<0,0>\<notin>r"
  shows "converse(r) = {\<langle>snd(x),fst(x)\<rangle> . x\<in>r} - {<0,0>}"
  using converse_subset assms
proof(intro equalityI subsetI,auto)
  fix z
  assume "z\<in>r" "snd(z)\<noteq>0"
  then
  obtain a b where "z = \<langle>a,b\<rangle>" unfolding snd_def by force
  with \<open>z\<in>r\<close>
  show "\<langle>fst(z),snd(z)\<rangle> \<in> r"
    by auto
next
  fix z
  assume "z\<in>r" "fst(z)\<noteq>0"
  then
  obtain a b where "z = \<langle>a,b\<rangle>" unfolding fst_def by force
  with \<open>z\<in>r\<close>
  show "\<langle>fst(z),snd(z)\<rangle> \<in> r"
    by auto
qed

lemma diff_un : "b\<subseteq>a \<Longrightarrow> (a-b) \<union> b = a"
  by auto

lemma converse_eq: "converse(r) = ({\<langle>snd(x),fst(x)\<rangle> . x\<in>r} - {<0,0>}) \<union> (r\<inter>{<0,0>})"
proof(cases "<0,0>\<in>r")
  case True
  then
  have "converse(r) = {\<langle>snd(x),fst(x)\<rangle> . x\<in>r}"
    using converse_eq_aux  by auto
  moreover
  from True
  have "r\<inter>{<0,0>} = {<0,0>}" "{<0,0>}\<subseteq>{\<langle>snd(x),fst(x)\<rangle> . x\<in>r}"
    using converse_subset by auto
  moreover from this True
  have "{\<langle>snd(x),fst(x)\<rangle> . x\<in>r} = ({\<langle>snd(x),fst(x)\<rangle> . x\<in>r} - {<0,0>}) \<union> ({<0,0>})"
    using diff_un[of "{<0,0>}",symmetric] converse_eq_aux  by auto
  ultimately
  show ?thesis
    by simp
next
  case False
  then
  have "r\<inter>{<0,0>} = 0" by auto
  then
  have "({\<langle>snd(x),fst(x)\<rangle> . x\<in>r} - {<0,0>}) \<union> (r\<inter>{<0,0>}) = ({\<langle>snd(x),fst(x)\<rangle> . x\<in>r} - {<0,0>})"
    by simp
  with False
  show ?thesis
    using converse_eq_aux' by auto
qed

lemma range_subset : "range(r) \<subseteq> {snd(x). x\<in>r}"
  unfolding range_def domain_def converse_def
proof(intro  subsetI, auto)
  fix u v
  assume "\<langle>u,v\<rangle>\<in>r" (is "?z\<in>r")
  moreover
  have "v=snd(?z)" "u=fst(?z)" by simp_all
  ultimately
  show "\<exists>z\<in>r. v=snd(z)"
    using rexI[where x="v"] by force
qed

lemma lam_replacement_imp_strong_replacement_aux:
  assumes "lam_replacement(M, b)" "\<forall>x[M]. M(b(x))"
  shows "strong_replacement(M, \<lambda>x y. y = b(x))"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M(\<lambda>x\<in>A. b(x))" using lam_replacement_iff_lam_closed by auto
    ultimately
    have "M((\<lambda>x\<in>A. b(x))``A)" "\<forall>z[M]. z \<in> (\<lambda>x\<in>A. b(x))``A \<longleftrightarrow> (\<exists>x\<in>A. z = b(x))"
      by (auto simp:lam_def)
  }
  then
  show ?thesis unfolding strong_replacement_def
    by clarsimp (rule_tac x="(\<lambda>x\<in>A. b(x))``A" in rexI, auto)
qed

lemma lam_replacement_imp_RepFun_Lam:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=\<langle>x,f(x)\<rangle>})"
proof -
  from assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from calculation
  have "Y = {y . x\<in>A , M(y) \<and> y = \<langle>x,f(x)\<rangle>}" (is "Y=?R")
  proof(intro equalityI subsetI)
    fix y
    assume "y\<in>Y"
    moreover from this 1
    obtain x where "x\<in>A" "y=\<langle>x,f(x)\<rangle>" "M(y)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    ultimately
    show "y\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=\<langle>a,f(a)\<rangle>" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    ultimately
    show "z\<in>Y" using 1 by simp
  qed
  ultimately
  show ?thesis by auto
qed

lemma lam_closed_imp_closed:
  assumes "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
  shows "\<forall>x[M]. M(f(x))"
proof
  fix x
  assume "M(x)"
  moreover from this and assms
  have "M(\<lambda>x\<in>{x}. f(x))" by simp
  ultimately
  show "M(f(x))"
    using image_lam[of "{x}" "{x}" f]
      image_closed[of "{x}" "(\<lambda>x\<in>{x}. f(x))"] by (auto dest:transM)
qed

lemma lam_replacement_if:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "separation(M,b)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. if b(x) then f(x) else g(x))"
proof -
  let ?G="\<lambda>x. if b(x) then f(x) else g(x)"
  let ?b="\<lambda>A . {x\<in>A. b(x)}" and ?b'="\<lambda>A . {x\<in>A. \<not>b(x)}"
  have eq:"(\<lambda>x\<in>A . ?G(x)) = (\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x))" for A
    unfolding lam_def by auto
  have "?b'(A) = A - ?b(A)" for A by auto
  moreover
  have "M(?b(A))" if "M(A)" for A using assms that by simp
  moreover from calculation
  have "M(?b'(A))" if "M(A)" for A using that by simp
  moreover from calculation assms
  have "M(\<lambda>x\<in>?b(A). f(x))" "M(\<lambda>x\<in>?b'(A) . g(x))" if "M(A)" for A
    using lam_replacement_iff_lam_closed that
    by simp_all
  moreover from this
  have "M((\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x)))" if "M(A)" for A
    using that by simp
  ultimately
  have "M(\<lambda>x\<in>A. if b(x) then f(x) else g(x))" if "M(A)" for A
    using that eq by simp
  with assms
  show ?thesis using lam_replacement_iff_lam_closed by simp
qed

lemma lam_replacement_constant: "M(b) \<Longrightarrow> lam_replacement(M,\<lambda>_. b)"
  unfolding lam_replacement_def strong_replacement_def
  by safe (rule_tac x="_\<times>{b}" in rexI; blast)

subsection\<open>Replacement instances obtained through Powerset\<close>

txt\<open>The next few lemmas provide bounds for certain constructions.\<close>

lemma not_functional_Replace_0:
  assumes "\<not>(\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y')"
  shows "{y . x \<in> A, P(y)} = 0"
  using assms by (blast elim!: ReplaceE)

lemma Replace_in_Pow_rel:
  assumes "\<And>x b. x \<in> A \<Longrightarrow> P(x,b) \<Longrightarrow> b \<in> U" "\<forall>x\<in>A. \<forall>y y'. P(x,y) \<and> P(x,y') \<longrightarrow> y=y'"
    "separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> P(x, y))"
    "M(U)" "M(A)"
  shows "{y . x \<in> A, P(x, y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof -
  from assms
  have "{y . x \<in> A, P(x, y)} \<subseteq> U"
    "z \<in> {y . x \<in> A, P(x, y)} \<Longrightarrow> M(z)" for z
    by (auto dest:transM)
  with assms
  have "{y . x \<in> A, P(x, y)} = {y\<in>U . \<exists>x[M]. x\<in>A \<and> P(x,y)}"
    by (intro equalityI) (auto, blast)
  with assms
  have "M({y . x \<in> A, P(x, y)})"
    by simp
  with assms
  show ?thesis
    using mem_Pow_rel_abs by auto
qed

lemma Replace_sing_0_in_Pow_rel:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "{y . x \<in> {0}, P(y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof (cases "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y'")
  case True
  with assms
  show ?thesis by (rule_tac Replace_in_Pow_rel) auto
next
  case False
  with assms
  show ?thesis
    using nonempty not_functional_Replace_0[of P "{0}"] Pow_rel_char by auto
qed

lemma The_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U" "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "(THE i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
proof -
  note assms
  moreover from this
  have "(THE i. P(i)) \<in> Pow(\<Union>U)"
    unfolding the_def by auto
  moreover from assms
  have "M(THE i. P(i))"
    using Replace_sing_0_in_Pow_rel[of P U] unfolding the_def
    by (auto dest:transM)
  ultimately
  show ?thesis
    using Pow_rel_char by auto
qed

lemma separation_least: "separation(M, \<lambda>y. Ord(y) \<and> P(y) \<and> (\<forall>j. j < y \<longrightarrow> \<not> P(j)))"
  unfolding separation_def
proof
  fix z
  assume "M(z)"
  have "M({x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))})"
    (is "M(?y)")
  proof (cases "\<exists>x\<in>z. Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))")
    case True
    with \<open>M(z)\<close>
    have "\<exists>x[M]. ?y = {x}"
      by (safe, rename_tac x, rule_tac x=x in rexI)
        (auto dest:transM, intro equalityI, auto elim:Ord_linear_lt)
    then
    show ?thesis
      by auto
  next
    case False
    then
    have "{x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))} = 0"
      by auto
    then
    show ?thesis by auto
  qed
  moreover from this
  have "\<forall>x[M]. x \<in> ?y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))" by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))"
    by blast
qed

lemma Least_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "M(U)"
  shows "(\<mu> i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
  using assms separation_least unfolding Least_def
  by (rule_tac The_in_Pow_rel_Union) simp

lemma bounded_lam_replacement:
  fixes U
  assumes "\<forall>X[M]. \<forall>x\<in>X. f(x) \<in> U(X)"
    and separation_f:"\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>)"
    and U_closed [intro,simp]: "\<And>X. M(X) \<Longrightarrow> M(U(X))"
  shows "lam_replacement(M, f)"
proof -
  have "M(\<lambda>x\<in>A. f(x))" if "M(A)" for A
  proof -
    have "(\<lambda>x\<in>A. f(x)) = {y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>}"
      using \<open>M(A)\<close> unfolding lam_def
    proof (intro equalityI, auto)
      fix x
      assume "x\<in>A"
      moreover
      note \<open>M(A)\<close>
      moreover from calculation assms
      have "f(x) \<in> U(A)" by simp
      moreover from calculation
      have "{x, f(x)} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))" "{x,x} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))"
        using Pow_rel_char[of "A \<union> U(A)"] by (auto dest:transM)
      ultimately
      show "\<langle>x, f(x)\<rangle> \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A)))"
        using Pow_rel_char[of "Pow\<^bsup>M\<^esup>(A \<union> U(A))"] unfolding Pair_def
        by (auto dest:transM)
    qed
    moreover from \<open>M(A)\<close>
    have "M({y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>})"
      using separation_f
      by (rule_tac separation_closed) simp_all
    ultimately
    show ?thesis
      by simp
  qed
  moreover from this
  have "\<forall>x[M]. M(f(x))"
    using lam_closed_imp_closed by simp
  ultimately
  show ?thesis
    using assms
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD2]) simp_all
qed

lemma lam_replacement_domain':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, domain(x)\<rangle>)"
  shows "lam_replacement(M,domain)"
proof -
  have "\<forall>x\<in>X. domain(x) \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)" if "M(X)" for X
  proof
    fix x
    assume "x\<in>X"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(x)" by (auto dest:transM)
    ultimately
    show "domain(x) \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"
      by(rule_tac mem_Pow_rel_abs[of "domain(x)" "\<Union>\<Union>\<Union>X",THEN iffD2],auto simp:Pair_def,force)
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of domain "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"] by simp
qed

\<comment> \<open>Below we assume the replacement instance for @{term fst}. Alternatively it follows from the
instance of separation assumed in this lemma.\<close>
lemma lam_replacement_fst':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, fst(x)\<rangle>)"
  shows "lam_replacement(M,fst)"
proof -
  have "\<forall>x\<in>X. fst(x) \<in> {0} \<union> \<Union>\<Union>X" if "M(X)" for X
  proof
    fix x
    assume "x\<in>X"
    moreover
    note \<open>M(X)\<close>
    moreover from calculation
    have "M(x)" by (auto dest:transM)
    ultimately
    show "fst(x) \<in> {0} \<union> \<Union>\<Union>X" unfolding fst_def Pair_def
      by (auto, rule_tac [1] the_0) force\<comment> \<open>tricky! And slow. It doesn't work for \<^term>\<open>snd\<close>\<close>
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of fst "\<lambda>X. {0} \<union> \<Union>\<Union>X"] by simp
qed

lemma lam_replacement_restrict:
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x,B)\<rangle>)"  "M(B)"
  shows "lam_replacement(M, \<lambda>r . restrict(r,B))"
proof -
  have "\<forall>r\<in>R. restrict(r,B)\<in>Pow\<^bsup>M\<^esup>(\<Union>R)" if "M(R)" for R
  proof -
    {
      fix r
      assume "r\<in>R"
      with \<open>M(B)\<close>
      have "restrict(r,B)\<in>Pow(\<Union>R)" "M(restrict(r,B))"
        using Union_upper subset_Pow_Union subset_trans[OF restrict_subset]
          transM[OF _ \<open>M(R)\<close>]
        by simp_all
    } then show ?thesis
      using Pow_rel_char that by simp
  qed
  with assms
  show ?thesis
    using bounded_lam_replacement[of "\<lambda>r . restrict(r,B)" "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>X)"]
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

locale M_replacement = M_basic +
  assumes
    lam_replacement_domain: "lam_replacement(M,domain)"
    and
    lam_replacement_fst: "lam_replacement(M,fst)"
    and
    lam_replacement_snd: "lam_replacement(M,snd)"
    and
    lam_replacement_Union: "lam_replacement(M,Union)"
    and
    middle_del_replacement: "strong_replacement(M, \<lambda>x y. y=\<langle>fst(fst(x)),snd(snd(x))\<rangle>)"
    and
    product_replacement:
    "strong_replacement(M, \<lambda>x y. y=\<langle>snd(fst(x)),\<langle>fst(fst(x)),snd(snd(x))\<rangle>\<rangle>)"
    and
    lam_replacement_Upair:"lam_replacement(M, \<lambda>p. Upair(fst(p),snd(p)))"
    and
    lam_replacement_Diff:"lam_replacement(M, \<lambda>p. fst(p) - snd(p))"
    and
    lam_replacement_Image:"lam_replacement(M, \<lambda>p. fst(p) `` snd(p))"
    and
    middle_separation: "separation(M, \<lambda>x. snd(fst(x))=fst(snd(x)))"
    and
    separation_fst_in_snd: "separation(M, \<lambda>y. fst(snd(y)) \<in> snd(snd(y)))"
    and
    lam_replacement_converse : "lam_replacement(M,converse)"
    and
    lam_replacement_comp: "lam_replacement(M, \<lambda>x. fst(x) O snd(x))"
begin

lemma lam_replacement_imp_strong_replacement:
  assumes "lam_replacement(M, f)"
  shows "strong_replacement(M, \<lambda>x y. y = f(x))"
proof -
  {
    fix A
    assume "M(A)"
    moreover from calculation assms
    obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
      unfolding lam_replacement_def strong_replacement_def
      by auto
    moreover from this
    have "M({snd(b) . b \<in> Y})"
      using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
        RepFun_closed by simp
    moreover
    have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(f(x)) \<and> y=f(x)}" (is "?L=?R")
    proof(intro equalityI subsetI)
      fix x
      assume "x\<in>?L"
      moreover from this
      obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
        using transM[OF _ \<open>M(Y)\<close>] by auto
      moreover from this 1
      obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
      moreover from calculation
      have "x=f(a)" by simp
      ultimately show "x\<in>?R"
        by auto
    next
      fix z
      assume "z\<in>?R"
      moreover from this
      obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
        using transM[OF _ \<open>M(A)\<close>]
        by auto
      moreover from calculation this 1
      have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
      ultimately
      show "z\<in>?L" by force
    qed
    ultimately
    have "\<exists>Z[M]. \<forall>z[M]. z\<in>Z \<longleftrightarrow> (\<exists>a[M]. a\<in>A \<and> z=f(a))"
      by (rule_tac rexI[where x="{snd(b) . b \<in> Y}"],auto)
  }
  then
  show ?thesis unfolding strong_replacement_def by simp
qed

lemma Collect_middle: "{p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)) . snd(fst(p))=fst(snd(p))}
     = { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }"
  by (intro equalityI; auto simp:lam_def)

lemma RepFun_middle_del: "{ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }}
        =  { \<langle>x,g(f(x))\<rangle> . x\<in>A }"
  by auto

lemma lam_replacement_imp_RepFun:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=f(x)})"
proof -
  from assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from this
  have "M({snd(b) . b \<in> Y})"
    using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
      RepFun_closed by simp
  moreover
  have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(y) \<and> y=f(x)}" (is "?L=?R")
  proof(intro equalityI subsetI)
    fix x
    assume "x\<in>?L"
    moreover from this
    obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    moreover from this 1
    obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
    moreover from calculation
    have "x=f(a)" by simp
    ultimately show "x\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    moreover from calculation this 1
    have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
    ultimately
    show "z\<in>?L" by force
  qed
  ultimately
  show ?thesis by simp
qed

lemma lam_replacement_product:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
  shows "lam_replacement(M, \<lambda>x. \<langle>f(x),g(x)\<rangle>)"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , M(y) \<and> y=f(x)}"
    let ?Y'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,f(x)\<rangle>}"
    let ?Z="{y . x\<in>A , M(y) \<and> y=g(x)}"
    let ?Z'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,g(x)\<rangle>}"
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> fst(x) = fst(y) \<longrightarrow> M(fst(y)) \<and> M(snd(x)) \<and> M(snd(y))" if "M(C)" for C y x
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from \<open>M(A)\<close> assms(1)
    have "M(converse(?Y'))" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(?Z)" "M(?Z')"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(converse(?Y')\<times>?Z')"
      by simp
    moreover from this
    have "M({p \<in> converse(?Y')\<times>?Z' . snd(fst(p))=fst(snd(p))})" (is "M(?P)")
      using middle_separation by simp
    moreover from calculation
    have "M({ \<langle>snd(fst(p)),\<langle>fst(fst(p)),snd(snd(p))\<rangle>\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF product_replacement \<open>M(?P)\<close> ] by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)" if "M(b)" for b
      using that
      apply(intro iffI)apply(auto)[1]
    proof -
      assume " \<exists>x[M]. x \<in> A \<and> b = \<langle>x, f(x), g(x)\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, \<langle>f(x), g(x)\<rangle>\<rangle>"
        by auto
      moreover from calculation that
      have "M(\<langle>x,f(x)\<rangle>)" "M(\<langle>x,g(x)\<rangle>)" by auto
      moreover from calculation
      have "\<langle>f(x),x\<rangle> \<in> converse(?Y')" "\<langle>x,g(x)\<rangle> \<in> ?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>f(x),x\<rangle>,\<langle>x,g(x)\<rangle>\<rangle>\<in>converse(?Y')\<times>?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>f(x),x\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>snd(fst(?p)),\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<rangle>" by auto
      moreover from calculation
      have "\<langle>snd(fst(?p)),\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_hcomp:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M, \<lambda>x. g(f(x)))"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , y=f(x)}"
    let ?Y'="{y . x\<in>A , y=\<langle>x,f(x)\<rangle>}"
    have "\<forall>x\<in>C. M(\<langle>fst(fst(x)),snd(snd(x))\<rangle>)" if "M(C)" for C
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from assms
    have eq:"?Y = {y . x\<in>A ,M(y) \<and> y=f(x)}"  "?Y' = {y . x\<in>A ,M(y) \<and> y=\<langle>x,f(x)\<rangle>}"
      using transM[OF _ \<open>M(A)\<close>] by auto
    moreover from \<open>M(A)\<close> assms(1)
    have "M(?Y')" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun eq by auto
    moreover from calculation
    have "M({z . y\<in>?Y , M(z) \<and> z=\<langle>y,g(y)\<rangle>})" (is "M(?Z)")
      using lam_replacement_imp_RepFun_Lam by auto
    moreover from calculation
    have "M(?Y'\<times>?Z)"
      by simp
    moreover from this
    have "M({p \<in> ?Y'\<times>?Z . snd(fst(p))=fst(snd(p))})" (is "M(?P)")
      using middle_separation by simp
    moreover from calculation
    have "M({ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF middle_del_replacement \<open>M(?P)\<close>] by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)" if "M(b)" for b
      using that assms(3)
      apply(intro iffI) apply(auto)[1]
    proof -
      assume "\<exists>x[M]. x \<in> A \<and> b = \<langle>x, g(f(x))\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, g(f(x))\<rangle>"
        by auto
      moreover from calculation that assms(3)
      have "M(f(x))" "M(g(f(x)))" by auto
      moreover from calculation
      have "\<langle>x,f(x)\<rangle> \<in> ?Y'" by auto
      moreover from calculation
      have "\<langle>f(x),g(f(x))\<rangle>\<in>?Z" by auto
      moreover from calculation
      have "\<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>fst(fst(?p)),snd(snd(?p))\<rangle>" by auto
      moreover from calculation
      have "\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_Collect :
  assumes "M(A)" "\<forall>x[M]. separation(M,F(x))"
    "separation(M,\<lambda>p . \<forall>x\<in>A. x\<in>snd(p) \<longleftrightarrow> F(fst(p),x))"
  shows "lam_replacement(M,\<lambda>x. {y\<in>A . F(x,y)})"
proof -
  {
    fix Z
    let ?Y="\<lambda>z.{x\<in>A . F(z,x)}"
    assume "M(Z)"
    moreover from this
    have "M(?Y(z))" if "z\<in>Z" for z
      using assms that transM[of _ Z] by simp
    moreover from this
    have "?Y(z)\<in>Pow\<^bsup>M\<^esup>(A)" if "z\<in>Z" for z
      using Pow_rel_char that assms by auto
    moreover from calculation \<open>M(A)\<close>
    have "M(Z\<times>Pow\<^bsup>M\<^esup>(A))" by simp
    moreover from this
    have "M({p \<in> Z\<times>Pow\<^bsup>M\<^esup>(A) . \<forall>x\<in>A. x\<in>snd(p) \<longleftrightarrow> F(fst(p),x)})" (is "M(?P)")
      using assms by simp
    ultimately
    have "b \<in> ?P \<longleftrightarrow> (\<exists>z[M]. z\<in>Z \<and> b=\<langle>z,?Y(z)\<rangle>)" if "M(b)" for b
      using  assms(1) Pow_rel_char[OF \<open>M(A)\<close>] that
      by(intro iffI,auto,intro equalityI,auto)
    with \<open>M(?P)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>z[M]. z \<in> Z \<and> b = \<langle>z,?Y(z)\<rangle>)"
      by (rule_tac rexI[where x="?P"],simp_all)
  }
  then
  show ?thesis
    unfolding lam_replacement_def strong_replacement_def
    by simp
qed

lemma lam_replacement_hcomp2:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
    "lam_replacement(M, \<lambda>p. h(fst(p),snd(p)))"
    "\<forall>x[M]. \<forall>y[M]. M(h(x,y))"
  shows "lam_replacement(M, \<lambda>x. h(f(x),g(x)))"
  using assms lam_replacement_product[of f g]
    lam_replacement_hcomp[of "\<lambda>x. \<langle>f(x), g(x)\<rangle>" "\<lambda>\<langle>x,y\<rangle>. h(x,y)"]
  unfolding split_def by simp

lemma lam_replacement_identity: "lam_replacement(M,\<lambda>x. x)"
proof -
  {
    fix A
    assume "M(A)"
    moreover from this
    have "id(A) = {\<langle>snd(fst(z)),fst(snd(z))\<rangle> . z\<in> {z\<in> (A\<times>A)\<times>(A\<times>A). snd(fst(z)) = fst(snd(z))}}"
      unfolding id_def lam_def
      by(intro equalityI subsetI,simp_all,auto)
    moreover from calculation
    have "M({z\<in> (A\<times>A)\<times>(A\<times>A). snd(fst(z)) = fst(snd(z))})" (is "M(?A')")
      using middle_separation by simp
    moreover from calculation
    have "M({\<langle>snd(fst(z)),fst(snd(z))\<rangle> . z\<in> ?A'})"
      using transM[of _ A]
        lam_replacement_product lam_replacement_hcomp lam_replacement_fst lam_replacement_snd
        lam_replacement_imp_strong_replacement[THEN RepFun_closed]
      by simp_all
    ultimately
    have "M(id(A))" by simp
  }
  then
  show ?thesis using lam_replacement_iff_lam_closed
    unfolding id_def by simp
qed

lemma lam_replacement_vimage :
  shows "lam_replacement(M, \<lambda>x. fst(x)-``snd(x))"
  unfolding vimage_def using
    lam_replacement_hcomp2[OF
      lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_converse] lam_replacement_snd
      _ _ lam_replacement_Image]
  by auto

lemma strong_replacement_separation_aux :
  assumes "strong_replacement(M,\<lambda> x y . y=f(x))" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=f(x))"
proof -
  {
    fix A
    let ?Q="\<lambda>X. \<forall>b[M]. b \<in> X \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
    assume "M(A)"
    moreover from this
    have "M({x\<in>A . P(x)})" (is "M(?B)") using assms by simp
    moreover from calculation assms
    obtain Y where "M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> ?B \<and> b = f(x))"
      unfolding strong_replacement_def by auto
    then
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
      using rexI[of ?Q _ M] by simp
  }
  then
  show ?thesis
    unfolding strong_replacement_def by simp
qed

lemma separation_in:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x)\<in>g(x))"
proof -
  let ?Z="\<lambda>A. {\<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>. x\<in>A}"
  have "M(?Z(A))" if "M(A)" for A
    using assms lam_replacement_iff_lam_closed that
      lam_replacement_product[of f g]
    unfolding lam_def
    by auto
  then
  have "M({u\<in>?Z(A) . fst(snd(u)) \<in>snd(snd(u))})" (is "M(?W(A))") if "M(A)" for A
    using that separation_fst_in_snd assms
    by auto
  then
  have "M({fst(u) . u \<in> ?W(A)})" if "M(A)" for A
    using that lam_replacement_imp_strong_replacement[OF lam_replacement_fst,THEN
        RepFun_closed] fst_closed[OF transM]
    by auto
  moreover
  have "{x\<in>A. f(x)\<in>g(x)} = {fst(u) . u\<in>?W(A)}" for A
    by auto
  ultimately
  show ?thesis
    using separation_iff
    by auto
qed

lemma lam_replacement_swap: "lam_replacement(M, \<lambda>x. \<langle>snd(x),fst(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
    lam_replacement_product[of "snd" "fst"] by simp

lemma lam_replacement_range : "lam_replacement(M,range)"
  unfolding range_def
  using lam_replacement_hcomp[OF lam_replacement_converse lam_replacement_domain]
  by auto

lemma separation_in_range : "M(a) \<Longrightarrow> separation(M, \<lambda>x. a\<in>range(x))"
  using lam_replacement_range lam_replacement_constant separation_in
  by auto

lemma separation_in_domain : "M(a) \<Longrightarrow> separation(M, \<lambda>x. a\<in>domain(x))"
  using lam_replacement_domain lam_replacement_constant separation_in
  by auto

lemma lam_replacement_separation :
  assumes "lam_replacement(M,f)" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=\<langle>x,f(x)\<rangle>)"
  using strong_replacement_separation_aux assms
  unfolding lam_replacement_def
  by simp

lemmas strong_replacement_separation =
  strong_replacement_separation_aux[OF lam_replacement_imp_strong_replacement]

lemma id_closed: "M(A) \<Longrightarrow> M(id(A))"
  using lam_replacement_identity lam_replacement_iff_lam_closed
  unfolding id_def by simp

lemma relation_separation: "separation(M, \<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle>)"
  unfolding separation_def
proof (clarify)
  fix A
  assume "M(A)"
  moreover from this
  have "{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>} = {z\<in>A. \<exists>x\<in>domain(A). \<exists>y\<in>range(A). pair(M, x, y, z)}"
    (is "?rel = _")
    by (intro equalityI, auto dest:transM)
      (intro bexI, auto dest:transM simp:Pair_def)
  moreover from calculation
  have "M(?rel)"
    using cartprod_separation[THEN separation_closed, of "domain(A)" "range(A)" A]
    by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> A \<and> (\<exists>w y. x = \<langle>w, y\<rangle>)"
    by (rule_tac x="{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>}" in rexI) auto
qed

lemma separation_pair:
  assumes "separation(M, \<lambda>y . P(fst(y), snd(y)))"
  shows "separation(M, \<lambda>y. \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover from this
  have "M({z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>})" (is "M(?P)")
    using relation_separation by simp
  moreover from this assms
  have "M({z\<in>?P . P(fst(z),snd(z))})"
    by(rule_tac separation_closed,simp_all)
  moreover
  have "{y\<in>A . \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v) } = {z\<in>?P . P(fst(z),snd(z))}"
    by(rule equalityI subsetI,auto)
  moreover from calculation
  have "M({y\<in>A . \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v) })"
    by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> A \<and> (\<exists>w y. x = \<langle>w, y\<rangle> \<and> P(w,y))"
    by (rule_tac x="{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> P(x,y)}" in rexI) auto
qed

lemma lam_replacement_Pair:
  shows "lam_replacement(M, \<lambda>x. \<langle>fst(x), snd(x)\<rangle>)"
  unfolding lam_replacement_def strong_replacement_def
proof (clarsimp)
  fix A
  assume "M(A)"
  then
  show "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>A. b = \<langle>x, fst(x), snd(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
  proof (cases "relation(A)")
    case True
    with \<open>M(A)\<close>
    show ?thesis
      using id_closed unfolding relation_def
      by (rule_tac x="id(A)" in rexI) auto
  next
    case False
    moreover
    note \<open>M(A)\<close>
    moreover from this
    have "M({z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>})" (is "M(?rel)")
      using relation_separation by auto
    moreover
    have "z = \<langle>fst(z), snd(z)\<rangle>" if "fst(z) \<noteq> 0 \<or> snd(z) \<noteq> 0" for z
      using that
      by (cases "\<exists>a b. z=\<langle>a,b\<rangle>") (auto simp add: the_0 fst_def snd_def)
    ultimately
    show ?thesis
      using id_closed unfolding relation_def
      by (rule_tac x="id(?rel) \<union> (A-?rel)\<times>{0}\<times>{0}" in rexI)
        (force simp:fst_def snd_def)+
  qed
qed

lemma lam_replacement_Un: "lam_replacement(M, \<lambda>p. fst(p) \<union> snd(p))"
  using lam_replacement_Upair lam_replacement_Union
    lam_replacement_hcomp[where g=Union and f="\<lambda>p. Upair(fst(p),snd(p))"]
  unfolding Un_def by simp

lemma lam_replacement_cons: "lam_replacement(M, \<lambda>p. cons(fst(p),snd(p)))"
  using  lam_replacement_Upair
    lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_hcomp2[of fst fst "Upair"]
    lam_replacement_Un lam_replacement_fst lam_replacement_snd
  unfolding cons_def
  by auto

lemma lam_replacement_sing: "lam_replacement(M, \<lambda>x. {x})"
  using lam_replacement_constant lam_replacement_cons
    lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>_. 0" cons]
  by (force intro: lam_replacement_identity)

lemmas tag_replacement = lam_replacement_constant[unfolded lam_replacement_def]

lemma lam_replacement_id2: "lam_replacement(M, \<lambda>x. \<langle>x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_product[of "\<lambda>x. x" "\<lambda>x. x"]
  by simp

lemmas id_replacement = lam_replacement_id2[unfolded lam_replacement_def]

lemma lam_replacement_apply2:"lam_replacement(M, \<lambda>p. fst(p) ` snd(p))"
  using lam_replacement_sing lam_replacement_fst lam_replacement_snd
    lam_replacement_Image lam_replacement_Union
  unfolding apply_def
  by (rule_tac lam_replacement_hcomp[of _ Union],
      rule_tac lam_replacement_hcomp2[of _ _ "(``)"])
    (force intro:lam_replacement_hcomp)+

definition map_snd where
  "map_snd(X) = {snd(z) . z\<in>X}"

lemma map_sndE: "y\<in>map_snd(X) \<Longrightarrow> \<exists>p\<in>X. y=snd(p)"
  unfolding map_snd_def by auto

lemma map_sndI : "\<exists>p\<in>X. y=snd(p) \<Longrightarrow> y\<in>map_snd(X)"
  unfolding map_snd_def by auto

lemma map_snd_closed: "M(x) \<Longrightarrow> M(map_snd(x))"
  unfolding map_snd_def
  using lam_replacement_imp_strong_replacement[OF lam_replacement_snd]
    RepFun_closed snd_closed[OF transM[of _ x]]
  by simp

lemma lam_replacement_imp_lam_replacement_RepFun:
  assumes "lam_replacement(M, f)" "\<forall>x[M]. M(f(x))"
    "separation(M, \<lambda>x. ((\<forall>y\<in>snd(x). fst(y) \<in> fst(x)) \<and> (\<forall>y\<in>fst(x). \<exists>u\<in>snd(x). y=fst(u))))"
    and
    lam_replacement_RepFun_snd:"lam_replacement(M,map_snd)"
  shows "lam_replacement(M, \<lambda>x. {f(y) . y\<in>x})"
proof -
  have f_closed:"M(\<langle>fst(z),map_snd(snd(z))\<rangle>)" if "M(z)" for z
    using pair_in_M_iff fst_closed snd_closed map_snd_closed that
    by simp
  have p_closed:"M(\<langle>x,{f(y) . y\<in>x}\<rangle>)" if "M(x)" for x
    using pair_in_M_iff RepFun_closed lam_replacement_imp_strong_replacement
      transM[OF _ that] that assms by auto
  {
    fix A
    assume "M(A)"
    then
    have "M({\<langle>y,f(y)\<rangle> . y\<in>x})" if "x\<in>A" for x
      using lam_replacement_iff_lam_closed assms that transM[of _ A]
      unfolding lam_def by simp
    from assms \<open>M(A)\<close>
    have "\<forall>x\<in>\<Union>A. M(f(x))"
      using transM[of _ "\<Union>A"] by auto
    with assms \<open>M(A)\<close>
    have "M({\<langle>y,f(y)\<rangle> . y \<in> \<Union>A})" (is "M(?fUnA)")
      using lam_replacement_iff_lam_closed[THEN iffD1,OF assms(2) assms(1)]
      unfolding lam_def
      by simp
    with \<open>M(A)\<close>
    have "M(Pow_rel(M,?fUnA))" by simp
    with \<open>M(A)\<close>
    have "M({z\<in>A\<times>Pow_rel(M,?fUnA) . ((\<forall>y\<in>snd(z). fst(y) \<in> fst(z)) \<and> (\<forall>y\<in>fst(z). \<exists>u\<in>snd(z). y=fst(u)))})" (is "M(?T)")
      using assms(3) by simp
    then
    have 1:"M({\<langle>fst(z),map_snd(snd(z))\<rangle> . z\<in>?T})" (is "M(?Y)")
      using lam_replacement_product[OF lam_replacement_fst
          lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_RepFun_snd]]
        RepFun_closed lam_replacement_imp_strong_replacement
        f_closed[OF transM[OF _ \<open>M(?T)\<close>]]
      by simp
    have 2:"?Y = {\<langle>x,{f(y) . y\<in>x}\<rangle> . x\<in>A}" (is "_ = ?R")
    proof(intro equalityI subsetI)
      fix p
      assume "p\<in>?R"
      with \<open>M(A)\<close>
      obtain x where "x\<in>A" "p=\<langle>x,{f(y) . y \<in> x}\<rangle>" "M(x)"
        using transM[OF _ \<open>M(A)\<close>]
        by auto
      moreover from calculation
      have "M({\<langle>y,f(y)\<rangle> . y\<in>x})" (is "M(?Ux)")
        using lam_replacement_iff_lam_closed assms
        unfolding lam_def by auto
      moreover from calculation
      have "?Ux \<subseteq> ?fUnA"
        by auto
      moreover from calculation
      have "?Ux \<in> Pow_rel(M,?fUnA)"
        using Pow_rel_char[OF \<open>M(?fUnA)\<close>] by simp
      moreover from calculation
      have "\<forall>u\<in>x. \<exists>w\<in>?Ux. u=fst(w)"
        by force
      moreover from calculation
      have "\<langle>x,?Ux\<rangle> \<in> ?T" by auto
      moreover from calculation
      have "{f(y).y\<in>x} = map_snd(?Ux)"
        unfolding map_snd_def
        by(intro equalityI,auto)
      ultimately
      show "p\<in>?Y"
        by (auto,rule_tac bexI[where x=x],simp_all,rule_tac bexI[where x="?Ux"],simp_all)
    next
      fix u
      assume "u\<in>?Y"
      moreover from this
      obtain z where "z\<in>?T" "u=\<langle>fst(z),map_snd(snd(z))\<rangle>"
        by blast
      moreover from calculation
      obtain x U where
        1:"x\<in>A" "U\<in>Pow_rel(M,?fUnA)" "(\<forall>u\<in>U. fst(u) \<in> x) \<and> (\<forall>w\<in>x. \<exists>v\<in>U. w=fst(v))" "z=\<langle>x,U\<rangle>"
        by force
      moreover from this
      have "fst(u)\<in>\<Union>A" "snd(u) = f(fst(u))" if "u\<in>U" for u
        using that Pow_rel_char[OF \<open>M(?fUnA)\<close>]
        by auto
      moreover from calculation
      have "map_snd(U) = {f(y) . y\<in>x}"
        unfolding map_snd_def
        by(intro equalityI subsetI,auto)
      moreover from calculation
      have "u=\<langle>x,map_snd(U)\<rangle>"
        by simp
      ultimately
      show "u\<in>?R"
        by (auto)
    qed
    from 1 2
    have "M({\<langle>x,{f(y) . y\<in>x}\<rangle> . x\<in>A})"
      by simp
  }
  then
  have "\<forall>A[M]. M(\<lambda>x\<in>A. {f(y) . y\<in>x})"
    unfolding lam_def by auto
  then
  show ?thesis
    using lam_replacement_iff_lam_closed[THEN iffD2] p_closed
    by simp
qed


lemma lam_replacement_apply:"M(S) \<Longrightarrow> lam_replacement(M, \<lambda>x.  S ` x)"
  using lam_replacement_Union lam_replacement_constant lam_replacement_identity
    lam_replacement_Image lam_replacement_cons
    lam_replacement_hcomp2[of _ _ Image] lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>_. 0" cons]
  unfolding apply_def
  by (rule_tac lam_replacement_hcomp[of _ Union]) (force intro:lam_replacement_hcomp)+

lemma apply_replacement:"M(S) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = S ` x)"
  using lam_replacement_apply lam_replacement_imp_strong_replacement by simp

lemma lam_replacement_id_const: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<langle>x, b\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. x" "\<lambda>x. b"] by simp

lemmas pospend_replacement = lam_replacement_id_const[unfolded lam_replacement_def]

lemma lam_replacement_const_id: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>z. \<langle>b, z\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. b" "\<lambda>x. x"] by simp

lemmas prepend_replacement = lam_replacement_const_id[unfolded lam_replacement_def]

lemma lam_replacement_apply_const_id: "M(f) \<Longrightarrow> M(z) \<Longrightarrow>
      lam_replacement(M, \<lambda>x. f ` \<langle>z, x\<rangle>)"
  using lam_replacement_const_id[of z] lam_replacement_apply[of f]
    lam_replacement_hcomp[of "\<lambda>x. \<langle>z, x\<rangle>" "\<lambda>x. f`x"] by simp

lemmas apply_replacement2 = lam_replacement_apply_const_id[unfolded lam_replacement_def]

lemma lam_replacement_Inl: "lam_replacement(M, Inl)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. 0" "\<lambda>x. x"]
  unfolding Inl_def by simp

lemma lam_replacement_Inr: "lam_replacement(M, Inr)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. 1" "\<lambda>x. x"]
  unfolding Inr_def by simp

lemmas Inl_replacement1 = lam_replacement_Inl[unfolded lam_replacement_def]

lemma lam_replacement_Diff': "M(X) \<Longrightarrow> lam_replacement(M, \<lambda>x. x - X)"
  using lam_replacement_Diff
  by (force intro: lam_replacement_hcomp2 lam_replacement_constant
      lam_replacement_identity)+

lemmas Pair_diff_replacement = lam_replacement_Diff'[unfolded lam_replacement_def]

lemma diff_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=\<langle>x,x-{p}\<rangle>)"
  using Pair_diff_replacement by simp

lemma swap_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>y, x\<rangle>)(x)\<rangle>)"
  using lam_replacement_swap unfolding lam_replacement_def split_def by simp

lemma lam_replacement_Un_const:"M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. x \<union> b)"
  using lam_replacement_Un lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_constant[of b] lam_replacement_identity by simp

lemmas tag_union_replacement = lam_replacement_Un_const[unfolded lam_replacement_def]

lemma lam_replacement_csquare: "lam_replacement(M,\<lambda>p. \<langle>fst(p) \<union> snd(p), fst(p), snd(p)\<rangle>)"
  using lam_replacement_Un lam_replacement_fst lam_replacement_snd
  by (fast intro: lam_replacement_product lam_replacement_hcomp2)

lemma csquare_lam_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>x \<union> y, x, y\<rangle>)(x)\<rangle>)"
  using lam_replacement_csquare unfolding split_def lam_replacement_def .

lemma lam_replacement_assoc:"lam_replacement(M,\<lambda>x. \<langle>fst(fst(x)), snd(fst(x)), snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_product lam_replacement_hcomp)

lemma assoc_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x, y, z\<rangle>)(x)\<rangle>)"
  using lam_replacement_assoc unfolding split_def lam_replacement_def .

lemma lam_replacement_prod_fun: "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M,\<lambda>x. \<langle>f ` fst(x), g ` snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_product lam_replacement_hcomp lam_replacement_apply)

lemma prod_fun_replacement:"M(f) \<Longrightarrow> M(g) \<Longrightarrow>
  strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>w,y\<rangle>. \<langle>f ` w, g ` y\<rangle>)(x)\<rangle>)"
  using lam_replacement_prod_fun unfolding split_def lam_replacement_def .

lemma lam_replacement_vimage_sing: "lam_replacement(M, \<lambda>p. fst(p) -`` {snd(p)})"
  using lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_sing]
    lam_replacement_hcomp2[OF lam_replacement_fst  _ _ _ lam_replacement_vimage]
  by simp

lemma lam_replacement_vimage_sing_fun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f -`` {x})"
  using lam_replacement_hcomp2[OF lam_replacement_constant[of f]
      lam_replacement_identity _ _ lam_replacement_vimage_sing]
  by simp
lemma lam_replacement_image_sing_fun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f `` {x})"
  using lam_replacement_hcomp2[OF lam_replacement_constant[of f]
      lam_replacement_hcomp[OF lam_replacement_identity lam_replacement_sing]
      _ _ lam_replacement_Image]
  by simp

lemma converse_apply_projs: "\<forall>x[M]. \<Union> (fst(x) -`` {snd(x)}) = converse(fst(x)) ` (snd(x))"
  using converse_apply_eq by auto

lemma lam_replacement_converse_app: "lam_replacement(M, \<lambda>p. converse(fst(p)) ` snd(p))"
  using lam_replacement_cong[OF _ converse_apply_projs]
    lam_replacement_hcomp[OF lam_replacement_vimage_sing lam_replacement_Union]
  by simp

lemmas cardinal_lib_assms4 = lam_replacement_vimage_sing_fun[unfolded lam_replacement_def]

lemma lam_replacement_sing_const_id:
  "M(x) \<Longrightarrow> lam_replacement(M, \<lambda>y. {\<langle>x, y\<rangle>})"
  using lam_replacement_hcomp[OF lam_replacement_const_id[of x]]
    lam_replacement_sing pair_in_M_iff
  by simp

lemma tag_singleton_closed: "M(x) \<Longrightarrow> M(z) \<Longrightarrow> M({{\<langle>z, y\<rangle>} . y \<in> x})"
  using RepFun_closed[where A=x and f="\<lambda> u. {\<langle>z,u\<rangle>}"]
    lam_replacement_imp_strong_replacement lam_replacement_sing_const_id
    transM[of _ x]
  by simp

lemma separation_eq:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x) = g(x))"
proof -
  let ?Z="\<lambda>A. {\<langle>x,\<langle>f(x),\<langle>g(x),x\<rangle>\<rangle>\<rangle>. x\<in>A}"
  let ?Y="\<lambda>A. {\<langle>\<langle>x,f(x)\<rangle>,\<langle>g(x),x\<rangle>\<rangle>. x\<in>A}"
  note sndsnd = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_snd]
  note fstsnd = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_fst]
  note sndfst = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  have "M(?Z(A))" if "M(A)" for A
    using assms lam_replacement_iff_lam_closed that
      lam_replacement_product[OF assms(2)
        lam_replacement_product[OF assms(4) lam_replacement_identity]]
    unfolding lam_def
    by auto
  moreover
  have "?Y(A) = {\<langle>\<langle>fst(x), fst(snd(x))\<rangle>, fst(snd(snd(x))), snd(snd(snd(x)))\<rangle> . x \<in> ?Z(A)}" for A
    by auto
  moreover from calculation
  have "M(?Y(A))" if "M(A)" for A
    using
      lam_replacement_imp_strong_replacement[OF
        lam_replacement_product[OF
          lam_replacement_product[OF lam_replacement_fst fstsnd]
          lam_replacement_product[OF
            lam_replacement_hcomp[OF sndsnd lam_replacement_fst]
            lam_replacement_hcomp[OF lam_replacement_snd sndsnd]
            ]
          ], THEN RepFun_closed,simplified,of "?Z(A)"]
      fst_closed[OF transM] snd_closed[OF transM] that
    by auto
  then
  have "M({u\<in>?Y(A) . snd(fst(u)) = fst(snd(u))})" (is "M(?W(A))") if "M(A)" for A
    using that middle_separation assms
    by auto
  then
  have "M({fst(fst(u)) . u \<in> ?W(A)})" if "M(A)" for A
    using that lam_replacement_imp_strong_replacement[OF
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst], THEN RepFun_closed]
      fst_closed[OF transM]
    by auto
  moreover
  have "{x\<in>A. f(x) = g(x)} = {fst(fst(u)) . u\<in>?W(A)}" for A
    by auto
  ultimately
  show ?thesis
    using separation_iff by auto
qed

lemma separation_subset:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x) \<subseteq> g(x))"
proof -
  have "f(x) \<subseteq> g(x) \<longleftrightarrow> f(x)\<union>g(x) = g(x)" for x
    using subset_Un_iff by simp
  moreover from assms
  have "separation(M,\<lambda>x . f(x)\<union>g(x) = g(x))"
    using separation_eq lam_replacement_Un lam_replacement_hcomp2
    by simp
  ultimately
  show ?thesis
    using separation_cong[THEN iffD1] by auto
qed

lemma separation_ball:
  assumes "separation(M, \<lambda>y. f(fst(y),snd(y)))" "M(X)"
  shows "separation(M, \<lambda>y. \<forall>u\<in>X. f(y,u))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover
  note \<open>M(X)\<close>
  moreover from calculation
  have "M(A\<times>X)"
    by simp
  then
  have "M({p \<in> A\<times>X . f(fst(p),snd(p))})" (is "M(?P)")
    using assms(1)
    by auto
  moreover from calculation
  have "M({a\<in>A . ?P``{a} = X})" (is "M(?A')")
    using separation_eq lam_replacement_image_sing_fun[of "?P"] lam_replacement_constant
    by simp
  moreover
  have "f(a,x)" if "a\<in>?A'" and "x\<in>X" for a x
  proof -
    from that
    have "a\<in>A" "?P``{a}=X"
      by auto
    then
    have "x\<in>?P``{a}"
      using that by simp
    then
    show ?thesis using image_singleton_iff by simp
  qed
  moreover from this
  have "\<forall>a[M]. a \<in> ?A' \<longleftrightarrow> a \<in> A \<and> (\<forall>x\<in>X. f(a, x))"
    using image_singleton_iff
    by auto
  with \<open>M(?A')\<close>
  show "\<exists>y[M]. \<forall>a[M]. a \<in> y \<longleftrightarrow> a \<in> A \<and> (\<forall>x\<in>X. f(a, x))"
    by (rule_tac x="?A'" in rexI,simp_all)
qed

lemma lam_replacement_twist: "lam_replacement(M,\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
    lam_replacement_Pair[THEN [5] lam_replacement_hcomp2,
      of "\<lambda>x. snd(fst(x))" "\<lambda>x. snd(x)", THEN [2] lam_replacement_Pair[
        THEN [5] lam_replacement_hcomp2, of "\<lambda>x. fst(fst(x))"]]
    lam_replacement_hcomp unfolding split_def by simp

lemma twist_closed[intro,simp]: "M(x) \<Longrightarrow> M((\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)(x))"
  unfolding split_def by simp

lemma lam_replacement_Lambda:
  assumes "lam_replacement(M, \<lambda>y. b(fst(y), snd(y)))"
    "\<forall>w[M]. \<forall>y[M]. M(b(w, y))" "M(W)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>W. b(x, w))"
proof (intro lam_replacement_iff_lam_closed[THEN iffD2]; clarify)
  have aux_sep: "\<forall>x[M]. separation(M,\<lambda>y. \<langle>fst(x), y\<rangle> \<in> A)"
    if "M(X)" "M(A)" for X A
    using separation_in lam_replacement_hcomp2[OF lam_replacement_hcomp[OF  lam_replacement_constant lam_replacement_fst]
        lam_replacement_identity _ _ lam_replacement_Pair]
      lam_replacement_constant[of A]
      that
    by simp
  have aux_closed: "\<forall>x[M]. M({y \<in> X . \<langle>fst(x), y\<rangle> \<in> A})" if "M(X)" "M(A)" for X A
    using aux_sep that by simp
  have aux_lemma: "lam_replacement(M,\<lambda>p . {y \<in> X . \<langle>fst(p), y\<rangle> \<in> A})"
    if "M(X)" "M(A)" for X A
  proof -
    note lr = lam_replacement_Collect[OF \<open>M(X)\<close>]
    note fst3 = lam_replacement_hcomp[OF lam_replacement_fst
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]]
    then show ?thesis
      using lam_replacement_Collect[OF \<open>M(X)\<close> aux_sep separation_ball[OF separation_iff']]
        separation_in[OF _ lam_replacement_snd _ lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]]
        separation_in[OF _ lam_replacement_hcomp2[OF fst3 lam_replacement_snd _ _  lam_replacement_Pair] _
          lam_replacement_constant[of A]] that
      by auto
  qed
  from assms
  show lbc:"M(x) \<Longrightarrow> M(\<lambda>w\<in>W. b(x, w))" for x
    using lam_replacement_constant lam_replacement_identity
      lam_replacement_hcomp2[where h=b]
    by (intro lam_replacement_iff_lam_closed[THEN iffD1, rule_format])
      simp_all
  fix A
  assume "M(A)"
  moreover from this assms
  have "M({b(fst(x),snd(x)). x \<in> A\<times>W})" (is "M(?RFb)")\<comment> \<open>\<^term>\<open>RepFun\<close> \<^term>\<open>b\<close>\<close>
    using lam_replacement_imp_strong_replacement transM[of _ "A\<times>W"]
    by (rule_tac RepFun_closed) auto
  moreover
  have "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (A\<times>W)\<times>?RFb. z = b(x,y)} = (\<lambda>\<langle>x,y\<rangle>\<in>A\<times>W. b(x,y)) \<inter> (A\<times>W)\<times>?RFb"
    (is "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (A\<times>W)\<times>?B. _ } = ?lam")
    unfolding lam_def by auto
  moreover from calculation and assms
  have "M(?lam)"
    using lam_replacement_iff_lam_closed unfolding split_def by simp
  moreover
  have "{\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (X \<times> Y) \<times> Z . P(x, y, z)} \<subseteq> (X \<times> Y) \<times> Z" for X Y Z P
    by auto
  then
  have "{\<langle>x,y,z\<rangle> \<in> X\<times>Y\<times>Z. P(x,y,z) }= (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>\<in>(X\<times>Y)\<times>Z. \<langle>x,y,z\<rangle>) ``
        {\<langle>\<langle>x,y\<rangle>,z\<rangle> \<in> (X\<times>Y)\<times>Z. P(x,y,z) }" (is "?C' = Lambda(?A,?f) `` ?C")
    for X Y Z P
    using image_lam[of ?C ?A ?f]
    by (intro equalityI) (auto)
  with calculation
  have "{\<langle>x,y,z\<rangle> \<in> A\<times>W\<times>?RFb. z = b(x,y) } =
        (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>\<in>(A\<times>W)\<times>?RFb. \<langle>x,y,z\<rangle>) `` ?lam" (is "?H = ?G ")
    by simp
  with \<open>M(A)\<close> \<open>M(W)\<close> \<open>M(?lam)\<close> \<open>M(?RFb)\<close>
  have "M(?H)"
    using lam_replacement_iff_lam_closed[THEN iffD1, rule_format, OF _ lam_replacement_twist]
    by simp
  moreover from this and \<open>M(A)\<close>
  have "(\<lambda>x\<in>A. \<lambda>w\<in>W. b(x, w)) =
    {\<langle>x,Z\<rangle> \<in> A \<times> Pow\<^bsup>M\<^esup>(range(?H)). Z = {y \<in> W\<times>?RFb . \<langle>x, y\<rangle> \<in> ?H}}"
    unfolding lam_def
    by (intro equalityI; subst Pow_rel_char[of "range(?H)"])
      (auto dest:transM simp: lbc[unfolded lam_def], force+)
  moreover from calculation and \<open>M(A)\<close> and \<open>M(W)\<close>
  have "M(A\<times>Pow\<^bsup>M\<^esup>(range(?H)))" "M(W\<times>?RFb)"
    by auto
  moreover
  note \<open>M(W)\<close>
  moreover from calculation
  have "M({\<langle>x,Z\<rangle> \<in> A \<times> Pow\<^bsup>M\<^esup>(range(?H)). Z = {y \<in> W\<times>?RFb . \<langle>x, y\<rangle> \<in> ?H}})"
    using separation_eq[OF _ lam_replacement_snd
        aux_closed[OF \<open>M(W\<times>?RFb)\<close> \<open>M(?H)\<close>]
        aux_lemma[OF \<open>M(W\<times>?RFb)\<close> \<open>M(?H)\<close>]]
      \<open>M(A\<times>Pow\<^bsup>M\<^esup>(_))\<close> assms
    unfolding split_def
    by auto
  ultimately
  show "M(\<lambda>x\<in>A. \<lambda>w\<in>W. b(x, w))" by simp
qed

lemma lam_replacement_apply_Pair:
  assumes "M(y)"
  shows "lam_replacement(M, \<lambda>x. y ` \<langle>fst(x), snd(x)\<rangle>)"
  using assms lam_replacement_constant lam_replacement_Pair
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma lam_replacement_apply_fst_snd:
  shows "lam_replacement(M, \<lambda>w. fst(w) ` fst(snd(w)) ` snd(snd(w)))"
  using lam_replacement_fst lam_replacement_snd lam_replacement_hcomp
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma separation_snd_in_fst: "separation(M, \<lambda>x. snd(x) \<in> fst(x))"
  using separation_in lam_replacement_fst lam_replacement_snd
  by auto

lemma lam_replacement_if_mem:
  "lam_replacement(M, \<lambda>x. if snd(x) \<in> fst(x) then 1 else 0)"
  using separation_snd_in_fst
    lam_replacement_constant lam_replacement_if
  by auto

lemma lam_replacement_Lambda_apply_fst_snd:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. x ` fst(w) ` snd(w))"
  using assms lam_replacement_apply_fst_snd lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_apply_Pair:
  assumes "M(X)" "M(y)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. y ` \<langle>x, w\<rangle>)"
  using assms lam_replacement_apply_Pair lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_if_mem:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>xa\<in>X. if xa \<in> x then 1 else 0)"
  using assms lam_replacement_if_mem lam_replacement_Lambda
  by simp

lemma lam_replacement_comp':
  "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M, \<lambda>x . f O x O g)"
  using lam_replacement_comp[THEN [5] lam_replacement_hcomp2,
      OF lam_replacement_constant lam_replacement_comp,
      THEN [5] lam_replacement_hcomp2] lam_replacement_constant
    lam_replacement_identity by simp

lemma separation_bex:
  assumes "separation(M, \<lambda>y. f(fst(y),snd(y)))" "M(X)"
  shows "separation(M, \<lambda>y. \<exists>u\<in>X. f(y,u))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover
  note \<open>M(X)\<close>
  moreover from calculation
  have "M(A\<times>X)"
    by simp
  then
  have "M({p \<in> A\<times>X . f(fst(p),snd(p))})" (is "M(?P)")
    using assms(1)
    by auto
  moreover from calculation
  have "M({a\<in>A . ?P``{a} \<noteq> 0})" (is "M(?A')")
    using separation_eq lam_replacement_image_sing_fun[of "?P"] lam_replacement_constant
      separation_neg
    by simp
  moreover from this
  have "\<forall>a[M]. a \<in> ?A' \<longleftrightarrow> a \<in> A \<and> (\<exists>x\<in>X. f(a, x))"
    using image_singleton_iff
    by auto
  with \<open>M(?A')\<close>
  show "\<exists>y[M]. \<forall>a[M]. a \<in> y \<longleftrightarrow> a \<in> A \<and> (\<exists>x\<in>X. f(a, x))"
    by (rule_tac x="?A'" in rexI,simp_all)
qed

lemma case_closed :
  assumes "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "\<forall>x[M]. M(case(f,g,x))"
  unfolding case_def split_def cond_def
  using assms by simp

lemma separation_fst_equal : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(x)=a)"
  using separation_eq lam_replacement_fst lam_replacement_constant
  by auto

lemma lam_replacement_case :
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x . case(f,g,x))"
  unfolding case_def split_def cond_def
  using lam_replacement_if separation_fst_equal
    lam_replacement_hcomp[of "snd" g]
    lam_replacement_hcomp[of "snd" f]
    lam_replacement_snd assms
  by simp

lemma Pi_replacement1: "M(x) \<Longrightarrow> M(y) \<Longrightarrow>  strong_replacement(M, \<lambda>ya z. ya \<in> y \<and> z = {\<langle>x, ya\<rangle>})"
  using lam_replacement_imp_strong_replacement
    strong_replacement_separation[OF lam_replacement_sing_const_id[of x],where P="\<lambda>x . x \<in>y"]
    separation_in_constant
  by simp

lemma surj_imp_inj_replacement1:
  "M(f) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using Pi_replacement1 vimage_closed singleton_closed
  by simp

lemmas domain_replacement = lam_replacement_domain[unfolded lam_replacement_def]

lemma domain_replacement_simp: "strong_replacement(M, \<lambda>x y. y=domain(x))"
  using lam_replacement_domain lam_replacement_imp_strong_replacement by simp

lemma un_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y = x\<union>{p})"
  using lam_replacement_Un_const[THEN lam_replacement_imp_strong_replacement] by simp

lemma diff_replacement: "M(X) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = x - X)"
  using lam_replacement_Diff'[THEN lam_replacement_imp_strong_replacement] by simp

lemma lam_replacement_succ:
  "lam_replacement(M,\<lambda>z . succ(z))"
  unfolding succ_def
  using lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>x. x" cons]
    lam_replacement_cons lam_replacement_identity
  by simp

lemma lam_replacement_hcomp_Least:
  assumes "lam_replacement(M, g)" "lam_replacement(M,\<lambda>x. \<mu> i. x\<in>F(i,x))"
    "\<forall>x[M]. M(g(x))" "\<And>x i. M(x) \<Longrightarrow> i \<in> F(i, x) \<Longrightarrow> M(i)"
  shows "lam_replacement(M,\<lambda>x. \<mu> i. g(x)\<in>F(i,g(x)))"
  using assms
  by (rule_tac lam_replacement_hcomp[of _ "\<lambda>x. \<mu> i. x\<in>F(i,x)"])
    (auto intro:Least_closed')

lemma domain_mem_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>x . domain(x)\<in>A)"
  using separation_in lam_replacement_constant lam_replacement_domain
  by auto

lemma domain_eq_separation: "M(p) \<Longrightarrow> separation(M, \<lambda>x . domain(x) = p)"
  using separation_eq lam_replacement_domain lam_replacement_constant
  by auto

lemma lam_replacement_Int:
  shows "lam_replacement(M, \<lambda>x. fst(x) \<inter> snd(x))"
proof -
  have "A\<inter>B = (A\<union>B) - ((A- B) \<union> (B-A))" (is "_=?f(A,B)")for A B
    by auto
  then
  show ?thesis
    using lam_replacement_cong
      lam_replacement_Diff[THEN[5] lam_replacement_hcomp2]
      lam_replacement_Un[THEN[5] lam_replacement_hcomp2]
      lam_replacement_fst lam_replacement_snd
    by simp
qed

lemma lam_replacement_CartProd:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. f(x) \<times> g(x))"
proof -
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  {
    fix A
    assume "M(A)"
    moreover
    note transM[OF _ \<open>M(A)\<close>]
    moreover from calculation assms
    have "M({\<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle> . x\<in>A})" (is "M(?A')")
      using lam_replacement_product[THEN lam_replacement_imp_lam_closed[unfolded lam_def]]
      by simp
    moreover from calculation
    have "M(\<Union>{f(x) . x\<in>A})" (is "M(?F)")
      using rep_closed[OF assms(1)] assms(3)
      by simp
    moreover from calculation
    have "M(\<Union>{g(x) . x\<in>A})" (is "M(?G)")
      using rep_closed[OF assms(2)] assms(4)
      by simp
    moreover from calculation
    have "M(?A' \<times> (?F \<times> ?G))" (is "M(?T)")
      by simp
    moreover from this
    have "M({t \<in> ?T . fst(snd(t)) \<in> fst(snd(fst(t))) \<and> snd(snd(t)) \<in> snd(snd(fst(t)))})" (is "M(?Q)")
      using
        lam_replacement_hcomp[OF lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd] _ ]
        lam_replacement_hcomp lam_replacement_identity  lam_replacement_fst lam_replacement_snd
        separation_in separation_conj
      by simp
    moreover from this
    have "M({\<langle>fst(fst(t)),snd(t)\<rangle> . t\<in>?Q})" (is "M(?R)")
      using rep_closed lam_replacement_Pair[THEN [5] lam_replacement_hcomp2]
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst] lam_replacement_snd
        transM[of _ ?Q]
      by simp
    moreover from calculation
    have "M({\<langle>x,?R``{x}\<rangle> . x\<in>A})"
      using lam_replacement_imp_lam_closed[unfolded lam_def] lam_replacement_sing
        lam_replacement_Image[THEN [5] lam_replacement_hcomp2] lam_replacement_constant[of ?R]
      by simp
    moreover
    have "?R``{x} = f(x)\<times>g(x)" if "x\<in>A" for x
      by(rule equalityI subsetI,force,rule subsetI,rule_tac a="x" in imageI)
        (auto simp:that,(rule_tac rev_bexI[of x],simp_all add:that)+)
    ultimately
    have "M({\<langle>x,f(x) \<times> g(x)\<rangle> . x\<in>A})" by auto
  }
  with assms
  show ?thesis using lam_replacement_iff_lam_closed[THEN iffD2,unfolded lam_def]
    by simp
qed

lemma restrict_eq_separation': "M(B) \<Longrightarrow> \<forall>A[M]. separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)"
proof(clarify)
  fix A
  have "restrict(r,B) = r \<inter> (B \<times> range(r))" for r
    unfolding restrict_def by(rule equalityI subsetI,auto)
  moreover
  assume "M(A)" "M(B)"
  moreover from this
  have "separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, x \<inter> (B \<times> range(x))\<rangle>)"
    using lam_replacement_Int[THEN[5] lam_replacement_hcomp2]
      lam_replacement_Pair[THEN[5] lam_replacement_hcomp2]
    using lam_replacement_fst lam_replacement_snd lam_replacement_constant
      lam_replacement_hcomp lam_replacement_range lam_replacement_identity
      lam_replacement_CartProd separation_bex separation_eq
    by simp_all
  ultimately
  show "separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)"
    by simp
qed

lemmas lam_replacement_restrict' = lam_replacement_restrict[OF restrict_eq_separation']

lemma restrict_strong_replacement: "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y=restrict(x,A))"
  using lam_replacement_restrict restrict_eq_separation'
    lam_replacement_imp_strong_replacement
  by simp

lemma restrict_eq_separation: "M(r) \<Longrightarrow> M(p) \<Longrightarrow> separation(M, \<lambda>x . restrict(x,r) = p)"
  using separation_eq lam_replacement_restrict' lam_replacement_constant
  by auto

lemma separation_equal_fst2 : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(fst(x))=a)"
  using separation_eq lam_replacement_hcomp lam_replacement_fst lam_replacement_constant
  by auto

lemma separation_equal_apply: "M(f) \<Longrightarrow> M(a) \<Longrightarrow> separation(M,\<lambda>x. f`x=a)"
  using separation_eq lam_replacement_apply[of f] lam_replacement_constant
  by auto

lemma lam_apply_replacement: "M(A) \<Longrightarrow> M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x . \<lambda>n\<in>A. f ` \<langle>x, n\<rangle>)"
  using lam_replacement_Lambda lam_replacement_hcomp[OF _ lam_replacement_apply[of f]] lam_replacement_Pair
  by simp

lemma separation_all:
  assumes "separation(M, \<lambda>x  .P(fst(x),snd(x)))"
  shows "separation(M, \<lambda>z. \<forall>x\<in>z. P(z,x))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  let ?B="\<Union>A"
  let ?C="A\<times>?B"
  note \<open>M(A)\<close>
  moreover from calculation
  have "M(?C)"
    by simp
  moreover from calculation
  have "M({p\<in>?C . P(fst(p),snd(p)) \<and> snd(p)\<in>fst(p)})" (is "M(?Prod)")
    using assms separation_conj separation_in lam_replacement_fst lam_replacement_snd
    by simp
  moreover from calculation
  have "M({z\<in>A . z=?Prod``{z}})" (is "M(?L)")
    using separation_eq lam_replacement_identity
      lam_replacement_constant[of ?Prod] lam_replacement_image_sing_fun
    by simp
  moreover
  have "?L = {z\<in>A . \<forall>x\<in>z. P(z,x)}"
  proof -
    have "P(z,x)" if "z\<in>A" "x\<in>z" "x\<in>?Prod``{z}" for z x
      using that
      by auto
    moreover
    have "z = ?Prod `` {z}" if "z\<in>A" "\<forall>x\<in>z. P(z, x)" for z
      using that
      by(intro equalityI subsetI,auto)
    ultimately
    show ?thesis
      by(intro equalityI subsetI,auto)
  qed
  ultimately
  show " \<exists>y[M]. \<forall>z[M]. z \<in> y \<longleftrightarrow> z \<in> A \<and> (\<forall>x\<in>z . P(z,x))"
    by (rule_tac x="?L" in rexI,simp_all)
qed

lemma separation_Transset: "separation(M,Transset)"
  unfolding Transset_def
  using separation_all separation_subset lam_replacement_fst lam_replacement_snd
  by auto

lemma separation_comp :
  assumes "separation(M,P)" "lam_replacement(M,f)" "\<forall>x[M]. M(f(x))"
  shows "separation(M,\<lambda>x. P(f(x)))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  let ?B="{f(a) . a \<in> A}"
  let ?C="A\<times>{b\<in>?B . P(b)}"
  note \<open>M(A)\<close>
  moreover from calculation
  have "M(?C)"
    using lam_replacement_imp_strong_replacement assms RepFun_closed transM[of _ A]
    by simp
  moreover from calculation
  have "M({p\<in>?C . f(fst(p)) = snd(p)})" (is "M(?Prod)")
    using assms separation_eq lam_replacement_fst lam_replacement_snd
      lam_replacement_hcomp
    by simp
  moreover from calculation
  have "M({fst(p) . p\<in>?Prod})" (is "M(?L)")
    using lam_replacement_imp_strong_replacement lam_replacement_fst RepFun_closed
      transM[of _ ?Prod]
    by simp
  moreover
  have "?L = {z\<in>A . P(f(z))}"
    by(intro equalityI subsetI,auto)
  ultimately
  show " \<exists>y[M]. \<forall>z[M]. z \<in> y \<longleftrightarrow> z \<in> A \<and> P(f(z))"
    by (rule_tac x="?L" in rexI,simp_all)
qed

lemma separation_Ord: "separation(M,Ord)"
  unfolding Ord_def
  using separation_conj separation_Transset separation_all
    separation_comp separation_Transset lam_replacement_snd
  by auto

end \<comment> \<open>\<^locale>\<open>M_replacement\<close>\<close>

locale M_replacement_extra = M_replacement +
  assumes
    lam_replacement_minimum:"lam_replacement(M, \<lambda>p. minimum(fst(p),snd(p)))"
    and
    lam_replacement_RepFun_cons:"lam_replacement(M, \<lambda>p. RepFun(fst(p), \<lambda>x. {\<langle>snd(p),x\<rangle>}))"
    \<comment> \<open>This one is too particular: It is for \<^term>\<open>Sigfun\<close>.
        I would like greater modularity here.\<close>

begin
lemma lam_replacement_Sigfun:
  assumes "lam_replacement(M,f)" "\<forall>y[M]. M(f(y))"
  shows "lam_replacement(M, \<lambda>x. Sigfun(x,f))"
  using lam_replacement_Union lam_replacement_identity
    lam_replacement_sing[THEN lam_replacement_imp_strong_replacement]
    lam_replacement_hcomp[of _ Union] assms tag_singleton_closed
    lam_replacement_RepFun_cons[THEN [5] lam_replacement_hcomp2]
  unfolding Sigfun_def
  by (rule_tac lam_replacement_hcomp[of _ Union],simp_all)

subsection\<open>Particular instances\<close>

lemma surj_imp_inj_replacement2:
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. f -`` {y}))"
  using lam_replacement_imp_strong_replacement lam_replacement_Sigfun
    lam_replacement_vimage_sing_fun
  by simp

lemma lam_replacement_minimum_vimage:
  "M(f) \<Longrightarrow> M(r) \<Longrightarrow> lam_replacement(M, \<lambda>x. minimum(r, f -`` {x}))"
  using lam_replacement_minimum lam_replacement_vimage_sing_fun lam_replacement_constant
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemmas surj_imp_inj_replacement4 = lam_replacement_minimum_vimage[unfolded lam_replacement_def]

lemma lam_replacement_Pi: "M(y) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<Union>xa\<in>y. {\<langle>x, xa\<rangle>})"
  using lam_replacement_Union lam_replacement_identity lam_replacement_constant
    lam_replacement_RepFun_cons[THEN [5] lam_replacement_hcomp2] tag_singleton_closed
  by (rule_tac lam_replacement_hcomp[of _ Union],simp_all)

lemma Pi_replacement2: "M(y) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = (\<Union>xa\<in>y. {\<langle>x, xa\<rangle>}))"
  using lam_replacement_Pi[THEN lam_replacement_imp_strong_replacement, of y]
proof -
  assume "M(y)"
  then
  have "M(x) \<Longrightarrow> M(\<Union>xa\<in>y. {\<langle>x, xa\<rangle>})" for x
    using tag_singleton_closed
    by (rule_tac Union_closed RepFun_closed)
  with \<open>M(y)\<close>
  show ?thesis
    using lam_replacement_Pi[THEN lam_replacement_imp_strong_replacement, of y]
    by blast
qed

lemma if_then_Inj_replacement:
  shows "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then Inl(x) else Inr(x)\<rangle>)"
  using lam_replacement_if lam_replacement_Inl lam_replacement_Inr separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma lam_if_then_replacement:
  "M(b) \<Longrightarrow>
    M(a) \<Longrightarrow> M(f) \<Longrightarrow> strong_replacement(M, \<lambda>y ya. ya = \<langle>y, if y = a then b else f ` y\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma if_then_replacement:
  "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then f ` x else g ` x\<rangle>)"
  using lam_replacement_if lam_replacement_apply[of f] lam_replacement_apply[of g]
    separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma ifx_replacement:
  "M(f) \<Longrightarrow>
    M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> range(f) then converse(f) ` x else b\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma if_then_range_replacement2:
  "M(A) \<Longrightarrow> M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x = Inl(A) then C else x\<rangle>)"
  using lam_replacement_if lam_replacement_constant lam_replacement_identity
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma if_then_range_replacement:
  "M(u) \<Longrightarrow>
    M(f) \<Longrightarrow>
    strong_replacement
     (M,
      \<lambda>z y. y = \<langle>z, if z = u then f ` 0 else if z \<in> range(f) then f ` succ(converse(f) ` z) else z\<rangle>)"
  using lam_replacement_if separation_equal separation_in_constant
    lam_replacement_constant lam_replacement_identity
    lam_replacement_succ lam_replacement_apply
    lam_replacement_hcomp[of "\<lambda>x. converse(f)`x" "succ"]
    lam_replacement_hcomp[of "\<lambda>x. succ(converse(f)`x)" "\<lambda>x . f`x"]
  unfolding lam_replacement_def
  by simp

lemma Inl_replacement2:
  "M(A) \<Longrightarrow>
    strong_replacement(M, \<lambda>x y. y = \<langle>x, if fst(x) = A then Inl(snd(x)) else Inr(x)\<rangle>)"
  using lam_replacement_if separation_fst_equal
    lam_replacement_hcomp[of "snd" "Inl"]
    lam_replacement_Inl lam_replacement_Inr lam_replacement_snd
  unfolding lam_replacement_def
  by simp

lemma case_replacement1:
  "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(Inr, Inl, z)\<rangle>)"
  using lam_replacement_case lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement2:
  "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
    case_closed[of Inl "\<lambda>x. Inr(Inl(x))"]
    lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement4:
  "M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>z y. y = \<langle>z, case(\<lambda>w. Inl(f ` w), \<lambda>y. Inr(g ` y), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
    lam_replacement_Inl lam_replacement_Inr lam_replacement_apply
  unfolding lam_replacement_def
  by simp

lemma case_replacement5:
  "strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,z\<rangle>. case(\<lambda>y. Inl(\<langle>y, z\<rangle>), \<lambda>y. Inr(\<langle>y, z\<rangle>), x))(x)\<rangle>)"
  unfolding split_def case_def cond_def
  using lam_replacement_if separation_equal_fst2
    lam_replacement_snd lam_replacement_Inl lam_replacement_Inr
    lam_replacement_hcomp[OF
      lam_replacement_product[OF
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]]]
  unfolding lam_replacement_def
  by simp

end \<comment> \<open>\<^locale>\<open>M_replacement_extra\<close>\<close>

\<comment> \<open>To be used in the relativized treatment of Cohen posets\<close>
definition
  \<comment> \<open>"domain collect F"\<close>
  dC_F :: "i \<Rightarrow> i \<Rightarrow> i" where
  "dC_F(A,d) \<equiv> {p \<in> A. domain(p) = d }"

definition
  \<comment> \<open>"domain restrict SepReplace Y"\<close>
  drSR_Y :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "drSR_Y(B,D,A,x) \<equiv> {y . r\<in>A , restrict(r,B) = x \<and> y = domain(r) \<and> domain(r) \<in> D}"

lemma drSR_Y_equality: "drSR_Y(B,D,A,x) = { dr\<in>D . (\<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r)) }"
  unfolding drSR_Y_def by auto

context M_replacement_extra
begin

lemma separation_restrict_eq_dom_eq:"\<forall>x[M].separation(M, \<lambda>dr. \<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r))"
  if "M(A)" and "M(B)" for A B
  using that
    separation_eq[OF _
      lam_replacement_fst _
      lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_domain ]]
    separation_eq[OF _
      lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_restrict'] _
      lam_replacement_constant]
  by(clarify,rule_tac separation_bex[OF _ \<open>M(A)\<close>],rule_tac separation_conj,simp_all)


lemma separation_is_insnd_restrict_eq_dom : "separation(M, \<lambda>p. \<forall>x\<in>D. x \<in> snd(p) \<longleftrightarrow> (\<exists>r\<in>A. restrict(r, B) = fst(p) \<and> x = domain(r)))"
  if "M(B)" "M(D)" "M(A)" for A B D
  using that lam_replacement_fst lam_replacement_hcomp lam_replacement_snd separation_in
    separation_eq[OF _
      lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd] _
      lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_domain]]
    separation_eq separation_restrict_eq_dom_eq
    lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_restrict']
    lam_replacement_hcomp[OF lam_replacement_fst
      lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]]
  by(rule_tac separation_ball,rule_tac separation_iff',simp_all,
      rule_tac separation_bex[OF _ \<open>M(A)\<close>],rule_tac separation_conj,simp_all)

lemma lam_replacement_drSR_Y:
  assumes
    "M(B)" "M(D)" "M(A)"
  shows "lam_replacement(M, drSR_Y(B,D,A))"
  using lam_replacement_cong lam_replacement_Collect[OF \<open>M(D)\<close> separation_restrict_eq_dom_eq[of A B]]
    assms drSR_Y_equality separation_is_insnd_restrict_eq_dom separation_restrict_eq_dom_eq
  by simp

lemma drSR_Y_closed:
  assumes
    "M(B)" "M(D)" "M(A)" "M(f)"
  shows "M(drSR_Y(B,D,A,f))"
  using assms drSR_Y_equality lam_replacement_Collect[OF \<open>M(D)\<close> separation_restrict_eq_dom_eq[of A B]]
    assms drSR_Y_equality separation_is_insnd_restrict_eq_dom separation_restrict_eq_dom_eq
  by simp

lemma lam_if_then_apply_replacement: "M(f) \<Longrightarrow> M(v) \<Longrightarrow> M(u) \<Longrightarrow>
     lam_replacement(M, \<lambda>x. if f ` x = v then f ` u else f ` x)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma  lam_if_then_apply_replacement2: "M(f) \<Longrightarrow> M(m) \<Longrightarrow> M(y) \<Longrightarrow>
     lam_replacement(M, \<lambda>z . if f ` z = m then y else f ` z)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma lam_if_then_replacement2: "M(A) \<Longrightarrow> M(f) \<Longrightarrow>
     lam_replacement(M, \<lambda>x . if x \<in> A then f ` x else x)"
  using lam_replacement_if separation_in_constant lam_replacement_identity lam_replacement_apply
  by simp

lemma lam_if_then_replacement_apply: "M(G) \<Longrightarrow> lam_replacement(M, \<lambda>x. if M(x) then G ` x else 0)"
  using lam_replacement_if separation_in_constant lam_replacement_identity lam_replacement_apply
    lam_replacement_constant[of 0] separation_univ
  by simp

lemma lam_replacement_dC_F:
  assumes "M(A)"
  shows "lam_replacement(M, dC_F(A))"
proof -
  have "separation(M, \<lambda>p. \<forall>x\<in>A. x \<in> snd(p) \<longleftrightarrow> domain(x) = fst(p))" if "M(A)" for A
    using separation_ball separation_iff'
      lam_replacement_hcomp lam_replacement_fst lam_replacement_snd lam_replacement_domain
      separation_in separation_eq that
    by simp_all
  then
  show ?thesis
    unfolding dC_F_def
    using assms lam_replacement_Collect[of A "\<lambda> d x . domain(x) = d"]
      separation_eq[OF _ lam_replacement_domain _ lam_replacement_constant]
    by simp
qed

lemma dCF_closed:
  assumes "M(A)" "M(f)"
  shows "M(dC_F(A,f))"
  unfolding dC_F_def
  using assms lam_replacement_Collect[of A "\<lambda> d x . domain(x) = d"]
    separation_eq[OF _ lam_replacement_domain _ lam_replacement_constant]
  by simp

lemma lam_replacement_min: "M(f) \<Longrightarrow> M(r) \<Longrightarrow> lam_replacement(M, \<lambda>x . minimum(r, f -`` {x}))"
  using lam_replacement_hcomp2[OF lam_replacement_constant[of r] lam_replacement_vimage_sing_fun]
    lam_replacement_minimum
  by simp

lemma lam_replacement_Collect_ball_Pair:
  assumes "separation(M, \<lambda>p. \<forall>x\<in>G. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> Q))" "M(G)" "M(Q)"
  shows "lam_replacement(M, \<lambda>x . {a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})"
proof -
  have 1:"\<forall>x[M]. separation(M, \<lambda>a .  \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q)" if "M(Q)" for Q
    using separation_in lam_replacement_hcomp2[OF _ _ _ _ lam_replacement_Pair]
      lam_replacement_constant separation_ball
      lam_replacement_hcomp lam_replacement_fst lam_replacement_snd that
    by simp
  then
  show ?thesis
    using assms lam_replacement_Collect
    by simp_all
qed

lemma surj_imp_inj_replacement3:
  "(\<And>x. M(x) \<Longrightarrow> separation(M, \<lambda>y. \<forall>s\<in>x. \<langle>s, y\<rangle> \<in> Q)) \<Longrightarrow> M(G) \<Longrightarrow> M(Q) \<Longrightarrow> M(x) \<Longrightarrow>
  strong_replacement(M, \<lambda>y z. y \<in> {a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q} \<and> z = {\<langle>x, y\<rangle>})"
  using lam_replacement_imp_strong_replacement
  using lam_replacement_sing_const_id[THEN lam_replacement_imp_strong_replacement, of x]
  unfolding strong_replacement_def
  by (simp, safe, drule_tac x="A \<inter> {a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q}" in rspec,
      simp, erule_tac rexE, rule_tac x=Y in rexI) auto

lemmas replacements = Pair_diff_replacement id_replacement tag_replacement
  pospend_replacement prepend_replacement
  Inl_replacement1  diff_Pair_replacement
  swap_replacement tag_union_replacement csquare_lam_replacement
  assoc_replacement prod_fun_replacement
  cardinal_lib_assms4  domain_replacement
  apply_replacement
  un_Pair_replacement restrict_strong_replacement diff_replacement
  if_then_Inj_replacement lam_if_then_replacement if_then_replacement
  ifx_replacement if_then_range_replacement2 if_then_range_replacement
  Inl_replacement2
  case_replacement1 case_replacement2 case_replacement4 case_replacement5

end \<comment> \<open>\<^locale>\<open>M_replacement_extra\<close>\<close>

end