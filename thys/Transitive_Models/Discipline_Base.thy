theory Discipline_Base
  imports
    "ZF-Constructible.Rank"
    M_Basic_No_Repl
    Relativization
    ZF_Miscellanea

begin

hide_const (open) Order.pred
declare [[syntax_ambiguity_warning = false]]

subsection\<open>Discipline of relativization of basic concepts\<close>

definition
  is_singleton :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_singleton(A,x,z) \<equiv> \<exists>c[A]. empty(A,c) \<and> is_cons(A,x,c,z)"

lemma (in M_trivial) singleton_abs[simp] :
  "\<lbrakk> M(x) ; M(s) \<rbrakk> \<Longrightarrow> is_singleton(M,x,s) \<longleftrightarrow> s = {x}"
  unfolding is_singleton_def using nonempty by simp

synthesize "singleton" from_definition "is_singleton"
notation singleton_fm (\<open>\<cdot>{_} is _\<cdot>\<close>)

lemmas (in M_trivial) singleton_closed = singleton_in_MI

lemma (in M_trivial) Upair_closed[simp]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> M(Upair(a,b))"
  using Upair_eq_cons by simp


text\<open>The following named theorems gather instances of transitivity
that arise from closure theorems\<close>
named_theorems trans_closed

definition
  is_hcomp :: "[i\<Rightarrow>o,i\<Rightarrow>i\<Rightarrow>o,i\<Rightarrow>i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_hcomp(M,is_f,is_g,a,w) \<equiv> \<exists>z[M]. is_g(a,z) \<and> is_f(z,w)"

lemma (in M_trivial) is_hcomp_abs:
  assumes
    is_f_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_f(a,z) \<longleftrightarrow> z = f(a)" and
    is_g_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_g(a,z) \<longleftrightarrow> z = g(a)" and
    g_closed:"\<And>a. M(a) \<Longrightarrow> M(g(a))"
    "M(a)" "M(w)"
  shows
    "is_hcomp(M,is_f,is_g,a,w) \<longleftrightarrow> w = f(g(a))"
  unfolding is_hcomp_def using assms by simp

definition
  hcomp_fm :: "[i\<Rightarrow>i\<Rightarrow>i,i\<Rightarrow>i\<Rightarrow>i,i,i] \<Rightarrow> i" where
  "hcomp_fm(pf,pg,a,w) \<equiv> Exists(And(pg(succ(a),0),pf(0,succ(w))))"

lemma sats_hcomp_fm:
  assumes
    f_iff_sats:"\<And>a b z. a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> z\<in>M \<Longrightarrow>
                 is_f(nth(a,Cons(z,env)),nth(b,Cons(z,env))) \<longleftrightarrow> sats(M,pf(a,b),Cons(z,env))"
    and
    g_iff_sats:"\<And>a b z. a\<in>nat \<Longrightarrow> b\<in>nat \<Longrightarrow> z\<in>M \<Longrightarrow>
                is_g(nth(a,Cons(z,env)),nth(b,Cons(z,env))) \<longleftrightarrow> sats(M,pg(a,b),Cons(z,env))"
    and
    "a\<in>nat" "w\<in>nat" "env\<in>list(M)"
  shows
    "sats(M,hcomp_fm(pf,pg,a,w),env) \<longleftrightarrow> is_hcomp(##M,is_f,is_g,nth(a,env),nth(w,env))"
proof -
  have "sats(M, pf(0, succ(w)), Cons(x, env)) \<longleftrightarrow> is_f(x,nth(w,env))" if "x\<in>M" "w\<in>nat" for x w
    using f_iff_sats[of 0 "succ(w)" x] that by simp
  moreover
  have "sats(M, pg(succ(a), 0), Cons(x, env)) \<longleftrightarrow> is_g(nth(a,env),x)" if "x\<in>M" "a\<in>nat" for x a
    using g_iff_sats[of "succ(a)" 0 x] that by simp
  ultimately
  show ?thesis unfolding hcomp_fm_def is_hcomp_def using assms by simp
qed


definition
  hcomp_r :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "hcomp_r(M,is_f,is_g,a,w) \<equiv> \<exists>z[M]. is_g(M,a,z) \<and> is_f(M,z,w)"

definition
  is_hcomp2_2 :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w) \<equiv> \<exists>g1ab[M]. \<exists>g2ab[M].
       is_g1(M,a,b,g1ab) \<and> is_g2(M,a,b,g2ab) \<and> is_f(M,g1ab,g2ab,w)"

lemma (in M_trivial) hcomp_abs:
  assumes
    is_f_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_f(M,a,z) \<longleftrightarrow> z = f(a)" and
    is_g_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_g(M,a,z) \<longleftrightarrow> z = g(a)" and
    g_closed:"\<And>a. M(a) \<Longrightarrow> M(g(a))"
    "M(a)" "M(w)"
  shows
    "hcomp_r(M,is_f,is_g,a,w) \<longleftrightarrow> w = f(g(a))"
  unfolding hcomp_r_def using assms by simp

lemma hcomp_uniqueness:
  assumes
    uniq_is_f:
    "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_f(M, r, d) \<Longrightarrow> is_f(M, r, d') \<Longrightarrow>
               d = d'"
    and
    uniq_is_g:
    "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g(M, r, d) \<Longrightarrow> is_g(M, r, d') \<Longrightarrow>
               d = d'"
    and
    "M(a)" "M(w)" "M(w')"
    "hcomp_r(M,is_f,is_g,a,w)"
    "hcomp_r(M,is_f,is_g,a,w')"
  shows
    "w=w'"
proof -
  from assms
  obtain z z' where "is_g(M, a, z)" "is_g(M, a, z')"
    "is_f(M,z,w)" "is_f(M,z',w')"
    "M(z)" "M(z')"
    unfolding hcomp_r_def by blast
  moreover from this and uniq_is_g and \<open>M(a)\<close>
  have "z=z'" by blast
  moreover note uniq_is_f and \<open>M(w)\<close> \<open>M(w')\<close>
  ultimately
  show ?thesis by blast
qed

lemma hcomp_witness:
  assumes
    wit_is_f: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_f(M,r,d)" and
    wit_is_g: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_g(M,r,d)" and
    "M(a)"
  shows
    "\<exists>w[M]. hcomp_r(M,is_f,is_g,a,w)"
proof -
  from \<open>M(a)\<close> and wit_is_g
  obtain z where "is_g(M,a,z)" "M(z)" by blast
  moreover from this and wit_is_f
  obtain w where "is_f(M,z,w)" "M(w)" by blast
  ultimately
  show ?thesis
    using assms unfolding hcomp_r_def by auto
qed

\<comment> \<open>In the next lemma, the absoluteness hypotheses on \<^term>\<open>g1\<close> and \<^term>\<open>g2\<close> can be restricted
to the actual parameters.\<close>
lemma (in M_trivial) hcomp2_2_abs:
  assumes
    is_f_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_f(M,r1,r2,z) \<longleftrightarrow> z = f(r1,r2)" and
    is_g1_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_g1(M,r1,r2,z) \<longleftrightarrow> z = g1(r1,r2)" and
    is_g2_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_g2(M,r1,r2,z) \<longleftrightarrow> z = g2(r1,r2)" and
    types: "M(a)" "M(b)" "M(w)" "M(g1(a,b))" "M(g2(a,b))"
  shows
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w) \<longleftrightarrow> w = f(g1(a,b),g2(a,b))"
  unfolding is_hcomp2_2_def
  using assms
  by simp

lemma hcomp2_2_uniqueness:
  assumes
    uniq_is_f:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow>
        is_f(M, r1, r2 , d) \<Longrightarrow> is_f(M, r1, r2, d') \<Longrightarrow>  d = d'"
    and
    uniq_is_g1:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2)\<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g1(M, r1,r2, d) \<Longrightarrow> is_g1(M, r1,r2, d') \<Longrightarrow>
               d = d'"
    and
    uniq_is_g2:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2)\<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g2(M, r1,r2, d) \<Longrightarrow> is_g2(M, r1,r2, d') \<Longrightarrow>
               d = d'"
    and
    "M(a)" "M(b)" "M(w)" "M(w')"
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w)"
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w')"
  shows
    "w=w'"
proof -
  from assms
  obtain z z' y y' where "is_g1(M, a,b, z)" "is_g1(M, a,b, z')"
    "is_g2(M, a,b, y)" "is_g2(M, a,b, y')"
    "is_f(M,z,y,w)" "is_f(M,z',y',w')"
    "M(z)" "M(z')" "M(y)" "M(y')"
    unfolding is_hcomp2_2_def by force
  moreover from this and uniq_is_g1 uniq_is_g2 and \<open>M(a)\<close> \<open>M(b)\<close>
  have "z=z'" "y=y'" by blast+
  moreover note uniq_is_f and \<open>M(w)\<close> \<open>M(w')\<close>
  ultimately
  show ?thesis by blast
qed

lemma hcomp2_2_witness:
  assumes
    wit_is_f: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_f(M,r1,r2,d)" and
    wit_is_g1: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_g1(M,r1,r2,d)" and
    wit_is_g2: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_g2(M,r1,r2,d)" and
    "M(a)" "M(b)"
  shows
    "\<exists>w[M]. is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w)"
proof -
  from \<open>M(a)\<close> \<open>M(b)\<close> and wit_is_g1
  obtain g1a where "is_g1(M,a,b,g1a)" "M(g1a)" by blast
  moreover from \<open>M(a)\<close> \<open>M(b)\<close> and wit_is_g2
  obtain g2a where "is_g2(M,a,b,g2a)" "M(g2a)" by blast
  moreover from calculation and wit_is_f
  obtain w where "is_f(M,g1a,g2a,w)" "M(w)" by blast
  ultimately
  show ?thesis
    using assms unfolding is_hcomp2_2_def by auto
qed

lemma (in M_trivial) extensionality_trans:
  assumes
    "M(d) \<and> (\<forall>x[M]. x\<in>d  \<longleftrightarrow> P(x))"
    "M(d') \<and> (\<forall>x[M]. x\<in>d' \<longleftrightarrow> P(x))"
  shows
    "d=d'"
proof -
  from assms
  have "\<forall>x. x\<in>d \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d] by auto
  moreover from assms
  have  "\<forall>x. x\<in>d' \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d'] by auto
  ultimately
  show ?thesis by auto
qed

definition
  lt_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "lt_rel(M,a,b) \<equiv> a\<in>b \<and> ordinal(M,b)"

lemma (in M_trans) lt_abs[absolut]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> lt_rel(M,a,b) \<longleftrightarrow> a<b"
  unfolding lt_rel_def lt_def by auto

definition
  le_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "le_rel(M,a,b) \<equiv> \<exists>sb[M]. successor(M,b,sb) \<and> lt_rel(M,a,sb)"

lemma (in M_trivial) le_abs[absolut]: "M(a) \<Longrightarrow> M(b) \<Longrightarrow> le_rel(M,a,b) \<longleftrightarrow> a\<le>b"
  unfolding le_rel_def by (simp add:absolut)

subsection\<open>Discipline for \<^term>\<open>Pow\<close>\<close>

definition
  is_Pow :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_Pow(M,A,z) \<equiv> M(z) \<and> (\<forall>x[M]. x \<in> z \<longleftrightarrow> subset(M,x,A))"

definition
  Pow_rel :: "[i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>Pow\<^bsup>_\<^esup>'(_')\<close>) where
  "Pow_rel(M,r) \<equiv> THE d. is_Pow(M,r,d)"

abbreviation
  Pow_r_set ::  "[i,i] \<Rightarrow> i" (\<open>Pow\<^bsup>_\<^esup>'(_')\<close>) where
  "Pow_r_set(M) \<equiv> Pow_rel(##M)"

context M_basic_no_repl
begin

lemma is_Pow_uniqueness:
  assumes
    "M(r)"
    "is_Pow(M,r,d)" "is_Pow(M,r,d')"
  shows
    "d=d'"
  using assms extensionality_trans
  unfolding is_Pow_def
  by simp

lemma is_Pow_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_Pow(M,r,d)"
  using power_ax unfolding power_ax_def powerset_def is_Pow_def
  by simp \<comment> \<open>We have to do this by hand, using axioms\<close>

lemma is_Pow_closed : "\<lbrakk> M(r);is_Pow(M,r,d) \<rbrakk> \<Longrightarrow> M(d)"
  unfolding is_Pow_def by simp

lemma Pow_rel_closed[intro,simp]: "M(r) \<Longrightarrow> M(Pow_rel(M,r))"
  unfolding Pow_rel_def
  using is_Pow_closed theI[OF ex1I[of "\<lambda>d. is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    is_Pow_witness
  by fastforce

lemmas trans_Pow_rel_closed[trans_closed] = transM[OF _ Pow_rel_closed]

text\<open>The proof of \<^term>\<open>f_rel_iff\<close> lemma is schematic and it can reused by copy-paste
     replacing appropriately.\<close>

lemma Pow_rel_iff:
  assumes "M(r)"  "M(d)"
  shows "is_Pow(M,r,d) \<longleftrightarrow> d = Pow_rel(M,r)"
proof (intro iffI)
  assume "d = Pow_rel(M,r)"
  with assms
  show "is_Pow(M, r, d)"
    using is_Pow_uniqueness[of r] is_Pow_witness
      theI[OF ex1I[of "\<lambda>d. is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    unfolding Pow_rel_def
    by auto
next
  assume "is_Pow(M, r, d)"
  with assms
  show "d = Pow_rel(M,r)"
    using is_Pow_uniqueness unfolding Pow_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed

text\<open>The next "def\_" result really corresponds to @{thm Pow_iff}\<close>
lemma def_Pow_rel: "M(A) \<Longrightarrow> M(r) \<Longrightarrow> A\<in>Pow_rel(M,r) \<longleftrightarrow> A \<subseteq> r"
  using Pow_rel_iff[OF _ Pow_rel_closed, of r r]
  unfolding is_Pow_def by simp

lemma Pow_rel_char: "M(r) \<Longrightarrow> Pow_rel(M,r) = {A\<in>Pow(r). M(A)}"
proof -
  assume "M(r)"
  moreover from this
  have "x \<in> Pow_rel(M,r) \<Longrightarrow> x\<subseteq>r" "M(x) \<Longrightarrow> x \<subseteq> r \<Longrightarrow> x \<in> Pow_rel(M,r)" for x
    using def_Pow_rel by (auto intro!:trans_Pow_rel_closed)
  ultimately
  show ?thesis
    using trans_Pow_rel_closed by blast
qed

lemma mem_Pow_rel_abs: "M(a) \<Longrightarrow> M(r) \<Longrightarrow> a \<in> Pow_rel(M,r) \<longleftrightarrow> a \<in> Pow(r)"
  using Pow_rel_char by simp

end \<comment> \<open>\<^locale>\<open>M_basic_no_repl\<close>\<close>

subsection\<open>Discipline for \<^term>\<open>PiP\<close>\<close>

definition
  PiP_rel:: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "PiP_rel(M,A,f) \<equiv> \<exists>df[M]. is_domain(M,f,df) \<and> subset(M,A,df) \<and>
                             is_function(M,f)"

context M_basic
begin

lemma def_PiP_rel:
  assumes
    "M(A)" "M(f)"
  shows
    "PiP_rel(M,A,f) \<longleftrightarrow> A \<subseteq> domain(f) \<and> function(f)"
  using assms unfolding PiP_rel_def by simp

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

definition
  Sigfun :: "[i,i\<Rightarrow>i]\<Rightarrow>i"  where
  "Sigfun(x,B) \<equiv> \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}"

lemma SigFun_char : "Sigfun(x,B) = {x}\<times>B(x)"
  unfolding Sigfun_def by auto

lemma Sigma_Sigfun: "Sigma(A,B) = \<Union> {Sigfun(x,B) . x\<in>A}"
  unfolding Sigma_def Sigfun_def ..

definition \<comment> \<open>Note that $B$ below is a higher order argument\<close>
  is_Sigfun :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Sigfun(M,x,B,Sd) \<equiv> M(Sd) \<and> (\<exists>RB[M]. is_Replace(M,B(x),\<lambda>y z. z={\<langle>x,y\<rangle>},RB)
                         \<and> big_union(M,RB,Sd))"

context M_trivial
begin

lemma is_Sigfun_abs:
  assumes
    "strong_replacement(M,\<lambda>y z. z={\<langle>x,y\<rangle>})"
    "M(x)" "M(B(x))" "M(Sd)"
  shows
    "is_Sigfun(M,x,B,Sd) \<longleftrightarrow> Sd = Sigfun(x,B)"
proof -
  have "\<Union>{z . y \<in> B(x), z = {\<langle>x, y\<rangle>}} = (\<Union>y\<in>B(x). {\<langle>x, y\<rangle>})" by auto
  then
  show ?thesis
    using assms transM[OF _ \<open>M(B(x))\<close>] Replace_abs
    unfolding is_Sigfun_def Sigfun_def by auto
qed

lemma Sigfun_closed:
  assumes
    "strong_replacement(M, \<lambda>y z. y \<in> B(x) \<and> z = {\<langle>x, y\<rangle>})"
    "M(x)" "M(B(x))"
  shows
    "M(Sigfun(x,B))"
  using assms transM[OF _ \<open>M(B(x))\<close>] RepFun_closed2
  unfolding Sigfun_def by simp

lemmas trans_Sigfun_closed[trans_closed] = transM[OF _ Sigfun_closed]

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

definition
  is_Sigma :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Sigma(M,A,B,S) \<equiv> M(S) \<and> (\<exists>RSf[M].
      is_Replace(M,A,\<lambda>x z. z=Sigfun(x,B),RSf) \<and> big_union(M,RSf,S))"

locale M_Pi = M_basic +
  assumes
    Pi_separation: "M(A) \<Longrightarrow> separation(M, PiP_rel(M,A))"
    and
    Pi_replacement:
    "M(x) \<Longrightarrow> M(y) \<Longrightarrow>
      strong_replacement(M, \<lambda>ya z. ya \<in> y \<and> z = {\<langle>x, ya\<rangle>})"
    "M(y) \<Longrightarrow>
      strong_replacement(M, \<lambda>x z. z = (\<Union>xa\<in>y. {\<langle>x, xa\<rangle>}))"

locale M_Pi_assumptions = M_Pi +
  fixes A B
  assumes
    Pi_assumptions:
    "M(A)"
    "\<And>x. x\<in>A \<Longrightarrow>  M(B(x))"
    "\<forall>x\<in>A. strong_replacement(M, \<lambda>y z. y \<in> B(x) \<and> z = {\<langle>x, y\<rangle>})"
    "strong_replacement(M,\<lambda>x z. z=Sigfun(x,B))"
begin

lemma Sigma_abs[simp]:
  assumes
    "M(S)"
  shows
    "is_Sigma(M,A,B,S) \<longleftrightarrow> S = Sigma(A,B)"
proof -
  have "\<Union>{z . x \<in> A, z = Sigfun(x, B)} = (\<Union>x\<in>A. Sigfun(x, B))"
    by auto
  with assms
  show ?thesis
    using Replace_abs[of A _ "\<lambda>x z. z=Sigfun(x,B)"]
      Sigfun_closed Sigma_Sigfun transM[of _ A]
      Pi_assumptions is_Sigfun_abs
    unfolding is_Sigma_def by simp
qed

lemma Sigma_closed[intro,simp]: "M(Sigma(A,B))"
proof -
  have "(\<Union>x\<in>A. Sigfun(x, B)) = \<Union>{z . x \<in> A, z = Sigfun(x, B)}"
    by auto
  then
  show ?thesis
    using Sigma_Sigfun[of A B] transM[of _ A] Sigfun_closed Pi_assumptions
    by simp
qed

lemmas trans_Sigma_closed[trans_closed] = transM[OF _ Sigma_closed]

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions\<close>\<close>

subsection\<open>Discipline for \<^term>\<open>Pi\<close>\<close>

definition \<comment> \<open>completely relational\<close>
  is_Pi :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Pi(M,A,B,I) \<equiv> M(I) \<and> (\<exists>S[M]. \<exists>PS[M]. is_Sigma(M,A,B,S) \<and>
       is_Pow(M,S,PS) \<and>
       is_Collect(M,PS,PiP_rel(M,A),I))"

definition
  Pi_rel :: "[i\<Rightarrow>o,i,i\<Rightarrow>i] \<Rightarrow> i"  (\<open>Pi\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Pi_rel(M,A,B) \<equiv> THE d. is_Pi(M,A,B,d)"

abbreviation
  Pi_r_set ::  "[i,i,i\<Rightarrow>i] \<Rightarrow> i" (\<open>Pi\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Pi_r_set(M,A,B) \<equiv> Pi_rel(##M,A,B)"

context M_basic
begin

lemmas Pow_rel_iff = mbnr.Pow_rel_iff
lemmas Pow_rel_char = mbnr.Pow_rel_char
lemmas mem_Pow_rel_abs = mbnr.mem_Pow_rel_abs
lemmas Pow_rel_closed = mbnr.Pow_rel_closed
lemmas def_Pow_rel = mbnr.def_Pow_rel
lemmas trans_Pow_rel_closed = mbnr.trans_Pow_rel_closed

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

context M_Pi_assumptions
begin

lemma is_Pi_uniqueness:
  assumes
    "is_Pi(M,A,B,d)" "is_Pi(M,A,B,d')"
  shows
    "d=d'"
  using assms Pi_assumptions extensionality_trans
    Pow_rel_iff
  unfolding is_Pi_def by simp


lemma is_Pi_witness: "\<exists>d[M]. is_Pi(M,A,B,d)"
  using Pow_rel_iff Pi_separation Pi_assumptions
  unfolding is_Pi_def by simp

lemma is_Pi_closed : "is_Pi(M,A,B,d) \<Longrightarrow> M(d)"
  unfolding is_Pi_def by simp

lemma Pi_rel_closed[intro,simp]:  "M(Pi_rel(M,A,B))"
proof -
  have "is_Pi(M, A, B, THE xa. is_Pi(M, A, B, xa))"
    using Pi_assumptions
      theI[OF ex1I[of "is_Pi(M,A,B)"], OF _ is_Pi_uniqueness]
      is_Pi_witness is_Pi_closed
    by auto
  then show ?thesis
    using is_Pi_closed
    unfolding Pi_rel_def
    by simp
qed

\<comment> \<open>From this point on, the higher order variable \<^term>\<open>B\<close> must be
explicitly instantiated, and proof methods are slower\<close>

lemmas trans_Pi_rel_closed[trans_closed] = transM[OF _ Pi_rel_closed]

lemma Pi_rel_iff:
  assumes "M(d)"
  shows "is_Pi(M,A,B,d) \<longleftrightarrow> d = Pi_rel(M,A,B)"
proof (intro iffI)
  assume "d = Pi_rel(M,A,B)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_Pi(M,A,B,e)"
    using is_Pi_witness by blast
  ultimately
  show "is_Pi(M, A, B, d)"
    using is_Pi_uniqueness is_Pi_witness is_Pi_closed
      theI[OF ex1I[of "is_Pi(M,A,B)"], OF _ is_Pi_uniqueness, of e]
    unfolding Pi_rel_def
    by simp
next
  assume "is_Pi(M, A, B, d)"
  with assms
  show "d = Pi_rel(M,A,B)"
    using is_Pi_uniqueness is_Pi_closed unfolding Pi_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_Pi_rel:
  "Pi_rel(M,A,B) = {f\<in>Pow_rel(M,Sigma(A,B)). A\<subseteq>domain(f) \<and> function(f)}"
proof -
  have "Pi_rel(M,A, B) \<subseteq> Pow_rel(M,Sigma(A,B))"
    using Pi_assumptions Pi_rel_iff[of "Pi_rel(M,A,B)"] Pow_rel_iff
    unfolding is_Pi_def by auto
  moreover
  have "f \<in> Pi_rel(M,A, B) \<Longrightarrow> A\<subseteq>domain(f) \<and> function(f)" for f
    using Pi_assumptions Pi_rel_iff[of "Pi_rel(M,A,B)"]
      def_PiP_rel[of A f] trans_closed Pow_rel_iff
    unfolding is_Pi_def by simp
  moreover
  have "f \<in> Pow_rel(M,Sigma(A,B)) \<Longrightarrow> A\<subseteq>domain(f) \<and> function(f) \<Longrightarrow> f \<in> Pi_rel(M,A, B)" for f
    using Pi_rel_iff[of "Pi_rel(M,A,B)"] Pi_assumptions
      def_PiP_rel[of A f] trans_closed Pow_rel_iff
    unfolding is_Pi_def by simp
  ultimately
  show ?thesis by force
qed

lemma Pi_rel_char: "Pi_rel(M,A,B) = {f\<in>Pi(A,B). M(f)}"
  using Pi_assumptions def_Pi_rel Pow_rel_char[OF Sigma_closed] unfolding Pi_def
  by fastforce

lemma mem_Pi_rel_abs:
  assumes "M(f)"
  shows  "f \<in> Pi_rel(M,A,B) \<longleftrightarrow> f \<in> Pi(A,B)"
  using assms Pi_rel_char by simp

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions\<close>\<close>

text\<open>The next locale (and similar ones below) are used to
show the relationship between versions of simple (i.e.
$\Sigma_1^{\mathit{ZF}}$, $\Pi_1^{\mathit{ZF}}$) concepts in two
different transitive models.\<close>
locale M_N_Pi_assumptions = M:M_Pi_assumptions + N:M_Pi_assumptions N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin

lemma Pi_rel_transfer: "Pi\<^bsup>M\<^esup>(A,B) \<subseteq> Pi\<^bsup>N\<^esup>(A,B)"
  using  M.Pi_rel_char N.Pi_rel_char M_imp_N by auto

end \<comment> \<open>\<^locale>\<open>M_N_Pi_assumptions\<close>\<close>


locale M_Pi_assumptions_0 = M_Pi_assumptions _ 0
begin

text\<open>This is used in the proof of \<^term>\<open>AC_Pi_rel\<close>\<close>
lemma Pi_rel_empty1[simp]: "Pi\<^bsup>M\<^esup>(0,B) = {0}"
  using Pi_assumptions Pow_rel_char
  by (unfold def_Pi_rel function_def) (auto)

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions_0\<close>\<close>

context M_Pi_assumptions
begin

subsection\<open>Auxiliary ported results on \<^term>\<open>Pi_rel\<close>, now unused\<close>
lemma Pi_rel_iff':
  assumes types:"M(f)"
  shows
    "f \<in> Pi_rel(M,A,B) \<longleftrightarrow> function(f) \<and> f \<subseteq> Sigma(A,B) \<and> A \<subseteq> domain(f)"
  using assms Pow_rel_char
  by (simp add:def_Pi_rel, blast)


lemma lam_type_M:
  assumes "M(A)" "\<And>x. x\<in>A \<Longrightarrow>  M(B(x))"
    "\<And>x. x \<in> A \<Longrightarrow> b(x)\<in>B(x)" "strong_replacement(M,\<lambda>x y. y=\<langle>x, b(x)\<rangle>) "
  shows "(\<lambda>x\<in>A. b(x)) \<in> Pi_rel(M,A,B)"
proof (auto simp add: lam_def def_Pi_rel function_def)
  from assms
  have "M({\<langle>x, b(x)\<rangle> . x \<in> A})"
    using Pi_assumptions transM[OF _ \<open>M(A)\<close>]
    by (rule_tac RepFun_closed, auto intro!:transM[OF _ \<open>\<And>x. x\<in>A \<Longrightarrow>  M(B(x))\<close>])
  with assms
  show "{\<langle>x, b(x)\<rangle> . x \<in> A} \<in> Pow\<^bsup>M\<^esup>(Sigma(A, B))"
    using Pow_rel_char by auto
qed

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions\<close>\<close>

locale M_Pi_assumptions2 = M_Pi_assumptions +
  PiC: M_Pi_assumptions _ _ C for C
begin

lemma Pi_rel_type:
  assumes "f \<in> Pi\<^bsup>M\<^esup>(A,C)" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B(x)"
    and types: "M(f)"
  shows "f \<in> Pi\<^bsup>M\<^esup>(A,B)"
  using assms Pi_assumptions
  by (simp only: Pi_rel_iff' PiC.Pi_rel_iff')
    (blast dest: function_apply_equality)

lemma Pi_rel_weaken_type:
  assumes "f \<in> Pi\<^bsup>M\<^esup>(A,B)" "\<And>x. x \<in> A \<Longrightarrow> B(x) \<subseteq> C(x)"
    and types: "M(f)"
  shows "f \<in> Pi\<^bsup>M\<^esup>(A,C)"
  using assms Pi_assumptions
  by (simp only: Pi_rel_iff' PiC.Pi_rel_iff')
    (blast intro: Pi_rel_type  dest: apply_type)

end \<comment> \<open>\<^locale>\<open>M_Pi_assumptions2\<close>\<close>

end