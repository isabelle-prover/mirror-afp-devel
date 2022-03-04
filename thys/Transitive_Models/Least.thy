section\<open>The binder \<^term>\<open>Least\<close>\<close>
theory Least
  imports
    "Internalizations"

begin

text\<open>We have some basic results on the least ordinal satisfying
a predicate.\<close>

lemma Least_Ord: "(\<mu> \<alpha>. R(\<alpha>)) = (\<mu> \<alpha>. Ord(\<alpha>) \<and> R(\<alpha>))"
  unfolding Least_def by (simp add:lt_Ord)

lemma Ord_Least_cong:
  assumes "\<And>y. Ord(y) \<Longrightarrow> R(y) \<longleftrightarrow> Q(y)"
  shows "(\<mu> \<alpha>. R(\<alpha>)) = (\<mu> \<alpha>. Q(\<alpha>))"
proof -
  from assms
  have "(\<mu> \<alpha>. Ord(\<alpha>) \<and> R(\<alpha>)) = (\<mu> \<alpha>. Ord(\<alpha>) \<and> Q(\<alpha>))"
    by simp
  then
  show ?thesis using Least_Ord by simp
qed

definition
  least :: "[i\<Rightarrow>o,i\<Rightarrow>o,i] \<Rightarrow> o" where
  "least(M,Q,i) \<equiv> ordinal(M,i) \<and> (
         (empty(M,i) \<and> (\<forall>b[M]. ordinal(M,b) \<longrightarrow> \<not>Q(b)))
       \<or> (Q(i) \<and> (\<forall>b[M]. ordinal(M,b) \<and> b\<in>i\<longrightarrow> \<not>Q(b))))"

definition
  least_fm :: "[i,i] \<Rightarrow> i" where
  "least_fm(q,i) \<equiv> And(ordinal_fm(i),
   Or(And(empty_fm(i),Forall(Implies(ordinal_fm(0),Neg(q)))),
      And(Exists(And(q,Equal(0,succ(i)))),
          Forall(Implies(And(ordinal_fm(0),Member(0,succ(i))),Neg(q))))))"

lemma least_fm_type[TC] :"i \<in> nat \<Longrightarrow> q\<in>formula \<Longrightarrow> least_fm(q,i) \<in> formula"
  unfolding least_fm_def
  by simp

(* Refactorize Formula and Relative to include the following three lemmas *)
lemmas basic_fm_simps = sats_subset_fm' sats_transset_fm' sats_ordinal_fm'

lemma sats_least_fm :
  assumes p_iff_sats:
    "\<And>a. a \<in> A \<Longrightarrow> P(a) \<longleftrightarrow> sats(A, p, Cons(a, env))"
  shows
    "\<lbrakk>y \<in> nat; env \<in> list(A) ; 0\<in>A\<rbrakk>
    \<Longrightarrow> sats(A, least_fm(p,y), env) \<longleftrightarrow>
        least(##A, P, nth(y,env))"
  using nth_closed p_iff_sats unfolding least_def least_fm_def
  by (simp add:basic_fm_simps)

lemma least_iff_sats [iff_sats]:
  assumes is_Q_iff_sats:
    "\<And>a. a \<in> A \<Longrightarrow> is_Q(a) \<longleftrightarrow> sats(A, q, Cons(a,env))"
  shows
    "\<lbrakk>nth(j,env) = y; j \<in> nat; env \<in> list(A); 0\<in>A\<rbrakk>
   \<Longrightarrow> least(##A, is_Q, y) \<longleftrightarrow> sats(A, least_fm(q,j), env)"
  using sats_least_fm [OF is_Q_iff_sats, of j , symmetric]
  by simp

lemma least_conj: "a\<in>M \<Longrightarrow> least(##M, \<lambda>x. x\<in>M \<and> Q(x),a) \<longleftrightarrow> least(##M,Q,a)"
  unfolding least_def by simp


context M_trivial
begin

subsection\<open>Uniqueness, absoluteness and closure under \<^term>\<open>Least\<close>\<close>

lemma unique_least:
  assumes "M(a)" "M(b)" "least(M,Q,a)" "least(M,Q,b)"
  shows "a=b"
proof -
  from assms
  have "Ord(a)" "Ord(b)"
    unfolding least_def
    by simp_all
  then
  consider (le) "a\<in>b" | "a=b" | (ge) "b\<in>a"
    using Ord_linear[OF \<open>Ord(a)\<close> \<open>Ord(b)\<close>] by auto
  then
  show ?thesis
  proof(cases)
    case le
    then show ?thesis using assms unfolding least_def by auto
  next
    case ge
    then show ?thesis using assms unfolding least_def by auto
  qed
qed

lemma least_abs:
  assumes "\<And>x. Q(x) \<Longrightarrow> Ord(x) \<Longrightarrow> \<exists>y[M]. Q(y) \<and> Ord(y)" "M(a)"
  shows "least(M,Q,a) \<longleftrightarrow> a = (\<mu> x. Q(x))"
  unfolding least_def
proof (cases "\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)"; intro iffI; simp add:assms)
  case True
  with assms
  have "\<not> (\<exists>i. Ord(i) \<and> Q(i)) " by blast
  then
  show "0 =(\<mu> x. Q(x))" using Least_0 by simp
  then
  show "ordinal(M, \<mu> x. Q(x)) \<and> (empty(M, Least(Q)) \<or> Q(Least(Q)))"
    by simp
next
  assume "\<exists>b[M]. Ord(b) \<and> Q(b)"
  then
  obtain i where "M(i)" "Ord(i)" "Q(i)" by blast
  assume "a = (\<mu> x. Q(x))"
  moreover
  note \<open>M(a)\<close>
  moreover from  \<open>Q(i)\<close> \<open>Ord(i)\<close>
  have "Q(\<mu> x. Q(x))" (is ?G)
    by (blast intro:LeastI)
  moreover
  have "(\<forall>b[M]. Ord(b) \<and> b \<in> (\<mu> x. Q(x)) \<longrightarrow> \<not> Q(b))" (is "?H")
    using less_LeastE[of Q _ False]
    by (auto, drule_tac ltI, simp, blast)
  ultimately
  show "ordinal(M, \<mu> x. Q(x)) \<and> (empty(M, \<mu> x. Q(x)) \<and> (\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)) \<or> ?G \<and> ?H)"
    by simp
next
  assume 1:"\<exists>b[M]. Ord(b) \<and> Q(b)"
  then
  obtain i where "M(i)" "Ord(i)" "Q(i)" by blast
  assume "Ord(a) \<and> (a = 0 \<and> (\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)) \<or> Q(a) \<and> (\<forall>b[M]. Ord(b) \<and> b \<in> a \<longrightarrow> \<not> Q(b)))"
  with 1
  have "Ord(a)" "Q(a)" "\<forall>b[M]. Ord(b) \<and> b \<in> a \<longrightarrow> \<not> Q(b)"
    by blast+
  moreover from this and assms
  have "Ord(b) \<Longrightarrow> b \<in> a \<Longrightarrow> \<not> Q(b)" for b
    by (auto dest:transM)
  moreover from this and \<open>Ord(a)\<close>
  have "b < a \<Longrightarrow> \<not> Q(b)" for b
    unfolding lt_def using Ord_in_Ord by blast
  ultimately
  show "a = (\<mu> x. Q(x))"
    using Least_equality by simp
qed

lemma Least_closed:
  assumes "\<And>x. Q(x) \<Longrightarrow> Ord(x) \<Longrightarrow> \<exists>y[M]. Q(y) \<and> Ord(y)"
  shows "M(\<mu> x. Q(x))"
  using assms Least_le[of Q] Least_0[of Q]
  by (cases "(\<exists>i[M]. Ord(i) \<and> Q(i))") (force dest:transM ltD)+

text\<open>Older, easier to apply versions (with a simpler assumption
on \<^term>\<open>Q\<close>).\<close>
lemma least_abs':
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)" "M(a)"
  shows "least(M,Q,a) \<longleftrightarrow> a = (\<mu> x. Q(x))"
  using assms least_abs[of Q] by auto

lemma Least_closed':
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)"
  shows "M(\<mu> x. Q(x))"
  using assms Least_closed[of Q] by auto

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

end