section\<open>Fully relational versions of higher order constructs\<close>
theory Higher_Order_Constructs
  imports
    Recursion_Thms
    Least
begin

syntax
  "_sats"  :: "[i, i, i] \<Rightarrow> o"  ("(_, _ \<Turnstile> _)" [36,36,36] 25)
translations
  "(M,env \<Turnstile> \<phi>)" \<rightleftharpoons> "CONST sats(M,\<phi>,env)"

definition
  is_If :: "[i\<Rightarrow>o,o,i,i,i] \<Rightarrow> o" where
  "is_If(M,b,t,f,r) \<equiv> (b \<longrightarrow> r=t) \<and> (\<not>b \<longrightarrow> r=f)"

lemma (in M_trans) If_abs:
  "is_If(M,b,t,f,r) \<longleftrightarrow> r = If(b,t,f)"
  by (simp add: is_If_def)


definition
  is_If_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_If_fm(\<phi>,t,f,r) \<equiv> Or(And(\<phi>,Equal(t,r)),And(Neg(\<phi>),Equal(f,r)))"

lemma is_If_fm_type [TC]: "\<phi> \<in> formula \<Longrightarrow> t \<in> nat \<Longrightarrow> f \<in> nat \<Longrightarrow> r \<in> nat \<Longrightarrow>
  is_If_fm(\<phi>,t,f,r) \<in> formula"
  unfolding is_If_fm_def by auto

lemma sats_is_If_fm:
  assumes Qsats: "Q \<longleftrightarrow> A, env \<Turnstile> \<phi>" "env \<in> list(A)"
  shows "is_If(##A, Q, nth(t, env), nth(f, env), nth(r, env)) \<longleftrightarrow> A, env \<Turnstile> is_If_fm(\<phi>,t,f,r)"
  using assms unfolding is_If_def is_If_fm_def by auto

lemma is_If_fm_iff_sats [iff_sats]:
  assumes Qsats: "Q \<longleftrightarrow> A, env \<Turnstile> \<phi>" and
    "nth(t, env) = ta" "nth(f, env) = fa" "nth(r, env) = ra"
    "t \<in> nat" "f \<in> nat" "r \<in> nat" "env \<in> list(A)"
  shows "is_If(##A,Q,ta,fa,ra) \<longleftrightarrow> A, env \<Turnstile> is_If_fm(\<phi>,t,f,r)"
  using assms sats_is_If_fm[of Q A \<phi> env t f r] by simp

lemma arity_is_If_fm [arity]:
  "\<phi> \<in> formula \<Longrightarrow> t \<in> nat \<Longrightarrow> f \<in> nat \<Longrightarrow> r \<in> nat \<Longrightarrow>
    arity(is_If_fm(\<phi>, t, f, r)) = arity(\<phi>) \<union> succ(t) \<union> succ(r) \<union> succ(f)"
  unfolding is_If_fm_def
  by auto

definition
  is_The :: "[i\<Rightarrow>o,i\<Rightarrow>o,i] \<Rightarrow> o" where
  "is_The(M,Q,i) \<equiv> (Q(i) \<and> (\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x))) \<or>
                   (\<not>(\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x))) \<and> empty(M,i) "

(*
definition
  is_The_fm :: "[i,i] \<Rightarrow> i" where
  "is_The_fm(q,i) \<equiv> Or(And(Exists(And(Equal(succ(i),0),q)),
                  Exists(And(q,Forall(Implies(q,Equal(1,0)))))),
                          And(Neg(Exists(And(q,Forall(Implies(q,Equal(1,0)))))),empty_fm(i)))"

(* this doesn't work yet *)
lemma sats_The_fm :
  assumes p_iff_sats:
    "\<And>a. a \<in> A \<Longrightarrow> P(a) \<longleftrightarrow> sats(A, p, Cons(a, env))"
  shows
    "\<lbrakk>y \<in> nat; env \<in> list(A) ; 0\<in>A\<rbrakk>
    \<Longrightarrow> sats(A, is_The_fm(p,y), env) \<longleftrightarrow>
        is_The(##A, P, nth(y,env))"
  using nth_closed p_iff_sats
  unfolding is_The_def is_The_fm_def
  oops

lemma The_iff_sats [iff_sats]:
  assumes is_Q_iff_sats:
      "\<And>a. a \<in> A \<Longrightarrow> is_Q(a) \<longleftrightarrow> sats(A, q, Cons(a,env))"
  shows
  "\<lbrakk>nth(j,env) = y; j \<in> nat; env \<in> list(A); 0\<in>A\<rbrakk>
   \<Longrightarrow> is_The(##A, is_Q, y) \<longleftrightarrow> sats(A, is_The_fm(q,j), env)"
  using sats_The_fm [OF is_Q_iff_sats, of j , symmetric]
  by simp
*)

lemma (in M_trans) The_abs:
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)" "M(a)"
  shows "is_The(M,Q,a) \<longleftrightarrow> a = (THE x. Q(x))"
proof (cases "\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x)")
  case True
  with assms
  show ?thesis
    unfolding is_The_def
    by (intro iffI the_equality[symmetric])
      (auto, blast intro:theI)
next
  case False
  with \<open>\<And>x. Q(x) \<Longrightarrow> M(x)\<close>
  have " \<not> (\<exists>x. Q(x) \<and> (\<forall>y. Q(y) \<longrightarrow> y = x))"
    by auto
  then
  have "The(Q) = 0"
    by (intro the_0) auto
  with assms and False
  show ?thesis
    unfolding is_The_def
    by auto
qed

(*
definition
  recursor  :: "[i, [i,i]=>i, i]=>i"  where
    "recursor(a,b,k) \<equiv>  transrec(k, \<lambda>n f. nat_case(a, \<lambda>m. b(m, f`m), n))"
*)

definition
  is_recursor :: "[i\<Rightarrow>o,i,[i,i,i]\<Rightarrow>o,i,i] \<Rightarrow>o" where
  "is_recursor(M,a,is_b,k,r) \<equiv> is_transrec(M, \<lambda>n f ntc. is_nat_case(M,a,
      \<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,f,m,fm) \<and> is_b(m,fm,bmfm),n,ntc),k,r)"

lemma (in M_eclose) recursor_abs:
  assumes "Ord(k)" and
    types: "M(a)" "M(k)" "M(r)" and
    b_iff: "\<And>m f bmf. M(m) \<Longrightarrow> M(f) \<Longrightarrow> M(bmf) \<Longrightarrow> is_b(m,f,bmf)  \<longleftrightarrow> bmf = b(m,f)" and
    b_closed: "\<And>m f bmf. M(m) \<Longrightarrow> M(f) \<Longrightarrow> M(b(m,f))" and
    repl: "transrec_replacement(M, \<lambda>n f ntc. is_nat_case(M, a,
        \<lambda>m bmfm. \<exists>fm[M]. fun_apply(M, f, m, fm) \<and> is_b( m, fm, bmfm), n, ntc), k)"
  shows
    "is_recursor(M,a,is_b,k,r) \<longleftrightarrow> r = recursor(a,b,k)"
  unfolding is_recursor_def recursor_def
  using assms
  apply (rule_tac transrec_abs)
       apply (auto simp:relation2_def)
   apply (rule nat_case_abs[THEN iffD1, where is_b1="\<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,_,m,fm) \<and> is_b(m,fm,bmfm)"])
      apply (auto simp:relation1_def)
  apply (rule nat_case_abs[THEN iffD2, where is_b1="\<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,_,m,fm) \<and> is_b(m,fm,bmfm)"])
     apply (auto simp:relation1_def)
  done

definition
  is_wfrec_on :: "[i=>o,[i,i,i]=>o,i,i,i, i] => o" where
  "is_wfrec_on(M,MH,A,r,a,z) == is_wfrec(M,MH,r,a,z)"

lemma (in M_trancl) trans_wfrec_on_abs:
  "[|wf(r);  trans(r);  relation(r);  M(r);  M(a);  M(z);
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g));
     r-``{a}\<subseteq>A; a \<in> A|]
   ==> is_wfrec_on(M,MH,A,r,a,z) \<longleftrightarrow> z=wfrec[A](r,a,H)"
  using trans_wfrec_abs wfrec_trans_restr
  unfolding is_wfrec_on_def by simp

end