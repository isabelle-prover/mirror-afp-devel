section\<open>Relative, Choice-less Cardinal Arithmetic\<close>

theory CardinalArith_Relative
  imports
    Cardinal_Relative

begin


(* rvimage(?A, ?f, ?r) \<equiv> {z \<in> ?A \<times> ?A . \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>?f ` x, ?f ` y\<rangle> \<in> ?r} *)
relativize functional "rvimage" "rvimage_rel" external
relationalize "rvimage_rel" "is_rvimage"

definition
  csquare_lam :: "i\<Rightarrow>i" where
  "csquare_lam(K) \<equiv> \<lambda>\<langle>x,y\<rangle>\<in>K\<times>K. \<langle>x \<union> y, x, y\<rangle>"

\<comment> \<open>Can't do the next thing because split is a missing HOC\<close>
(* relativize functional "csquare_lam" "csquare_lam_rel" *)
relativize_tm "<fst(x) \<union> snd(x), fst(x), snd(x)>" "is_csquare_lam_body"

definition
  is_csquare_lam :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "is_csquare_lam(M,K,l) \<equiv> \<exists>K2[M]. cartprod(M,K,K,K2) \<and>
        is_lambda(M,K2,is_csquare_lam_body(M),l)"

definition jump_cardinal_body :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
  "jump_cardinal_body(M,X) \<equiv>
    {z . r \<in> Pow\<^bsup>M\<^esup>(X \<times> X), M(z) \<and> M(r) \<and> well_ord(X, r) \<and> z = ordertype(X, r)} "

lemma (in M_cardinals) csquare_lam_closed[intro,simp]: "M(K) \<Longrightarrow> M(csquare_lam(K))"
  using csquare_lam_replacement  unfolding csquare_lam_def
  by (rule lam_closed) (auto dest:transM)

locale M_pre_cardinal_arith = M_cardinals +
  assumes
    wfrec_pred_replacement:"M(A) \<Longrightarrow> M(r) \<Longrightarrow>
      wfrec_replacement(M, \<lambda>x f z. z = f `` Order.pred(A, x, r), r)"
begin

lemma ord_iso_separation: "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow>
      separation(M, \<lambda>f. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> s)"
  using
    lam_replacement_Pair[THEN[5] lam_replacement_hcomp2]
    lam_replacement_hcomp lam_replacement_fst  lam_replacement_snd
    separation_in lam_replacement_fst lam_replacement_apply2[THEN[5] lam_replacement_hcomp2]
    lam_replacement_identity  lam_replacement_constant
  by(rule_tac separation_ball,rule_tac separation_ball,simp_all,rule_tac separation_iff',simp_all)

end

locale M_cardinal_arith = M_pre_cardinal_arith +
  assumes
    ordertype_replacement :
    "M(X) \<Longrightarrow> strong_replacement(M,\<lambda> x z . M(z) \<and> M(x) \<and> x\<in>Pow_rel(M,X\<times>X) \<and> well_ord(X, x) \<and> z=ordertype(X,x))"
    and
    strong_replacement_jc_body :
    "strong_replacement(M,\<lambda> x z . M(z) \<and> M(x) \<and> z = jump_cardinal_body(M,x))"

lemmas (in M_cardinal_arith) surj_imp_inj_replacement =
  surj_imp_inj_replacement1 surj_imp_inj_replacement2 surj_imp_inj_replacement4
  lam_replacement_vimage_sing_fun[THEN lam_replacement_imp_strong_replacement]

relativize_tm "\<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> r \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> s)"
  "is_rmultP"

relativize functional "rmult" "rmult_rel" external
relationalize "rmult_rel" "is_rmult"

lemma (in M_trivial) rmultP_abs [absolut]: "\<lbrakk> M(r); M(s); M(z) \<rbrakk> \<Longrightarrow> is_rmultP(M,s,r,z) \<longleftrightarrow>
    (\<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> r \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> s))"
  unfolding is_rmultP_def by (auto dest:transM)

definition
  is_csquare_rel :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o"  where
  "is_csquare_rel(M,K,cs) \<equiv> \<exists>K2[M]. \<exists>la[M]. \<exists>memK[M].
      \<exists>rmKK[M]. \<exists>rmKK2[M].
        cartprod(M,K,K,K2) \<and> is_csquare_lam(M,K,la) \<and>
        membership(M,K,memK) \<and> is_rmult(M,K,memK,K,memK,rmKK) \<and>
        is_rmult(M,K,memK,K2,rmKK,rmKK2) \<and> is_rvimage(M,K2,la,rmKK2,cs)"

context M_basic
begin

lemma rvimage_abs[absolut]:
  assumes "M(A)" "M(f)" "M(r)" "M(z)"
  shows "is_rvimage(M,A,f,r,z) \<longleftrightarrow> z = rvimage(A,f,r)"
  using assms transM[OF _ \<open>M(A)\<close>]
  unfolding is_rvimage_def rvimage_def
  by auto

lemma rmult_abs [absolut]: "\<lbrakk> M(A); M(r); M(B); M(s); M(z) \<rbrakk> \<Longrightarrow>
    is_rmult(M,A,r,B,s,z) \<longleftrightarrow> z=rmult(A,r,B,s)"
  using rmultP_abs transM[of _ "(A \<times> B) \<times> A \<times> B"]
  unfolding is_rmultP_def is_rmult_def rmult_def
  by (auto del: iffI)

lemma csquare_lam_body_abs[absolut]: "M(x) \<Longrightarrow> M(z) \<Longrightarrow>
  is_csquare_lam_body(M,x,z) \<longleftrightarrow> z = <fst(x) \<union> snd(x), fst(x), snd(x)>"
  unfolding is_csquare_lam_body_def by (simp add:absolut)

lemma csquare_lam_abs[absolut]: "M(K) \<Longrightarrow> M(l) \<Longrightarrow>
  is_csquare_lam(M,K,l) \<longleftrightarrow> l = (\<lambda>x\<in>K\<times>K. \<langle>fst(x) \<union> snd(x), fst(x), snd(x)\<rangle>)"
  unfolding is_csquare_lam_def
  using lambda_abs2[of "K\<times>K" "is_csquare_lam_body(M)"
      "\<lambda>x. \<langle>fst(x) \<union> snd(x), fst(x), snd(x)\<rangle>"]
  unfolding Relation1_def by (simp add:absolut)

lemma csquare_lam_eq_lam:"csquare_lam(K) = (\<lambda>z\<in>K\<times>K. <fst(z) \<union> snd(z), fst(z), snd(z)>)"
proof -
  have "(\<lambda>\<langle>x,y\<rangle>\<in>K \<times> K. \<langle>x \<union> y, x, y\<rangle>)`z =
      (\<lambda>z\<in>K\<times>K. <fst(z) \<union> snd(z), fst(z), snd(z)>)`z" if "z\<in>K\<times>K" for z
    using that by auto
  then
  show ?thesis
    unfolding csquare_lam_def
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

context M_pre_cardinal_arith
begin

lemma csquare_rel_closed[intro,simp]: "M(K) \<Longrightarrow> M(csquare_rel(K))"
  using csquare_lam_replacement unfolding csquare_rel_def
  by (intro rvimage_closed lam_closed) (auto dest:transM)

(* Ugly proof ahead, please enhance *)
lemma csquare_rel_abs[absolut]: "\<lbrakk> M(K); M(cs)\<rbrakk> \<Longrightarrow>
     is_csquare_rel(M,K,cs) \<longleftrightarrow> cs = csquare_rel(K)"
  unfolding is_csquare_rel_def csquare_rel_def
  using csquare_lam_closed[unfolded csquare_lam_eq_lam]
  by (simp add:absolut csquare_lam_eq_lam[unfolded csquare_lam_def])

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

(*************   Discipline for csucc  ****************)
relativize functional "csucc" "csucc_rel" external
relationalize "csucc_rel" "is_csucc"
synthesize "is_csucc" from_definition assuming "nonempty"
arity_theorem for "is_csucc_fm"

abbreviation
  csucc_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r(x,M) \<equiv> csucc_rel(M,x)"

abbreviation
  csucc_r_set :: "[i,i] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r_set(x,M) \<equiv> csucc_rel(##M,x)"

context M_Perm
begin

rel_closed for "csucc"
  using Least_closed'[of "\<lambda> L. M(L) \<and> Card\<^bsup>M\<^esup>(L) \<and> K < L"]
  unfolding csucc_rel_def
  by simp

is_iff_rel for "csucc"
  using least_abs'[of "\<lambda> L. M(L) \<and> Card\<^bsup>M\<^esup>(L) \<and> K < L" res]
    is_Card_iff
  unfolding is_csucc_def csucc_rel_def
  by (simp add:absolut)

end \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

notation csucc_rel (\<open>csucc\<^bsup>_\<^esup>'(_')\<close>)

(***************  end Discipline  *********************)

context M_cardinals
begin

lemma Card_rel_Union [simp,intro,TC]:
  assumes A: "\<And>x. x\<in>A \<Longrightarrow> Card\<^bsup>M\<^esup>(x)" and
    types:"M(A)"
  shows "Card\<^bsup>M\<^esup>(\<Union>(A))"
proof (rule Card_relI)
  show "Ord(\<Union>A)" using A
    by (simp add: Card_rel_is_Ord types transM)
next
  fix j
  assume j: "j < \<Union>A"
  moreover from this
  have "M(j)" unfolding lt_def by (auto simp add:types dest:transM)
  from j
  have "\<exists>c\<in>A. j \<in> c \<and> Card\<^bsup>M\<^esup>(c)" using A types
    unfolding lt_def
    by (simp)
  then
  obtain c where c: "c\<in>A" "j < c" "Card\<^bsup>M\<^esup>(c)" "M(c)"
    using Card_rel_is_Ord types unfolding lt_def
    by (auto dest:transM)
  with \<open>M(j)\<close>
  have jls: "j \<prec>\<^bsup>M\<^esup> c"
    by (simp add: lt_Card_rel_imp_lesspoll_rel types)
  { assume eqp: "j \<approx>\<^bsup>M\<^esup> \<Union>A"
    have  "c \<lesssim>\<^bsup>M\<^esup> \<Union>A" using c
      by (blast intro: subset_imp_lepoll_rel types)
    also from types \<open>M(j)\<close>
    have "... \<approx>\<^bsup>M\<^esup> j"  by (rule_tac eqpoll_rel_sym [OF eqp]) (simp_all add:types)
    also have "... \<prec>\<^bsup>M\<^esup> c"  by (rule jls)
    finally have "c \<prec>\<^bsup>M\<^esup> c" by (simp_all add:\<open>M(c)\<close> \<open>M(j)\<close> types)
    with \<open>M(c)\<close>
    have False
      by (auto dest:lesspoll_rel_irrefl)
  } thus "\<not> j \<approx>\<^bsup>M\<^esup> \<Union>A" by blast
qed (simp_all add:types)

(*
lemma Card_UN: "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x\<in>A. K(x))"
  by blast


lemma Card_OUN [simp,intro,TC]:
     "(!!x. x \<in> A ==> Card(K(x))) ==> Card(\<Union>x<A. K(x))"
  by (auto simp add: OUnion_def Card_0)
*)

lemma in_Card_imp_lesspoll: "[| Card\<^bsup>M\<^esup>(K); b \<in> K; M(K); M(b) |] ==> b \<prec>\<^bsup>M\<^esup> K"
  apply (unfold lesspoll_rel_def)
  apply (simp add: Card_rel_iff_initial)
  apply (fast intro!: le_imp_lepoll_rel ltI leI)
  done


subsection\<open>Cardinal addition\<close>

text\<open>Note (Paulson): Could omit proving the algebraic laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get most laws for free.\<close>

subsubsection\<open>Cardinal addition is commutative\<close>

lemma sum_commute_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A+B \<approx>\<^bsup>M\<^esup> B+A"
proof (simp add: def_eqpoll_rel, rule rexI)
  show "(\<lambda>z\<in>A+B. case(Inr,Inl,z)) \<in> bij(A+B, B+A)"
    by (auto intro: lam_bijective [where d = "case(Inr,Inl)"])
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>z\<in>A + B. case(Inr, Inl, z))"
    using case_replacement1
    by (rule_tac lam_closed) (auto dest:transM)
qed

lemma cadd_rel_commute: "M(i) \<Longrightarrow> M(j) \<Longrightarrow> i \<oplus>\<^bsup>M\<^esup> j = j \<oplus>\<^bsup>M\<^esup> i"
  apply (unfold cadd_rel_def)
  apply (auto intro: sum_commute_eqpoll_rel [THEN cardinal_rel_cong])
  done

subsubsection\<open>Cardinal addition is associative\<close>

lemma sum_assoc_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A+B)+C \<approx>\<^bsup>M\<^esup> A+(B+C)"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule sum_assoc_bij)
  using case_replacement2
  by (rule_tac lam_closed) (auto dest:transM)

text\<open>Unconditional version requires AC\<close>
lemma well_ord_cadd_rel_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<oplus>\<^bsup>M\<^esup> j) \<oplus>\<^bsup>M\<^esup> k = i \<oplus>\<^bsup>M\<^esup> (j \<oplus>\<^bsup>M\<^esup> k)"
proof (simp add: assms cadd_rel_def, rule cardinal_rel_cong)
  from types
  have "|i + j|\<^bsup>M\<^esup> + k \<approx>\<^bsup>M\<^esup> (i + j) + k"
    by (auto intro!: sum_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_refl well_ord_radd i j)
  also have "...  \<approx>\<^bsup>M\<^esup> i + (j + k)"
    by (rule sum_assoc_eqpoll_rel) (simp_all add:types)
  also
  have "...  \<approx>\<^bsup>M\<^esup> i + |j + k|\<^bsup>M\<^esup>"
  proof (auto intro!: sum_eqpoll_rel_cong intro:eqpoll_rel_refl simp add:types)
    from types
    have "|j + k|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> j + k"
      using well_ord_cardinal_rel_eqpoll_rel[OF well_ord_radd, OF j k]
      by (simp)
    with types
    show "j + k \<approx>\<^bsup>M\<^esup> |j + k|\<^bsup>M\<^esup>"
      using eqpoll_rel_sym by simp
  qed
  finally show "|i + j|\<^bsup>M\<^esup> + k \<approx>\<^bsup>M\<^esup> i + |j + k|\<^bsup>M\<^esup>" by (simp_all add:types)
qed (simp_all add:types)


subsubsection\<open>0 is the identity for addition\<close>

lemma case_id_eq: "x\<in>sum(A,B) \<Longrightarrow> case(\<lambda>z . z, \<lambda>z. z ,x) = snd(x)"
  unfolding case_def cond_def by (auto simp:Inl_def Inr_def)

lemma lam_case_id: "(\<lambda>z\<in>0 + A. case(\<lambda>x. x, \<lambda>y. y, z)) = (\<lambda>z\<in>0 + A . snd(z))"
  using case_id_eq by simp

lemma sum_0_eqpoll_rel: "M(A) \<Longrightarrow> 0+A \<approx>\<^bsup>M\<^esup> A"
  apply (simp add:def_eqpoll_rel)
  apply (rule rexI)
   apply (rule bij_0_sum,subst lam_case_id)
  using lam_replacement_snd[unfolded lam_replacement_def]
  by (rule lam_closed)
    (auto simp add:case_def cond_def Inr_def dest:transM)

lemma cadd_rel_0 [simp]: "Card\<^bsup>M\<^esup>(K) \<Longrightarrow> M(K) \<Longrightarrow> 0 \<oplus>\<^bsup>M\<^esup> K = K"
  apply (simp add: cadd_rel_def)
  apply (simp add: sum_0_eqpoll_rel [THEN cardinal_rel_cong] Card_rel_cardinal_rel_eq)
  done

subsubsection\<open>Addition by another cardinal\<close>

lemma sum_lepoll_rel_self: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> A+B"
proof (simp add: def_lepoll_rel, rule rexI)
  show "(\<lambda>x\<in>A. Inl (x)) \<in> inj(A, A + B)"
    by (simp add: inj_def)
  assume "M(A)" "M(B)"
  then
  show "M(\<lambda>x\<in>A. Inl(x))"
    using Inl_replacement1 transM[OF _ \<open>M(A)\<close>]
    by (rule_tac lam_closed) (auto simp add: Inl_def)
qed

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)

lemma cadd_rel_le_self:
  assumes K: "Card\<^bsup>M\<^esup>(K)" and L: "Ord(L)" and
    types:"M(K)" "M(L)"
  shows "K \<le> (K \<oplus>\<^bsup>M\<^esup> L)"
proof (simp add:types cadd_rel_def)
  have "K \<le> |K|\<^bsup>M\<^esup>"
    by (rule Card_rel_cardinal_rel_le [OF K]) (simp add:types)
  moreover have "|K|\<^bsup>M\<^esup> \<le> |K + L|\<^bsup>M\<^esup>" using K L
    by (blast intro: well_ord_lepoll_rel_imp_cardinal_rel_le sum_lepoll_rel_self
        well_ord_radd well_ord_Memrel Card_rel_is_Ord types)
  ultimately show "K \<le> |K + L|\<^bsup>M\<^esup>"
    by (blast intro: le_trans)
qed

subsubsection\<open>Monotonicity of addition\<close>

lemma sum_lepoll_rel_mono:
  "[| A \<lesssim>\<^bsup>M\<^esup> C;  B \<lesssim>\<^bsup>M\<^esup> D; M(A); M(B); M(C); M(D) |] ==> A + B \<lesssim>\<^bsup>M\<^esup> C + D"
  apply (simp add: def_lepoll_rel)
  apply (elim rexE)
  apply (rule_tac x = "\<lambda>z\<in>A+B. case (%w. Inl(f`w), %y. Inr(fa`y), z)" in rexI)
   apply (rule_tac d = "case (%w. Inl(converse(f) `w), %y. Inr(converse(fa) ` y))"
      in lam_injective)
    apply (typecheck add: inj_is_fun, auto)
  apply (rule_tac lam_closed, auto dest:transM intro:case_replacement4)
  done

lemma cadd_rel_le_mono:
  "[| K' \<le> K;  L' \<le> L;M(K');M(K);M(L');M(L) |] ==> (K' \<oplus>\<^bsup>M\<^esup> L') \<le> (K \<oplus>\<^bsup>M\<^esup> L)"
  apply (unfold cadd_rel_def)
  apply (safe dest!: le_subset_iff [THEN iffD1])
  apply (rule well_ord_lepoll_rel_imp_cardinal_rel_le)
      apply (blast intro: well_ord_radd well_ord_Memrel)
     apply (auto intro: sum_lepoll_rel_mono subset_imp_lepoll_rel)
  done

subsubsection\<open>Addition of finite cardinals is "ordinary" addition\<close>

lemma sum_succ_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> succ(A)+B \<approx>\<^bsup>M\<^esup> succ(A+B)"
  apply (simp add:def_eqpoll_rel)
  apply (rule rexI)
   apply (rule_tac c = "%z. if z=Inl (A) then A+B else z"
      and d = "%z. if z=A+B then Inl (A) else z" in lam_bijective)
      apply simp_all
      apply (blast dest: sym [THEN eq_imp_not_mem] elim: mem_irrefl)+
  apply(rule_tac lam_closed, auto dest:transM intro:if_then_range_replacement2)
  done

(*Pulling the  succ(...)  outside the |...| requires m, n \<in> nat  *)
(*Unconditional version requires AC*)
lemma cadd_succ_lemma:
  assumes "Ord(m)" "Ord(n)" and
    types: "M(m)" "M(n)"
  shows "succ(m) \<oplus>\<^bsup>M\<^esup> n = |succ(m \<oplus>\<^bsup>M\<^esup> n)|\<^bsup>M\<^esup>"
  using types
proof (simp add: cadd_rel_def)
  have [intro]: "m + n \<approx>\<^bsup>M\<^esup> |m + n|\<^bsup>M\<^esup>" using assms
    by (blast intro: eqpoll_rel_sym well_ord_cardinal_rel_eqpoll_rel well_ord_radd well_ord_Memrel)

  have "|succ(m) + n|\<^bsup>M\<^esup> = |succ(m + n)|\<^bsup>M\<^esup>"
    by (rule sum_succ_eqpoll_rel [THEN cardinal_rel_cong]) (simp_all add:types)
  also have "... = |succ(|m + n|\<^bsup>M\<^esup>)|\<^bsup>M\<^esup>"
    by (blast intro: succ_eqpoll_rel_cong cardinal_rel_cong types)
  finally show "|succ(m) + n|\<^bsup>M\<^esup> = |succ(|m + n|\<^bsup>M\<^esup>)|\<^bsup>M\<^esup>" .
qed

lemma nat_cadd_rel_eq_add:
  assumes m: "m \<in> nat" and [simp]: "n \<in> nat" shows"m \<oplus>\<^bsup>M\<^esup> n = m +\<^sub>\<omega> n"
  using m
proof (induct m)
  case 0 thus ?case
    using transM[OF _ M_nat]
    by (auto simp add: nat_into_Card_rel)
next
  case (succ m) thus ?case
    using transM[OF _ M_nat]
    by (simp add: cadd_succ_lemma nat_into_Card_rel Card_rel_cardinal_rel_eq)
qed


subsection\<open>Cardinal multiplication\<close>

subsubsection\<open>Cardinal multiplication is commutative\<close>

lemma prod_commute_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A*B \<approx>\<^bsup>M\<^esup> B*A"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule_tac c = "%<x,y>.<y,x>" and d = "%<x,y>.<y,x>" in lam_bijective,
      auto)
  apply(rule_tac lam_closed, auto intro:swap_replacement dest:transM)
  done

lemma cmult_rel_commute: "M(i) \<Longrightarrow> M(j) \<Longrightarrow> i \<otimes>\<^bsup>M\<^esup> j = j \<otimes>\<^bsup>M\<^esup> i"
  apply (unfold cmult_rel_def)
  apply (rule prod_commute_eqpoll_rel [THEN cardinal_rel_cong], simp_all)
  done

subsubsection\<open>Cardinal multiplication is associative\<close>

lemma prod_assoc_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A*B)*C \<approx>\<^bsup>M\<^esup> A*(B*C)"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule prod_assoc_bij)
  apply(rule_tac lam_closed, auto intro:assoc_replacement dest:transM)
  done


text\<open>Unconditional version requires AC\<close>
lemma well_ord_cmult_rel_assoc:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<otimes>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = i \<otimes>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
proof (simp add: assms cmult_rel_def, rule cardinal_rel_cong)
  have "|i * j|\<^bsup>M\<^esup> * k \<approx>\<^bsup>M\<^esup> (i * j) * k"
    by (auto intro!: prod_eqpoll_rel_cong
        well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_refl
        well_ord_rmult i j simp add:types)
  also have "...  \<approx>\<^bsup>M\<^esup> i * (j * k)"
    by (rule prod_assoc_eqpoll_rel, simp_all add:types)
  also have "...  \<approx>\<^bsup>M\<^esup> i * |j * k|\<^bsup>M\<^esup>"
    by (blast intro: prod_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel
        eqpoll_rel_refl well_ord_rmult j k eqpoll_rel_sym types)
  finally show "|i * j|\<^bsup>M\<^esup> * k \<approx>\<^bsup>M\<^esup> i * |j * k|\<^bsup>M\<^esup>" by (simp add:types)
qed (simp_all add:types)


subsubsection\<open>Cardinal multiplication distributes over addition\<close>

lemma sum_prod_distrib_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> M(C) \<Longrightarrow> (A+B)*C \<approx>\<^bsup>M\<^esup> (A*C)+(B*C)"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule sum_prod_distrib_bij)
  apply(rule_tac lam_closed, auto intro:case_replacement5 dest:transM)
  done


lemma well_ord_cadd_cmult_distrib:
  assumes i: "well_ord(i,ri)" and j: "well_ord(j,rj)" and k: "well_ord(k,rk)"
    and
    types: "M(i)" "M(ri)" "M(j)" "M(rj)" "M(k)" "M(rk)"
  shows "(i \<oplus>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = (i \<otimes>\<^bsup>M\<^esup> k) \<oplus>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
proof (simp add: assms cadd_rel_def cmult_rel_def, rule cardinal_rel_cong)
  have "|i + j|\<^bsup>M\<^esup> * k \<approx>\<^bsup>M\<^esup> (i + j) * k"
    by (blast intro: prod_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel
        eqpoll_rel_refl well_ord_radd i j types)
  also have "...  \<approx>\<^bsup>M\<^esup> i * k + j * k"
    by (rule sum_prod_distrib_eqpoll_rel) (simp_all add:types)
  also have "...  \<approx>\<^bsup>M\<^esup> |i * k|\<^bsup>M\<^esup> + |j * k|\<^bsup>M\<^esup>"
    by (blast intro: sum_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel
        well_ord_rmult i j k eqpoll_rel_sym types)
  finally show "|i + j|\<^bsup>M\<^esup> * k \<approx>\<^bsup>M\<^esup> |i * k|\<^bsup>M\<^esup> + |j * k|\<^bsup>M\<^esup>" by (simp add:types)
qed (simp_all add:types)


subsubsection\<open>Multiplication by 0 yields 0\<close>

lemma prod_0_eqpoll_rel: "M(A) \<Longrightarrow> 0*A \<approx>\<^bsup>M\<^esup> 0"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule lam_bijective, auto)
  done

lemma cmult_rel_0 [simp]: "M(i) \<Longrightarrow> 0 \<otimes>\<^bsup>M\<^esup> i = 0"
  by (simp add: cmult_rel_def prod_0_eqpoll_rel [THEN cardinal_rel_cong])

subsubsection\<open>1 is the identity for multiplication\<close>

lemma prod_singleton_eqpoll_rel: "M(x) \<Longrightarrow> M(A) \<Longrightarrow> {x}*A \<approx>\<^bsup>M\<^esup> A"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule singleton_prod_bij [THEN bij_converse_bij])
  apply (rule converse_closed)
  apply(rule_tac lam_closed, auto intro:prepend_replacement dest:transM)
  done

lemma cmult_rel_1 [simp]: "Card\<^bsup>M\<^esup>(K) \<Longrightarrow> M(K) \<Longrightarrow> 1 \<otimes>\<^bsup>M\<^esup> K = K"
  apply (simp add: cmult_rel_def succ_def)
  apply (simp add: prod_singleton_eqpoll_rel[THEN cardinal_rel_cong] Card_rel_cardinal_rel_eq)
  done

subsection\<open>Some inequalities for multiplication\<close>

lemma prod_square_lepoll_rel: "M(A) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> A*A"
  apply (simp add:def_lepoll_rel inj_def)
  apply (rule_tac x = "\<lambda>x\<in>A. <x,x>" in rexI, simp)
  apply(rule_tac lam_closed, auto intro:id_replacement dest:transM)
  done

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
lemma cmult_rel_square_le: "Card\<^bsup>M\<^esup>(K) \<Longrightarrow> M(K) \<Longrightarrow> K \<le> K \<otimes>\<^bsup>M\<^esup> K"
  apply (unfold cmult_rel_def)
  apply (rule le_trans)
   apply (rule_tac [2] well_ord_lepoll_rel_imp_cardinal_rel_le)
       apply (rule_tac [3] prod_square_lepoll_rel)
       apply (simp add: le_refl Card_rel_is_Ord Card_rel_cardinal_rel_eq)
      apply (blast intro: well_ord_rmult well_ord_Memrel Card_rel_is_Ord)
     apply simp_all
  done

subsubsection\<open>Multiplication by a non-zero cardinal\<close>

lemma prod_lepoll_rel_self: "b \<in> B \<Longrightarrow> M(b) \<Longrightarrow> M(B) \<Longrightarrow> M(A) \<Longrightarrow> A \<lesssim>\<^bsup>M\<^esup> A*B"
  apply (simp add: def_lepoll_rel inj_def)
  apply (rule_tac x = "\<lambda>x\<in>A. <x,b>" in rexI, simp)
  apply(rule_tac lam_closed, auto intro:pospend_replacement dest:transM)
  done

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
lemma cmult_rel_le_self:
  "[| Card\<^bsup>M\<^esup>(K);  Ord(L);  0<L; M(K);M(L) |] ==> K \<le> (K \<otimes>\<^bsup>M\<^esup> L)"
  apply (unfold cmult_rel_def)
  apply (rule le_trans [OF Card_rel_cardinal_rel_le well_ord_lepoll_rel_imp_cardinal_rel_le])
        apply assumption apply simp
      apply (blast intro: well_ord_rmult well_ord_Memrel Card_rel_is_Ord)
     apply (auto intro: prod_lepoll_rel_self ltD)
  done

subsubsection\<open>Monotonicity of multiplication\<close>

lemma prod_lepoll_rel_mono:
  "[| A \<lesssim>\<^bsup>M\<^esup> C;  B \<lesssim>\<^bsup>M\<^esup> D; M(A); M(B); M(C); M(D)|] ==> A * B  \<lesssim>\<^bsup>M\<^esup>  C * D"
  apply (simp add:def_lepoll_rel)
  apply (elim rexE)
  apply (rule_tac x = "lam <w,y>:A*B. <f`w, fa`y>" in rexI)
   apply (rule_tac d = "%<w,y>. <converse (f) `w, converse (fa) `y>"
      in lam_injective)
    apply (typecheck add: inj_is_fun, auto)
  apply(rule_tac lam_closed, auto intro:prod_fun_replacement dest:transM)
  done

lemma cmult_rel_le_mono:
  "[| K' \<le> K;  L' \<le> L;M(K');M(K);M(L');M(L) |] ==> (K' \<otimes>\<^bsup>M\<^esup> L') \<le> (K \<otimes>\<^bsup>M\<^esup> L)"
  apply (unfold cmult_rel_def)
  apply (safe dest!: le_subset_iff [THEN iffD1])
  apply (rule well_ord_lepoll_rel_imp_cardinal_rel_le)
      apply (blast intro: well_ord_rmult well_ord_Memrel)
     apply (auto intro: prod_lepoll_rel_mono subset_imp_lepoll_rel)
  done

subsection\<open>Multiplication of finite cardinals is "ordinary" multiplication\<close>

lemma prod_succ_eqpoll_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> succ(A)*B \<approx>\<^bsup>M\<^esup> B + A*B"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (rule_tac c = "\<lambda>p. if fst(p)=A then Inl (snd(p)) else Inr (p)"
      and d = "case (%y. <A,y>, %z. z)" in lam_bijective)
      apply safe
          apply (simp_all add: succI2 if_type mem_imp_not_eq)
  apply(rule_tac lam_closed, auto intro:Inl_replacement2 dest:transM)
  done

(*Unconditional version requires AC*)
lemma cmult_rel_succ_lemma:
  "[| Ord(m);  Ord(n) ; M(m); M(n) |] ==> succ(m) \<otimes>\<^bsup>M\<^esup> n = n \<oplus>\<^bsup>M\<^esup> (m \<otimes>\<^bsup>M\<^esup> n)"
  apply (simp add: cmult_rel_def cadd_rel_def)
  apply (rule prod_succ_eqpoll_rel [THEN cardinal_rel_cong, THEN trans], simp_all)
  apply (rule cardinal_rel_cong [symmetric], simp_all)
  apply (rule sum_eqpoll_rel_cong [OF eqpoll_rel_refl well_ord_cardinal_rel_eqpoll_rel], assumption)
        apply (blast intro: well_ord_rmult well_ord_Memrel)
       apply simp_all
  done

lemma nat_cmult_rel_eq_mult: "[| m \<in> nat;  n \<in> nat |] ==> m \<otimes>\<^bsup>M\<^esup> n = m#*n"
  using transM[OF _ M_nat]
  apply (induct_tac m)
   apply (simp_all add: cmult_rel_succ_lemma nat_cadd_rel_eq_add)
  done

lemma cmult_rel_2: "Card\<^bsup>M\<^esup>(n) \<Longrightarrow> M(n) \<Longrightarrow> 2 \<otimes>\<^bsup>M\<^esup> n = n \<oplus>\<^bsup>M\<^esup> n"
  by (simp add: cmult_rel_succ_lemma Card_rel_is_Ord cadd_rel_commute [of _ 0])

lemma sum_lepoll_rel_prod:
  assumes C: "2 \<lesssim>\<^bsup>M\<^esup> C" and
    types:"M(C)" "M(B)"
  shows "B+B \<lesssim>\<^bsup>M\<^esup> C*B"
proof -
  have "B+B \<lesssim>\<^bsup>M\<^esup> 2*B"
    by (simp add: sum_eq_2_times types)
  also have "... \<lesssim>\<^bsup>M\<^esup> C*B"
    by (blast intro: prod_lepoll_rel_mono lepoll_rel_refl C types)
  finally show "B+B \<lesssim>\<^bsup>M\<^esup> C*B" by (simp_all add:types)
qed

lemma lepoll_imp_sum_lepoll_prod: "[| A \<lesssim>\<^bsup>M\<^esup> B; 2 \<lesssim>\<^bsup>M\<^esup> A; M(A) ;M(B) |] ==> A+B \<lesssim>\<^bsup>M\<^esup> A*B"
  by (blast intro: sum_lepoll_rel_mono sum_lepoll_rel_prod lepoll_rel_trans lepoll_rel_refl)

end \<comment> \<open>\<^locale>\<open>M_cardinals\<close>\<close>

subsection\<open>Infinite Cardinals are Limit Ordinals\<close>

(*This proof is modelled upon one assuming nat<=A, with injection
  \<lambda>z\<in>cons(u,A). if z=u then 0 else if z \<in> nat then succ(z) else z
  and inverse %y. if y \<in> nat then nat_case(u, %z. z, y) else y.  \
  If f \<in> inj(nat,A) then range(f) behaves like the natural numbers.*)


context M_pre_cardinal_arith
begin

lemma nat_cons_lepoll_rel: "nat \<lesssim>\<^bsup>M\<^esup> A \<Longrightarrow> M(A) \<Longrightarrow> M(u) ==> cons(u,A) \<lesssim>\<^bsup>M\<^esup> A"
  apply (simp add: def_lepoll_rel)
  apply (erule rexE)
  apply (rule_tac x =
      "\<lambda>z\<in>cons (u,A).
             if z=u then f`0
             else if z \<in> range (f) then f`succ (converse (f) `z) else z"
      in rexI)
   apply (rule_tac d =
      "%y. if y \<in> range(f) then nat_case (u, %z. f`z, converse(f) `y)
                              else y"
      in lam_injective)
    apply (fast intro!: if_type apply_type intro: inj_is_fun inj_converse_fun)
   apply (simp add: inj_is_fun [THEN apply_rangeI]
      inj_converse_fun [THEN apply_rangeI]
      inj_converse_fun [THEN apply_funtype])
proof -
  fix f
  assume "M(A)" "M(f)" "M(u)"
  then
  show "M(\<lambda>z\<in>cons(u, A). if z = u then f ` 0 else if z \<in> range(f) then f ` succ(converse(f) ` z) else z)"
    using if_then_range_replacement transM[OF _ \<open>M(A)\<close>]
    by (rule_tac lam_closed, auto)
qed

lemma nat_cons_eqpoll_rel: "nat \<lesssim>\<^bsup>M\<^esup> A ==> M(A) \<Longrightarrow> M(u) \<Longrightarrow> cons(u,A) \<approx>\<^bsup>M\<^esup> A"
  apply (erule nat_cons_lepoll_rel [THEN eqpoll_relI], assumption+)
    apply (rule subset_consI [THEN subset_imp_lepoll_rel], simp_all)
  done

lemma nat_succ_eqpoll_rel: "nat \<subseteq> A ==> M(A) \<Longrightarrow> succ(A) \<approx>\<^bsup>M\<^esup> A"
  apply (unfold succ_def)
  apply (erule subset_imp_lepoll_rel [THEN nat_cons_eqpoll_rel], simp_all)
  done

lemma InfCard_rel_nat: "InfCard\<^bsup>M\<^esup>(nat)"
  apply (simp add: InfCard_rel_def)
  apply (blast intro: Card_rel_nat Card_rel_is_Ord)
  done

lemma InfCard_rel_is_Card_rel: "M(K) \<Longrightarrow> InfCard\<^bsup>M\<^esup>(K) \<Longrightarrow> Card\<^bsup>M\<^esup>(K)"
  apply (simp add: InfCard_rel_def)
  done

lemma InfCard_rel_Un:
  "[| InfCard\<^bsup>M\<^esup>(K);  Card\<^bsup>M\<^esup>(L); M(K); M(L) |] ==> InfCard\<^bsup>M\<^esup>(K \<union> L)"
  apply (simp add: InfCard_rel_def)
  apply (simp add: Card_rel_Un Un_upper1_le [THEN [2] le_trans]  Card_rel_is_Ord)
  done

lemma InfCard_rel_is_Limit: "InfCard\<^bsup>M\<^esup>(K) ==> M(K) \<Longrightarrow> Limit(K)"
  apply (simp add: InfCard_rel_def)
  apply (erule conjE)
  apply (frule Card_rel_is_Ord, assumption)
  apply (rule ltI [THEN non_succ_LimitI])
    apply (erule le_imp_subset [THEN subsetD])
    apply (safe dest!: Limit_nat [THEN Limit_le_succD])
  apply (unfold Card_rel_def)
  apply (drule trans)
   apply (erule le_imp_subset [THEN nat_succ_eqpoll_rel, THEN cardinal_rel_cong], simp_all)
  apply (erule Ord_cardinal_rel_le [THEN lt_trans2, THEN lt_irrefl], assumption)
  apply (rule le_eqI) prefer 2
   apply (rule Ord_cardinal_rel, assumption+)
  done

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)


lemma (in M_ordertype) ordertype_abs[absolut]:
  assumes "wellordered(M,A,r)" "M(A)" "M(r)" "M(i)"
  shows "otype(M,A,r,i) \<longleftrightarrow> i = ordertype(A,r)"
    \<comment> \<open>Awful proof, it essentially repeats the same argument twice\<close>
proof (intro iffI)
  note assms
  moreover
  assume "otype(M, A, r, i)"
  moreover from calculation
  obtain f j where "M(f)"  "M(j)"  "Ord(j)" "f \<in> \<langle>A, r\<rangle> \<cong> \<langle>j, Memrel(j)\<rangle>"
    using ordertype_exists[of A r] by auto
  moreover from calculation
  have "\<exists>f[M]. f \<in> \<langle>A, r\<rangle> \<cong> \<langle>j, Memrel(j)\<rangle>" by auto
  moreover
  have "\<exists>f[M]. f \<in> \<langle>A, r\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"
  proof -
    note calculation
    moreover from this
    obtain h where "omap(M, A, r, h)" "M(h)"
      using omap_exists by auto
    moreover from calculation
    have "h \<in> \<langle>A, r\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"
      using omap_ord_iso obase_equals by simp
    moreover from calculation
    have "h O converse(f) \<in> \<langle>j, Memrel(j)\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"
      using ord_iso_sym ord_iso_trans by blast
    moreover from calculation
    have "i=j"
      using Ord_iso_implies_eq[of j i "h O converse(f)"]
        Ord_otype[OF _ well_ord_is_trans_on] by simp
    ultimately
    show ?thesis by simp
  qed
  ultimately
  show "i = ordertype(A, r)"
    by (force intro:ordertypes_are_absolute[of A r _ i]
        simp add:Ord_otype[OF _ well_ord_is_trans_on])
next
  note assms
  moreover
  assume "i = ordertype(A, r)"
  moreover from calculation
  obtain h where "omap(M, A, r, h)" "M(h)"
    using omap_exists by auto
  moreover from calculation
  obtain j where "otype(M,A,r,j)" "M(j)"
    using otype_exists by auto
  moreover from calculation
  have "h \<in> \<langle>A, r\<rangle> \<cong> \<langle>j, Memrel(j)\<rangle>"
    using omap_ord_iso_otype by simp
  moreover from calculation
  obtain f where "f \<in> \<langle>A, r\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"
    using ordertype_ord_iso by auto
  moreover
  have "j=i"
  proof -
    note calculation
    moreover from this
    have "h O converse(f) \<in> \<langle>i, Memrel(i)\<rangle> \<cong> \<langle>j, Memrel(j)\<rangle>"
      using ord_iso_sym ord_iso_trans by blast
    moreover from calculation
    have "Ord(i)" using Ord_ordertype by simp
    ultimately
    show "j=i"
      using Ord_iso_implies_eq[of i j "h O converse(f)"]
        Ord_otype[OF _ well_ord_is_trans_on] by simp
  qed
  ultimately
  show "otype(M, A, r, i)" by simp
qed

lemma (in M_ordertype) ordertype_closed[intro,simp]: "\<lbrakk> wellordered(M,A,r);M(A);M(r)\<rbrakk> \<Longrightarrow> M(ordertype(A,r))"
  using ordertype_exists ordertypes_are_absolute by blast

(*
definition
  jump_cardinal :: "i=>i"  where
    \<comment> \<open>This definition is more complex than Kunen's but it more easily proved to
        be a cardinal\<close>
    "jump_cardinal(K) ==
         \<Union>X\<in>Pow(K). {z. r \<in> Pow(K*K), well_ord(X,r) & z = ordertype(X,r)}"
*)

relationalize "transitive_rel" "is_transitive" external
synthesize "is_transitive" from_definition assuming "nonempty"
arity_theorem for "is_transitive_fm"

lemma (in M_trivial) is_transitive_iff_transitive_rel:
  "M(A)\<Longrightarrow> M(r) \<Longrightarrow> transitive_rel(M, A, r) \<longleftrightarrow> is_transitive(M,A, r)"
  unfolding transitive_rel_def is_transitive_def by simp

relationalize "linear_rel" "is_linear" external
synthesize "is_linear" from_definition assuming "nonempty"
arity_theorem for "is_linear_fm"

lemma (in M_trivial) is_linear_iff_linear_rel:
  "M(A)\<Longrightarrow> M(r) \<Longrightarrow> is_linear(M,A, r) \<longleftrightarrow> linear_rel(M, A, r)"
  unfolding linear_rel_def is_linear_def by simp

relationalize "wellfounded_on" "is_wellfounded_on" external
synthesize "is_wellfounded_on" from_definition assuming "nonempty"
arity_theorem for "is_wellfounded_on_fm"

lemma (in M_trivial) is_wellfounded_on_iff_wellfounded_on:
  "M(A)\<Longrightarrow> M(r) \<Longrightarrow> is_wellfounded_on(M,A, r) \<longleftrightarrow> wellfounded_on(M, A, r)"
  unfolding wellfounded_on_def is_wellfounded_on_def by simp

definition
  is_well_ord :: "[i=>o,i,i]=>o" where
  \<comment> \<open>linear and wellfounded on \<open>A\<close>\<close>
  "is_well_ord(M,A,r) ==
        is_transitive(M,A,r) \<and> is_linear(M,A,r) \<and> is_wellfounded_on(M,A,r)"

lemma (in M_trivial) is_well_ord_iff_wellordered:
  "M(A)\<Longrightarrow> M(r) \<Longrightarrow>  is_well_ord(M,A, r) \<longleftrightarrow> wellordered(M, A, r)"
  using is_wellfounded_on_iff_wellfounded_on is_linear_iff_linear_rel
    is_transitive_iff_transitive_rel
  unfolding wellordered_def is_well_ord_def by simp

reldb_add relational "well_ord" "is_well_ord"
reldb_add functional "well_ord" "well_ord"
synthesize "is_well_ord" from_definition assuming "nonempty"
arity_theorem for "is_well_ord_fm"

\<comment> \<open>One keyword (functional or relational) means going
    from an absolute term to that kind of term\<close>
reldb_add relational "Order.pred" "pred_set"

\<comment> \<open>The following form (twice the same argument) is only correct
    when an "\_abs" theorem is available\<close>
reldb_add functional "Order.pred" "Order.pred"

(*
\<comment> \<open>Two keywords denote origin and destination, respectively\<close>
reldb_add functional relational "Ord" "ordinal"
*)

relativize functional "ord_iso" "ord_iso_rel" external
  \<comment> \<open>The following corresponds to "relativize functional relational"\<close>
relationalize "ord_iso_rel" "is_ord_iso"

context M_pre_cardinal_arith
begin

is_iff_rel for "ord_iso"
  using bij_rel_iff
  unfolding is_ord_iso_def ord_iso_rel_def
  by simp

rel_closed for "ord_iso"
  using ord_iso_separation unfolding ord_iso_rel_def
  by simp

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

synthesize "is_ord_iso" from_definition assuming "nonempty"

lemma is_lambda_iff_sats[iff_sats]:
  assumes is_F_iff_sats:
    "!!a0 a1 a2.
        [|a0\<in>Aa; a1\<in>Aa; a2\<in>Aa|]
        ==> is_F(a1, a0) \<longleftrightarrow> sats(Aa, is_F_fm, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows
    "nth(A, env) = Ab \<Longrightarrow>
    nth(r, env) = ra \<Longrightarrow>
    A \<in> nat \<Longrightarrow>
    r \<in> nat \<Longrightarrow>
    env \<in> list(Aa) \<Longrightarrow>
    is_lambda(##Aa, Ab, is_F, ra) \<longleftrightarrow> Aa, env \<Turnstile> lambda_fm(is_F_fm,A, r)"
  using sats_lambda_fm[OF assms, of A r] by simp

\<comment> \<open>same as @{thm sats_is_wfrec_fm}, but changing length assumptions to
    \<^term>\<open>0\<close> being in the model\<close>
lemma sats_is_wfrec_fm':
  assumes MH_iff_sats:
    "!!a0 a1 a2 a3 a4.
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|]
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
    "[|x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A); 0 \<in> A|]
       ==> sats(A, is_wfrec_fm(p,x,y,z), env) \<longleftrightarrow>
           is_wfrec(##A, MH, nth(x,env), nth(y,env), nth(z,env))"
  using MH_iff_sats [THEN iff_sym] nth_closed sats_is_recfun_fm
  by (simp add: is_wfrec_fm_def is_wfrec_def) blast

lemma is_wfrec_iff_sats'[iff_sats]:
  assumes MH_iff_sats:
    "!!a0 a1 a2 a3 a4.
        [|a0\<in>Aa; a1\<in>Aa; a2\<in>Aa; a3\<in>Aa; a4\<in>Aa|]
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(Aa, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
    "nth(x, env) = xx" "nth(y, env) = yy" "nth(z, env) = zz"
    "x \<in> nat" "y \<in> nat" "z \<in> nat" "env \<in> list(Aa)" "0 \<in> Aa"
  shows
    "is_wfrec(##Aa, MH, xx, yy, zz) \<longleftrightarrow> Aa, env \<Turnstile> is_wfrec_fm(p,x,y,z)"
  using assms(2-4) sats_is_wfrec_fm'[OF assms(1,5-9)] by simp

lemma is_wfrec_on_iff_sats[iff_sats]:
  assumes MH_iff_sats:
    "!!a0 a1 a2 a3 a4.
        [|a0\<in>Aa; a1\<in>Aa; a2\<in>Aa; a3\<in>Aa; a4\<in>Aa|]
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(Aa, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
    "nth(x, env) = xx \<Longrightarrow>
    nth(y, env) = yy \<Longrightarrow>
    nth(z, env) = zz \<Longrightarrow>
    x \<in> nat \<Longrightarrow>
    y \<in> nat \<Longrightarrow>
    z \<in> nat \<Longrightarrow>
    env \<in> list(Aa) \<Longrightarrow>
    0 \<in> Aa \<Longrightarrow> is_wfrec_on(##Aa, MH, aa,xx, yy, zz) \<longleftrightarrow> Aa, env \<Turnstile> is_wfrec_fm(p,x,y,z)"
  using assms sats_is_wfrec_fm'[OF assms] unfolding is_wfrec_on_def by simp

lemma trans_on_iff_trans: "trans[A](r) \<longleftrightarrow> trans(r \<inter> A\<times>A)"
  unfolding trans_on_def trans_def by auto

lemma trans_on_subset: "trans[A](r) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> trans[B](r)"
  unfolding trans_on_def
  by auto

lemma relation_Int: "relation(r \<inter> B\<times>B)"
  unfolding relation_def
  by auto

text\<open>Discipline for \<^term>\<open>ordermap\<close>\<close>
relativize functional "ordermap" "ordermap_rel" external
relationalize "ordermap_rel" "is_ordermap"

context M_pre_cardinal_arith
begin

lemma wfrec_on_pred_eq:
  assumes "r \<in> Pow(A\<times>A)" "M(A)" "M(r)"
  shows "wfrec[A](r, x, \<lambda>x f. f `` Order.pred(A, x, r)) = wfrec(r, x, \<lambda>x f. f `` Order.pred(A, x, r))"
proof -
  from \<open>r \<in> Pow(A\<times>A)\<close>
  have "r \<inter> A\<times>A = r" by auto
  moreover from this
  show ?thesis
    unfolding wfrec_on_def by simp
qed

lemma wfrec_on_pred_closed:
  assumes "wf[A](r)" "trans[A](r)" "r \<in> Pow(A\<times>A)" "M(A)" "M(r)" "x \<in> A"
  shows "M(wfrec(r, x, \<lambda>x f. f `` Order.pred(A, x, r)))"
proof -
  from assms
  have "wfrec[A](r, x, \<lambda>x f. f `` Order.pred(A, x, r)) = wfrec(r, x, \<lambda>x f. f `` Order.pred(A, x, r))"
    using wfrec_on_pred_eq by simp
  moreover from assms
  have "M(wfrec(r, x, \<lambda>x f. f `` Order.pred(A, x, r)))"
    using wfrec_pred_replacement wf_on_imp_wf trans_on_imp_trans subset_Sigma_imp_relation
    by (rule_tac MH="\<lambda>x f b. \<exists>a[M]. image(M, f, a, b) \<and> pred_set(M, A, x, r, a)" in trans_wfrec_closed)
      (auto dest:transM simp:relation2_def)
  ultimately
  show ?thesis by simp
qed

lemma wfrec_on_pred_closed':
  assumes "wf[A](r)" "trans[A](r)" "r \<in> Pow(A\<times>A)" "M(A)" "M(r)" "x \<in> A"
  shows "M(wfrec[A](r, x, \<lambda>x f. f `` Order.pred(A, x, r)))"
  using assms wfrec_on_pred_closed wfrec_on_pred_eq by simp


lemma ordermap_rel_closed':
  assumes "wf[A](r)" "trans[A](r)" "r \<in> Pow(A\<times>A)" "M(A)" "M(r)"
  shows "M(ordermap_rel(M, A, r))"
proof -
  from assms
  have "r \<inter> A\<times>A = r" by auto
  with assms have "wf(r)" "trans(r)" "relation(r)"
    unfolding wf_on_def using trans_on_iff_trans relation_def by auto
  then
  have 1:"\<And> x z . M(x) \<Longrightarrow> M(z) \<Longrightarrow>
    (\<exists>y[M]. pair(M, x, y, z) \<and> is_wfrec(M, \<lambda>x f z. z = f `` Order.pred(A, x, r), r, x, y))
      \<longleftrightarrow>
    z = <x,wfrec(r,x,\<lambda>x f. f `` Order.pred(A, x, r))>"
    using trans_wfrec_abs[of r,where
        H="\<lambda>x f. f `` Order.pred(A, x, r)" and
        MH="\<lambda>x f z . z= f `` Order.pred(A, x, r)",simplified] assms
      wfrec_pred_replacement unfolding relation2_def
    by auto
  then
  have "strong_replacement(M,\<lambda>x z. z = <x,wfrec(r,x,\<lambda>x f. f `` Order.pred(A, x, r))>)"
    using strong_replacement_cong[of M,OF 1,THEN iffD1,OF _ _
        wfrec_pred_replacement[unfolded wfrec_replacement_def]] assms by simp
  then show ?thesis
    using Pow_iff assms
    unfolding ordermap_rel_def
    apply(subst lam_cong[OF refl wfrec_on_pred_eq],simp_all)
    using wfrec_on_pred_closed lam_closed
    by simp
qed

lemma ordermap_rel_closed[intro,simp]:
  assumes "wf[A](r)" "trans[A](r)" "r \<in> Pow(A\<times>A)"
  shows "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(ordermap_rel(M, A, r))"
  using ordermap_rel_closed' assms by simp

lemma is_ordermap_iff:
  assumes "r \<in> Pow(A\<times>A)" "wf[A](r)" "trans[A](r)"
    "M(A)" "M(r)" "M(res)"
  shows "is_ordermap(M, A, r, res) \<longleftrightarrow> res = ordermap_rel(M, A, r)"
proof -
  from \<open>r \<in> Pow(A\<times>A)\<close>
  have "r \<inter> A\<times>A = r" by auto
  with assms have 1:"wf(r)" "trans(r)" "relation(r)"
    unfolding wf_on_def using trans_on_iff_trans relation_def by auto
  from assms
  have "r \<inter> A\<times>A = r" "r \<subseteq> A\<times>A" "<x,y> \<in> r \<Longrightarrow> x\<in>A \<and> y\<in>A" for x y by auto
  then
  show ?thesis
    using ordermap_rel_closed[of r A] assms wfrec_on_pred_closed wfrec_pred_replacement 1
    unfolding is_ordermap_def ordermap_rel_def
    apply (rule_tac lambda_abs2)
       apply (simp_all add:Relation1_def)
     apply clarify
     apply (rule trans_wfrec_on_abs)
               apply (auto dest:transM simp add: relation_Int relation2_def)
    by(rule_tac wfrec_on_pred_closed'[of A r],auto)
qed

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

synthesize "is_ordermap" from_definition assuming "nonempty"

text\<open>Discipline for \<^term>\<open>ordertype\<close>\<close>
relativize functional "ordertype" "ordertype_rel" external
relationalize "ordertype_rel" "is_ordertype"

context M_pre_cardinal_arith
begin

lemma is_ordertype_iff:
  assumes "r \<in> Pow(A\<times>A)" "wf[A](r)" "trans[A](r)"
  shows "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(res) \<Longrightarrow> is_ordertype(M, A, r, res) \<longleftrightarrow> res = ordertype_rel(M, A, r)"
  using assms is_ordermap_iff[of r A] trans_on_iff_trans
    ordermap_rel_closed[of A r]
  unfolding is_ordertype_def ordertype_rel_def wf_on_def by simp

lemma is_ordertype_iff':
  assumes "r \<in> Pow_rel(M,A\<times>A)" "well_ord(A,r)"
  shows "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(res) \<Longrightarrow> is_ordertype(M, A, r, res) \<longleftrightarrow> res = ordertype_rel(M, A, r)"
  using assms is_ordertype_iff Pow_rel_char
  unfolding well_ord_def part_ord_def tot_ord_def by simp

lemma is_ordertype_iff'':
  assumes "well_ord(A,r)" "r\<subseteq>A\<times>A"
  shows "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(res) \<Longrightarrow> is_ordertype(M, A, r, res) \<longleftrightarrow> res = ordertype_rel(M, A, r)"
  using assms is_ordertype_iff
  unfolding well_ord_def part_ord_def tot_ord_def by simp

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

synthesize "is_ordertype" from_definition assuming "nonempty"

\<comment> \<open>NOTE: not quite the same as \<^term>\<open>jump_cardinal\<close>,
    note \<^term>\<open>Pow(X*X)\<close>.\<close>
definition
  jump_cardinal' :: "i\<Rightarrow>i"  where
  "jump_cardinal'(K) \<equiv>
         \<Union>X\<in>Pow(K). {z. r \<in> Pow(X*X), well_ord(X,r) & z = ordertype(X,r)}"

relativize functional "jump_cardinal'" "jump_cardinal'_rel" external
relationalize "jump_cardinal'_rel" "is_jump_cardinal'"
synthesize "is_jump_cardinal'" from_definition assuming "nonempty"
arity_theorem for "is_jump_cardinal'_fm"
definition jump_cardinal_body' where
  "jump_cardinal_body'(X) \<equiv> {z . r \<in> Pow(X \<times> X),  well_ord(X, r) \<and> z = ordertype(X, r)}"

relativize functional "jump_cardinal_body'" "jump_cardinal_body'_rel" external
relationalize "jump_cardinal_body'_rel" "is_jump_cardinal_body'"
synthesize "is_jump_cardinal_body'" from_definition assuming "nonempty"
arity_theorem for "is_jump_cardinal_body'_fm"

context M_pre_cardinal_arith
begin

lemma ordertype_rel_closed':
  assumes "wf[A](r)" "trans[A](r)" "r \<in> Pow(A\<times>A)" "M(r)" "M(A)"
  shows "M(ordertype_rel(M,A,r))"
  unfolding ordertype_rel_def
  using ordermap_rel_closed image_closed assms by simp

lemma ordertype_rel_closed[intro,simp]:
  assumes "well_ord(A,r)" "r \<in> Pow_rel(M,A\<times>A)" "M(A)"
  shows "M(ordertype_rel(M,A,r))"
  using assms Pow_rel_char ordertype_rel_closed'
  unfolding well_ord_def tot_ord_def part_ord_def
  by simp

lemma ordertype_rel_abs:
  assumes "wellordered(M,X,r)" "M(X)" "M(r)"
  shows "ordertype_rel(M,X,r) = ordertype(X,r)"
  using assms ordertypes_are_absolute[of X r]
  unfolding ordertype_def ordertype_rel_def ordermap_rel_def ordermap_def
  by simp

lemma univalent_aux1: "M(X) \<Longrightarrow> univalent(M,Pow_rel(M,X\<times>X),
  \<lambda>r z. M(z) \<and> M(r) \<and> r\<in>Pow_rel(M,X\<times>X) \<and> is_well_ord(M, X, r) \<and> is_ordertype(M, X, r, z))"
  using is_well_ord_iff_wellordered
    is_ordertype_iff[of _ X]
    trans_on_subset[OF well_ord_is_trans_on]
    well_ord_is_wf[THEN wf_on_subset_A] mem_Pow_rel_abs
  unfolding univalent_def
  by (simp)

lemma jump_cardinal_body_eq :
  "M(X) \<Longrightarrow> jump_cardinal_body(M,X) = jump_cardinal_body'_rel(M,X)"
  unfolding jump_cardinal_body_def jump_cardinal_body'_rel_def
  using ordertype_rel_abs
  by auto

end \<comment> \<open>\<^locale>\<open>M_pre_cardinal_arith\<close>\<close>

context M_cardinal_arith
begin
lemma jump_cardinal_closed_aux1:
  assumes "M(X)"
  shows
    "M(jump_cardinal_body(M,X))"
  unfolding jump_cardinal_body_def
  using \<open>M(X)\<close> ordertype_rel_abs
    ordertype_replacement[OF \<open>M(X)\<close>] univalent_aux1[OF \<open>M(X)\<close>]
    strong_replacement_closed[where A="Pow\<^bsup>M\<^esup>(X \<times> X)" and
      P="\<lambda> r z . M(z) \<and> M(r) \<and>  r \<in> Pow\<^bsup>M\<^esup>(X \<times> X) \<and> well_ord(X, r) \<and> z = ordertype(X, r)"]
  by auto

lemma univalent_jc_body: "M(X) \<Longrightarrow> univalent(M,X,\<lambda> x z . M(z) \<and> M(x) \<and> z = jump_cardinal_body(M,x))"
  using transM[of _ X]  jump_cardinal_closed_aux1 by auto

lemma jump_cardinal_body_closed:
  assumes "M(K)"
  shows "M({a . X \<in> Pow\<^bsup>M\<^esup>(K), M(a) \<and> M(X) \<and> a = jump_cardinal_body(M,X)})"
  using assms univalent_jc_body jump_cardinal_closed_aux1 strong_replacement_jc_body
  by simp

rel_closed for "jump_cardinal'"
  using jump_cardinal_body_closed ordertype_rel_abs
  unfolding jump_cardinal_body_def jump_cardinal'_rel_def
  by simp

is_iff_rel for "jump_cardinal'"
proof -
  assume types: "M(K)" "M(res)"
  have "is_Replace(M, Pow_rel(M,X\<times>X), \<lambda>r z. M(z) \<and> M(r) \<and> is_well_ord(M, X, r) \<and> is_ordertype(M, X, r, z),
   a) \<longleftrightarrow> a = {z . r \<in> Pow_rel(M,X\<times>X), M(z) \<and> M(r) \<and> is_well_ord(M,X,r) \<and> is_ordertype(M, X, r, z)}"
    if "M(X)" "M(a)" for X a
    using that univalent_aux1
    by (rule_tac Replace_abs) (simp_all)
  then
  have "is_Replace(M, Pow_rel(M,X\<times>X), \<lambda>r z. M(z) \<and> M(r) \<and> is_well_ord(M, X, r) \<and> is_ordertype(M, X, r, z),
   a) \<longleftrightarrow> a = {z . r \<in> Pow_rel(M,X\<times>X), M(z) \<and> M(r) \<and> well_ord(X, r) \<and> z = ordertype_rel(M, X, r)}"
    if "M(X)" "M(a)" for X a
    using that univalent_aux1 is_ordertype_iff' is_well_ord_iff_wellordered well_ord_abs by auto
  moreover
  have "is_Replace(M, d, \<lambda>X a. M(a) \<and> M(X) \<and>
      a = {z . r \<in> Pow\<^bsup>M\<^esup>(X \<times> X), M(z) \<and> M(r) \<and> well_ord(X, r) \<and> z = ordertype(X, r)}, e)
    \<longleftrightarrow>
    e ={a . X \<in> d, M(a) \<and> M(X) \<and> a = jump_cardinal_body(M,X)}"
    if "M(d)" "M(e)" for d e
    using jump_cardinal_closed_aux1 that
    unfolding jump_cardinal_body_def
    by (rule_tac Replace_abs) simp_all
  ultimately
  show ?thesis
    using Pow_rel_iff jump_cardinal_body_closed[of K] ordertype_rel_abs
    unfolding is_jump_cardinal'_def jump_cardinal'_rel_def jump_cardinal_body_def
    by (simp add: types)
qed

end

context M_cardinal_arith
begin

lemma (in M_ordertype) ordermap_closed[intro,simp]:
  assumes "wellordered(M,A,r)" and types:"M(A)" "M(r)"
  shows "M(ordermap(A,r))"
proof -
  note assms
  moreover from this
  obtain i f where "Ord(i)" "f \<in> ord_iso(A, r, i, Memrel(i))"
    "M(i)" "M(f)" using ordertype_exists by blast
  moreover from calculation
  have "i = ordertype(A,r)" using ordertypes_are_absolute by force
  moreover from calculation
  have "ordermap(A,r) \<in> ord_iso(A, r, i, Memrel(i))"
    using ordertype_ord_iso by simp
  ultimately
  have "f = ordermap(A,r)" using well_ord_iso_unique by fastforce
  with \<open>M(f)\<close>
  show ?thesis by simp
qed


(*A general fact about ordermap*)
lemma ordermap_eqpoll_pred:
  "[| well_ord(A,r);  x \<in> A ; M(A);M(r);M(x)|] ==> ordermap(A,r)`x \<approx>\<^bsup>M\<^esup> Order.pred(A,x,r)"
  apply (simp add: def_eqpoll_rel)
  apply (rule rexI)
   apply (simp add: ordermap_eq_image well_ord_is_wf)
   apply (erule ordermap_bij [THEN bij_is_inj, THEN restrict_bij,
        THEN bij_converse_bij])
   apply (rule pred_subset, simp)
  done

text\<open>Kunen: "each \<^term>\<open>\<langle>x,y\<rangle> \<in> K \<times> K\<close> has no more than \<^term>\<open>z \<times> z\<close> predecessors..." (page 29)\<close>
lemma ordermap_csquare_le:
  assumes K: "Limit(K)" and x: "x<K" and y: " y<K"
    and types: "M(K)" "M(x)" "M(y)"
  shows "|ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>|\<^bsup>M\<^esup> \<le> |succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<otimes>\<^bsup>M\<^esup> |succ(succ(x \<union> y))|\<^bsup>M\<^esup>"
  using types
proof (simp add: cmult_rel_def, rule_tac well_ord_lepoll_rel_imp_cardinal_rel_le)
  let ?z="succ(x \<union> y)"
  show "well_ord(|succ(?z)|\<^bsup>M\<^esup> \<times> |succ(?z)|\<^bsup>M\<^esup>,
                 rmult(|succ(?z)|\<^bsup>M\<^esup>, Memrel(|succ(?z)|\<^bsup>M\<^esup>), |succ(?z)|\<^bsup>M\<^esup>, Memrel(|succ(?z)|\<^bsup>M\<^esup>)))"
    by (blast intro: well_ord_Memrel well_ord_rmult types)
next
  let ?z="succ(x \<union> y)"
  have zK: "?z<K" using x y K
    by (blast intro: Un_least_lt Limit_has_succ)
  hence oz: "Ord(?z)" by (elim ltE)
  from assms
  have Mom:"M(ordermap(K \<times> K, csquare_rel(K)))"
    using well_ord_csquare Limit_is_Ord by fastforce
  then
  have "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim>\<^bsup>M\<^esup> ordermap(K \<times> K, csquare_rel(K)) ` \<langle>?z,?z\<rangle>"
    by (blast intro: ordermap_z_lt leI le_imp_lepoll_rel K x y types)
  also have "... \<approx>\<^bsup>M\<^esup>  Order.pred(K \<times> K, \<langle>?z,?z\<rangle>, csquare_rel(K))"
  proof (rule ordermap_eqpoll_pred)
    show "well_ord(K \<times> K, csquare_rel(K))" using K
      by (rule Limit_is_Ord [THEN well_ord_csquare])
  next
    show "\<langle>?z, ?z\<rangle> \<in> K \<times> K" using zK
      by (blast intro: ltD)
  qed (simp_all add:types)
  also have "...  \<lesssim>\<^bsup>M\<^esup> succ(?z) \<times> succ(?z)" using zK
    by (rule_tac pred_csquare_subset [THEN subset_imp_lepoll_rel]) (simp_all add:types)
  also have "... \<approx>\<^bsup>M\<^esup> |succ(?z)|\<^bsup>M\<^esup> \<times> |succ(?z)|\<^bsup>M\<^esup>" using oz
    by (blast intro: prod_eqpoll_rel_cong Ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym types)
  finally show "ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle> \<lesssim>\<^bsup>M\<^esup> |succ(?z)|\<^bsup>M\<^esup> \<times> |succ(?z)|\<^bsup>M\<^esup>"
    by (simp_all add:types Mom)
  from Mom
  show "M(ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x, y\<rangle>)" by (simp_all add:types)
qed (simp_all add:types)

text\<open>Kunen: "... so the order type is \<open>\<le>\<close> K"\<close>
lemma ordertype_csquare_le_M:
  assumes IK: "InfCard\<^bsup>M\<^esup>(K)" and eq: "\<And>y. y\<in>K \<Longrightarrow> InfCard\<^bsup>M\<^esup>(y) \<Longrightarrow> M(y) \<Longrightarrow> y \<otimes>\<^bsup>M\<^esup> y = y"
    \<comment> \<open>Note the weakened hypothesis @{thm eq}\<close>
    and types: "M(K)"
  shows "ordertype(K*K, csquare_rel(K)) \<le> K"
proof -
  have  CK: "Card\<^bsup>M\<^esup>(K)" using IK by (rule_tac InfCard_rel_is_Card_rel) (simp_all add:types)
  hence OK: "Ord(K)"  by (rule Card_rel_is_Ord) (simp_all add:types)
  moreover have "Ord(ordertype(K \<times> K, csquare_rel(K)))" using OK
    by (rule well_ord_csquare [THEN Ord_ordertype])
  ultimately show ?thesis
  proof (rule all_lt_imp_le)
    fix i
    assume i:"i < ordertype(K \<times> K, csquare_rel(K))"
    hence Oi: "Ord(i)" by (elim ltE)
    obtain x y where x: "x \<in> K" and y: "y \<in> K"
      and ieq: "i = ordermap(K \<times> K, csquare_rel(K)) ` \<langle>x,y\<rangle>"
      using i by (auto simp add: ordertype_unfold elim: ltE)
    hence xy: "Ord(x)" "Ord(y)" "x < K" "y < K" using OK
      by (blast intro: Ord_in_Ord ltI)+
    hence ou: "Ord(x \<union> y)"
      by (simp)
    from OK types
    have "M(ordertype(K \<times> K, csquare_rel(K)))"
      using well_ord_csquare by fastforce
    with i x y types
    have types': "M(K)" "M(i)" "M(x)" "M(y)"
      using types by (auto dest:transM ltD)
    show "i < K"
    proof (rule Card_rel_lt_imp_lt [OF _ Oi CK])
      have "|i|\<^bsup>M\<^esup> \<le> |succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<otimes>\<^bsup>M\<^esup> |succ(succ(x \<union> y))|\<^bsup>M\<^esup>" using IK xy
        by (auto simp add: ieq types intro: InfCard_rel_is_Limit [THEN ordermap_csquare_le] types')
      moreover have "|succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<otimes>\<^bsup>M\<^esup> |succ(succ(x \<union> y))|\<^bsup>M\<^esup> < K"
      proof (cases rule: Ord_linear2 [OF ou Ord_nat])
        assume "x \<union> y < nat"
        hence "|succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<otimes>\<^bsup>M\<^esup> |succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<in> nat"
          by (simp add: lt_def nat_cmult_rel_eq_mult nat_succI
              nat_into_Card_rel [THEN Card_rel_cardinal_rel_eq] types')
        also have "... \<subseteq> K" using IK
          by (simp add: InfCard_rel_def le_imp_subset types)
        finally show "|succ(succ(x \<union> y))|\<^bsup>M\<^esup> \<otimes>\<^bsup>M\<^esup> |succ(succ(x \<union> y))|\<^bsup>M\<^esup> < K"
          by (simp add: ltI OK)
      next
        assume natxy: "nat \<le> x \<union> y"
        hence seq: "|succ(succ(x \<union> y))|\<^bsup>M\<^esup> = |x \<union> y|\<^bsup>M\<^esup>" using xy
          by (simp add: le_imp_subset nat_succ_eqpoll_rel [THEN cardinal_rel_cong] le_succ_iff types')
        also have "... < K" using xy
          by (simp add: Un_least_lt Ord_cardinal_rel_le [THEN lt_trans1] types')
        finally have "|succ(succ(x \<union> y))|\<^bsup>M\<^esup> < K" .
        moreover have "InfCard\<^bsup>M\<^esup>(|succ(succ(x \<union> y))|\<^bsup>M\<^esup>)" using xy natxy
          by (simp add: seq InfCard_rel_def nat_le_cardinal_rel types')
        ultimately show ?thesis by (simp add: eq ltD types')
      qed
      ultimately show "|i|\<^bsup>M\<^esup> < K" by (blast intro: lt_trans1)
    qed (simp_all add:types')
  qed
qed

(*Main result: Kunen's Theorem 10.12*)
lemma InfCard_rel_csquare_eq:
  assumes IK: "InfCard\<^bsup>M\<^esup>(K)" and
    types: "M(K)"
  shows "K \<otimes>\<^bsup>M\<^esup> K = K"
proof -
  have  OK: "Ord(K)" using IK by (simp add: Card_rel_is_Ord InfCard_rel_is_Card_rel types)
  from OK assms
  show "K \<otimes>\<^bsup>M\<^esup> K = K"
  proof (induct rule: trans_induct)
    case (step i)
    note types = \<open>M(K)\<close> \<open>M(i)\<close>
    show "i \<otimes>\<^bsup>M\<^esup> i = i"
    proof (rule le_anti_sym)
      from step types
      have Mot:"M(ordertype(i \<times> i, csquare_rel(i)))" "M(ordermap(i \<times> i, csquare_rel(i)))"
        using well_ord_csquare Limit_is_Ord by simp_all
      then
      have "|i \<times> i|\<^bsup>M\<^esup> = |ordertype(i \<times> i, csquare_rel(i))|\<^bsup>M\<^esup>"
        by (rule_tac cardinal_rel_cong,
            simp_all add: step.hyps well_ord_csquare [THEN ordermap_bij, THEN bij_imp_eqpoll_rel] types)
      with Mot
      have "i \<otimes>\<^bsup>M\<^esup> i \<le> ordertype(i \<times> i, csquare_rel(i))"
        by (simp add: step.hyps cmult_rel_def Ord_cardinal_rel_le well_ord_csquare [THEN Ord_ordertype] types)
      moreover
      have "ordertype(i \<times> i, csquare_rel(i)) \<le> i" using step
        by (rule_tac ordertype_csquare_le_M) (simp add: types)
      ultimately show "i \<otimes>\<^bsup>M\<^esup> i \<le> i" by (rule le_trans)
    next
      show "i \<le> i \<otimes>\<^bsup>M\<^esup> i" using step
        by (blast intro: cmult_rel_square_le InfCard_rel_is_Card_rel)
    qed
  qed
qed


(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
lemma well_ord_InfCard_rel_square_eq:
  assumes r: "well_ord(A,r)" and I: "InfCard\<^bsup>M\<^esup>(|A|\<^bsup>M\<^esup>)" and
    types: "M(A)" "M(r)"
  shows "A \<times> A \<approx>\<^bsup>M\<^esup> A"
proof -
  have "A \<times> A \<approx>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup> \<times> |A|\<^bsup>M\<^esup>"
    by (blast intro: prod_eqpoll_rel_cong well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym r types)
  also have "... \<approx>\<^bsup>M\<^esup> A"
  proof (rule well_ord_cardinal_rel_eqE [OF _ r])
    show "well_ord(|A|\<^bsup>M\<^esup> \<times> |A|\<^bsup>M\<^esup>, rmult(|A|\<^bsup>M\<^esup>, Memrel(|A|\<^bsup>M\<^esup>), |A|\<^bsup>M\<^esup>, Memrel(|A|\<^bsup>M\<^esup>)))"
      by (blast intro: well_ord_rmult well_ord_Memrel r types)
  next
    show "||A|\<^bsup>M\<^esup> \<times> |A|\<^bsup>M\<^esup>|\<^bsup>M\<^esup> = |A|\<^bsup>M\<^esup>" using InfCard_rel_csquare_eq I
      by (simp add: cmult_rel_def types)
  qed (simp_all add:types)
  finally show ?thesis by (simp_all add:types)
qed

lemma InfCard_rel_square_eqpoll:
  assumes "InfCard\<^bsup>M\<^esup>(K)" and types:"M(K)" shows "K \<times> K \<approx>\<^bsup>M\<^esup> K"
  using assms
  apply (rule_tac well_ord_InfCard_rel_square_eq)
     apply (erule InfCard_rel_is_Card_rel [THEN Card_rel_is_Ord, THEN well_ord_Memrel])
      apply (simp_all add: InfCard_rel_is_Card_rel [THEN Card_rel_cardinal_rel_eq] types)
  done

lemma Inf_Card_rel_is_InfCard_rel: "[| Card\<^bsup>M\<^esup>(i); ~ Finite_rel(M,i) ; M(i) |] ==> InfCard\<^bsup>M\<^esup>(i)"
  by (simp add: InfCard_rel_def Card_rel_is_Ord [THEN nat_le_infinite_Ord])

subsubsection\<open>Toward's Kunen's Corollary 10.13 (1)\<close>

lemma InfCard_rel_le_cmult_rel_eq: "[| InfCard\<^bsup>M\<^esup>(K);  L \<le> K;  0<L; M(K) ; M(L) |] ==> K \<otimes>\<^bsup>M\<^esup> L = K"
  apply (rule le_anti_sym)
   prefer 2
   apply (erule ltE, blast intro: cmult_rel_le_self InfCard_rel_is_Card_rel)
  apply (frule InfCard_rel_is_Card_rel [THEN Card_rel_is_Ord, THEN le_refl]) prefer 3
    apply (rule cmult_rel_le_mono [THEN le_trans], assumption+)
    apply (simp_all add: InfCard_rel_csquare_eq)
  done

(*Corollary 10.13 (1), for cardinal multiplication*)
lemma InfCard_rel_cmult_rel_eq: "[| InfCard\<^bsup>M\<^esup>(K);  InfCard\<^bsup>M\<^esup>(L); M(K) ; M(L) |] ==> K \<otimes>\<^bsup>M\<^esup> L = K \<union> L"
  apply (rule_tac i = K and j = L in Ord_linear_le)
     apply (typecheck add: InfCard_rel_is_Card_rel Card_rel_is_Ord)
   apply (rule cmult_rel_commute [THEN ssubst]) prefer 3
     apply (rule Un_commute [THEN ssubst])
     apply (simp_all add: InfCard_rel_is_Limit [THEN Limit_has_0] InfCard_rel_le_cmult_rel_eq
      subset_Un_iff2 [THEN iffD1] le_imp_subset)
  done

lemma InfCard_rel_cdouble_eq: "InfCard\<^bsup>M\<^esup>(K) \<Longrightarrow> M(K) \<Longrightarrow>  K \<oplus>\<^bsup>M\<^esup> K = K"
  apply (simp add: cmult_rel_2 [symmetric] InfCard_rel_is_Card_rel cmult_rel_commute)
  apply (simp add: InfCard_rel_le_cmult_rel_eq InfCard_rel_is_Limit Limit_has_0 Limit_has_succ)
  done

(*Corollary 10.13 (1), for cardinal addition*)
lemma InfCard_rel_le_cadd_rel_eq: "[| InfCard\<^bsup>M\<^esup>(K);  L \<le> K ; M(K) ; M(L)|] ==> K \<oplus>\<^bsup>M\<^esup> L = K"
  apply (rule le_anti_sym)
   prefer 2
   apply (erule ltE, blast intro: cadd_rel_le_self InfCard_rel_is_Card_rel)
  apply (frule InfCard_rel_is_Card_rel [THEN Card_rel_is_Ord, THEN le_refl]) prefer 3
    apply (rule cadd_rel_le_mono [THEN le_trans], assumption+)
    apply (simp_all add: InfCard_rel_cdouble_eq)
  done

lemma InfCard_rel_cadd_rel_eq: "[| InfCard\<^bsup>M\<^esup>(K);  InfCard\<^bsup>M\<^esup>(L); M(K) ; M(L) |] ==> K \<oplus>\<^bsup>M\<^esup> L = K \<union> L"
  apply (rule_tac i = K and j = L in Ord_linear_le)
     apply (typecheck add: InfCard_rel_is_Card_rel Card_rel_is_Ord)
   apply (rule cadd_rel_commute [THEN ssubst]) prefer 3
     apply (rule Un_commute [THEN ssubst])
     apply (simp_all add: InfCard_rel_le_cadd_rel_eq subset_Un_iff2 [THEN iffD1] le_imp_subset)
  done

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

end \<comment> \<open>\<^locale>\<open>M_cardinal_arith\<close>\<close>

subsection\<open>For Every Cardinal Number There Exists A Greater One\<close>

text\<open>This result is Kunen's Theorem 10.16, which would be trivial using AC\<close>

locale M_cardinal_arith_jump = M_cardinal_arith + M_ordertype
begin

lemma well_ord_restr: "well_ord(X, r) \<Longrightarrow> well_ord(X, r \<inter> X\<times>X)"
proof -
  have "r \<inter> X\<times>X \<inter> X\<times>X = r \<inter> X\<times>X" by auto
  moreover
  assume "well_ord(X, r)"
  ultimately
  show ?thesis
    unfolding well_ord_def tot_ord_def part_ord_def linear_def
      irrefl_def wf_on_def
    by simp_all (simp only: trans_on_def, blast)
qed

lemma ordertype_restr_eq :
  assumes "well_ord(X,r)"
  shows "ordertype(X, r) = ordertype(X, r \<inter> X\<times>X)"
  using ordermap_restr_eq assms unfolding ordertype_def
  by simp

lemma def_jump_cardinal_rel_aux:
  "X \<in> Pow\<^bsup>M\<^esup>(K) \<Longrightarrow> well_ord(X, w) \<Longrightarrow> M(K) \<Longrightarrow>
  {z . r \<in> Pow\<^bsup>M\<^esup>(X \<times> X), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)} =
  {z . r \<in> Pow\<^bsup>M\<^esup>(K \<times> K), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)}"
proof(rule,auto simp:Pow_rel_char dest:transM)
  let ?L="{z . r \<in> Pow\<^bsup>M\<^esup>(X \<times> X), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)}"
  let ?R="{z . r \<in> Pow\<^bsup>M\<^esup>(K \<times> K), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)}"
  show "ordertype(X, r) \<in> {y . x \<in> {x \<in> Pow(X \<times> X) . M(x)}, M(y) \<and> well_ord(X, x) \<and> y = ordertype(X, x)}"
    if "M(K)" "M(r)" "r\<subseteq>K\<times>K" "X\<subseteq>K" "M(X)" "well_ord(X,r)" for r
  proof -
    from that
    have "ordertype(X,r) = ordertype(X,r\<inter>X\<times>X)" "(r\<inter>X\<times>X)\<subseteq>X\<times>X" "M(r\<inter>X\<times>X)"
      "well_ord(X,r\<inter>X\<times>X)" "wellordered(M,X,r\<inter>X\<times>X)"
      using well_ord_restr ordertype_restr_eq by auto
    moreover from this
    have "ordertype(X,r\<inter>X\<times>X) \<in> ?L"
      using that Pow_rel_char
        ReplaceI[of "\<lambda> z r . M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)" "ordertype(X,r\<inter>X\<times>X)"]
      by auto
    ultimately
    show ?thesis using Pow_rel_char by auto
  qed
qed

lemma def_jump_cardinal_rel:
  assumes "M(K)"
  shows "jump_cardinal'_rel(M,K) =
         (\<Union>X\<in>Pow_rel(M,K). {z. r \<in> Pow_rel(M,K*K), well_ord(X,r) & z = ordertype(X,r)})"
proof -
  have "M({z . r \<in> Pow\<^bsup>M\<^esup>(X \<times> X), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)})"
    (is "M(Replace(_,?P))")
    if "M(X)" for X
    using that jump_cardinal_closed_aux1[of X] ordertype_rel_abs[of X]
      jump_cardinal_body_def
    by (subst Replace_cong[where P="?P"
          and Q="\<lambda>r z. M(z) \<and> M(r) \<and> well_ord(X, r) \<and> z = ordertype_rel(M,X,r)",
          OF refl, of "Pow\<^bsup>M\<^esup>(X \<times> X)"]) (auto dest:transM)
  then
  have "M({z . r \<in> Pow\<^bsup>M\<^esup>(Y \<times> Y), M(z) \<and> well_ord(X, r) \<and> z = ordertype(X, r)})"
    if "M(Y)" "M(X)" "X \<in> Pow\<^bsup>M\<^esup>(Y)" "well_ord(X,r)" for Y X r
    using that def_jump_cardinal_rel_aux[of X Y r, symmetric] by simp
  moreover from \<open>M(K)\<close>
  have "R \<in> Pow\<^bsup>M\<^esup>(X \<times> X) \<Longrightarrow> X \<in> Pow\<^bsup>M\<^esup>(K) \<Longrightarrow> R \<in> Pow\<^bsup>M\<^esup>(K \<times> K)"
    for X R using mem_Pow_rel_abs transM[OF _ Pow_rel_closed, of R "X\<times>X"]
      transM[OF _ Pow_rel_closed, of X K] by auto
  ultimately
  show ?thesis
    using assms is_ordertype_iff is_well_ord_iff_wellordered
      ordertype_rel_abs transM[of _ "Pow\<^bsup>M\<^esup>(K)"] transM[of _ "Pow\<^bsup>M\<^esup>(K\<times>K)"]
      def_jump_cardinal_rel_aux
    unfolding jump_cardinal'_rel_def
    apply (intro equalityI)
     apply (auto dest:transM)
     apply (rename_tac X R)
     apply (rule_tac x=X in bexI)
      apply (rule_tac x=R in ReplaceI)
        apply auto
    apply (rule_tac x="{y . xa \<in> Pow\<^bsup>M\<^esup>(K \<times> K), M(y) \<and> M(xa) \<and> well_ord(X, xa) \<and> y = ordertype(X, xa)}" in bexI)
     apply auto
    by (rule_tac x=X in ReplaceI) auto
qed

notation jump_cardinal'_rel (\<open>jump'_cardinal'_rel\<close>)

lemma Ord_jump_cardinal_rel: "M(K) \<Longrightarrow> Ord(jump_cardinal_rel(M,K))"
  apply (unfold def_jump_cardinal_rel)
  apply (rule Ord_is_Transset [THEN [2] OrdI])
   prefer 2 apply (blast intro!: Ord_ordertype)
  apply (unfold Transset_def)
  apply (safe del: subsetI)
  apply (subst ordertype_pred_unfold, simp, safe)
  apply (rule UN_I)
   apply (rule_tac [2] ReplaceI)
     prefer 4 apply (blast intro: well_ord_subset elim!: predE, simp_all)
   prefer 2 apply (blast intro: well_ord_subset elim!: predE)
proof -
  fix X r xb
  assume "M(K)" "X \<in> Pow\<^bsup>M\<^esup>(K)" "r \<in> Pow\<^bsup>M\<^esup>(K \<times> K)" "well_ord(X, r)" "xb \<in> X"
  moreover from this
  have "M(X)" "M(r)"
    using cartprod_closed trans_Pow_rel_closed by auto
  moreover from this
  have "M(xb)" using transM[OF \<open>xb\<in>X\<close>] by simp
  ultimately
  show "Order.pred(X, xb, r) \<in> Pow\<^bsup>M\<^esup>(K)"
    using def_Pow_rel by (auto dest:predE)
qed

declare conj_cong [cong del]
  \<comment> \<open>incompatible with some of the proofs of the original theory\<close>

lemma jump_cardinal_rel_iff_old:
  "M(i) \<Longrightarrow> M(K) \<Longrightarrow> i \<in> jump_cardinal_rel(M,K) \<longleftrightarrow>
      (\<exists>r[M]. \<exists>X[M]. r \<subseteq> K*K & X \<subseteq> K & well_ord(X,r) & i = ordertype(X,r))"
  apply (unfold def_jump_cardinal_rel)
  apply (auto del: subsetI)
   apply (rename_tac y r)
   apply (rule_tac x=r in rexI, intro conjI) prefer 2
     apply (rule_tac x=y in rexI, intro conjI)
        apply (auto dest:mem_Pow_rel transM)
   apply (rule_tac A=r in rev_subsetD, assumption)
   defer
   apply (rename_tac r y)
   apply (rule_tac x=y in bexI)
    apply (rule_tac x=r in ReplaceI, auto)
  using def_Pow_rel
    apply (force+)[2]
  apply (rule_tac A=r in rev_subsetD, assumption)
  using mem_Pow_rel[THEN conjunct1]
  apply auto
  done

(*The easy part of Theorem 10.16: jump_cardinal_rel(K) exceeds K*)
lemma K_lt_jump_cardinal_rel: "Ord(K) ==> M(K) \<Longrightarrow> K < jump_cardinal_rel(M,K)"
  apply (rule Ord_jump_cardinal_rel [THEN [2] ltI])
   apply (rule jump_cardinal_rel_iff_old [THEN iffD2], assumption+)
   apply (rule_tac x="Memrel(K)" in rexI)
    apply (rule_tac x=K in rexI)
     apply (simp add: ordertype_Memrel well_ord_Memrel)
  using Memrel_closed
     apply (simp_all add: Memrel_def subset_iff)
  done

(*The proof by contradiction: the bijection f yields a wellordering of X
  whose ordertype is jump_cardinal_rel(K).  *)
lemma Card_rel_jump_cardinal_rel_lemma:
  "[| well_ord(X,r);  r \<subseteq> K * K;  X \<subseteq> K;
         f \<in> bij(ordertype(X,r), jump_cardinal_rel(M,K));
         M(X); M(r); M(K); M(f) |]
      ==> jump_cardinal_rel(M,K) \<in> jump_cardinal_rel(M,K)"
  apply (subgoal_tac "f O ordermap (X,r) \<in> bij (X, jump_cardinal_rel (M,K))")
   prefer 2 apply (blast intro: comp_bij ordermap_bij)
  apply (rule jump_cardinal_rel_iff_old [THEN iffD2], simp+)
  apply (intro rexI conjI)
       apply (rule subset_trans [OF rvimage_type Sigma_mono], assumption+)
     apply (erule bij_is_inj [THEN well_ord_rvimage])
     apply (rule Ord_jump_cardinal_rel [THEN well_ord_Memrel])
     apply (simp_all add: well_ord_Memrel [THEN [2] bij_ordertype_vimage]
      ordertype_Memrel Ord_jump_cardinal_rel)
  done

(*The hard part of Theorem 10.16: jump_cardinal_rel(K) is itself a cardinal*)
lemma Card_rel_jump_cardinal_rel: "M(K) \<Longrightarrow> Card_rel(M,jump_cardinal_rel(M,K))"
  apply (rule Ord_jump_cardinal_rel [THEN Card_relI])
    apply (simp_all add: def_eqpoll_rel)
  apply (drule_tac i1=j in jump_cardinal_rel_iff_old [THEN iffD1, OF _ _ ltD, of _ K], safe)
  apply (blast intro: Card_rel_jump_cardinal_rel_lemma [THEN mem_irrefl])
  done

subsection\<open>Basic Properties of Successor Cardinals\<close>

lemma csucc_rel_basic: "Ord(K) ==> M(K) \<Longrightarrow> Card_rel(M,csucc_rel(M,K)) & K < csucc_rel(M,K)"
  apply (unfold csucc_rel_def)
  apply (rule LeastI[of "\<lambda>i. M(i) \<and> Card_rel(M,i) \<and> K < i", THEN conjunct2])
   apply (blast intro: Card_rel_jump_cardinal_rel K_lt_jump_cardinal_rel Ord_jump_cardinal_rel)+
  done

lemmas Card_rel_csucc_rel = csucc_rel_basic [THEN conjunct1]

lemmas lt_csucc_rel = csucc_rel_basic [THEN conjunct2]

lemma Ord_0_lt_csucc_rel: "Ord(K) ==> M(K) \<Longrightarrow> 0 < csucc_rel(M,K)"
  by (blast intro: Ord_0_le lt_csucc_rel lt_trans1)

lemma csucc_rel_le: "[| Card_rel(M,L);  K<L; M(K); M(L) |] ==> csucc_rel(M,K) \<le> L"
  apply (unfold csucc_rel_def)
  apply (rule Least_le)
   apply (blast intro: Card_rel_is_Ord)+
  done

lemma lt_csucc_rel_iff: "[| Ord(i); Card_rel(M,K); M(K); M(i)|] ==> i < csucc_rel(M,K) \<longleftrightarrow> |i|\<^bsup>M\<^esup> \<le> K"
  apply (rule iffI)
   apply (rule_tac [2] Card_rel_lt_imp_lt)
       apply (erule_tac [2] lt_trans1)
       apply (simp_all add: lt_csucc_rel Card_rel_csucc_rel Card_rel_is_Ord)
  apply (rule notI [THEN not_lt_imp_le])
    apply (rule Card_rel_cardinal_rel [THEN csucc_rel_le, THEN lt_trans1, THEN lt_irrefl], simp_all+)
   apply (rule Ord_cardinal_rel_le [THEN lt_trans1])
     apply (simp_all add: Card_rel_is_Ord)
  done

lemma Card_rel_lt_csucc_rel_iff:
  "[| Card_rel(M,K'); Card_rel(M,K); M(K'); M(K) |] ==> K' < csucc_rel(M,K) \<longleftrightarrow> K' \<le> K"
  by (simp add: lt_csucc_rel_iff Card_rel_cardinal_rel_eq Card_rel_is_Ord)

lemma InfCard_rel_csucc_rel: "InfCard_rel(M,K) \<Longrightarrow> M(K) ==> InfCard_rel(M,csucc_rel(M,K))"
  by (simp add: InfCard_rel_def Card_rel_csucc_rel Card_rel_is_Ord
      lt_csucc_rel [THEN leI, THEN [2] le_trans])


subsubsection\<open>Theorems by Krzysztof Grabczewski, proofs by lcp\<close>

lemma nat_sum_eqpoll_rel_sum:
  assumes m: "m \<in> nat" and n: "n \<in> nat" shows "m + n \<approx>\<^bsup>M\<^esup> m +\<^sub>\<omega> n"
proof -
  have "m + n \<approx>\<^bsup>M\<^esup> |m+n|\<^bsup>M\<^esup>" using m n
    by (blast intro: nat_implies_well_ord well_ord_radd well_ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym)
  also have "... = m +\<^sub>\<omega> n" using m n
    by (simp add: nat_cadd_rel_eq_add [symmetric] cadd_rel_def transM[OF _ M_nat])
  finally show ?thesis .
qed

lemma Ord_nat_subset_into_Card_rel: "[| Ord(i); i \<subseteq> nat |] ==> Card\<^bsup>M\<^esup>(i)"
  by (blast dest: Ord_subset_natD intro: Card_rel_nat nat_into_Card_rel)

end \<comment> \<open>\<^locale>\<open>M_cardinal_arith_jump\<close>\<close>
end
