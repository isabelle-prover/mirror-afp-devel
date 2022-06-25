subsection\<open>More Instances of Separation\<close>

theory Separation_Instances
  imports
    Names
begin

text\<open>The following instances are mostly the same repetitive task; and we just
copied and pasted, tweaking some lemmas if needed (for example, we might have
needed to use some closedness results).
\<close>

definition radd_body :: "[i,i,i] \<Rightarrow> o" where
  "radd_body(R,S) \<equiv> \<lambda>z. (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>) \<or>
                  (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x', x\<rangle> \<in> R) \<or>
                  (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y', y\<rangle> \<in> S)"

relativize functional "radd_body" "radd_body_rel"
relationalize "radd_body_rel" "is_radd_body"

synthesize "is_radd_body" from_definition
arity_theorem for "is_radd_body_fm"

lemma (in M_ZF1_trans) radd_body_abs:
  assumes "(##M)(R)" "(##M)(S)" "(##M)(x)"
  shows "is_radd_body(##M,R,S,x) \<longleftrightarrow> radd_body(R,S,x)"
  using assms pair_in_M_iff Inl_in_M_iff Inr_in_M_iff
  unfolding radd_body_def is_radd_body_def
  by (auto)

lemma (in M_ZF1_trans) separation_radd_body:
 "(##M)(R) \<Longrightarrow> (##M)(S) \<Longrightarrow> separation
        (##M, \<lambda>z. (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>) \<or>
                  (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x', x\<rangle> \<in> R) \<or>
                  (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y', y\<rangle> \<in> S))"
  using separation_in_ctm[where \<phi>="is_radd_body_fm(1,2,0)" and env="[R,S]"]
    is_radd_body_def arity_is_radd_body_fm ord_simp_union is_radd_body_fm_type radd_body_abs
  unfolding radd_body_def
  by simp

definition rmult_body :: "[i,i,i] \<Rightarrow> o" where
  "rmult_body(b,d) \<equiv> \<lambda>z. \<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in>
b \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> d)"

relativize functional "rmult_body" "rmult_body_rel"
relationalize "rmult_body_rel" "is_rmult_body"

synthesize "is_rmult_body" from_definition
arity_theorem for "is_rmult_body_fm"

lemma (in M_ZF1_trans) rmult_body_abs:
  assumes "(##M)(b)" "(##M)(d)" "(##M)(x)"
  shows "is_rmult_body(##M,b,d,x) \<longleftrightarrow> rmult_body(b,d,x)"
  using assms pair_in_M_iff apply_closed
  unfolding rmult_body_def is_rmult_body_def
  by (auto)

lemma (in M_ZF1_trans) separation_rmult_body:
 "(##M)(b) \<Longrightarrow> (##M)(d) \<Longrightarrow> separation
        (##M, \<lambda>z. \<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> b \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> d))"
  using separation_in_ctm[where \<phi>="is_rmult_body_fm(1,2,0)" and env="[b,d]"]
    is_rmult_body_def arity_is_rmult_body_fm ord_simp_union is_rmult_body_fm_type rmult_body_abs
  unfolding rmult_body_def
  by simp

lemma (in M_replacement) separation_well_ord:
  "(M)(f) \<Longrightarrow> (M)(r) \<Longrightarrow> (M)(A) \<Longrightarrow> separation
        (M, \<lambda>x. x \<in> A \<longrightarrow> (\<exists>y[M]. \<exists>p[M]. is_apply(M, f, x, y) \<and> pair(M, y, x, p) \<and> p \<in> r))"
  using separation_imp  separation_in lam_replacement_identity lam_replacement_constant
    lam_replacement_apply[of f] lam_replacement_Pair[THEN [5] lam_replacement_hcomp2]
  by simp

definition is_obase_body :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_obase_body(N,A,r,x) \<equiv> x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[N].
                         \<exists>g[N].
                            ordinal(N, y) \<and>
                            (\<exists>my[N].
                                \<exists>pxr[N].
                                   membership(N, y, my) \<and>
                                   pred_set(N, A, x, r, pxr) \<and>
                                   order_isomorphism(N, pxr, r, y, my, g)))"

synthesize "is_obase_body" from_definition
arity_theorem for "is_obase_body_fm"

lemma (in M_ZF1_trans) separation_is_obase:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>x. x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[##M].
                         \<exists>g[##M].
                            ordinal(##M, y) \<and>
                            (\<exists>my[##M].
                                \<exists>pxr[##M].
                                   membership(##M, y, my) \<and>
                                   pred_set(##M, A, x, r, pxr) \<and>
                                   order_isomorphism(##M, pxr, r, y, my, g))))"
  using separation_in_ctm[where \<phi>="is_obase_body_fm(1,2,0)" and env="[A,r]"]
    is_obase_body_def arity_is_obase_body_fm ord_simp_union is_obase_body_fm_type
  by simp

definition is_obase_equals :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_obase_equals(N,A,r,a) \<equiv> \<exists>x[N].
                     \<exists>g[N].
                        \<exists>mx[N].
                           \<exists>par[N].
                              ordinal(N, x) \<and>
                              membership(N, x, mx) \<and>
                              pred_set(N, A, a, r, par) \<and> order_isomorphism(N, par, r, x, mx, g)"

synthesize "is_obase_equals" from_definition
arity_theorem for "is_obase_equals_fm"

lemma (in M_ZF1_trans) separation_obase_equals:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>a. \<exists>x[##M].
                     \<exists>g[##M].
                        \<exists>mx[##M].
                           \<exists>par[##M].
                              ordinal(##M, x) \<and>
                              membership(##M, x, mx) \<and>
                              pred_set(##M, A, a, r, par) \<and> order_isomorphism(##M, par, r, x, mx, g))"
  using separation_in_ctm[where \<phi>="is_obase_equals_fm(1,2,0)" and env="[A,r]"]
    is_obase_equals_def arity_is_obase_equals_fm ord_simp_union is_obase_equals_fm_type
  by simp

synthesize "PiP_rel" from_definition assuming "nonempty"
arity_theorem for "PiP_rel_fm"

lemma (in M_ZF1_trans) separation_PiP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, PiP_rel(##M,A))"
  using separation_in_ctm[where env="[A]" and \<phi>="PiP_rel_fm(1,0)"]
    nonempty PiP_rel_iff_sats[symmetric] arity_PiP_rel_fm PiP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "injP_rel" from_definition assuming "nonempty"
arity_theorem for "injP_rel_fm"

lemma (in M_ZF1_trans) separation_injP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, injP_rel(##M,A))"
  using separation_in_ctm[where env="[A]" and \<phi>="injP_rel_fm(1,0)"]
    nonempty injP_rel_iff_sats[symmetric] arity_injP_rel_fm injP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "surjP_rel" from_definition assuming "nonempty"
arity_theorem for "surjP_rel_fm"

lemma (in M_ZF1_trans) separation_surjP_rel:
 "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> separation(##M, surjP_rel(##M,A,B))"
  using separation_in_ctm[where env="[A,B]" and \<phi>="surjP_rel_fm(1,2,0)"]
    nonempty surjP_rel_iff_sats[symmetric] arity_surjP_rel_fm surjP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "cons_like_rel" from_definition assuming "nonempty"
arity_theorem for "cons_like_rel_fm"

lemma (in M_ZF1_trans) separation_cons_like_rel:
 "separation(##M, cons_like_rel(##M))"
  using separation_in_ctm[where env="[]" and \<phi>="cons_like_rel_fm(0)"]
    nonempty cons_like_rel_iff_sats[symmetric] arity_cons_like_rel_fm cons_like_rel_fm_type
  by simp

lemma (in M_ZF1_trans) separation_is_function:
 "separation(##M, is_function(##M))"
  using separation_in_ctm[where env="[]" and \<phi>="function_fm(0)"] arity_function_fm
  by simp

(* Instances in M_replacement*)

definition fstsnd_in_sndsnd :: "[i] \<Rightarrow> o" where
  "fstsnd_in_sndsnd \<equiv> \<lambda>x. fst(snd(x)) \<in> snd(snd(x))"
relativize "fstsnd_in_sndsnd" "is_fstsnd_in_sndsnd"
synthesize "is_fstsnd_in_sndsnd" from_definition assuming "nonempty"
arity_theorem for "is_fstsnd_in_sndsnd_fm"

lemma (in M_ZF1_trans) fstsnd_in_sndsnd_abs:
  assumes "(##M)(x)"
  shows "is_fstsnd_in_sndsnd(##M,x) \<longleftrightarrow> fstsnd_in_sndsnd(x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding fstsnd_in_sndsnd_def is_fstsnd_in_sndsnd_def
  by auto

lemma (in M_ZF1_trans) separation_fstsnd_in_sndsnd:
 "separation(##M, \<lambda>x. fst(snd(x)) \<in> snd(snd(x)))"
  using separation_in_ctm[where env="[]" and \<phi>="is_fstsnd_in_sndsnd_fm(0)" and Q=fstsnd_in_sndsnd]
    nonempty fstsnd_in_sndsnd_abs arity_is_fstsnd_in_sndsnd_fm
  unfolding fstsnd_in_sndsnd_def
  by simp

definition sndfst_eq_fstsnd :: "[i] \<Rightarrow> o" where
  "sndfst_eq_fstsnd \<equiv> \<lambda>x. snd(fst(x)) = fst(snd(x))"
relativize "sndfst_eq_fstsnd" "is_sndfst_eq_fstsnd"
synthesize "is_sndfst_eq_fstsnd" from_definition assuming "nonempty"
arity_theorem for "is_sndfst_eq_fstsnd_fm"

lemma (in M_ZF1_trans) sndfst_eq_fstsnd_abs:
  assumes "(##M)(x)"
  shows "is_sndfst_eq_fstsnd(##M,x) \<longleftrightarrow> sndfst_eq_fstsnd(x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding sndfst_eq_fstsnd_def is_sndfst_eq_fstsnd_def
  by auto

lemma (in M_ZF1_trans) separation_sndfst_eq_fstsnd:
 "separation(##M, \<lambda>x. snd(fst(x)) = fst(snd(x)))"
  using separation_in_ctm[where env="[]" and \<phi>="is_sndfst_eq_fstsnd_fm(0)" and Q=sndfst_eq_fstsnd]
    nonempty sndfst_eq_fstsnd_abs arity_is_sndfst_eq_fstsnd_fm
  unfolding sndfst_eq_fstsnd_def
  by simp

(*  "M(G) \<Longrightarrow> M(Q) \<Longrightarrow> separation(M, \<lambda>p. \<forall>x\<in>G. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> Q))" *)
definition insnd_ballPair :: "[i,i,i] \<Rightarrow> o" where
  "insnd_ballPair(B,A) \<equiv> \<lambda>p. \<forall>x\<in>B. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> A)"

relativize "insnd_ballPair" "is_insnd_ballPair"
synthesize "is_insnd_ballPair" from_definition assuming "nonempty"
arity_theorem for "is_insnd_ballPair_fm"

lemma (in M_ZF1_trans) insnd_ballPair_abs:
  assumes "(##M)(B)" "(##M)(A)" "(##M)(x)"
  shows "is_insnd_ballPair(##M,B,A,x) \<longleftrightarrow> insnd_ballPair(B,A,x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
    transM[of _ B] transM[of _ "snd(x)"] transM[of _ "fst(x)"]
  unfolding insnd_ballPair_def is_insnd_ballPair_def
  by (auto)

lemma (in M_ZF1_trans) separation_insnd_ballPair:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, \<lambda>p. \<forall>x\<in>B. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> A))"
  using insnd_ballPair_abs nonempty
    separation_in_ctm[where \<phi>="is_insnd_ballPair_fm(2,1,0)" and env="[A,B]"]
    arity_is_insnd_ballPair_fm ord_simp_union is_insnd_ballPair_fm_type
  unfolding insnd_ballPair_def
  by simp

end