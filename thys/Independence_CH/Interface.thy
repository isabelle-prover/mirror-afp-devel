section\<open>Interface between set models and Constructibility\<close>

text\<open>This theory provides an interface between Paulson's
relativization results and set models of ZFC. In particular,
it is used to prove that the locale \<^term>\<open>forcing_data\<close> is
a sublocale of all relevant locales in \<^session>\<open>ZF-Constructible\<close>
(\<^term>\<open>M_trivial\<close>, \<^term>\<open>M_basic\<close>, \<^term>\<open>M_eclose\<close>, etc).

In order to interpret the locales in \<^session>\<open>ZF-Constructible\<close> we
introduce new locales, each stronger than the previous one, assuming
only the instances of Replacement needed to interpret the subsequent
locales of that session. From the start we assume Separation for
every internalized formula (with one parameter, but this is not a
problem since we can use pairing).\<close>

theory Interface
  imports
    Fm_Definitions
    Transitive_Models.Cardinal_AC_Relative
begin

locale M_Z_basic =
  fixes M
  assumes
    upair_ax:      "upair_ax(##M)" and
    Union_ax:      "Union_ax(##M)" and
    power_ax:      "power_ax(##M)" and
    extensionality:"extensionality(##M)" and
    foundation_ax: "foundation_ax(##M)" and
    infinity_ax:   "infinity_ax(##M)" and
    separation_ax: "\<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
                    arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. (M, [x] @ env \<Turnstile> \<phi>))"

locale M_transset =
  fixes M
  assumes
    trans_M:       "Transset(M)"

locale M_Z_trans = M_Z_basic + M_transset

locale M_ZF1 = M_Z_basic +
  assumes
    replacement_ax1:
    "replacement_assm(M,env,list_repl1_intf_fm)"
    "replacement_assm(M,env,list_repl2_intf_fm)"
    "replacement_assm(M,env,formula_repl1_intf_fm)"
    "replacement_assm(M,env,formula_repl2_intf_fm)"
    "replacement_assm(M,env,eclose_repl1_intf_fm)"
    "replacement_assm(M,env,eclose_repl2_intf_fm)"
    "replacement_assm(M,env,wfrec_rank_fm)"
    "replacement_assm(M,env,trans_repl_HVFrom_fm)"
    "replacement_assm(M,env,tl_repl_intf_fm)"

definition instances1_fms where "instances1_fms \<equiv>
  { list_repl1_intf_fm,
    list_repl2_intf_fm,
    formula_repl1_intf_fm,
    formula_repl2_intf_fm,
    eclose_repl1_intf_fm,
    eclose_repl2_intf_fm,
    wfrec_rank_fm,
    trans_repl_HVFrom_fm,
    tl_repl_intf_fm
 }"

text\<open>This set has 9 internalized formulas.\<close>

lemmas replacement_instances1_defs =
  list_repl1_intf_fm_def list_repl2_intf_fm_def
  formula_repl1_intf_fm_def formula_repl2_intf_fm_def
  eclose_repl1_intf_fm_def eclose_repl2_intf_fm_def
  wfrec_rank_fm_def trans_repl_HVFrom_fm_def tl_repl_intf_fm_def

lemma instances1_fms_type[TC]: "instances1_fms \<subseteq> formula"
  using Lambda_in_M_fm_type
  unfolding replacement_instances1_defs instances1_fms_def by simp

declare (in M_ZF1) replacement_instances1_defs[simp]

locale M_ZF1_trans = M_ZF1 + M_Z_trans

context M_Z_trans
begin

lemmas transitivity = Transset_intf[OF trans_M]

subsection\<open>Interface with \<^term>\<open>M_trivial\<close>\<close>

lemma zero_in_M:  "0 \<in> M"
proof -
  obtain z where "empty(##M,z)"  "z\<in>M"
    using empty_intf[OF infinity_ax]
    by auto
  moreover from this
  have "z=0"
    using transitivity empty_def
    by auto
  ultimately
  show ?thesis
    by simp
qed

lemma separation_in_ctm :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)" and
    satsQ: "\<And>x. x\<in>M \<Longrightarrow> (M, [x]@env \<Turnstile> \<phi>) \<longleftrightarrow> Q(x)"
  shows
    "separation(##M,Q)"
  using assms separation_ax satsQ transitivity
    separation_cong[of "##M" "\<lambda>y. (M, [y]@env \<Turnstile> \<phi>)" "Q"]
  by simp

end \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

locale M_ZC_basic = M_Z_basic + M_AC "##M"

locale M_ZFC1 = M_ZF1 + M_ZC_basic

locale M_ZFC1_trans = M_ZF1_trans + M_ZFC1

sublocale M_Z_trans \<subseteq> M_trans "##M"
  using transitivity zero_in_M exI[of "\<lambda>x. x\<in>M"]
  by unfold_locales simp_all

sublocale M_Z_trans \<subseteq> M_trivial "##M"
  using upair_ax Union_ax by unfold_locales

subsection\<open>Interface with \<^term>\<open>M_basic\<close>\<close>

definition Intersection where
  "Intersection(N,B,x) \<equiv> (\<forall>y[N]. y\<in>B \<longrightarrow> x\<in>y)"

synthesize "Intersection" from_definition "Intersection" assuming "nonempty"
arity_theorem for "Intersection_fm"

definition CartProd where
  "CartProd(N,B,C,z) \<equiv> (\<exists>x[N]. x\<in>B \<and> (\<exists>y[N]. y\<in>C \<and> pair(N,x,y,z)))"

synthesize "CartProd" from_definition "CartProd" assuming "nonempty"
arity_theorem for "CartProd_fm"

definition ImageSep where
  "ImageSep(N,B,r,y) \<equiv> (\<exists>p[N]. p\<in>r \<and> (\<exists>x[N]. x\<in>B \<and> pair(N,x,y,p)))"

synthesize "ImageSep" from_definition  assuming "nonempty"
arity_theorem for "ImageSep_fm"

definition Converse where
  "Converse(N,R,z) \<equiv> \<exists>p[N]. p\<in>R \<and> (\<exists>x[N].\<exists>y[N]. pair(N,x,y,p) \<and> pair(N,y,x,z))"

synthesize "Converse" from_definition "Converse" assuming "nonempty"
arity_theorem for "Converse_fm"

definition Restrict where
  "Restrict(N,A,z) \<equiv> \<exists>x[N]. x\<in>A \<and> (\<exists>y[N]. pair(N,x,y,z))"

synthesize "Restrict" from_definition "Restrict" assuming "nonempty"
arity_theorem for "Restrict_fm"

definition Comp where
  "Comp(N,R,S,xz) \<equiv> \<exists>x[N]. \<exists>y[N]. \<exists>z[N]. \<exists>xy[N]. \<exists>yz[N].
              pair(N,x,z,xz) \<and> pair(N,x,y,xy) \<and> pair(N,y,z,yz) \<and> xy\<in>S \<and> yz\<in>R"

synthesize "Comp" from_definition "Comp" assuming "nonempty"
arity_theorem for "Comp_fm"

definition Pred where
  "Pred(N,R,X,y) \<equiv> \<exists>p[N]. p\<in>R \<and> pair(N,y,X,p)"

synthesize "Pred" from_definition "Pred" assuming "nonempty"
arity_theorem for "Pred_fm"

definition is_Memrel where
  "is_Memrel(N,z) \<equiv> \<exists>x[N]. \<exists>y[N]. pair(N,x,y,z) \<and> x \<in> y"

synthesize "is_Memrel" from_definition "is_Memrel" assuming "nonempty"
arity_theorem for "is_Memrel_fm"

definition RecFun where
  "RecFun(N,r,f,g,a,b,x) \<equiv> \<exists>xa[N]. \<exists>xb[N].
                    pair(N,x,a,xa) \<and> xa \<in> r \<and> pair(N,x,b,xb) \<and> xb \<in> r \<and>
                    (\<exists>fx[N]. \<exists>gx[N]. fun_apply(N,f,x,fx) \<and> fun_apply(N,g,x,gx) \<and>
                                     fx \<noteq> gx)"

synthesize "RecFun" from_definition "RecFun" assuming "nonempty"
arity_theorem for "RecFun_fm"

arity_theorem for "rtran_closure_mem_fm"

synthesize "wellfounded_trancl" from_definition assuming "nonempty"
arity_theorem for "wellfounded_trancl_fm"

context M_Z_trans
begin

lemma inter_sep_intf :
  assumes "A\<in>M"
  shows "separation(##M,\<lambda>x . \<forall>y\<in>M . y\<in>A \<longrightarrow> x\<in>y)"
  using assms separation_in_ctm[of "Intersection_fm(1,0)" "[A]" "Intersection(##M,A)"]
    Intersection_iff_sats[of 1 "[_,A]" A 0 _ M] arity_Intersection_fm Intersection_fm_type
    ord_simp_union zero_in_M
  unfolding Intersection_def
  by simp

lemma diff_sep_intf :
  assumes "B\<in>M"
  shows "separation(##M,\<lambda>x . x\<notin>B)"
  using assms separation_in_ctm[of "Neg(Member(0,1))" "[B]" "\<lambda>x . x\<notin>B"] ord_simp_union
  by simp

lemma cartprod_sep_intf :
  assumes "A\<in>M" and "B\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. y\<in>B \<and> pair(##M,x,y,z)))"
  using assms separation_in_ctm[of "CartProd_fm(1,2,0)" "[A,B]" "CartProd(##M,A,B)"]
    CartProd_iff_sats[of 1 "[_,A,B]" A 2 B 0 _ M] arity_CartProd_fm  CartProd_fm_type
    ord_simp_union zero_in_M
  unfolding CartProd_def
  by simp

lemma image_sep_intf :
  assumes "A\<in>M" and "B\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>B \<and> (\<exists>x\<in>M. x\<in>A \<and> pair(##M,x,y,p)))"
  using assms separation_in_ctm[of "ImageSep_fm(1,2,0)" "[A,B]" "ImageSep(##M,A,B)"]
    ImageSep_iff_sats[of 1 "[_,A,B]" _ 2 _ 0 _ M] arity_ImageSep_fm ImageSep_fm_type
    ord_simp_union zero_in_M
  unfolding ImageSep_def
  by simp

lemma converse_sep_intf :
  assumes "R\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>p\<in>M. p\<in>R \<and> (\<exists>x\<in>M.\<exists>y\<in>M. pair(##M,x,y,p) \<and> pair(##M,y,x,z)))"
  using assms separation_in_ctm[of "Converse_fm(1,0)" "[R]" "Converse(##M,R)"]
    Converse_iff_sats[of 1 "[_,R]" _ 0 _ M] arity_Converse_fm Converse_fm_type
    ord_simp_union zero_in_M
  unfolding Converse_def
  by simp

lemma restrict_sep_intf :
  assumes "A\<in>M"
  shows "separation(##M,\<lambda>z. \<exists>x\<in>M. x\<in>A \<and> (\<exists>y\<in>M. pair(##M,x,y,z)))"
  using assms separation_in_ctm[of "Restrict_fm(1,0)" "[A]" "Restrict(##M,A)"]
    Restrict_iff_sats[of 1 "[_,A]" _ 0 _ M] arity_Restrict_fm Restrict_fm_type
    ord_simp_union zero_in_M
  unfolding Restrict_def
  by simp

lemma comp_sep_intf :
  assumes "R\<in>M" and "S\<in>M"
  shows "separation(##M,\<lambda>xz. \<exists>x\<in>M. \<exists>y\<in>M. \<exists>z\<in>M. \<exists>xy\<in>M. \<exists>yz\<in>M.
           pair(##M,x,z,xz) \<and> pair(##M,x,y,xy) \<and> pair(##M,y,z,yz) \<and> xy\<in>S \<and> yz\<in>R)"
  using assms separation_in_ctm[of "Comp_fm(1,2,0)" "[R,S]" "Comp(##M,R,S)"]
    Comp_iff_sats[of 1 "[_,R,S]" _ 2 _ 0 _ M] arity_Comp_fm Comp_fm_type
    ord_simp_union zero_in_M
  unfolding Comp_def
  by simp

lemma pred_sep_intf:
  assumes "R\<in>M" and "X\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>p\<in>M. p\<in>R \<and> pair(##M,y,X,p))"
  using assms separation_in_ctm[of "Pred_fm(1,2,0)" "[R,X]" "Pred(##M,R,X)"]
    Pred_iff_sats[of 1 "[_,R,X]" _ 2 _ 0 _ M] arity_Pred_fm Pred_fm_type
    ord_simp_union zero_in_M
  unfolding Pred_def
  by simp

lemma memrel_sep_intf:
  "separation(##M, \<lambda>z. \<exists>x\<in>M. \<exists>y\<in>M. pair(##M,x,y,z) \<and> x \<in> y)"
  using separation_in_ctm[of "is_Memrel_fm(0)" "[]" "is_Memrel(##M)"]
    is_Memrel_iff_sats[of 0 "[_]" _ M] arity_is_Memrel_fm is_Memrel_fm_type
    ord_simp_union zero_in_M
  unfolding is_Memrel_def
  by simp

lemma is_recfun_sep_intf :
  assumes "r\<in>M" "f\<in>M" "g\<in>M" "a\<in>M" "b\<in>M"
  shows "separation(##M,\<lambda>x. \<exists>xa\<in>M. \<exists>xb\<in>M.
                    pair(##M,x,a,xa) \<and> xa \<in> r \<and> pair(##M,x,b,xb) \<and> xb \<in> r \<and>
                    (\<exists>fx\<in>M. \<exists>gx\<in>M. fun_apply(##M,f,x,fx) \<and> fun_apply(##M,g,x,gx) \<and>
                                     fx \<noteq> gx))"
  using assms separation_in_ctm[of "RecFun_fm(1,2,3,4,5,0)" "[r,f,g,a,b]" "RecFun(##M,r,f,g,a,b)"]
    RecFun_iff_sats[of 1 "[_,r,f,g,a,b]" _ 2 _ 3 _ 4 _ 5 _ 0 _ M] arity_RecFun_fm RecFun_fm_type
    ord_simp_union zero_in_M
  unfolding RecFun_def
  by simp

lemmas M_basic_sep_instances =
  inter_sep_intf diff_sep_intf cartprod_sep_intf
  image_sep_intf converse_sep_intf restrict_sep_intf
  pred_sep_intf memrel_sep_intf comp_sep_intf is_recfun_sep_intf

end \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

sublocale M_Z_trans \<subseteq> M_basic_no_repl "##M"
  using power_ax M_basic_sep_instances
  by unfold_locales simp_all

lemma Replace_eq_Collect:
  assumes "\<And>x y y'. x\<in>A \<Longrightarrow> P(x,y) \<Longrightarrow> P(x,y') \<Longrightarrow> y=y'" "{y . x \<in> A, P(x, y)} \<subseteq> B"
  shows "{y . x \<in> A, P(x, y)} = {y\<in>B . \<exists>x\<in>A. P(x,y)}"
  using assms by blast

context M_Z_trans
begin

lemma Pow_inter_M_closed: assumes "A \<in> M" shows "Pow(A) \<inter> M \<in> M"
proof -
  have "{a \<in> Pow(A) . a \<in> M} = Pow(A) \<inter> M" by auto
  then
  show ?thesis
    using power_ax powerset_abs assms unfolding power_ax_def
    by auto
qed

lemma Pow'_inter_M_closed: assumes "A \<in> M" shows "{a \<in> Pow(A) . a \<in> M} \<in> M"
  using power_ax powerset_abs assms unfolding power_ax_def by auto

end \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

context M_basic_no_repl
begin

lemma Replace_funspace_succ_rep_intf_sub:
  assumes
    "M(A)" "M(n)"
  shows
    "{z . p \<in> A, funspace_succ_rep_intf_rel(M,p,z,n)}
      \<subseteq> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>domain(A) \<union> ({n} \<times> range(A)) \<union> (\<Union>({n} \<times> range(A)))))"
  unfolding funspace_succ_rep_intf_rel_def using assms mem_Pow_rel_abs
  by clarsimp (auto simp: cartprod_def)

lemma funspace_succ_rep_intf_uniq:
  assumes
    "funspace_succ_rep_intf_rel(M,p,z,n)" "funspace_succ_rep_intf_rel(M,p,z',n)"
  shows
    "z = z'"
  using assms unfolding funspace_succ_rep_intf_rel_def by auto

lemma Replace_funspace_succ_rep_intf_eq:
  assumes
    "M(A)" "M(n)"
  shows
    "{z . p \<in> A, funspace_succ_rep_intf_rel(M,p,z,n)} =
     {z \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>domain(A) \<union> ({n} \<times> range(A)) \<union> (\<Union>({n} \<times> range(A))))) .
        \<exists>p\<in>A. funspace_succ_rep_intf_rel(M,p,z,n)}"
  using assms Replace_eq_Collect[OF funspace_succ_rep_intf_uniq, of A,
      OF _ _ Replace_funspace_succ_rep_intf_sub[of A n], of "\<lambda>x y z. x" "\<lambda>x y z. n"]
  by (intro equalityI)
    (auto dest:transM simp:funspace_succ_rep_intf_rel_def)

end \<comment> \<open>\<^locale>\<open>M_basic_no_repl\<close>\<close>

definition fsri where
  "fsri(N,A,B) \<equiv> \<lambda>z. \<exists>p\<in>A. \<exists>f[N]. \<exists>b[N]. p = \<langle>f, b\<rangle> \<and> z = {cons(\<langle>B, b\<rangle>, f)}"

relationalize "fsri" "is_fsri"
synthesize "is_fsri" from_definition assuming "nonempty"
arity_theorem for "is_fsri_fm"


context M_Z_trans
begin

lemma separation_fsri:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> separation(##M, is_fsri(##M,A,B))"
  using separation_in_ctm[where env="[A,B]" and \<phi>="is_fsri_fm(1,2,0)"]
    zero_in_M is_fsri_iff_sats[symmetric] arity_is_fsri_fm is_fsri_fm_type
  by (simp_all add: ord_simp_union)

lemma separation_funspace_succ_rep_intf_rel:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> separation(##M, \<lambda>z. \<exists>p\<in>A. funspace_succ_rep_intf_rel(##M,p,z,B))"
  using separation_fsri zero_in_M
  by (rule_tac separation_cong[THEN iffD1, of _ "is_fsri(##M,A,B)"])
    (auto simp flip:setclass_iff dest:transM
      simp:is_fsri_def funspace_succ_rep_intf_rel_def, force)

lemma Replace_funspace_succ_rep_intf_in_M:
  assumes
    "A \<in> M" "n \<in> M"
  shows
    "{z . p \<in> A, funspace_succ_rep_intf_rel(##M,p,z,n)} \<in> M"
proof -
  have "(##M)({z \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>domain(A) \<union> ({n} \<times> range(A)) \<union> (\<Union>({n} \<times> range(A))))) .
        \<exists>p\<in>A. funspace_succ_rep_intf_rel(##M,p,z,n)})"
    using assms separation_funspace_succ_rep_intf_rel
    by (intro separation_closed) (auto simp flip:setclass_iff)
  with assms
  show ?thesis
    using Replace_funspace_succ_rep_intf_eq by auto
qed

lemma funspace_succ_rep_intf:
  assumes "n\<in>M"
  shows
    "strong_replacement(##M,
          \<lambda>p z. \<exists>f\<in>M. \<exists>b\<in>M. \<exists>nb\<in>M. \<exists>cnbf\<in>M.
                pair(##M,f,b,p) \<and> pair(##M,n,b,nb) \<and> is_cons(##M,nb,f,cnbf) \<and>
                upair(##M,cnbf,cnbf,z))"
  using assms pair_in_M_iff[simplified] cons_closed[simplified]
  unfolding strong_replacement_def univalent_def
  apply (clarsimp, rename_tac A)
  apply (rule_tac x="{z . p \<in> A, funspace_succ_rep_intf_rel(##M,p,z,n)}" in bexI)
   apply (auto simp:funspace_succ_rep_intf_rel_def
      Replace_funspace_succ_rep_intf_in_M[unfolded funspace_succ_rep_intf_rel_def, simplified])
  done

end \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

sublocale M_Z_trans \<subseteq> M_basic "##M"
  using power_ax M_basic_sep_instances funspace_succ_rep_intf
  by unfold_locales auto

subsection\<open>Interface with \<^term>\<open>M_trancl\<close>\<close>

context M_ZF1_trans
begin

lemma rtrancl_separation_intf:
  assumes "r\<in>M" "A\<in>M"
  shows "separation (##M, rtran_closure_mem(##M,A,r))"
  using assms separation_in_ctm[of "rtran_closure_mem_fm(1,2,0)" "[A,r]" "rtran_closure_mem(##M,A,r)"]
    arity_rtran_closure_mem_fm ord_simp_union zero_in_M
  by simp

lemma wftrancl_separation_intf:
  assumes "r\<in>M" and "Z\<in>M"
  shows "separation (##M, wellfounded_trancl(##M,Z,r))"
  using assms separation_in_ctm[of "wellfounded_trancl_fm(1,2,0)" "[Z,r]" "wellfounded_trancl(##M,Z,r)"]
    arity_wellfounded_trancl_fm ord_simp_union zero_in_M
  by simp

text\<open>To prove \<^term>\<open>nat \<in> M\<close> we get an infinite set \<^term>\<open>I\<close> from \<^term>\<open>infinity_ax\<close>
closed under \<^term>\<open>0\<close> and \<^term>\<open>succ\<close>; that shows \<^term>\<open>nat\<subseteq>I\<close>. Then we
can separate \<^term>\<open>I\<close> with the predicate \<^term>\<open>\<lambda>x. x\<in>nat\<close>.\<close>
lemma finite_sep_intf: "separation(##M, \<lambda>x. x\<in>nat)"
proof -
  have "(\<forall>v\<in>M. separation(##M,\<lambda>x. (M, [x,v] \<Turnstile> finite_ordinal_fm(0))))"
    using separation_ax arity_finite_ordinal_fm
    by simp
  then
  have "(\<forall>v\<in>M. separation(##M,finite_ordinal(##M)))"
    unfolding separation_def
    by simp
  then
  have "separation(##M,finite_ordinal(##M))"
    using separation_in_ctm zero_in_M
    by auto
  then
  show ?thesis
    unfolding separation_def
    by simp
qed

lemma nat_subset_I: "\<exists>I\<in>M. nat \<subseteq> I"
proof -
  have "nat \<subseteq> I"
    if "I\<in>M" and "0\<in>I" and "\<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I" for I
    using that
    by (rule_tac subsetI,induct_tac x,simp_all)
  moreover
  obtain I where
    "I\<in>M" "0\<in>I" "\<And>x. x\<in>I \<Longrightarrow> succ(x)\<in>I"
    using infinity_ax transitivity
    unfolding infinity_ax_def
    by auto
  ultimately
  show ?thesis
    by auto
qed

lemma nat_in_M: "nat \<in> M"
proof -
  have "{x\<in>B . x\<in>A}=A" if "A\<subseteq>B" for A B
    using that by auto
  moreover
  obtain I where
    "I\<in>M" "nat\<subseteq>I"
    using nat_subset_I by auto
  moreover from this
  have "{x\<in>I . x\<in>nat} \<in> M"
    using finite_sep_intf separation_closed[of "\<lambda>x . x\<in>nat"]
    by simp
  ultimately
  show ?thesis
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

sublocale M_ZF1_trans \<subseteq> M_trancl "##M"
  using rtrancl_separation_intf wftrancl_separation_intf nat_in_M
    wellfounded_trancl_def
  by unfold_locales auto

subsection\<open>Interface with \<^term>\<open>M_eclose\<close>\<close>

lemma repl_sats:
  assumes
    sat:"\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> (M, Cons(x,Cons(z,env)) \<Turnstile> \<phi>) \<longleftrightarrow> P(x,z)"
  shows
    "strong_replacement(##M,\<lambda>x z. (M, Cons(x,Cons(z,env)) \<Turnstile> \<phi>)) \<longleftrightarrow>
   strong_replacement(##M,P)"
  by (rule strong_replacement_cong,simp add:sat)

arity_theorem for "list_functor_fm"
arity_theorem for "formula_functor_fm"
arity_theorem for "Inl_fm"
arity_theorem for "Inr_fm"
arity_theorem for "Nil_fm"
arity_theorem for "Cons_fm"
arity_theorem for "quasilist_fm"
arity_theorem for "tl_fm"
arity_theorem for "big_union_fm"

context M_ZF1_trans
begin

lemma list_repl1_intf:
  assumes "A\<in>M"
  shows "iterates_replacement(##M, is_list_functor(##M,A), 0)"
proof -
  let ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0)))"
  have "arity(?f) = 5"
    using arity_iterates_MH_fm[where isF="list_functor_fm(13,1,0)" and i=14]
      arity_wfrec_replacement_fm[where i=11] arity_list_functor_fm ord_simp_union
    by simp
  {
    fix n
    assume "n\<in>nat"
    then
    have "Memrel(succ(n))\<in>M"
      using nat_into_M Memrel_closed
      by simp
    moreover
    note assms zero_in_M
    moreover from calculation
    have "is_list_functor(##M, A, a, b)
       \<longleftrightarrow> (M, [b,a,c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0] \<Turnstile> list_functor_fm(13,1,0))"
      if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a b c d a0 a1 a2 a3 a4 y x z
      using that
      by simp
    moreover from calculation
    have "(M, [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),A,0] \<Turnstile>
            iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0)) \<longleftrightarrow>
          iterates_MH(##M,is_list_functor(##M,A),0,a2, a1, a0)"
      if "a0\<in>M" "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
      for a0 a1 a2 a3 a4 y x z
      using that sats_iterates_MH_fm[of M "is_list_functor(##M,A)" _]
      by simp
    moreover from calculation
    have "(M, [y,x,z,Memrel(succ(n)),A,0] \<Turnstile>
              is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0)) \<longleftrightarrow>
          is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using that sats_is_wfrec_fm
      by simp
    moreover from calculation
    have "(M, [x,z,Memrel(succ(n)),A,0] \<Turnstile> ?f) \<longleftrightarrow>

        (\<exists>y\<in>M. pair(##M,x,y,z) \<and>
        is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that
      by (simp del:pair_abs)
    moreover
    note \<open>arity(?f) = 5\<close>
    moreover from calculation
    have "strong_replacement(##M,\<lambda>x z. (M, [x,z,Memrel(succ(n)),A,0] \<Turnstile> ?f))"
      using replacement_ax1(1)[unfolded replacement_assm_def]
      by simp
    moreover from calculation
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) \<and> is_wfrec(##M, iterates_MH(##M,is_list_functor(##M,A),0) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),A,0]"]
      by (simp del:pair_abs)
  }
  then
  show ?thesis
    unfolding iterates_replacement_def wfrec_replacement_def
    by simp
qed

text\<open>This lemma obtains \<^term>\<open>iterates_replacement\<close> for predicates
without parameters.\<close>
lemma iterates_repl_intf :
  assumes
    "v\<in>M" and
    isfm:"is_F_fm \<in> formula" and
    arty:"arity(is_F_fm)=2" and
    satsf: "\<And>a b env'. \<lbrakk> a\<in>M ; b\<in>M ; env'\<in>list(M) \<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow> (M,  [b,a]@env' \<Turnstile>  is_F_fm)"
    and is_F_fm_replacement:
    "\<And>env. (\<cdot>\<exists>\<cdot>\<cdot>\<langle>1,0\<rangle> is 2\<cdot> \<and> is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0) \<cdot>\<cdot>) \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow>
      arity((\<cdot>\<exists>\<cdot>\<cdot>\<langle>1,0\<rangle> is 2\<cdot> \<and> is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0) \<cdot>\<cdot>)) \<le> 2 +\<^sub>\<omega> length(env) \<Longrightarrow>
     strong_replacement(##M,\<lambda>x y.
         M, [x,y] @ env \<Turnstile> (\<cdot>\<exists>\<cdot>\<cdot>\<langle>1,0\<rangle> is 2\<cdot> \<and> is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0) \<cdot>\<cdot>))"
  shows
    "iterates_replacement(##M,is_F,v)"
proof -
  let ?f="(\<cdot>\<exists>\<cdot>\<cdot>\<langle>1,0\<rangle> is 2\<cdot> \<and> is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0) \<cdot>\<cdot>)"
  have "arity(?f) = 4" "?f\<in>formula"
    using arity_iterates_MH_fm[where isF=is_F_fm and i=2]
      arity_wfrec_replacement_fm[where i=10] isfm arty ord_simp_union
    by simp_all
  {
    fix n
    assume "n\<in>nat"
    then
    have "Memrel(succ(n))\<in>M"
      using nat_into_M Memrel_closed
      by simp
    moreover
    {
      fix a0 a1 a2 a3 a4 y x z
      assume "[a0,a1,a2,a3,a4,y,x,z]\<in>list(M)"
      moreover
      note \<open>v\<in>M\<close> \<open>Memrel(succ(n))\<in>M\<close>
      moreover from calculation
      have "(M, [b,a,c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v] \<Turnstile> is_F_fm) \<longleftrightarrow>
           is_F(a,b)"
        if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" for a b c d
        using that satsf[of a b "[c,d,a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v]"]
        by simp
      moreover from calculation
      have "(M, [a0,a1,a2,a3,a4,y,x,z,Memrel(succ(n)),v] \<Turnstile> iterates_MH_fm(is_F_fm,9,2,1,0)) \<longleftrightarrow>
           iterates_MH(##M,is_F,v,a2, a1, a0)"
        using sats_iterates_MH_fm[of M "is_F" "is_F_fm"]
        by simp
    }
    moreover from calculation
    have "(M, [y,x,z,Memrel(succ(n)),v] \<Turnstile> is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0)) \<longleftrightarrow>
          is_wfrec(##M, iterates_MH(##M,is_F,v),Memrel(succ(n)), x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using that sats_is_wfrec_fm \<open>v\<in>M\<close> by simp
    moreover from calculation
    have "(M, [x,z,Memrel(succ(n)),v] \<Turnstile> ?f) \<longleftrightarrow>

        (\<exists>y\<in>M. pair(##M,x,y,z) \<and>
        is_wfrec(##M, iterates_MH(##M,is_F,v) , Memrel(succ(n)), x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that \<open>v\<in>M\<close>
      by (simp del:pair_abs)
    moreover
    note \<open>arity(?f) = 4\<close> \<open>?f\<in>formula\<close>
    moreover from calculation \<open>v\<in>_\<close>
    have "strong_replacement(##M,\<lambda>x z. (M, [x,z,Memrel(succ(n)),v] \<Turnstile> ?f))"
      using is_F_fm_replacement
      by simp
    ultimately
    have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) \<and> is_wfrec(##M, iterates_MH(##M,is_F,v) ,
                Memrel(succ(n)), x, y))"
      using repl_sats[of M ?f "[Memrel(succ(n)),v]"]
      by (simp del:pair_abs)
  }
  then
  show ?thesis
    unfolding iterates_replacement_def wfrec_replacement_def
    by simp
qed

lemma formula_repl1_intf : "iterates_replacement(##M, is_formula_functor(##M), 0)"
  using arity_formula_functor_fm zero_in_M ord_simp_union
    iterates_repl_intf[where is_F_fm="formula_functor_fm(1,0)"]
    replacement_ax1(3)[unfolded replacement_assm_def]
  by simp

lemma tl_repl_intf:
  assumes "l \<in> M"
  shows "iterates_replacement(##M,\<lambda>l' t. is_tl(##M,l',t),l)"
  using assms arity_tl_fm ord_simp_union
    iterates_repl_intf[where is_F_fm="tl_fm(1,0)"]
    replacement_ax1(9)[unfolded replacement_assm_def]
  by simp

lemma eclose_repl1_intf:
  assumes "A\<in>M"
  shows "iterates_replacement(##M, big_union(##M), A)"
  using assms arity_big_union_fm
    iterates_repl_intf[where is_F_fm="big_union_fm(1,0)"]
    replacement_ax1(5)[unfolded replacement_assm_def]
    ord_simp_union
  by simp

lemma list_repl2_intf:
  assumes "A\<in>M"
  shows "strong_replacement(##M,\<lambda>n y. n\<in>nat \<and>
            is_iterates(##M, is_list_functor(##M,A), 0, n, y))"
proof -
  let ?f = "And(Member(0,4),is_iterates_fm(list_functor_fm(13,1,0),3,0,1))"
  note zero_in_M nat_in_M \<open>A\<in>M\<close>
  moreover from this
  have "is_list_functor(##M,A,a,b) \<longleftrightarrow>
        (M, [b,a,c,d,e,f,g,h,i,j,k,n,y,A,0,nat] \<Turnstile> list_functor_fm(13,1,0))"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that
    by simp
  moreover from calculation
  have "(M, [n,y,A,0,nat] \<Turnstile> is_iterates_fm(list_functor_fm(13,1,0),3,0,1)) \<longleftrightarrow>
           is_iterates(##M, is_list_functor(##M,A), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that sats_is_iterates_fm[of M "is_list_functor(##M,A)"]
    by simp
  moreover from calculation
  have "(M, [n,y,A,0,nat] \<Turnstile> ?f) \<longleftrightarrow>
        n\<in>nat \<and> is_iterates(##M, is_list_functor(##M,A), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that
    by simp
  moreover
  have "arity(?f) = 5"
    using arity_is_iterates_fm[where p="list_functor_fm(13,1,0)" and i=14]
      arity_list_functor_fm arity_And ord_simp_union
    by simp
  ultimately
  show ?thesis
    using replacement_ax1(2)[unfolded replacement_assm_def] repl_sats[of M ?f "[A,0,nat]"]
    by simp
qed

lemma formula_repl2_intf:
  "strong_replacement(##M,\<lambda>n y. n\<in>nat \<and> is_iterates(##M, is_formula_functor(##M), 0, n, y))"
proof -
  let ?f = "And(Member(0,3),is_iterates_fm(formula_functor_fm(1,0),2,0,1))"
  note zero_in_M nat_in_M
  moreover from this
  have "is_formula_functor(##M,a,b) \<longleftrightarrow>
        (M, [b,a,c,d,e,f,g,h,i,j,k,n,y,0,nat] \<Turnstile> formula_functor_fm(1,0))"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that
    by simp
  moreover from calculation
  have "(M, [n,y,0,nat] \<Turnstile> is_iterates_fm(formula_functor_fm(1,0),2,0,1)) \<longleftrightarrow>
           is_iterates(##M, is_formula_functor(##M), 0, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that sats_is_iterates_fm[of M "is_formula_functor(##M)"]
    by simp
  moreover from calculation
  have "(M, [n,y,0,nat] \<Turnstile> ?f) \<longleftrightarrow>
        n\<in>nat \<and> is_iterates(##M, is_formula_functor(##M), 0, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that
    by simp
  moreover
  have "arity(?f) = 4"
    using arity_is_iterates_fm[where p="formula_functor_fm(1,0)" and i=2]
      arity_formula_functor_fm arity_And ord_simp_union
    by simp
  ultimately
  show ?thesis
    using replacement_ax1(4)[unfolded replacement_assm_def] repl_sats[of M ?f "[0,nat]"]
    by simp
qed


lemma eclose_repl2_intf:
  assumes "A\<in>M"
  shows "strong_replacement(##M,\<lambda>n y. n\<in>nat \<and> is_iterates(##M, big_union(##M), A, n, y))"
proof -
  let ?f = "And(Member(0,3),is_iterates_fm(big_union_fm(1,0),2,0,1))"
  note nat_in_M \<open>A\<in>M\<close>
  moreover from this
  have "big_union(##M,a,b) \<longleftrightarrow>
        (M, [b,a,c,d,e,f,g,h,i,j,k,n,y,A,nat] \<Turnstile> big_union_fm(1,0))"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "f\<in>M""g\<in>M""h\<in>M""i\<in>M""j\<in>M" "k\<in>M" "n\<in>M" "y\<in>M"
    for a b c d e f g h i j k n y
    using that by simp
  moreover from calculation
  have "(M, [n,y,A,nat] \<Turnstile> is_iterates_fm(big_union_fm(1,0),2,0,1)) \<longleftrightarrow>
           is_iterates(##M, big_union(##M), A, n , y)"
    if "n\<in>M" "y\<in>M" for n y
    using that sats_is_iterates_fm[of M "big_union(##M)"]
    by simp
  moreover from calculation
  have "(M, [n,y,A,nat] \<Turnstile> ?f) \<longleftrightarrow>
        n\<in>nat \<and> is_iterates(##M, big_union(##M), A, n, y)"
    if "n\<in>M" "y\<in>M" for n y
    using that
    by simp
  moreover
  have "arity(?f) = 4"
    using arity_is_iterates_fm[where p="big_union_fm(1,0)" and i=2]
      arity_big_union_fm arity_And ord_simp_union
    by simp
  ultimately
  show ?thesis
    using repl_sats[of M ?f "[A,nat]"] replacement_ax1(6)[unfolded replacement_assm_def]
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

sublocale M_ZF1_trans \<subseteq> M_datatypes "##M"
  using list_repl1_intf list_repl2_intf formula_repl1_intf
    formula_repl2_intf tl_repl_intf
  by unfold_locales auto

sublocale M_ZF1_trans \<subseteq> M_eclose "##M"
  using eclose_repl1_intf eclose_repl2_intf
  by unfold_locales auto

text\<open>Interface with \<^locale>\<open>M_eclose\<close>.\<close>

schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env)) \<longleftrightarrow> (A, env \<Turnstile> ?ivs_fm(i,v))"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

synthesize "is_Vset" from_schematic "sats_is_Vset_fm_auto"
arity_theorem for "is_Vset_fm"

declare is_Hrank_fm_def[fm_definitions add]

context M_ZF1_trans
begin

lemma wfrec_rank :
  assumes "X\<in>M"
  shows "wfrec_replacement(##M,is_Hrank(##M),rrank(X))"
proof -
  let ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0)))"
  note assms zero_in_M
  moreover from this
  have
    "is_Hrank(##M,a2, a1, a0) \<longleftrightarrow>
             (M, [a0,a1,a2,a3,a4,y,x,z,rrank(X)] \<Turnstile> is_Hrank_fm(2,1,0))"
    if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
    using that rrank_in_M is_Hrank_iff_sats
    by simp
  moreover from calculation
  have "(M, [y,x,z,rrank(X)] \<Turnstile> is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0)) \<longleftrightarrow>
   is_wfrec(##M, is_Hrank(##M) ,rrank(X), x, y)"
    if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
    using that rrank_in_M sats_is_wfrec_fm
    by simp
  moreover from calculation
  have "(M, [x,z,rrank(X)] \<Turnstile> ?f) \<longleftrightarrow>
               (\<exists>y\<in>M. pair(##M,x,y,z) \<and> is_wfrec(##M, is_Hrank(##M) , rrank(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that rrank_in_M
    by (simp del:pair_abs)
  moreover
  have "arity(?f) = 3"
    using arity_wfrec_replacement_fm[where p="is_Hrank_fm(2,1,0)" and i=3,simplified]
      arity_is_Hrank_fm[of 2 1 0,simplified] ord_simp_union
    by simp
  moreover from calculation
  have "strong_replacement(##M,\<lambda>x z. (M, [x,z,rrank(X)] \<Turnstile> ?f))"
    using replacement_ax1(7)[unfolded replacement_assm_def] rrank_in_M
    by simp
  ultimately
  show ?thesis
    using repl_sats[of M ?f "[rrank(X)]"]
    unfolding wfrec_replacement_def
    by (simp del:pair_abs)
qed

lemma trans_repl_HVFrom :
  assumes "A\<in>M" "i\<in>M"
  shows "transrec_replacement(##M,is_HVfrom(##M,A),i)"
proof -
  let ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0)))"
  note facts = assms zero_in_M
  moreover
  have "\<exists>sa\<in>M. \<exists>esa\<in>M. \<exists>mesa\<in>M.
       upair(##M,a,a,sa) \<and> is_eclose(##M,sa,esa) \<and> membership(##M,esa,mesa)"
    if "a\<in>M" for a
    using that upair_ax eclose_closed Memrel_closed
    unfolding upair_ax_def
    by (simp del:upair_abs)
  moreover
  {
    fix mesa
    assume "mesa\<in>M"
    moreover
    note facts
    moreover from calculation
    have "is_HVfrom(##M,A,a2, a1, a0) \<longleftrightarrow>
      (M, [a0,a1,a2,a3,a4,y,x,z,A,mesa] \<Turnstile> is_HVfrom_fm(8,2,1,0))"
      if "a4\<in>M" "a3\<in>M" "a2\<in>M" "a1\<in>M" "a0\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" for a4 a3 a2 a1 a0 y x z
      using that sats_is_HVfrom_fm
      by simp
    moreover from calculation
    have "(M, [y,x,z,A,mesa] \<Turnstile> is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0)) \<longleftrightarrow>
         is_wfrec(##M, is_HVfrom(##M,A),mesa, x, y)"
      if "y\<in>M" "x\<in>M" "z\<in>M" for y x z
      using that sats_is_wfrec_fm
      by simp
    moreover from calculation
    have "(M, [x,z,A,mesa] \<Turnstile> ?f) \<longleftrightarrow>
               (\<exists>y\<in>M. pair(##M,x,y,z) \<and> is_wfrec(##M, is_HVfrom(##M,A) , mesa, x, y))"
      if "x\<in>M" "z\<in>M" for x z
      using that
      by (simp del:pair_abs)
    moreover
    have "arity(?f) = 4"
      using arity_wfrec_replacement_fm[where p="is_HVfrom_fm(8,2,1,0)" and i=9]
        arity_is_HVfrom_fm ord_simp_union
      by simp
    moreover from calculation
    have "strong_replacement(##M,\<lambda>x z. (M, [x,z,A,mesa] \<Turnstile> ?f))"
      using replacement_ax1(8)[unfolded replacement_assm_def]
      by simp
    ultimately
    have "wfrec_replacement(##M,is_HVfrom(##M,A),mesa)"
      using repl_sats[of M ?f "[A,mesa]"]
      unfolding wfrec_replacement_def
      by (simp del:pair_abs)
  }
  ultimately
  show ?thesis
    unfolding transrec_replacement_def
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

subsection\<open>Interface for proving Collects and Replace in M.\<close>
context M_ZF1_trans
begin

lemma Collect_in_M :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)" "A\<in>M" and
    satsQ: "\<And>x. x\<in>M \<Longrightarrow> (M, [x]@env \<Turnstile> \<phi>) \<longleftrightarrow> Q(x)"
  shows
    "{y\<in>A . Q(y)}\<in>M"
proof -
  have "separation(##M,\<lambda>x. (M, [x] @ env \<Turnstile> \<phi>))"
    using assms separation_ax by simp
  then
  show ?thesis
    using \<open>A\<in>M\<close> satsQ transitivity separation_closed
      separation_cong[of "##M" "\<lambda>y. (M, [y]@env \<Turnstile> \<phi>)" "Q"]
    by simp
qed

\<comment> \<open>This version has a weaker assumption.\<close>
lemma separation_in_M :
  assumes
    "\<phi> \<in> formula" "env\<in>list(M)"
    "arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)" "A\<in>M" and
    satsQ: "\<And>x. x\<in>A \<Longrightarrow> (M, [x]@env \<Turnstile> \<phi>) \<longleftrightarrow> Q(x)"
  shows
    "{y\<in>A . Q(y)} \<in> M"
proof -
  let ?\<phi>' = "And(\<phi>,Member(0,length(env)+\<^sub>\<omega>1))"
  note assms
  moreover
  have "arity(?\<phi>') \<le> 1 +\<^sub>\<omega> length(env@[A])"
    using assms Un_le le_trans[of "arity(\<phi>)" "1+\<^sub>\<omega>length(env)" "2+\<^sub>\<omega>length(env)"]
    by (force simp:FOL_arities)
  moreover from calculation
  have "?\<phi>'\<in>formula" "nth(length(env), env @ [A]) = A"
    using nth_append
    by auto
  moreover from calculation
  have "\<And> x . x \<in> M \<Longrightarrow> (M, [x]@env@[A] \<Turnstile> ?\<phi>') \<longleftrightarrow> Q(x) \<and> x\<in>A"
    using arity_sats_iff[of _ "[A]" _ "[_]@env"]
    by auto
  ultimately
  show ?thesis
    using Collect_in_M[of ?\<phi>' "env@[A]" _ "\<lambda>x . Q(x) \<and> x\<in>A", OF _ _ _ \<open>A\<in>M\<close>]
    by auto
qed

end \<comment> \<open>\<^locale>\<open>M_ZF1_trans\<close>\<close>

context M_Z_trans
begin

lemma strong_replacement_in_ctm:
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>M \<Longrightarrow> f(x) \<in> M" and
    phi_replacement:"replacement_assm(M,env,\<phi>)" and
    "env\<in>list(M)"
  shows "strong_replacement(##M, \<lambda>x y . y = f(x))"
  using assms
    strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env\<Turnstile>\<phi>" "\<lambda>x y. y = f(x)"]
  unfolding replacement_assm_def
  by auto

lemma strong_replacement_rel_in_ctm :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> f(x,y)"  and
    phi_replacement:"replacement_assm(M,env,\<phi>)" and
    "env\<in>list(M)"
  shows "strong_replacement(##M, f)"
  using assms
    strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env\<Turnstile>\<phi>" "f"]
  unfolding replacement_assm_def
  by auto

lemma Replace_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)" and
    phi'_replacement:"replacement_assm(M,env@[A], \<cdot>\<phi> \<and> \<cdot>0 \<in> length(env) +\<^sub>\<omega> 2\<cdot>\<cdot> )"
  shows "{f(x) . x\<in>A}\<in>M"
proof -
  let ?\<phi>' = "And(\<phi>,Member(0,length(env)+\<^sub>\<omega>2))"
  note assms
  moreover from this
  have "arity(?\<phi>') \<le> 2 +\<^sub>\<omega> length(env@[A])"
    using Un_le le_trans[of "arity(\<phi>)" "2+\<^sub>\<omega>(length(env))" "3+\<^sub>\<omega>length(env)"]
    by (force simp:FOL_arities)
  moreover from calculation
  have "?\<phi>'\<in>formula" "nth(length(env), env @ [A]) = A"
    using nth_append by auto
  moreover from calculation
  have "\<And> x y. x \<in> M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env@[A]\<Turnstile>?\<phi>') \<longleftrightarrow> y=f(x) \<and>x\<in>A"
    using arity_sats_iff[of _ "[A]" _ "[_,_]@env"]
    by auto
  moreover from calculation
  have "strong_replacement(##M, \<lambda>x y. M,[x,y]@env@[A] \<Turnstile> ?\<phi>')"
    using phi'_replacement assms(1-6) unfolding replacement_assm_def by simp
  ultimately
  have 4:"strong_replacement(##M, \<lambda>x y. y = f(x) \<and> x\<in>A)"
    using
      strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env@[A]\<Turnstile>?\<phi>'" "\<lambda>x y. y = f(x) \<and> x\<in>A"]
    by simp
  then
  have "{y . x\<in>A , y = f(x)} \<in> M"
    using \<open>A\<in>M\<close> strong_replacement_closed[OF 4,of A] fclosed by simp
  moreover
  have "{f(x). x\<in>A} = { y . x\<in>A , y = f(x)}"
    by auto
  ultimately
  show ?thesis by simp
qed

lemma Replace_relativized_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)" and
    phi'_replacement:"replacement_assm(M,env@[A], \<cdot>\<phi> \<and> \<cdot>0 \<in> length(env) +\<^sub>\<omega> 2\<cdot>\<cdot> )"
  shows "{f(x) . x\<in>A}\<in>M"
  using assms Replace_in_M[of \<phi>] by auto

lemma ren_action :
  assumes
    "env\<in>list(M)" "x\<in>M" "y\<in>M" "z\<in>M"
  shows "\<forall> i . i < 2+\<^sub>\<omega>length(env) \<longrightarrow>
          nth(i,[x,z]@env) = nth(\<rho>_repl(length(env))`i,[z,x,y]@env)"
proof -
  let ?f="{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}"
  have 1:"(\<And>j. j < length(env) \<Longrightarrow> nth(j, env) = nth(id(length(env)) ` j, env))"
    using assms ltD by simp
  have 2:"nth(j, [x,z]) = nth(?f ` j, [z,x,y])" if "j<2" for j
  proof -
    consider "j=0" | "j=1" using  ltD[OF \<open>j<2\<close>] by auto
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using apply_equality f_type by simp
    next
      case 2
      then show ?thesis using apply_equality f_type by simp
    qed
  qed
  show ?thesis
    using sum_action[OF _ _ _ _ f_type id_type _ _ _ _ _ _ _ 2 1,simplified] assms
    unfolding \<rho>_repl_def by simp
qed

lemma Lambda_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M" and
    "A\<in>M" "env\<in>list(M)" and
    phi'_replacement2: "replacement_assm(M,env@[A],Lambda_in_M_fm(\<phi>,length(env)))"
  shows "(\<lambda>x\<in>A . f(x)) \<in>M"
  unfolding lam_def
proof -
  let ?ren="\<rho>_repl(length(env))"
  let ?j="2+\<^sub>\<omega>length(env)"
  let ?k="3+\<^sub>\<omega>length(env)"
  let ?\<psi>="ren(\<phi>)`?j`?k`?ren"
  let ?\<phi>'="Exists(And(pair_fm(1,0,2),?\<psi>))"
  let ?p="\<lambda>x y. \<exists>z\<in>M. pair(##M,x,z,y) \<and> is_f(x,z)"
  have "?\<phi>'\<in>formula" "?\<psi>\<in>formula"
    using \<open>env\<in>_\<close> length_type f_fm ren_type ren_tc[of \<phi> "2+\<^sub>\<omega>length(env)" "3+\<^sub>\<omega>length(env)" ?ren]
    by simp_all
  moreover from this
  have "arity(?\<psi>)\<le>3+\<^sub>\<omega>(length(env))" "arity(?\<psi>)\<in>nat"
    using assms arity_ren[OF f_fm _ _ ren_type,of "length(env)"] by simp_all
  then
  have "arity(?\<phi>') \<le> 2+\<^sub>\<omega>(length(env))"
    using Un_le pred_Un_distrib assms pred_le
    by (simp add:arity)
  moreover from this calculation
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(x,y)" for x y
    using \<open>env\<in>_\<close> length_type[OF \<open>env\<in>_\<close>] assms transitivity[OF _ \<open>A\<in>M\<close>]
      sats_iff_sats_ren[OF f_fm _ _ _ _ ren_type f_ar ren_action[rule_format,of _ x y],of _ M ]
    by auto
  moreover
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> ?p(x,y) \<longleftrightarrow> y = <x,f(x)>" for x y
    using assms transitivity[OF _ \<open>A\<in>_\<close>] fclosed
    by simp
  moreover
  have "\<And> x . x\<in>A \<Longrightarrow> <x,f(x)> \<in> M"
    using transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fclosed by simp
  ultimately
  show "{\<langle>x,f(x)\<rangle> . x\<in>A } \<in> M"
    using Replace_in_M[of ?\<phi>' env A] phi'_replacement2 \<open>A\<in>M\<close> \<open>env\<in>_\<close>
    by simp
qed

lemma ren_action' :
  assumes
    "env\<in>list(M)" "x\<in>M" "y\<in>M" "z\<in>M" "u\<in>M"
  shows "\<forall> i . i < 3+\<^sub>\<omega>length(env) \<longrightarrow>
          nth(i,[x,z,u]@env) = nth(\<rho>_pair_repl(length(env))`i,[x,z,y,u]@env)"
proof -
  let ?f="{\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2,3\<rangle>}"
  have 1:"(\<And>j. j < length(env) \<Longrightarrow> nth(j, env) = nth(id(length(env)) ` j, env))"
    using assms ltD by simp
  have 2:"nth(j, [x,z,u]) = nth(?f ` j, [x,z,y,u])" if "j<3" for j
  proof -
    consider "j=0" | "j=1" | "j=2" using  ltD[OF \<open>j<3\<close>] by auto
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using apply_equality f_type' by simp
    next
      case 2
      then show ?thesis using apply_equality f_type' by simp
    next
      case 3
      then show ?thesis using apply_equality f_type' by simp
    qed
  qed
  show ?thesis
    using sum_action[OF _ _ _ _ f_type' id_type _ _ _ _ _ _ _ 2 1,simplified] assms
    unfolding \<rho>_pair_repl_def by simp
qed

lemma LambdaPair_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 3 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> (M,[x,z,r]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,z,r)" and
    fabs:  "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> is_f(x,z,r) \<longleftrightarrow> r = f(x,z)" and
    fclosed: "\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> f(x,z) \<in> M" and
    "A\<in>M" "env\<in>list(M)" and
    phi'_replacement3: "replacement_assm(M,env@[A],LambdaPair_in_M_fm(\<phi>,length(env)))"
  shows "(\<lambda>x\<in>A . f(fst(x),snd(x))) \<in>M"
proof -
  let ?ren="\<rho>_pair_repl(length(env))"
  let ?j="3+\<^sub>\<omega>length(env)"
  let ?k="4+\<^sub>\<omega>length(env)"
  let ?\<psi>="ren(\<phi>)`?j`?k`?ren"
  let ?\<phi>'="Exists(Exists(And(fst_fm(2,0),(And(snd_fm(2,1),?\<psi>)))))"
  let ?p="\<lambda>x y. is_f(fst(x),snd(x),y)"
  have "?\<phi>'\<in>formula" "?\<psi>\<in>formula"
    using \<open>env\<in>_\<close> length_type f_fm ren_type' ren_tc[of \<phi> ?j ?k ?ren]
    by simp_all
  moreover from this
  have "arity(?\<psi>)\<le>4+\<^sub>\<omega>(length(env))" "arity(?\<psi>)\<in>nat"
    using assms arity_ren[OF f_fm _ _ ren_type',of "length(env)"] by simp_all
  moreover from calculation
  have 1:"arity(?\<phi>') \<le> 2+\<^sub>\<omega>(length(env))" "?\<phi>'\<in>formula"
    using Un_le pred_Un_distrib assms pred_le
    by (simp_all add:arity)
  moreover from this calculation
  have 2:"x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(x,y)" for x y
    using
      sats_iff_sats_ren[OF f_fm _ _ _ _ ren_type' f_ar
        ren_action'[rule_format,of _ "fst(x)" x "snd(x)" y],simplified]
      \<open>env\<in>_\<close> length_type[OF \<open>env\<in>_\<close>] transitivity[OF _ \<open>A\<in>M\<close>]
      fst_snd_closed pair_in_M_iff fsats[of "fst(x)" "snd(x)" y,symmetric]
      fst_abs snd_abs
    by auto
  moreover from assms
  have 3:"x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> ?p(x,y) \<longleftrightarrow> y = f(fst(x),snd(x))" for x y
    using fclosed fst_snd_closed pair_in_M_iff fabs transitivity
    by auto
  moreover
  have 4:"\<And> x . x\<in>A \<Longrightarrow> <x,f(fst(x),snd(x))> \<in> M" "\<And> x . x\<in>A \<Longrightarrow> f(fst(x),snd(x)) \<in> M"
    using transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fclosed fst_snd_closed
    by simp_all
  ultimately
  show ?thesis
    using Lambda_in_M[unfolded Lambda_in_M_fm_def, of ?\<phi>', OF _ _ _ _ _ _ _
        phi'_replacement3[unfolded LambdaPair_in_M_fm_def]]
      \<open>env\<in>_\<close> \<open>A\<in>_\<close> by simp

qed

lemma (in M_ZF1_trans) lam_replacement2_in_ctm :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 3 +\<^sub>\<omega> length(env)" and
    fsats: "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> (M,[x,z,r]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,z,r)" and
    fabs:  "\<And>x z r. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> is_f(x,z,r) \<longleftrightarrow> r = f(x,z)" and
    fclosed: "\<And>x z. x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> f(x,z) \<in> M" and
    "env\<in>list(M)" and
    phi'_replacement3: "\<And>A. A\<in>M \<Longrightarrow> replacement_assm(M,env@[A],LambdaPair_in_M_fm(\<phi>,length(env)))"
  shows "lam_replacement(##M , \<lambda>x . f(fst(x),snd(x)))"
  using
    LambdaPair_in_M fabs
    f_ar ord_simp_union transitivity assms fst_snd_closed
  by (rule_tac lam_replacement_iff_lam_closed[THEN iffD2],simp_all)

simple_rename "ren_U" src "[z1,x_P, x_leq, x_o, x_t, z2_c]"
  tgt "[z2_c,z1,z,x_P, x_leq, x_o, x_t]"

simple_rename "ren_V" src "[fz,x_P, x_leq, x_o,x_f, x_t, gz]"
  tgt "[gz,fz,z,x_P, x_leq, x_o,x_f, x_t]"

simple_rename "ren_V3" src "[fz,x_P, x_leq, x_o,x_f, gz, hz]"
  tgt "[hz,gz,fz,z,x_P, x_leq, x_o,x_f]"

lemma separation_sat_after_function_1:
  assumes "[a,b,c,d]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 6"
    and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 6" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 7" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, g(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-4)
  let ?\<psi>="ren(\<chi>)`6`7`ren_U_fn"
  let  ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,?\<psi>))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d, g(z)]"
  let ?env="[a, b, c, d]"
  let ?\<eta>="\<lambda>z.[g(z),f(z),z]@?env"
  note types
  moreover from this
  have "arity(\<chi>) \<le> 7" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_U_thm(2)[folded ren_U_fn_def] le_trans[of "arity(\<chi>)" 6]
    by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 7" "?\<psi>'\<in>formula"
    using arity_ren ren_U_thm(2)[folded ren_U_fn_def] f_fm g_fm
    by simp_all
  moreover from calculation f_ar g_ar f_fm g_fm
  have "arity(?\<psi>') \<le> 5"
    using ord_simp_union pred_le arity_type
    by (simp add:arity)
  moreover from calculation fclosed gclosed
  have 0:"(M, [f(z), a, b, c, d,  g(z)] \<Turnstile> \<chi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of \<chi> 6 7 _ _ "?\<eta>(z)"]
      ren_U_thm(1)[where A=M,folded ren_U_fn_def] ren_U_thm(2)[folded ren_U_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z]  gsats[of "g(z)" "f(z)" z] fclosed gclosed f_fm g_fm
  proof(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp,(auto)[1])
    assume "M, [z] @ [a, b, c, d] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> ren(\<chi>) ` 6 ` 7 ` ren_U_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
    then
    have "\<exists>xa\<in>M. (M, [xa, z, a, b, c, d] \<Turnstile> f_fm) \<and>
          (\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d] \<Turnstile> g_fm) \<and>
            (M, [x, xa, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn))"
      using that calculation by auto
    then
    obtain xa x where "x\<in>M" "xa\<in>M" "M, [xa, z, a, b, c, d] \<Turnstile> f_fm"
      "(M, [x, xa, z, a, b, c, d] \<Turnstile> g_fm)"
      "(M, [x, xa, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn)"
      using that calculation by auto
    moreover from this
    have "xa=f(z)" "x=g(z)" using fsats[of xa]  gsats[of x xa] that by simp_all
    ultimately
    show "M, [g(z), f(z), z] @ [a, b, c, d] \<Turnstile> ren(\<chi>) ` 6 ` 7 ` ren_U_fn"
      by auto
  qed
  moreover from calculation
  have "separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
    by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma separation_sat_after_function3:
  assumes "[a, b, c, d]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
    and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 6" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 7" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M" and
    h_fm:  "h_fm \<in> formula" and
    h_ar:  "arity(h_fm) \<le> 8" and
    hsats: "\<And> hx gx fx x. hx\<in>M \<Longrightarrow> gx\<in>M \<Longrightarrow> fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[hx,gx,fx,x]@[a, b, c, d] \<Turnstile> h_fm) \<longleftrightarrow> hx=h(x)" and
    hclosed: "\<And>x . x\<in>M \<Longrightarrow> h(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, g(r), h(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-3)
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V3_fn"
  let ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,Exists(And(h_fm,?\<psi>))))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d,g(z), h(z)]"
  let ?env="[a, b, c, d]"
  let ?\<eta>="\<lambda>z.[h(z),g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 9" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V3_thm(2)[folded ren_V3_fn_def] le_trans[of "arity(\<chi>)" 7]
    by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V3_thm(2)[folded ren_V3_fn_def] f_fm g_fm h_fm
    by (simp_all)
  moreover from this f_ar g_ar f_fm g_fm h_fm h_ar \<open>?\<psi>'\<in>_\<close>
  have "arity(?\<psi>') \<le> 5"
    using ord_simp_union arity_type nat_into_Ord
    by (simp add:arity,(rule_tac pred_le,simp,rule_tac Un_le,simp)+,simp_all add: \<open>?\<psi>\<in>_\<close>)
  moreover from calculation fclosed gclosed hclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" M "?\<eta>(z)"]
      ren_V3_thm(1)[where A=M,folded ren_V3_fn_def,simplified] ren_V3_thm(2)[folded ren_V3_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z] gsats[of "g(z)" "f(z)" z]
      hsats[of "h(z)" "g(z)" "f(z)" z]
      fclosed gclosed hclosed f_fm g_fm h_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
     apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="g(z)"],simp)
     apply(rule_tac conjI,simp,rule_tac rev_bexI[where x="h(z)"],simp,rule_tac conjI,simp,simp)
  proof -
    assume "M, [z] @ [a, b, c, d] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> (\<cdot>\<exists>\<cdot>h_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn\<cdot>\<cdot>)\<cdot>\<cdot>)\<cdot>\<cdot>)"
    with calculation that
    have "\<exists>x\<in>M. (M, [x, z, a, b, c, d] \<Turnstile> f_fm) \<and>
           (\<exists>xa\<in>M. (M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by auto
    with calculation
    obtain x where "x\<in>M" "(M, [x, z, a, b, c, d] \<Turnstile> f_fm)"
      "(\<exists>xa\<in>M. (M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm) \<and> (\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)))"
      by force
    moreover from this
    have "x=f(z)" using fsats[of x] that by simp
    moreover from calculation
    obtain xa where "xa\<in>M" "(M, [xa, x, z, a, b, c, d] \<Turnstile> g_fm)"
      "(\<exists>xb\<in>M. (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm) \<and> (M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn))"
      by auto
    moreover from calculation
    have "xa=g(z)" using gsats[of xa x] that by simp
    moreover from calculation
    obtain xb where "xb\<in>M" "(M, [xb, xa, x, z, a, b, c, d] \<Turnstile> h_fm)"
      "(M, [xb, xa, x, z, a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn)"
      by auto
    moreover from calculation
    have "xb=h(z)" using hsats[of xb xa x] that by simp
    ultimately
    show "M, [h(z), g(z), f(z), z] @ [a, b, c, d] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V3_fn"
      by auto
  qed
  moreover from calculation \<open>?\<psi>'\<in>_\<close>
  have "separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
    by simp
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed

lemma separation_sat_after_function:
  assumes "[a, b, c, d, \<tau>]\<in>list(M)" and  "\<chi>\<in>formula" and "arity(\<chi>) \<le> 7"
    and
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm) \<le> 7" and
    fsats: "\<And> fx x. fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[fx,x]@[a, b, c, d, \<tau>] \<Turnstile> f_fm) \<longleftrightarrow> fx=f(x)" and
    fclosed: "\<And>x . x\<in>M \<Longrightarrow> f(x) \<in> M" and
    g_fm:  "g_fm \<in> formula" and
    g_ar:  "arity(g_fm) \<le> 8" and
    gsats: "\<And> gx fx x. gx\<in>M \<Longrightarrow>  fx\<in>M \<Longrightarrow> x\<in>M \<Longrightarrow> (M,[gx,fx,x]@[a, b, c, d, \<tau>] \<Turnstile> g_fm) \<longleftrightarrow> gx=g(x)" and
    gclosed: "\<And>x . x\<in>M \<Longrightarrow> g(x) \<in> M"
  shows  "separation(##M, \<lambda>r. M, [f(r), a, b, c, d, \<tau>, g(r)] \<Turnstile> \<chi>)"
proof -
  note types = assms(1-3)
  let ?\<phi>="\<chi>"
  let ?\<psi>="ren(?\<phi>)`7`8`ren_V_fn"
  let  ?\<psi>'="Exists(And(f_fm,Exists(And(g_fm,?\<psi>))))"
  let ?\<rho>="\<lambda>z.[f(z), a, b, c, d, \<tau>, g(z)]"
  let ?env="[a, b, c, d, \<tau>]"
  let ?\<eta>="\<lambda>z.[g(z),f(z),z]@?env"
  note types
  moreover from this
  have "?\<phi>\<in>formula" by simp
  moreover from calculation
  have "arity(?\<phi>) \<le> 8" "?\<psi>\<in>formula"
    using ord_simp_union ren_tc ren_V_thm(2)[folded ren_V_fn_def] le_trans[of "arity(\<chi>)" 7]
    by simp_all
  moreover from calculation
  have "arity(?\<psi>) \<le> 8" "?\<psi>'\<in>formula"
    using arity_ren ren_V_thm(2)[folded ren_V_fn_def] f_fm g_fm
    by (simp_all)
  moreover from calculation f_ar g_ar f_fm g_fm
  have "arity(?\<psi>') \<le> 6"
    using ord_simp_union pred_le arity_type
    by (simp add:arity)
  moreover from calculation fclosed gclosed
  have 0:"(M, ?\<rho>(z) \<Turnstile> ?\<phi>) \<longleftrightarrow> (M,?\<eta>(z)\<Turnstile> ?\<psi>)" if "(##M)(z)" for z
    using sats_iff_sats_ren[of ?\<phi> 7 8 "?\<rho>(z)" _ "?\<eta>(z)"]
      ren_V_thm(1)[where A=M,folded ren_V_fn_def] ren_V_thm(2)[folded ren_V_fn_def] that
    by simp
  moreover from calculation
  have 1:"(M,?\<eta>(z)\<Turnstile> ?\<psi>) \<longleftrightarrow> M,[z]@?env\<Turnstile>?\<psi>'" if "(##M)(z)" for z
    using that fsats[OF fclosed[of z],of z]  gsats[of "g(z)" "f(z)" z]
      fclosed gclosed f_fm g_fm
    apply(rule_tac iffI,simp,rule_tac rev_bexI[where x="f(z)"],simp)
     apply(auto)[1]
  proof -
    assume "M, [z] @ [a, b, c, d, \<tau>] \<Turnstile> (\<cdot>\<exists>\<cdot>f_fm \<and> (\<cdot>\<exists>\<cdot>g_fm \<and> ren(\<chi>) ` 7 ` 8 ` ren_V_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
    then have "\<exists>xa\<in>M. (M, [xa, z, a, b, c, d, \<tau>] \<Turnstile> f_fm) \<and>
       (\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      using that calculation by auto
    then
    obtain xa where "xa\<in>M" "M, [xa, z, a, b, c, d, \<tau>] \<Turnstile> f_fm"
      "(\<exists>x\<in>M. (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm) \<and> (M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn))"
      by auto
    moreover from this
    have "xa=f(z)" using fsats[of xa] that by simp
    moreover from calculation
    obtain x where "x\<in>M" "M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> g_fm" "M, [x, xa, z, a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
    moreover from calculation
    have "x=g(z)" using gsats[of x xa] that by simp
    ultimately
    show "M, [g(z), f(z), z] @ [a, b, c, d, \<tau>] \<Turnstile> ren(\<chi>) ` 7 ` 8 ` ren_V_fn"
      by auto
  qed
  moreover from calculation
  have "separation(##M, \<lambda>z. (M,[z]@?env \<Turnstile> ?\<psi>'))"
    using separation_ax
    by simp_all
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD2,OF iff_trans[OF 0 1]],clarify,force)
qed
end

definition separation_assm_fm :: "[i,i,i] \<Rightarrow> i"
  where
  "separation_assm_fm(A,x,f_fm) \<equiv> (\<cdot>\<exists> (\<cdot>\<exists> \<cdot>\<cdot>0 \<in> A +\<^sub>\<omega> 2\<cdot> \<and> \<cdot>\<cdot>\<langle>0,1\<rangle> is x+\<^sub>\<omega> 2 \<cdot> \<and> f_fm \<cdot>\<cdot>\<cdot>)\<cdot>)" 

lemma separation_assm_fm_type[TC]: 
  "A \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> f_fm \<in> formula \<Longrightarrow> separation_assm_fm(A, y,f_fm) \<in> formula"
  unfolding separation_assm_fm_def
  by simp

lemma arity_separation_assm_fm : "A \<in> \<omega> \<Longrightarrow> x \<in> \<omega> \<Longrightarrow> f_fm \<in> formula \<Longrightarrow>
  arity(separation_assm_fm(A, x, f_fm)) = succ(A) \<union> succ(x) \<union> pred(pred(arity(f_fm)))"
  using pred_Un_distrib
  unfolding separation_assm_fm_def
  by (auto simp add:arity)

definition separation_assm_bin_fm where
  "separation_assm_bin_fm(A,y,f_fm) \<equiv> 
    (\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>(\<cdot>\<cdot>3 \<in> A +\<^sub>\<omega> 4\<cdot> \<and>  \<cdot>\<langle>3,2\<rangle> is y +\<^sub>\<omega> 4\<cdot>\<cdot> ) \<and> \<cdot>f_fm \<and> \<cdot> \<cdot>fst(3) is 0 \<cdot> \<and> \<cdot>snd(3) is 1\<cdot>\<cdot>\<cdot>\<cdot> ) \<cdot>)\<cdot>)\<cdot>)\<cdot>) "

lemma separation_assm_bin_fm_type[TC]: 
  "A \<in> \<omega> \<Longrightarrow> y \<in> \<omega> \<Longrightarrow> f_fm \<in> formula \<Longrightarrow> separation_assm_bin_fm(A, y,f_fm) \<in> formula"
  unfolding separation_assm_bin_fm_def
  by simp

lemma arity_separation_assm_bin_fm : "A \<in> \<omega> \<Longrightarrow> x \<in> \<omega> \<Longrightarrow> f_fm \<in> formula \<Longrightarrow>
  arity(separation_assm_bin_fm(A, x, f_fm)) = succ(A) \<union> succ(x) \<union> (pred^4(arity(f_fm)))"
  using pred_Un_distrib
  unfolding separation_assm_bin_fm_def
  by (auto simp add:arity)

context M_Z_trans
begin

lemma separation_assm_sats : 
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>) = 2" and
    fsats: "\<And>env x y. env\<in>list(M) \<Longrightarrow> x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>M \<Longrightarrow> f(x) \<in> M" and
    "A\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, f(x)\<rangle>)"
proof -
  let ?\<phi>'="separation_assm_fm(1,0,\<phi>)"
  let ?p="\<lambda>y. \<exists>x\<in>M . x\<in>A \<and> y = \<langle>x, f(x)\<rangle>"
  from f_fm
  have "?\<phi>'\<in>formula"
     by simp
  moreover from this f_ar f_fm
  have "arity(?\<phi>') = 2"
    using arity_separation_assm_fm[of 1 0 \<phi>] ord_simp_union  
    by simp
  moreover from \<open>A\<in>M\<close> calculation
  have "separation(##M,\<lambda>y . M,[y,A] \<Turnstile> ?\<phi>')"
    using separation_ax by auto
  moreover
  have "y\<in>M \<Longrightarrow> (M,[y,A] \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(y)" for y
    using assms transitivity[OF _ \<open>A\<in>M\<close>]
    unfolding separation_assm_fm_def
    by auto  
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD1],auto)
qed

lemma separation_assm_bin_sats :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>) = 3" and
    fsats: "\<And>env x z y. env\<in>list(M) \<Longrightarrow> x\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> (M,[x,z,y]@env \<Turnstile> \<phi>) \<longleftrightarrow> is_f(x,z,y)" and
    fabs:  "\<And>x z y. x\<in>M \<Longrightarrow>  z\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,z,y) \<longleftrightarrow> y = f(x,z)" and
    fclosed: "\<And>x z . x\<in>M \<Longrightarrow>  z\<in>M \<Longrightarrow> f(x,z) \<in> M" and
    "A\<in>M"
  shows "separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, f(fst(x),snd(x))\<rangle>)"
proof -
  let ?\<phi>'="separation_assm_bin_fm(1,0,\<phi>)"
  let ?p="\<lambda>y. \<exists>x\<in>M . x\<in>A \<and> y = \<langle>x, f(fst(x),snd(x))\<rangle>"
  from f_fm
  have "?\<phi>'\<in>formula"
     by simp
  moreover from this f_ar f_fm
  have "arity(?\<phi>') = 2"
    using arity_separation_assm_bin_fm[of 1 0 \<phi>] ord_simp_union  
    by simp
  moreover from \<open>A\<in>M\<close> calculation
  have "separation(##M,\<lambda>y . M,[y,A] \<Turnstile> ?\<phi>')"
    using separation_ax by auto
  moreover
  have "y\<in>M \<Longrightarrow> (M,[y,A] \<Turnstile> ?\<phi>') \<longleftrightarrow> ?p(y)" for y
    using assms transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fst_abs snd_abs fst_closed snd_closed
    unfolding separation_assm_bin_fm_def
    by auto
  ultimately
  show ?thesis
    by(rule_tac separation_cong[THEN iffD1],auto)
qed

lemma separation_Union: "A\<in>M \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, Union(x)\<rangle>)"
  using separation_assm_sats[of "big_union_fm(0,1)"] arity_big_union_fm ord_simp_union
    Union_closed[simplified]
  by simp

lemma lam_replacement_Union: "lam_replacement(##M, Union)"
  using lam_replacement_Union' separation_Union transM by simp

lemma separation_fst: "A\<in>M \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, fst(x)\<rangle>)"
  using separation_assm_sats[of "fst_fm(0,1)"] arity_fst_fm ord_simp_union
    fst_closed fst_abs
  by simp

lemma lam_replacement_fst: "lam_replacement(##M, fst)"
  using lam_replacement_fst' separation_fst transM by simp

lemma separation_snd: "A\<in>M \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x \<in> M . x\<in>A \<and> y = \<langle>x, snd(x)\<rangle>)"
  using separation_assm_sats[of "snd_fm(0,1)"] arity_snd_fm ord_simp_union
    snd_closed[simplified] snd_abs
  by simp

lemma lam_replacement_snd: "lam_replacement(##M, snd)"
  using lam_replacement_snd' separation_snd transM by simp

text\<open>Binary lambda-replacements\<close>

lemma separation_Image: "A\<in>M \<Longrightarrow>
     separation(##M, \<lambda>y. \<exists>x\<in>M. x \<in> A \<and> y = \<langle>x, fst(x) `` snd(x)\<rangle>)"
  using  arity_image_fm ord_simp_union
    nonempty image_closed image_abs
  by (rule_tac separation_assm_bin_sats[of "image_fm(0,1,2)"],auto)

lemma lam_replacement_Image: "lam_replacement(##M, \<lambda>x . fst(x) `` snd(x))"
  using lam_replacement_Image' separation_Image
  by simp

lemma separation_middle_del: "A\<in>M \<Longrightarrow>
     separation(##M, \<lambda>y. \<exists>x\<in>M. x \<in> A \<and> y = \<langle>x, middle_del(fst(x), snd(x))\<rangle>)"
 using  arity_is_middle_del_fm ord_simp_union nonempty
    fst_abs snd_abs fst_closed snd_closed pair_in_M_iff
  by (rule_tac separation_assm_bin_sats[of "is_middle_del_fm(0,1,2)"],
      auto simp:is_middle_del_def middle_del_def)

lemma lam_replacement_middle_del: "lam_replacement(##M, \<lambda>r . middle_del(fst(r),snd(r)))"
  using lam_replacement_middle_del' separation_middle_del
  by simp

lemma separation_prodRepl: "A\<in>M \<Longrightarrow>
     separation(##M, \<lambda>y. \<exists>x\<in>M. x \<in> A \<and> y = \<langle>x, prodRepl(fst(x), snd(x))\<rangle>)"
   using  arity_is_prodRepl_fm ord_simp_union nonempty
    fst_abs snd_abs fst_closed snd_closed pair_in_M_iff
  by (rule_tac separation_assm_bin_sats[of "is_prodRepl_fm(0,1,2)"],
      auto simp:is_prodRepl_def prodRepl_def)

lemma lam_replacement_prodRepl: "lam_replacement(##M, \<lambda>r . prodRepl(fst(r),snd(r)))"
  using lam_replacement_prodRepl' separation_prodRepl
  by simp

end  \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

context M_trivial
begin

lemma first_closed:
  "M(B) \<Longrightarrow> M(r) \<Longrightarrow> first(u,r,B) \<Longrightarrow> M(u)"
  using transM[OF first_is_elem] by simp

is_iff_rel for "first"
  unfolding is_first_def first_rel_def by auto

is_iff_rel for "minimum"
  unfolding is_minimum_def minimum_rel_def
  using is_first_iff The_abs nonempty
  by force

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

context M_Z_trans
begin

lemma (in M_basic) is_minimum_equivalence :
  "M(R) \<Longrightarrow> M(X) \<Longrightarrow> M(u) \<Longrightarrow> is_minimum(M,R,X,u) \<longleftrightarrow> is_minimum'(M,R,X,u)"
  unfolding is_minimum_def is_minimum'_def is_The_def is_first_def by simp

lemma separation_minimum: "A\<in>M \<Longrightarrow>
     separation(##M, \<lambda>y. \<exists>x\<in>M. x \<in> A \<and> y = \<langle>x, minimum(fst(x), snd(x))\<rangle>)"
  using  arity_minimum_fm ord_simp_union is_minimum_iff minimum_abs
    is_minimum_equivalence nonempty minimum_closed minimum_abs
  by (rule_tac separation_assm_bin_sats[of "minimum_fm(0,1,2)"], auto)

lemma lam_replacement_minimum: "lam_replacement(##M, \<lambda>x . minimum(fst(x),snd(x)))"
  using lam_replacement_minimum' separation_minimum
  by simp

end \<comment> \<open>\<^locale>\<open>M_Z_trans\<close>\<close>

end