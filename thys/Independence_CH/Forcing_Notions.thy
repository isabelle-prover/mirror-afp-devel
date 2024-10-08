section\<open>Forcing notions\<close>
text\<open>This theory defines a locale for forcing notions, that is,
 preorders with a distinguished maximum element.\<close>

theory Forcing_Notions
  imports
    "ZF-Constructible.Relative"
    "Delta_System_Lemma.ZF_Library"
begin

hide_const (open) Order.pred

subsection\<open>Basic concepts\<close>
text\<open>We say that two elements $p,q$ are
  \<^emph>\<open>compatible\<close> if they have a lower bound in $P$\<close>
definition compat_in :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>o" where
  "compat_in(A,r,p,q) \<equiv> \<exists>d\<in>A . \<langle>d,p\<rangle>\<in>r \<and> \<langle>d,q\<rangle>\<in>r"

lemma compat_inI :
  "\<lbrakk> d\<in>A ; \<langle>d,p\<rangle>\<in>r ; \<langle>d,g\<rangle>\<in>r \<rbrakk> \<Longrightarrow> compat_in(A,r,p,g)"
  by (auto simp add: compat_in_def)

lemma refl_compat:
  "\<lbrakk> refl(A,r) ; \<langle>p,q\<rangle> \<in> r | p=q | \<langle>q,p\<rangle> \<in> r ; p\<in>A ; q\<in>A\<rbrakk> \<Longrightarrow> compat_in(A,r,p,q)"
  by (auto simp add: refl_def compat_inI)

lemma  chain_compat:
  "refl(A,r) \<Longrightarrow> linear(A,r) \<Longrightarrow>  (\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,r,p,q))"
  by (simp add: refl_compat linear_def)

lemma subset_fun_image: "f:N\<rightarrow>P \<Longrightarrow> f``N\<subseteq>P"
  by (auto simp add: image_fun apply_funtype)

lemma refl_monot_domain: "refl(B,r) \<Longrightarrow> A\<subseteq>B \<Longrightarrow> refl(A,r)"
  unfolding refl_def by blast

locale forcing_notion =
  fixes P (\<open>\<bbbP>\<close>) and leq and one (\<open>\<one>\<close>)
  assumes one_in_P:       "\<one> \<in> \<bbbP>"
    and leq_preord:       "preorder_on(\<bbbP>,leq)"
    and one_max:          "\<forall>p\<in>\<bbbP>. \<langle>p,\<one>\<rangle>\<in>leq"
begin

abbreviation Leq :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<preceq>\<close> 50)
  where "x \<preceq> y \<equiv> \<langle>x,y\<rangle>\<in>leq"

lemma refl_leq:
  "r\<in>\<bbbP> \<Longrightarrow> r\<preceq>r"
  using leq_preord unfolding preorder_on_def refl_def by simp

text\<open>A set $D$ is \<^emph>\<open>dense\<close> if every element $p\in \mathbb{P}$ has a lower
bound in $D$.\<close>
definition
  dense :: "i\<Rightarrow>o" where
  "dense(D) \<equiv> \<forall>p\<in>\<bbbP>. \<exists>d\<in>D . d\<preceq>p"

text\<open>There is also a weaker definition which asks for
a lower bound in $D$ only for the elements below some fixed
element $q$.\<close>
definition
  dense_below :: "i\<Rightarrow>i\<Rightarrow>o" where
  "dense_below(D,q) \<equiv> \<forall>p\<in>\<bbbP>. p\<preceq>q \<longrightarrow> (\<exists>d\<in>D. d\<in>\<bbbP> \<and> d\<preceq>p)"

lemma P_dense: "dense(\<bbbP>)"
  by (insert leq_preord, auto simp add: preorder_on_def refl_def dense_def)

definition
  increasing :: "i\<Rightarrow>o" where
  "increasing(F) \<equiv> \<forall>x\<in>F. \<forall> p \<in> \<bbbP> . x\<preceq>p \<longrightarrow> p\<in>F"

definition
  compat :: "i\<Rightarrow>i\<Rightarrow>o" where
  "compat(p,q) \<equiv> compat_in(\<bbbP>,leq,p,q)"

lemma leq_transD:  "a\<preceq>b \<Longrightarrow> b\<preceq>c \<Longrightarrow> a \<in> \<bbbP>\<Longrightarrow> b \<in> \<bbbP>\<Longrightarrow> c \<in> \<bbbP>\<Longrightarrow> a\<preceq>c"
  using leq_preord trans_onD unfolding preorder_on_def by blast

lemma leq_transD':  "A\<subseteq>\<bbbP> \<Longrightarrow> a\<preceq>b \<Longrightarrow> b\<preceq>c \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> \<bbbP>\<Longrightarrow> c \<in> \<bbbP>\<Longrightarrow> a\<preceq>c"
  using leq_preord trans_onD subsetD unfolding preorder_on_def by blast

lemma compatD[dest!]: "compat(p,q) \<Longrightarrow> \<exists>d\<in>\<bbbP>. d\<preceq>p \<and> d\<preceq>q"
  unfolding compat_def compat_in_def .

abbreviation Incompatible :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<bottom>\<close> 50)
  where "p \<bottom> q \<equiv> \<not> compat(p,q)"

lemma compatI[intro!]: "d\<in>\<bbbP> \<Longrightarrow> d\<preceq>p \<Longrightarrow> d\<preceq>q \<Longrightarrow> compat(p,q)"
  unfolding compat_def compat_in_def by blast

lemma Incompatible_imp_not_eq: "\<lbrakk> p \<bottom> q; p\<in>\<bbbP>; q\<in>\<bbbP> \<rbrakk>\<Longrightarrow> p \<noteq> q"
  using refl_leq by blast

lemma denseD [dest]: "dense(D) \<Longrightarrow> p\<in>\<bbbP> \<Longrightarrow>  \<exists>d\<in>D. d\<preceq> p"
  unfolding dense_def by blast

lemma denseI [intro!]: "\<lbrakk> \<And>p. p\<in>\<bbbP> \<Longrightarrow> \<exists>d\<in>D. d\<preceq> p \<rbrakk> \<Longrightarrow> dense(D)"
  unfolding dense_def by blast

lemma dense_belowD [dest]:
  assumes "dense_below(D,p)" "q\<in>\<bbbP>" "q\<preceq>p"
  shows "\<exists>d\<in>D. d\<in>\<bbbP> \<and> d\<preceq>q"
  using assms unfolding dense_below_def by simp

lemma dense_belowI [intro!]:
  assumes "\<And>q. q\<in>\<bbbP> \<Longrightarrow> q\<preceq>p \<Longrightarrow> \<exists>d\<in>D. d\<in>\<bbbP> \<and> d\<preceq>q"
  shows "dense_below(D,p)"
  using assms unfolding dense_below_def by simp

lemma dense_below_cong: "p\<in>\<bbbP> \<Longrightarrow> D = D' \<Longrightarrow> dense_below(D,p) \<longleftrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_cong': "p\<in>\<bbbP> \<Longrightarrow> \<lbrakk>\<And>x. x\<in>\<bbbP> \<Longrightarrow> Q(x) \<longleftrightarrow> Q'(x)\<rbrakk> \<Longrightarrow>
           dense_below({q\<in>\<bbbP>. Q(q)},p) \<longleftrightarrow> dense_below({q\<in>\<bbbP>. Q'(q)},p)"
  by blast

lemma dense_below_mono: "p\<in>\<bbbP> \<Longrightarrow> D \<subseteq> D' \<Longrightarrow> dense_below(D,p) \<Longrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_under:
  assumes "dense_below(D,p)" "p\<in>\<bbbP>" "q\<in>\<bbbP>" "q\<preceq>p"
  shows "dense_below(D,q)"
  using assms leq_transD by blast

lemma ideal_dense_below:
  assumes "\<And>q. q\<in>\<bbbP> \<Longrightarrow> q\<preceq>p \<Longrightarrow> q\<in>D"
  shows "dense_below(D,p)"
  using assms refl_leq by blast

lemma dense_below_dense_below:
  assumes "dense_below({q\<in>\<bbbP>. dense_below(D,q)},p)" "p\<in>\<bbbP>"
  shows "dense_below(D,p)"
  using assms leq_transD refl_leq  by blast

text\<open>A filter is an increasing set $G$ with all its elements
being compatible in $G$.\<close>
definition
  filter :: "i\<Rightarrow>o" where
  "filter(G) \<equiv> G\<subseteq>\<bbbP> \<and> increasing(G) \<and> (\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G,leq,p,q))"

lemma filterD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> x \<in> \<bbbP>"
  by (auto simp add : subsetD filter_def)

lemma filter_subset_notion[dest]: "filter(G) \<Longrightarrow> G \<subseteq> \<bbbP>"
  by (auto dest:filterD)

lemma filter_leqD : "filter(G) \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> \<bbbP> \<Longrightarrow> x\<preceq>y \<Longrightarrow> y \<in> G"
  by (simp add: filter_def increasing_def)

lemma filter_imp_compat: "filter(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>G \<Longrightarrow> compat(p,q)"
  unfolding filter_def compat_in_def compat_def by blast

lemma low_bound_filter: \<comment> \<open>says the compatibility is attained inside G\<close>
  assumes "filter(G)" and "p\<in>G" and "q\<in>G"
  shows "\<exists>r\<in>G. r\<preceq>p \<and> r\<preceq>q"
  using assms
  unfolding compat_in_def filter_def by blast

text\<open>We finally introduce the upward closure of a set
and prove that the closure of $A$ is a filter if its elements are
compatible in $A$.\<close>
definition
  upclosure :: "i\<Rightarrow>i" where
  "upclosure(A) \<equiv> {p\<in>\<bbbP>.\<exists>a\<in>A. a\<preceq>p}"

lemma  upclosureI [intro] : "p\<in>\<bbbP> \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>p \<Longrightarrow> p\<in>upclosure(A)"
  by (simp add:upclosure_def, auto)

lemma  upclosureE [elim] :
  "p\<in>upclosure(A) \<Longrightarrow> (\<And>x a. x\<in>\<bbbP> \<Longrightarrow> a\<in>A \<Longrightarrow> a\<preceq>x \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add:upclosure_def)

lemma  upclosureD [dest] :
  "p\<in>upclosure(A) \<Longrightarrow> \<exists>a\<in>A.(a\<preceq>p) \<and> p\<in>\<bbbP>"
  by (simp add:upclosure_def)

lemma upclosure_increasing :
  assumes "A\<subseteq>\<bbbP>"
  shows "increasing(upclosure(A))"
  unfolding increasing_def upclosure_def
  using leq_transD'[OF \<open>A\<subseteq>\<bbbP>\<close>] by auto

lemma  upclosure_in_P: "A \<subseteq> \<bbbP> \<Longrightarrow> upclosure(A) \<subseteq> \<bbbP>"
  using subsetI upclosure_def by simp

lemma  A_sub_upclosure: "A \<subseteq> \<bbbP> \<Longrightarrow> A\<subseteq>upclosure(A)"
  using subsetI leq_preord
  unfolding upclosure_def preorder_on_def refl_def by auto

lemma  elem_upclosure: "A\<subseteq>\<bbbP> \<Longrightarrow> x\<in>A  \<Longrightarrow> x\<in>upclosure(A)"
  by (blast dest:A_sub_upclosure)

lemma  closure_compat_filter:
  assumes "A\<subseteq>\<bbbP>" "(\<forall>p\<in>A.\<forall>q\<in>A. compat_in(A,leq,p,q))"
  shows "filter(upclosure(A))"
  unfolding filter_def
proof(auto)
  show "increasing(upclosure(A))"
    using assms upclosure_increasing by simp
next
  let ?UA="upclosure(A)"
  show "compat_in(upclosure(A), leq, p, q)" if "p\<in>?UA" "q\<in>?UA" for p q
  proof -
    from that
    obtain a b where 1:"a\<in>A" "b\<in>A" "a\<preceq>p" "b\<preceq>q" "p\<in>\<bbbP>" "q\<in>\<bbbP>"
      using upclosureD[OF \<open>p\<in>?UA\<close>] upclosureD[OF \<open>q\<in>?UA\<close>] by auto
    with assms(2)
    obtain d where "d\<in>A" "d\<preceq>a" "d\<preceq>b"
      unfolding compat_in_def by auto
    with 1
    have "d\<preceq>p" "d\<preceq>q" "d\<in>?UA"
      using A_sub_upclosure[THEN subsetD] \<open>A\<subseteq>\<bbbP>\<close>
        leq_transD'[of A d a] leq_transD'[of A d b] by auto
    then
    show ?thesis unfolding compat_in_def by auto
  qed
qed

lemma  aux_RS1:  "f \<in> N \<rightarrow> \<bbbP> \<Longrightarrow> n\<in>N \<Longrightarrow> f`n \<in> upclosure(f ``N)"
  using elem_upclosure[OF subset_fun_image] image_fun
  by (simp, blast)

lemma decr_succ_decr:
  assumes "f \<in> nat \<rightarrow> \<bbbP>" "preorder_on(\<bbbP>,leq)"
    "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    "m\<in>nat"
  shows "n\<in>nat \<Longrightarrow> n\<le>m \<Longrightarrow> \<langle>f ` m, f ` n\<rangle> \<in> leq"
  using \<open>m\<in>_\<close>
proof(induct m)
  case 0
  then show ?case using assms refl_leq by simp
next
  case (succ x)
  then
  have 1:"f`succ(x) \<preceq> f`x" "f`n\<in>\<bbbP>" "f`x\<in>\<bbbP>" "f`succ(x)\<in>\<bbbP>"
    using assms by simp_all
  consider (lt) "n<succ(x)" | (eq) "n=succ(x)"
    using succ le_succ_iff by auto
  then
  show ?case
  proof(cases)
    case lt
    with 1 show ?thesis using leI succ leq_transD by auto
  next
    case eq
    with 1 show ?thesis using refl_leq by simp
  qed
qed

lemma decr_seq_linear:
  assumes "refl(\<bbbP>,leq)" "f \<in> nat \<rightarrow> \<bbbP>"
    "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    "trans[\<bbbP>](leq)"
  shows "linear(f `` nat, leq)"
proof -
  have "preorder_on(\<bbbP>,leq)"
    unfolding preorder_on_def using assms by simp
  {
    fix n m
    assume "n\<in>nat" "m\<in>nat"
    then
    have "f`m \<preceq> f`n \<or> f`n \<preceq> f`m"
    proof(cases "m\<le>n")
      case True
      with \<open>n\<in>_\<close> \<open>m\<in>_\<close>
      show ?thesis
        using decr_succ_decr[of f n m] assms leI \<open>preorder_on(\<bbbP>,leq)\<close> by simp
    next
      case False
      with \<open>n\<in>_\<close> \<open>m\<in>_\<close>
      show ?thesis
        using decr_succ_decr[of f m n] assms leI not_le_iff_lt \<open>preorder_on(\<bbbP>,leq)\<close> by simp
    qed
  }
  then
  show ?thesis
    unfolding linear_def using ball_image_simp assms by auto
qed

end \<comment> \<open>\<^locale>\<open>forcing_notion\<close>\<close>

subsection\<open>Towards Rasiowa-Sikorski Lemma (RSL)\<close>
locale countable_generic = forcing_notion +
  fixes \<D>
  assumes countable_subs_of_P:  "\<D> \<in> nat\<rightarrow>Pow(\<bbbP>)"
    and     seq_of_denses:        "\<forall>n \<in> nat. dense(\<D>`n)"

begin

definition
  D_generic :: "i\<Rightarrow>o" where
  "D_generic(G) \<equiv> filter(G) \<and> (\<forall>n\<in>nat.(\<D>`n)\<inter>G\<noteq>0)"

text\<open>The next lemma identifies a sufficient condition for obtaining
RSL.\<close>
lemma RS_sequence_imp_rasiowa_sikorski:
  assumes
    "p\<in>\<bbbP>" "f : nat\<rightarrow>\<bbbP>" "f ` 0 = p"
    "\<And>n. n\<in>nat \<Longrightarrow> f ` succ(n)\<preceq> f ` n \<and> f ` succ(n) \<in> \<D> ` n"
  shows
    "\<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  note assms
  moreover from this
  have "f``nat  \<subseteq> \<bbbP>"
    by (simp add:subset_fun_image)
  moreover from calculation
  have "refl(f``nat, leq) \<and> trans[\<bbbP>](leq)"
    using leq_preord unfolding preorder_on_def by (blast intro:refl_monot_domain)
  moreover from calculation
  have "\<forall>n\<in>nat.  f ` succ(n)\<preceq> f ` n" by (simp)
  moreover from calculation
  have "linear(f``nat, leq)"
    using leq_preord and decr_seq_linear unfolding preorder_on_def by (blast)
  moreover from calculation
  have "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"
    using chain_compat by (auto)
  ultimately
  have "filter(upclosure(f``nat))" (is "filter(?G)")
    using closure_compat_filter by simp
  moreover
  have "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume "n\<in>nat"
    with assms
    have "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then
    show "\<D> ` n \<inter> ?G \<noteq> 0"  by blast
  qed
  moreover from assms
  have "p \<in> ?G"
    using aux_RS1 by auto
  ultimately
  show ?thesis unfolding D_generic_def by auto
qed

end \<comment> \<open>\<^locale>\<open>countable_generic\<close>\<close>

text\<open>Now, the following recursive definition will fulfill the
requirements of lemma \<^term>\<open>RS_sequence_imp_rasiowa_sikorski\<close> \<close>

consts RS_seq :: "[i,i,i,i,i,i] \<Rightarrow> i"
primrec
  "RS_seq(0,P,leq,p,enum,\<D>) = p"
  "RS_seq(succ(n),P,leq,p,enum,\<D>) =
    enum`(\<mu> m. \<langle>enum`m, RS_seq(n,P,leq,p,enum,\<D>)\<rangle> \<in> leq \<and> enum`m \<in> \<D> ` n)"

context countable_generic
begin

lemma countable_RS_sequence_aux:
  fixes p enum
  defines "f(n) \<equiv> RS_seq(n,\<bbbP>,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>\<bbbP>" "\<bbbP> \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
    "\<And>x k. x\<in>\<bbbP> \<Longrightarrow> k\<in>nat \<Longrightarrow>  \<exists>q\<in>\<bbbP>. q\<preceq> x \<and> q \<in> \<D> ` k"
  shows
    "f(succ(n)) \<in> \<bbbP> \<and> f(succ(n))\<preceq> f(n) \<and> f(succ(n)) \<in> \<D> ` n"
  using \<open>n\<in>nat\<close>
proof (induct)
  case 0
  from assms
  obtain q where "q\<in>\<bbbP>" "q\<preceq> p" "q \<in> \<D> ` 0" by blast
  moreover from this and \<open>\<bbbP> \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m = q"
    using Pi_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover
  have "\<D>`0 \<subseteq> \<bbbP>"
    using apply_funtype[OF countable_subs_of_P] by simp
  moreover note \<open>p\<in>\<bbbP>\<close>
  ultimately
  show ?case
    using LeastI[of "Q(p,0)" m] unfolding Q_def f_def by auto
next
  case (succ n)
  with assms
  obtain q where "q\<in>\<bbbP>" "q\<preceq> f(succ(n))" "q \<in> \<D> ` succ(n)" by blast
  moreover from this and \<open>\<bbbP> \<subseteq> range(enum)\<close>
  obtain m where "m\<in>nat" "enum`m\<preceq> f(succ(n))" "enum`m \<in> \<D> ` succ(n)"
    using Pi_rangeD[OF \<open>enum:nat\<rightarrow>M\<close>] by blast
  moreover note succ
  moreover from calculation
  have "\<D>`succ(n) \<subseteq> \<bbbP>"
    using apply_funtype[OF countable_subs_of_P] by auto
  ultimately
  show ?case
    using LeastI[of "Q(f(succ(n)),succ(n))" m] unfolding Q_def f_def by auto
qed

lemma countable_RS_sequence:
  fixes p enum
  defines "f \<equiv> \<lambda>n\<in>nat. RS_seq(n,\<bbbP>,leq,p,enum,\<D>)"
    and   "Q(q,k,m) \<equiv> enum`m\<preceq> q \<and> enum`m \<in> \<D> ` k"
  assumes "n\<in>nat" "p\<in>\<bbbP>" "\<bbbP> \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows
    "f`0 = p" "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n) \<in> \<bbbP>"
proof -
  from assms
  show "f`0 = p" by simp
  {
    fix x k
    assume "x\<in>\<bbbP>" "k\<in>nat"
    then
    have "\<exists>q\<in>\<bbbP>. q\<preceq> x \<and> q \<in> \<D> ` k"
      using seq_of_denses apply_funtype[OF countable_subs_of_P]
      unfolding dense_def by blast
  }
  with assms
  show "f`succ(n)\<preceq> f`n \<and> f`succ(n) \<in> \<D> ` n" "f`succ(n)\<in>\<bbbP>"
    unfolding f_def using countable_RS_sequence_aux by simp_all
qed

lemma RS_seq_type:
  assumes "n \<in> nat" "p\<in>\<bbbP>" "\<bbbP> \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "RS_seq(n,\<bbbP>,leq,p,enum,\<D>) \<in> \<bbbP>"
  using assms countable_RS_sequence(1,3)
  by (induct;simp)

lemma RS_seq_funtype:
  assumes "p\<in>\<bbbP>" "\<bbbP> \<subseteq> range(enum)" "enum:nat\<rightarrow>M"
  shows "(\<lambda>n\<in>nat. RS_seq(n,\<bbbP>,leq,p,enum,\<D>)): nat \<rightarrow> \<bbbP>"
  using assms lam_type RS_seq_type by auto

lemmas countable_rasiowa_sikorski =
  RS_sequence_imp_rasiowa_sikorski[OF _ RS_seq_funtype countable_RS_sequence(1,2)]

end \<comment> \<open>\<^locale>\<open>countable_generic\<close>\<close>

end
