section\<open>The definition of \<^term>\<open>forces\<close>\<close>

theory Forces_Definition
  imports
    Forcing_Data
begin

text\<open>This is the core of our development.\<close>

subsection\<open>The relation \<^term>\<open>frecrel\<close>\<close>

lemma names_belowsD:
  assumes "x \<in> names_below(P,z)"
  obtains f n1 n2 p where
    "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>P"
  using assms unfolding names_below_def by auto

context forcing_data1
begin

(* Absoluteness of components *)
lemma ftype_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_ftype(##M,x,y) \<longleftrightarrow> y = ftype(x)"
  unfolding ftype_def is_ftype_def by (simp add:absolut)

lemma name1_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name1(##M,x,y) \<longleftrightarrow> y = name1(x)"
  unfolding name1_def is_name1_def
  by (rule is_hcomp_abs[OF fst_abs],simp_all add: fst_snd_closed[simplified] absolut)

lemma snd_snd_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_snd_snd(##M,x,y) \<longleftrightarrow> y = snd(snd(x))"
  unfolding is_snd_snd_def
  by (rule is_hcomp_abs[OF snd_abs],
      simp_all add: conjunct2[OF fst_snd_closed,simplified] absolut)

lemma name2_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name2(##M,x,y) \<longleftrightarrow> y = name2(x)"
  unfolding name2_def is_name2_def
  by (rule is_hcomp_abs[OF fst_abs snd_snd_abs],simp_all add:absolut conjunct2[OF fst_snd_closed,simplified])

lemma cond_of_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_cond_of(##M,x,y) \<longleftrightarrow> y = cond_of(x)"
  unfolding cond_of_def is_cond_of_def
  by (rule is_hcomp_abs[OF snd_abs snd_snd_abs];simp_all add:fst_snd_closed[simplified])

lemma tuple_abs:
  "\<lbrakk>z\<in>M;t1\<in>M;t2\<in>M;p\<in>M;t\<in>M\<rbrakk> \<Longrightarrow>
   is_tuple(##M,z,t1,t2,p,t) \<longleftrightarrow> t = \<langle>z,t1,t2,p\<rangle>"
  unfolding is_tuple_def using pair_in_M_iff by simp

lemmas components_abs = ftype_abs name1_abs name2_abs cond_of_abs
  tuple_abs

lemma comp_in_M:
  "p \<preceq> q \<Longrightarrow> p\<in>M"
  "p \<preceq> q \<Longrightarrow> q\<in>M"
  using transitivity[of _ leq] pair_in_M_iff by auto

(* Absoluteness of Hfrc *)

lemma eq_case_abs [simp]:
  assumes "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M"
  shows "is_eq_case(##M,t1,t2,p,\<bbbP>,leq,f) \<longleftrightarrow> eq_case(t1,t2,p,\<bbbP>,leq,f)"
proof -
  have "q \<preceq> p \<Longrightarrow> q\<in>M" for q
    using comp_in_M by simp
  moreover
  have "\<langle>s,y\<rangle>\<in>t \<Longrightarrow> s\<in>domain(t)" if "t\<in>M" for s y t
    using that unfolding domain_def by auto
  ultimately
  have
    "(\<forall>s\<in>M. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q\<in>M. q\<in>\<bbbP> \<and> q \<preceq> p \<longrightarrow>
                              (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1))) \<longleftrightarrow>
    (\<forall>s. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q. q\<in>\<bbbP> \<and> q \<preceq> p \<longrightarrow>
                                  (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1)))"
    using assms domain_trans[OF trans_M,of t1] domain_trans[OF trans_M,of t2]
    by auto
  then
  show ?thesis
    unfolding eq_case_def is_eq_case_def
    using assms pair_in_M_iff nat_into_M domain_closed apply_closed zero_in_M Un_closed
    by (simp add:components_abs)
qed

lemma mem_case_abs [simp]:
  assumes "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M"
  shows "is_mem_case(##M,t1,t2,p,\<bbbP>,leq,f) \<longleftrightarrow> mem_case(t1,t2,p,\<bbbP>,leq,f)"
proof
  {
    fix v
    assume "v\<in>\<bbbP>" "v \<preceq> p" "is_mem_case(##M,t1,t2,p,\<bbbP>,leq,f)"
    moreover
    from this
    have "v\<in>M" "\<langle>v,p\<rangle> \<in> M" "(##M)(v)"
      using transitivity[OF _ P_in_M,of v] transitivity[OF _ leq_in_M]
      by simp_all
    moreover
    from calculation assms
    obtain q r s where
      "r \<in> \<bbbP> \<and> q \<in> \<bbbP> \<and> \<langle>q, v\<rangle> \<in> M \<and> \<langle>s, r\<rangle> \<in> M \<and> \<langle>q, r\<rangle> \<in> M \<and> 0 \<in> M \<and>
       \<langle>0, t1, s, q\<rangle> \<in> M \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      unfolding is_mem_case_def by (auto simp add:components_abs)
    then
    have "\<exists>q s r. r \<in> \<bbbP> \<and> q \<in> \<bbbP> \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      by auto
  }
  then
  show "mem_case(t1, t2, p, \<bbbP>, leq, f)" if "is_mem_case(##M, t1, t2, p, \<bbbP>, leq, f)"
    unfolding mem_case_def using that assms by auto
next
  { fix v
    assume "v \<in> M" "v \<in> \<bbbP>" "\<langle>v, p\<rangle> \<in> M" "v \<preceq> p" "mem_case(t1, t2, p, \<bbbP>, leq, f)"
    moreover
    from this
    obtain q s r where "r \<in> \<bbbP> \<and> q \<in> \<bbbP> \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      unfolding mem_case_def by auto
    moreover
    from this \<open>t2\<in>M\<close>
    have "r\<in>M" "q\<in>M" "s\<in>M" "r \<in> \<bbbP> \<and> q \<in> \<bbbP> \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      using transitivity domainI[of s r] domain_closed
      by auto
    moreover
    note \<open>t1\<in>M\<close>
    ultimately
    have "\<exists>q\<in>M . \<exists>s\<in>M. \<exists>r\<in>M.
         r \<in> \<bbbP> \<and> q \<in> \<bbbP> \<and> \<langle>q, v\<rangle> \<in> M \<and> \<langle>s, r\<rangle> \<in> M \<and> \<langle>q, r\<rangle> \<in> M \<and> 0 \<in> M \<and>
         \<langle>0, t1, s, q\<rangle> \<in> M \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      using pair_in_M_iff zero_in_M by auto
  }
  then
  show "is_mem_case(##M, t1, t2, p, \<bbbP>, leq, f)" if "mem_case(t1, t2, p, \<bbbP>, leq, f)"
    unfolding is_mem_case_def
    using assms that zero_in_M pair_in_M_iff apply_closed nat_into_M
    by (auto simp add:components_abs)
qed

lemma Hfrc_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc(##M,\<bbbP>,leq,fnnc,f) \<longleftrightarrow> Hfrc(\<bbbP>,leq,fnnc,f)"
  unfolding is_Hfrc_def Hfrc_def using pair_in_M_iff zero_in_M
  by (auto simp add:components_abs)

lemma Hfrc_at_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M ; z\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc_at(##M,\<bbbP>,leq,fnnc,f,z) \<longleftrightarrow>  z = bool_of_o(Hfrc(\<bbbP>,leq,fnnc,f)) "
  unfolding is_Hfrc_at_def using Hfrc_abs
  by auto

lemma components_closed :
  "x\<in>M \<Longrightarrow> (##M)(ftype(x))"
  "x\<in>M \<Longrightarrow> (##M)(name1(x))"
  "x\<in>M \<Longrightarrow> (##M)(name2(x))"
  "x\<in>M \<Longrightarrow> (##M)(cond_of(x))"
  unfolding ftype_def name1_def name2_def cond_of_def using fst_snd_closed by simp_all

lemma ecloseN_closed:
  "(##M)(A) \<Longrightarrow> (##M)(ecloseN(A))"
  "(##M)(A) \<Longrightarrow> (##M)(eclose_n(name1,A))"
  "(##M)(A) \<Longrightarrow> (##M)(eclose_n(name2,A))"
  unfolding ecloseN_def eclose_n_def
  using components_closed eclose_closed singleton_closed Un_closed by auto

lemma eclose_n_abs :
  assumes "x\<in>M" "ec\<in>M"
  shows "is_eclose_n(##M,is_name1,ec,x) \<longleftrightarrow> ec = eclose_n(name1,x)"
    "is_eclose_n(##M,is_name2,ec,x) \<longleftrightarrow> ec = eclose_n(name2,x)"
  unfolding is_eclose_n_def eclose_n_def
  using assms name1_abs name2_abs eclose_abs singleton_closed components_closed
  by auto


lemma ecloseN_abs :
  "\<lbrakk>x\<in>M;ec\<in>M\<rbrakk> \<Longrightarrow> is_ecloseN(##M,x,ec) \<longleftrightarrow> ec = ecloseN(x)"
  unfolding is_ecloseN_def ecloseN_def
  using eclose_n_abs Un_closed union_abs ecloseN_closed
  by auto

lemma frecR_abs :
  "x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> frecR(x,y) \<longleftrightarrow> is_frecR(##M,x,y)"
  unfolding frecR_def is_frecR_def
  using zero_in_M domain_closed Un_closed components_closed nat_into_M
  by (auto simp add: components_abs)

lemma frecrelP_abs :
  "z\<in>M \<Longrightarrow> frecrelP(##M,z) \<longleftrightarrow> (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y))"
  using pair_in_M_iff frecR_abs unfolding frecrelP_def by auto

lemma frecrel_abs:
  assumes "A\<in>M" "r\<in>M"
  shows "is_frecrel(##M,A,r) \<longleftrightarrow>  r = frecrel(A)"
proof -
  from \<open>A\<in>M\<close>
  have "z\<in>M" if "z\<in>A\<times>A" for z
    using cartprod_closed transitivity that by simp
  then
  have "Collect(A\<times>A,frecrelP(##M)) = Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y)))"
    using Collect_cong[of "A\<times>A" "A\<times>A" "frecrelP(##M)"] assms frecrelP_abs by simp
  with assms
  show ?thesis
    unfolding is_frecrel_def def_frecrel using cartprod_closed
    by simp
qed

lemma frecrel_closed:
  assumes "x\<in>M"
  shows "frecrel(x)\<in>M"
proof -
  have "Collect(x\<times>x,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y)))\<in>M"
    using Collect_in_M[of "frecrelP_fm(0)" "[]"] arity_frecrelP_fm sats_frecrelP_fm
      frecrelP_abs \<open>x\<in>M\<close> cartprod_closed
    by simp
  then
  show ?thesis
    unfolding frecrel_def Rrel_def frecrelP_def by simp
qed

lemma field_frecrel : "field(frecrel(names_below(\<bbbP>,x))) \<subseteq> names_below(\<bbbP>,x)"
  unfolding frecrel_def
  using field_Rrel by simp

lemma forcerelD : "uv \<in> forcerel(\<bbbP>,x) \<Longrightarrow> uv\<in> names_below(\<bbbP>,x) \<times> names_below(\<bbbP>,x)"
  unfolding forcerel_def
  using trancl_type field_frecrel by blast

lemma wf_forcerel :
  "wf(forcerel(\<bbbP>,x))"
  unfolding forcerel_def using wf_trancl wf_frecrel .

lemma restrict_trancl_forcerel:
  assumes "frecR(w,y)"
  shows "restrict(f,frecrel(names_below(\<bbbP>,x))-``{y})`w
       = restrict(f,forcerel(\<bbbP>,x)-``{y})`w"
  unfolding forcerel_def frecrel_def using assms restrict_trancl_Rrel[of frecR]
  by simp

lemma names_belowI :
  assumes "frecR(\<langle>ft,n1,n2,p\<rangle>,\<langle>a,b,c,d\<rangle>)" "p\<in>\<bbbP>"
  shows "\<langle>ft,n1,n2,p\<rangle> \<in> names_below(\<bbbP>,\<langle>a,b,c,d\<rangle>)" (is "?x \<in> names_below(_,?y)")
proof -
  from assms
  have "ft \<in> 2" "a \<in> 2"
    unfolding frecR_def by (auto simp add:components_simp)
  from assms
  consider (eq) "n1 \<in> domain(b) \<union> domain(c) \<and> (n2 = b \<or> n2 =c)"
    | (mem) "n1 = b \<and> n2 \<in> domain(c)"
    unfolding frecR_def by (auto simp add:components_simp)
  then show ?thesis
  proof cases
    case eq
    then
    have "n1 \<in> eclose(b) \<or> n1 \<in> eclose(c)"
      using Un_iff in_dom_in_eclose by auto
    with eq
    have "n1 \<in> ecloseN(?y)" "n2 \<in> ecloseN(?y)"
      using ecloseNI components_in_eclose by auto
    with \<open>ft\<in>2\<close> \<open>p\<in>\<bbbP>\<close>
    show ?thesis
      unfolding names_below_def by  auto
  next
    case mem
    then
    have "n1 \<in> ecloseN(?y)" "n2 \<in> ecloseN(?y)"
      using mem_eclose_trans ecloseNI in_dom_in_eclose components_in_eclose
      by auto
    with \<open>ft\<in>2\<close> \<open>p\<in>\<bbbP>\<close>
    show ?thesis
      unfolding names_below_def
      by auto
  qed
qed

lemma names_below_tr :
  assumes "x\<in> names_below(\<bbbP>,y)" "y\<in> names_below(\<bbbP>,z)"
  shows "x\<in> names_below(\<bbbP>,z)"
proof -
  let ?A="\<lambda>y . names_below(\<bbbP>,y)"
  note assms
  moreover from this
  obtain fx x1 x2 px where "x = \<langle>fx,x1,x2,px\<rangle>" "fx\<in>2" "x1\<in>ecloseN(y)" "x2\<in>ecloseN(y)" "px\<in>\<bbbP>"
    unfolding names_below_def by auto
  moreover from calculation
  obtain fy y1 y2 py where "y = \<langle>fy,y1,y2,py\<rangle>" "fy\<in>2" "y1\<in>ecloseN(z)" "y2\<in>ecloseN(z)" "py\<in>\<bbbP>"
    unfolding names_below_def by auto
  moreover from calculation
  have "x1\<in>ecloseN(z)" "x2\<in>ecloseN(z)"
    using ecloseN_mono names_simp by auto
  ultimately
  have "x\<in>?A(z)"
    unfolding names_below_def by simp
  then
  show ?thesis using subsetI by simp
qed

lemma arg_into_names_below2 :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,z))"
  shows  "x \<in> names_below(\<bbbP>,y)"
proof -
  from assms
  have "x\<in>names_below(\<bbbP>,z)" "y\<in>names_below(\<bbbP>,z)" "frecR(x,y)"
    unfolding frecrel_def Rrel_def
    by auto
  obtain f n1 n2 p where "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>\<bbbP>"
    using \<open>x\<in>names_below(\<bbbP>,z)\<close>
    unfolding names_below_def by auto
  moreover
  obtain fy m1 m2 q where "q\<in>\<bbbP>" "y = \<langle>fy,m1,m2,q\<rangle>"
    using \<open>y\<in>names_below(\<bbbP>,z)\<close>
    unfolding names_below_def by auto
  moreover
  note \<open>frecR(x,y)\<close>
  ultimately
  show ?thesis
    using names_belowI by simp
qed

lemma arg_into_names_below :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,z))"
  shows  "x \<in> names_below(\<bbbP>,x)"
proof -
  from assms
  have "x\<in>names_below(\<bbbP>,z)"
    unfolding frecrel_def Rrel_def
    by auto
  from \<open>x\<in>names_below(\<bbbP>,z)\<close>
  obtain f n1 n2 p where
    "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>\<bbbP>"
    unfolding names_below_def by auto
  then
  have "n1\<in>ecloseN(x)" "n2\<in>ecloseN(x)"
    using components_in_eclose by simp_all
  with \<open>f\<in>2\<close> \<open>p\<in>\<bbbP>\<close> \<open>x = \<langle>f,n1,n2,p\<rangle>\<close>
  show ?thesis
    unfolding names_below_def by simp
qed

lemma forcerel_arg_into_names_below :
  assumes "\<langle>x,y\<rangle> \<in> forcerel(\<bbbP>,z)"
  shows  "x \<in> names_below(\<bbbP>,x)"
  using assms
  unfolding forcerel_def
  by(rule trancl_induct;auto simp add: arg_into_names_below)

lemma names_below_mono :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,z))"
  shows "names_below(\<bbbP>,x) \<subseteq> names_below(\<bbbP>,y)"
proof -
  from assms
  have "x\<in>names_below(\<bbbP>,y)"
    using arg_into_names_below2 by simp
  then
  show ?thesis
    using names_below_tr subsetI by simp
qed

lemma frecrel_mono :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,z))"
  shows "frecrel(names_below(\<bbbP>,x)) \<subseteq> frecrel(names_below(\<bbbP>,y))"
  unfolding frecrel_def
  using Rrel_mono names_below_mono assms by simp

lemma forcerel_mono2 :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,z))"
  shows "forcerel(\<bbbP>,x) \<subseteq> forcerel(\<bbbP>,y)"
  unfolding forcerel_def
  using trancl_mono frecrel_mono assms by simp

lemma forcerel_mono_aux :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>, w))^+"
  shows "forcerel(\<bbbP>,x) \<subseteq> forcerel(\<bbbP>,y)"
  using assms
  by (rule trancl_induct,simp_all add: subset_trans forcerel_mono2)

lemma forcerel_mono :
  assumes "\<langle>x,y\<rangle> \<in> forcerel(\<bbbP>,z)"
  shows "forcerel(\<bbbP>,x) \<subseteq> forcerel(\<bbbP>,y)"
  using forcerel_mono_aux assms unfolding forcerel_def by simp

lemma forcerel_eq_aux: "x \<in> names_below(\<bbbP>, w) \<Longrightarrow> \<langle>x,y\<rangle> \<in> forcerel(\<bbbP>,z) \<Longrightarrow>
  (y \<in> names_below(\<bbbP>, w) \<longrightarrow> \<langle>x,y\<rangle> \<in> forcerel(\<bbbP>,w))"
  unfolding forcerel_def
proof (rule_tac a=x and b=y and
    P="\<lambda> y . y \<in> names_below(\<bbbP>, w) \<longrightarrow> \<langle>x,y\<rangle> \<in> frecrel(names_below(\<bbbP>,w))^+" in trancl_induct,simp)
  let ?A="\<lambda> a . names_below(\<bbbP>, a)"
  let ?R="\<lambda> a . frecrel(?A(a))"
  let ?fR="\<lambda> a .forcerel(a)"
  show "u\<in>?A(w) \<longrightarrow> \<langle>x,u\<rangle>\<in>?R(w)^+" if "x\<in>?A(w)" "\<langle>x,y\<rangle>\<in>?R(z)^+" "\<langle>x,u\<rangle>\<in>?R(z)"  for  u
    using that frecrelD frecrelI r_into_trancl
    unfolding names_below_def by simp
  {
    fix u v
    assume "x \<in> ?A(w)"
      "\<langle>x, y\<rangle> \<in> ?R(z)^+"
      "\<langle>x, u\<rangle> \<in> ?R(z)^+"
      "\<langle>u, v\<rangle> \<in> ?R(z)"
      "u \<in> ?A(w) \<Longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+"
    then
    have "v \<in> ?A(w) \<Longrightarrow> \<langle>x, v\<rangle> \<in> ?R(w)^+"
    proof -
      assume "v \<in>?A(w)"
      from \<open>\<langle>u,v\<rangle>\<in>_\<close>
      have "u\<in>?A(v)"
        using arg_into_names_below2 by simp
      with \<open>v \<in>?A(w)\<close>
      have "u\<in>?A(w)"
        using names_below_tr by simp
      with \<open>v\<in>_\<close> \<open>\<langle>u,v\<rangle>\<in>_\<close>
      have "\<langle>u,v\<rangle>\<in> ?R(w)"
        using frecrelD frecrelI r_into_trancl unfolding names_below_def by simp
      with \<open>u \<in> ?A(w) \<Longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+\<close> \<open>u\<in>?A(w)\<close>
      have "\<langle>x, u\<rangle> \<in> ?R(w)^+"
        by simp
      with \<open>\<langle>u,v\<rangle>\<in> ?R(w)\<close>
      show "\<langle>x,v\<rangle>\<in> ?R(w)^+" using trancl_trans r_into_trancl
        by simp
    qed
  }
  then
  show "v \<in> ?A(w) \<longrightarrow> \<langle>x, v\<rangle> \<in> ?R(w)^+"
    if "x \<in> ?A(w)"
      "\<langle>x, y\<rangle> \<in> ?R(z)^+"
      "\<langle>x, u\<rangle> \<in> ?R(z)^+"
      "\<langle>u, v\<rangle> \<in> ?R(z)"
      "u \<in> ?A(w) \<longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+" for u v
    using that
    by simp
qed

lemma forcerel_eq :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(\<bbbP>,x)"
  shows "forcerel(\<bbbP>,z) = forcerel(\<bbbP>,x) \<inter> names_below(\<bbbP>,z)\<times>names_below(\<bbbP>,z)"
  using assms forcerel_eq_aux forcerelD forcerel_mono[of z x x] subsetI
  by auto

lemma forcerel_below_aux :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(\<bbbP>,x)" "\<langle>u,z\<rangle> \<in> forcerel(\<bbbP>,x)"
  shows "u \<in> names_below(\<bbbP>,z)"
  using assms(2)
  unfolding forcerel_def
proof(rule trancl_induct)
  show  "u \<in> names_below(\<bbbP>,y)" if " \<langle>u, y\<rangle> \<in> frecrel(names_below(\<bbbP>, x))" for y
    using that vimage_singleton_iff arg_into_names_below2 by simp
next
  show "u \<in> names_below(\<bbbP>,z)"
    if "\<langle>u, y\<rangle> \<in> frecrel(names_below(\<bbbP>, x))^+"
      "\<langle>y, z\<rangle> \<in> frecrel(names_below(\<bbbP>, x))"
      "u \<in> names_below(\<bbbP>, y)"
    for y z
    using that arg_into_names_below2[of y z x] names_below_tr by simp
qed

lemma forcerel_below :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(\<bbbP>,x)"
  shows "forcerel(\<bbbP>,x) -`` {z} \<subseteq> names_below(\<bbbP>,z)"
  using vimage_singleton_iff assms forcerel_below_aux by auto

lemma relation_forcerel :
  shows "relation(forcerel(\<bbbP>,z))" "trans(forcerel(\<bbbP>,z))"
  unfolding forcerel_def using relation_trancl trans_trancl by simp_all

lemma Hfrc_restrict_trancl: "bool_of_o(Hfrc(\<bbbP>, leq, y, restrict(f,frecrel(names_below(\<bbbP>,x))-``{y})))
         = bool_of_o(Hfrc(\<bbbP>, leq, y, restrict(f,(frecrel(names_below(\<bbbP>,x))^+)-``{y})))"
  unfolding Hfrc_def bool_of_o_def eq_case_def mem_case_def
  using restrict_trancl_forcerel frecRI1 frecRI2 frecRI3
  unfolding forcerel_def
  by simp

(* Recursive definition of forces for atomic formulas using a transitive relation *)
lemma frc_at_trancl: "frc_at(\<bbbP>,leq,z) = wfrec(forcerel(\<bbbP>,z),z,\<lambda>x f. bool_of_o(Hfrc(\<bbbP>,leq,x,f)))"
  unfolding frc_at_def forcerel_def using wf_eq_trancl Hfrc_restrict_trancl by simp

lemma forcerelI1 :
  assumes "n1 \<in> domain(b) \<or> n1 \<in> domain(c)" "p\<in>\<bbbP>" "d\<in>\<bbbP>"
  shows "\<langle>\<langle>1, n1, b, p\<rangle>, \<langle>0,b,c,d\<rangle>\<rangle>\<in> forcerel(\<bbbP>,\<langle>0,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>1, n1, b, p\<rangle>"
  let ?y="\<langle>0,b,c,d\<rangle>"
  from assms
  have "frecR(?x,?y)"
    using frecRI1 by simp
  then
  have "?x\<in>names_below(\<bbbP>,?y)" "?y \<in> names_below(\<bbbP>,?y)"
    using names_belowI  assms components_in_eclose
    unfolding names_below_def by auto
  with \<open>frecR(?x,?y)\<close>
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemma forcerelI2 :
  assumes "n1 \<in> domain(b) \<or> n1 \<in> domain(c)" "p\<in>\<bbbP>" "d\<in>\<bbbP>"
  shows "\<langle>\<langle>1, n1, c, p\<rangle>, \<langle>0,b,c,d\<rangle>\<rangle>\<in> forcerel(\<bbbP>,\<langle>0,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>1, n1, c, p\<rangle>"
  let ?y="\<langle>0,b,c,d\<rangle>"
  note assms
  moreover from this
  have "frecR(?x,?y)"
    using frecRI2 by simp
  moreover from calculation
  have "?x\<in>names_below(\<bbbP>,?y)" "?y \<in> names_below(\<bbbP>,?y)"
    using names_belowI components_in_eclose
    unfolding names_below_def by auto
  ultimately
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemma forcerelI3 :
  assumes "\<langle>n2, r\<rangle> \<in> c" "p\<in>\<bbbP>" "d\<in>\<bbbP>" "r \<in> \<bbbP>"
  shows "\<langle>\<langle>0, b, n2, p\<rangle>,\<langle>1, b, c, d\<rangle>\<rangle> \<in> forcerel(\<bbbP>,\<langle>1,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>0, b, n2, p\<rangle>"
  let ?y="\<langle>1, b, c, d\<rangle>"
  note assms
  moreover from this
  have "frecR(?x,?y)"
    using frecRI3 by simp
  moreover from calculation
  have "?x\<in>names_below(\<bbbP>,?y)"  "?y \<in> names_below(\<bbbP>,?y)"
    using names_belowI components_in_eclose
    unfolding names_below_def by auto
  ultimately
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemmas forcerelI = forcerelI1[THEN vimage_singleton_iff[THEN iffD2]]
  forcerelI2[THEN vimage_singleton_iff[THEN iffD2]]
  forcerelI3[THEN vimage_singleton_iff[THEN iffD2]]

lemma  aux_def_frc_at:
  assumes "z \<in> forcerel(\<bbbP>,x) -`` {x}"
  shows "wfrec(forcerel(\<bbbP>,x), z, H) =  wfrec(forcerel(\<bbbP>,z), z, H)"
proof -
  let ?A="names_below(\<bbbP>,z)"
  from assms
  have "\<langle>z,x\<rangle> \<in> forcerel(\<bbbP>,x)"
    using vimage_singleton_iff by simp
  moreover from this
  have "z \<in> ?A"
    using forcerel_arg_into_names_below by simp
  moreover from calculation
  have "forcerel(\<bbbP>,z) = forcerel(\<bbbP>,x) \<inter> (?A\<times>?A)"
    "forcerel(\<bbbP>,x) -`` {z} \<subseteq> ?A"
    using forcerel_eq forcerel_below
    by auto
  moreover from calculation
  have "wfrec(forcerel(\<bbbP>,x), z, H) = wfrec[?A](forcerel(\<bbbP>,x), z, H)"
    using wfrec_trans_restr[OF relation_forcerel(1) wf_forcerel relation_forcerel(2), of x z ?A]
    by simp
  ultimately
  show ?thesis
    using wfrec_restr_eq by simp
qed

subsection\<open>Recursive expression of \<^term>\<open>frc_at\<close>\<close>

lemma def_frc_at :
  assumes "p\<in>\<bbbP>"
  shows
    "frc_at(\<bbbP>,leq,\<langle>ft,n1,n2,p\<rangle>) =
   bool_of_o( p \<in>\<bbbP> \<and>
  (  ft = 0 \<and>  (\<forall>s. s\<in>domain(n1) \<union> domain(n2) \<longrightarrow>
        (\<forall>q. q\<in>\<bbbP> \<and> q \<preceq> p \<longrightarrow> (frc_at(\<bbbP>,leq,\<langle>1,s,n1,q\<rangle>) =1 \<longleftrightarrow> frc_at(\<bbbP>,leq,\<langle>1,s,n2,q\<rangle>) =1)))
   \<or> ft = 1 \<and> ( \<forall>v\<in>\<bbbP>. v \<preceq> p \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>\<bbbP> \<and> q\<in>\<bbbP> \<and> q \<preceq> v \<and> \<langle>s,r\<rangle> \<in> n2 \<and> q \<preceq> r \<and>  frc_at(\<bbbP>,leq,\<langle>0,n1,s,q\<rangle>) = 1))))"
proof -
  let ?r="\<lambda>y. forcerel(\<bbbP>,y)" and ?Hf="\<lambda>x f. bool_of_o(Hfrc(\<bbbP>,leq,x,f))"
  let ?t="\<lambda>y. ?r(y) -`` {y}"
  let ?arg="\<langle>ft,n1,n2,p\<rangle>"
  from wf_forcerel
  have wfr: "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(?arg)" ?arg ?Hf]
  have "frc_at(\<bbbP>,leq,?arg) = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. wfrec(?r(?arg), x, ?Hf))"
    using frc_at_trancl by simp
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. frc_at(\<bbbP>,leq,x))"
    using aux_def_frc_at frc_at_trancl by simp
  finally
  show ?thesis
    unfolding Hfrc_def mem_case_def eq_case_def
    using forcerelI  assms
    by auto
qed


subsection\<open>Absoluteness of \<^term>\<open>frc_at\<close>\<close>

lemma forcerel_in_M :
  assumes "x\<in>M"
  shows "forcerel(\<bbbP>,x)\<in>M"
  unfolding forcerel_def def_frecrel names_below_def
proof -
  let ?Q = "2 \<times> ecloseN(x) \<times> ecloseN(x) \<times> \<bbbP>"
  have "?Q \<times> ?Q \<in> M"
    using \<open>x\<in>M\<close> nat_into_M ecloseN_closed cartprod_closed by simp
  moreover
  have "separation(##M,\<lambda>z. frecrelP(##M,z))"
    using separation_in_ctm[of "frecrelP_fm(0)",OF _ _ _ sats_frecrelP_fm]
      arity_frecrelP_fm frecrelP_fm_type
    by auto
  moreover from this
  have "separation(##M,\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y))"
    using separation_cong[OF frecrelP_abs]
    by force
  ultimately
  show "{z \<in> ?Q \<times> ?Q . \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)}^+ \<in> M"
    using separation_closed frecrelP_abs trancl_closed
    by simp
qed

lemma relation2_Hfrc_at_abs:
  "relation2(##M,is_Hfrc_at(##M,\<bbbP>,leq),\<lambda>x f. bool_of_o(Hfrc(\<bbbP>,leq,x,f)))"
  unfolding relation2_def using Hfrc_at_abs
  by simp

lemma Hfrc_at_closed :
  "\<forall>x\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> bool_of_o(Hfrc(\<bbbP>,leq,x,g))\<in>M"
  unfolding bool_of_o_def using zero_in_M nat_into_M[of 1] by simp

lemma wfrec_Hfrc_at :
  assumes "X\<in>M"
  shows "wfrec_replacement(##M,is_Hfrc_at(##M,\<bbbP>,leq),forcerel(\<bbbP>,X))"
proof -
  have 0:"is_Hfrc_at(##M,\<bbbP>,leq,a,b,c) \<longleftrightarrow>
        sats(M,Hfrc_at_fm(8,9,2,1,0),[c,b,a,d,e,y,x,z,\<bbbP>,leq,forcerel(\<bbbP>,X)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
    for a b c d e y x z
    using that \<open>X\<in>M\<close> forcerel_in_M
      Hfrc_at_iff_sats[of concl:M \<bbbP> leq a b c 8 9 2 1 0]
    by simp
  have 1:"sats(M,is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0),[y,x,z,\<bbbP>,leq,forcerel(\<bbbP>,X)]) \<longleftrightarrow>
                   is_wfrec(##M, is_Hfrc_at(##M,\<bbbP>,leq),forcerel(\<bbbP>,X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using that \<open>X\<in>M\<close> forcerel_in_M sats_is_wfrec_fm[OF 0]
    by simp
  let
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0)))"
  have satsf:"sats(M, ?f, [x,z,\<bbbP>,leq,forcerel(\<bbbP>,X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,\<bbbP>,leq),forcerel(\<bbbP>,X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> forcerel_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 5"
    using arity_wfrec_replacement_fm[where p="Hfrc_at_fm(8,9,2,1,0)" and i=10]
      arity_Hfrc_at_fm ord_simp_union
    by simp
  moreover
  have "?f\<in>formula" by simp
  ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,\<bbbP>,leq,forcerel(\<bbbP>,X)]))"
    using ZF_ground_replacements(1) 1 artyf \<open>X\<in>M\<close> forcerel_in_M
    unfolding replacement_assm_def wfrec_Hfrc_at_fm_def by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,\<bbbP>,leq),forcerel(\<bbbP>,X), x, y))"
    using repl_sats[of M ?f "[\<bbbP>,leq,forcerel(\<bbbP>,X)]"] satsf by (simp del:pair_abs)
  then
  show ?thesis unfolding wfrec_replacement_def by simp
qed

lemma names_below_abs :
  "\<lbrakk>Q\<in>M;x\<in>M;nb\<in>M\<rbrakk> \<Longrightarrow> is_names_below(##M,Q,x,nb) \<longleftrightarrow> nb = names_below(Q,x)"
  unfolding is_names_below_def names_below_def
  using succ_in_M_iff zero_in_M cartprod_closed ecloseN_abs ecloseN_closed
  by auto

lemma names_below_closed:
  "\<lbrakk>Q\<in>M;x\<in>M\<rbrakk> \<Longrightarrow> names_below(Q,x) \<in> M"
  unfolding names_below_def
  using zero_in_M cartprod_closed ecloseN_closed succ_in_M_iff
  by simp

lemma "names_below_productE" :
  assumes "Q \<in> M" "x \<in> M"
    "\<And>A1 A2 A3 A4. A1 \<in> M \<Longrightarrow> A2 \<in> M \<Longrightarrow> A3 \<in> M \<Longrightarrow> A4 \<in> M \<Longrightarrow> R(A1 \<times> A2 \<times> A3 \<times> A4)"
  shows "R(names_below(Q,x))"
  unfolding names_below_def using assms nat_into_M ecloseN_closed[of x] by auto

lemma forcerel_abs :
  "\<lbrakk>x\<in>M;z\<in>M\<rbrakk> \<Longrightarrow> is_forcerel(##M,\<bbbP>,x,z) \<longleftrightarrow> z = forcerel(\<bbbP>,x)"
  unfolding is_forcerel_def forcerel_def
  using frecrel_abs names_below_abs trancl_abs ecloseN_closed names_below_closed
    names_below_productE[of concl:"\<lambda>p. is_frecrel(##M,p,_) \<longleftrightarrow>  _ = frecrel(p)"] frecrel_closed
  by simp

lemma frc_at_abs:
  assumes "fnnc\<in>M" "z\<in>M"
  shows "is_frc_at(##M,\<bbbP>,leq,fnnc,z) \<longleftrightarrow> z = frc_at(\<bbbP>,leq,fnnc)"
proof -
  from assms
  have "(\<exists>r\<in>M. is_forcerel(##M,\<bbbP>,fnnc, r) \<and> is_wfrec(##M, is_Hfrc_at(##M, \<bbbP>, leq), r, fnnc, z))
        \<longleftrightarrow> is_wfrec(##M, is_Hfrc_at(##M, \<bbbP>, leq), forcerel(\<bbbP>,fnnc), fnnc, z)"
    using forcerel_abs forcerel_in_M by simp
  then
  show ?thesis
    unfolding frc_at_trancl is_frc_at_def
    using assms wfrec_Hfrc_at[of fnnc] wf_forcerel relation_forcerel forcerel_in_M
      Hfrc_at_closed relation2_Hfrc_at_abs
      trans_wfrec_abs[of "forcerel(\<bbbP>,fnnc)" fnnc z "is_Hfrc_at(##M,\<bbbP>,leq)" "\<lambda>x f. bool_of_o(Hfrc(\<bbbP>,leq,x,f))"]
    by (simp flip:setclass_iff)
qed

lemma forces_eq'_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_eq'(##M,\<bbbP>,leq,p,t1,t2) \<longleftrightarrow> forces_eq'(\<bbbP>,leq,p,t1,t2)"
  unfolding is_forces_eq'_def forces_eq'_def
  using frc_at_abs nat_into_M pair_in_M_iff by (auto simp add:components_abs)

lemma forces_mem'_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_mem'(##M,\<bbbP>,leq,p,t1,t2) \<longleftrightarrow> forces_mem'(\<bbbP>,leq,p,t1,t2)"
  unfolding is_forces_mem'_def forces_mem'_def
  using frc_at_abs nat_into_M pair_in_M_iff by (auto simp add:components_abs)

lemma forces_neq'_abs :
  assumes "p\<in>M" "t1\<in>M" "t2\<in>M"
  shows "is_forces_neq'(##M,\<bbbP>,leq,p,t1,t2) \<longleftrightarrow> forces_neq'(\<bbbP>,leq,p,t1,t2)"
proof -
  have "q\<in>M" if "q\<in>\<bbbP>" for q
    using that transitivity by simp
  with assms
  show ?thesis
    unfolding is_forces_neq'_def forces_neq'_def
    using forces_eq'_abs pair_in_M_iff
    by (auto simp add:components_abs,blast)
qed

lemma forces_nmem'_abs :
  assumes "p\<in>M" "t1\<in>M" "t2\<in>M"
  shows "is_forces_nmem'(##M,\<bbbP>,leq,p,t1,t2) \<longleftrightarrow> forces_nmem'(\<bbbP>,leq,p,t1,t2)"
proof -
  have "q\<in>M" if "q\<in>\<bbbP>" for q
    using that transitivity by simp
  with assms
  show ?thesis
    unfolding is_forces_nmem'_def forces_nmem'_def
    using forces_mem'_abs pair_in_M_iff
    by (auto simp add:components_abs,blast)
qed

lemma leq_abs:
  "\<lbrakk> l\<in>M ; q\<in>M ; p\<in>M \<rbrakk> \<Longrightarrow> is_leq(##M,l,q,p) \<longleftrightarrow> \<langle>q,p\<rangle>\<in>l"
  unfolding is_leq_def using pair_in_M_iff by simp

subsection\<open>Forcing for atomic formulas in context\<close>

definition
  forces_eq :: "[i,i,i] \<Rightarrow> o" (\<open>_ forces\<^sub>a '(_ = _')\<close> [36,1,1] 60) where
  "forces_eq \<equiv> forces_eq'(\<bbbP>,leq)"

definition
  forces_mem :: "[i,i,i] \<Rightarrow> o" (\<open>_ forces\<^sub>a '(_ \<in> _')\<close> [36,1,1] 60) where
  "forces_mem \<equiv> forces_mem'(\<bbbP>,leq)"

(* frc_at(\<bbbP>,leq,\<langle>0,t1,t2,p\<rangle>) = 1*)
abbreviation is_forces_eq
  where "is_forces_eq \<equiv> is_forces_eq'(##M,\<bbbP>,leq)"

(* frc_at(\<bbbP>,leq,\<langle>1,t1,t2,p\<rangle>) = 1*)
abbreviation
  is_forces_mem :: "[i,i,i] \<Rightarrow> o" where
  "is_forces_mem \<equiv> is_forces_mem'(##M,\<bbbP>,leq)"

lemma def_forces_eq: "p\<in>\<bbbP> \<Longrightarrow> p forces\<^sub>a (t1 = t2) \<longleftrightarrow>
      (\<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q\<in>\<bbbP> \<and> q \<preceq> p \<longrightarrow>
      (q forces\<^sub>a (s \<in> t1) \<longleftrightarrow> q forces\<^sub>a (s \<in> t2)))"
  unfolding forces_eq_def forces_mem_def forces_eq'_def forces_mem'_def
  using def_frc_at[of p 0 t1 t2 ]
  unfolding bool_of_o_def
  by auto

lemma def_forces_mem: "p\<in>\<bbbP> \<Longrightarrow> p forces\<^sub>a (t1 \<in> t2) \<longleftrightarrow>
     (\<forall>v\<in>\<bbbP>. v \<preceq> p \<longrightarrow>
      (\<exists>q. \<exists>s. \<exists>r. r\<in>\<bbbP> \<and> q\<in>\<bbbP> \<and> q \<preceq> v \<and> \<langle>s,r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> q forces\<^sub>a (t1 = s)))"
  unfolding forces_eq'_def forces_mem'_def forces_eq_def forces_mem_def
  using def_frc_at[of p 1 t1 t2]
  unfolding bool_of_o_def
  by auto

lemma forces_eq_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_eq(p,t1,t2) \<longleftrightarrow> p forces\<^sub>a (t1 = t2)"
  unfolding forces_eq_def
  using forces_eq'_abs by simp

lemma forces_mem_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_mem(p,t1,t2) \<longleftrightarrow> p forces\<^sub>a (t1 \<in> t2)"
  unfolding forces_mem_def
  using forces_mem'_abs
  by simp

definition
  forces_neq :: "[i,i,i] \<Rightarrow> o" (\<open>_ forces\<^sub>a '(_ \<noteq> _')\<close> [36,1,1] 60) where
  "p forces\<^sub>a (t1 \<noteq> t2) \<equiv> \<not> (\<exists>q\<in>\<bbbP>. q\<preceq>p \<and> q forces\<^sub>a (t1 = t2))"

definition
  forces_nmem :: "[i,i,i] \<Rightarrow> o" (\<open>_ forces\<^sub>a '(_ \<notin> _')\<close> [36,1,1] 60) where
  "p forces\<^sub>a (t1 \<notin> t2) \<equiv> \<not> (\<exists>q\<in>\<bbbP>. q\<preceq>p \<and> q forces\<^sub>a (t1 \<in> t2))"

lemma forces_neq :
  "p forces\<^sub>a (t1 \<noteq> t2) \<longleftrightarrow> forces_neq'(\<bbbP>,leq,p,t1,t2)"
  unfolding forces_neq_def forces_neq'_def forces_eq_def by simp

lemma forces_nmem :
  "p forces\<^sub>a (t1 \<notin> t2) \<longleftrightarrow> forces_nmem'(\<bbbP>,leq,p,t1,t2)"
  unfolding forces_nmem_def forces_nmem'_def forces_mem_def by simp

abbreviation Forces :: "[i, i, i] \<Rightarrow> o"  ("_ \<tturnstile> _ _" [36,36,36] 60) where
  "p \<tturnstile> \<phi> env   \<equiv>   M, ([p,\<bbbP>,leq,\<one>] @ env) \<Turnstile> forces(\<phi>)"

lemma sats_forces_Member :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)"
    "nth(x,env)=xx" "nth(y,env)=yy" "q\<in>M"
  shows "q \<tturnstile> \<cdot>x \<in> y\<cdot> env \<longleftrightarrow> q \<in> \<bbbP> \<and> is_forces_mem(q, xx, yy)"
  unfolding forces_def
  using assms
  by simp

lemma sats_forces_Equal :
  assumes "a\<in>nat" "b\<in>nat" "env\<in>list(M)" "nth(a,env)=x" "nth(b,env)=y" "q\<in>M"
  shows "q \<tturnstile> \<cdot>a = b\<cdot> env \<longleftrightarrow> q \<in> \<bbbP> \<and> is_forces_eq(q, x, y)"
  unfolding forces_def
  using assms
  by simp

lemma sats_forces_Nand :
  assumes "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "p \<tturnstile> \<cdot>\<not>(\<phi> \<and> \<psi>)\<cdot> env \<longleftrightarrow>
    p\<in>\<bbbP> \<and> \<not>(\<exists>q\<in>M. q\<in>\<bbbP> \<and> is_leq(##M,leq,q,p) \<and> (q \<tturnstile> \<phi> env) \<and> (q \<tturnstile> \<psi> env))"
  unfolding forces_def
  using sats_is_leq_fm_auto assms sats_ren_forces_nand zero_in_M
  by simp

lemma sats_forces_Neg :
  assumes "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "p \<tturnstile> \<cdot>\<not>\<phi>\<cdot> env \<longleftrightarrow>
         (p\<in>\<bbbP> \<and> \<not>(\<exists>q\<in>M. q\<in>\<bbbP> \<and> is_leq(##M,leq,q,p) \<and> (q \<tturnstile> \<phi> env)))"
  unfolding Neg_def using assms sats_forces_Nand
  by simp

lemma sats_forces_Forall :
  assumes "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "p \<tturnstile> (\<cdot>\<forall>\<phi>\<cdot>) env \<longleftrightarrow> p \<in> \<bbbP> \<and> (\<forall>x\<in>M. p \<tturnstile> \<phi> ([x] @ env))"
  unfolding forces_def using assms sats_ren_forces_forall
  by simp

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end