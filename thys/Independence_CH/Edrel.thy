theory Edrel
  imports
    Transitive_Models.ZF_Miscellanea
    Transitive_Models.Recursion_Thms

begin

subsection\<open>The well-founded relation \<^term>\<open>ed\<close>\<close>

lemma eclose_sing : "x \<in> eclose(a) \<Longrightarrow> x \<in> eclose({a})"
  using subsetD[OF mem_eclose_subset]
  by simp

lemma ecloseE :
  assumes  "x \<in> eclose(A)"
  shows  "x \<in> A \<or> (\<exists> B \<in> A . x \<in> eclose(B))"
  using assms
proof (induct rule:eclose_induct_down)
  case (1 y)
  then
  show ?case
    using arg_into_eclose by auto
next
  case (2 y z)
  from \<open>y \<in> A \<or> (\<exists>B\<in>A. y \<in> eclose(B))\<close>
  consider (inA) "y \<in> A" | (exB) "(\<exists>B\<in>A. y \<in> eclose(B))"
    by auto
  then show ?case
  proof (cases)
    case inA
    then
    show ?thesis using 2 arg_into_eclose by auto
  next
    case exB
    then obtain B where "y \<in> eclose(B)" "B\<in>A"
      by auto
    then
    show ?thesis using 2 ecloseD[of y B z] by auto
  qed
qed

lemma eclose_singE : "x \<in> eclose({a}) \<Longrightarrow> x = a \<or> x \<in> eclose(a)"
  by(blast dest: ecloseE)

lemma in_eclose_sing :
  assumes "x \<in> eclose({a})" "a \<in> eclose(z)"
  shows "x \<in> eclose({z})"
proof -
  from \<open>x\<in>eclose({a})\<close>
  consider "x=a" | "x\<in>eclose(a)"
    using eclose_singE by auto
  then
  show ?thesis
    using eclose_sing mem_eclose_trans assms
    by (cases, auto)
qed

lemma in_dom_in_eclose :
  assumes "x \<in> domain(z)"
  shows "x \<in> eclose(z)"
proof -
  from assms
  obtain y where "\<langle>x,y\<rangle> \<in> z"
    unfolding domain_def by auto
  then
  show ?thesis
    unfolding Pair_def
    using ecloseD[of "{x,x}"] ecloseD[of "{{x,x},{x,y}}"] arg_into_eclose
    by auto
qed

text\<open>term\<open>ed\<close> is the well-founded relation on which \<^term>\<open>val\<close> is defined.\<close>
definition
  ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) \<equiv> x \<in> domain(y)"

definition
  edrel :: "i \<Rightarrow> i" where
  "edrel(A) \<equiv> Rrel(ed,A)"

lemma edI[intro!]: "t\<in>domain(x) \<Longrightarrow> ed(t,x)"
  unfolding ed_def .

lemma edD[dest!]: "ed(t,x) \<Longrightarrow> t\<in>domain(x)"
  unfolding ed_def .

lemma rank_ed:
  assumes "ed(y,x)"
  shows "succ(rank(y)) \<le> rank(x)"
proof
  from assms
  obtain p where "\<langle>y,p\<rangle>\<in>x" by auto
  moreover
  obtain s where "y\<in>s" "s\<in>\<langle>y,p\<rangle>" unfolding Pair_def by auto
  ultimately
  have "rank(y) < rank(s)" "rank(s) < rank(\<langle>y,p\<rangle>)" "rank(\<langle>y,p\<rangle>) < rank(x)"
    using rank_lt by blast+
  then
  show "rank(y) < rank(x)"
    using lt_trans by blast
qed

lemma edrel_dest [dest]: "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =\<langle>a,b\<rangle>"
  by(auto simp add:ed_def edrel_def Rrel_def)

lemma edrelD : "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =\<langle>a,b\<rangle> \<and> a \<in> domain(b)"
  by(auto simp add:ed_def edrel_def Rrel_def)

lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> \<langle>x,y\<rangle>\<in>edrel(A)"
  by (simp add:ed_def edrel_def Rrel_def)

lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> \<langle>x,y\<rangle>\<in>edrel(A)"
  by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

lemma domain_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> x\<in>A"
  by (auto simp add: Transset_def domain_def Pair_def)

lemma relation_edrel : "relation(edrel(A))"
  by(auto simp add: relation_def)

lemma field_edrel : "field(edrel(A))\<subseteq>A"
  by blast

lemma edrel_sub_memrel: "edrel(A) \<subseteq> trancl(Memrel(eclose(A)))"
proof
  let
    ?r="trancl(Memrel(eclose(A)))"
  fix z
  assume "z\<in>edrel(A)"
  then
  obtain x y where "x\<in>A" "y\<in>A" "z=\<langle>x,y\<rangle>" "x\<in>domain(y)"
    using edrelD
    by blast
  moreover from this
  obtain u v where "x\<in>u" "u\<in>v" "v\<in>y"
    unfolding domain_def Pair_def by auto
  moreover from calculation
  have "x\<in>eclose(A)" "y\<in>eclose(A)" "y\<subseteq>eclose(A)"
    using arg_into_eclose Transset_eclose[unfolded Transset_def]
    by simp_all
  moreover from calculation
  have "v\<in>eclose(A)"
    by auto
  moreover from calculation
  have "u\<in>eclose(A)"
    using Transset_eclose[unfolded Transset_def]
    by auto
  moreover from calculation
  have"\<langle>x,u\<rangle>\<in>?r" "\<langle>u,v\<rangle>\<in>?r" "\<langle>v,y\<rangle>\<in>?r"
    by (auto simp add: r_into_trancl)
  moreover from this
  have "\<langle>x,y\<rangle>\<in>?r"
    using trancl_trans[OF _ trancl_trans[of _ v _ y]]
    by simp
  ultimately
  show "z\<in>?r"
    by simp
qed

lemma wf_edrel : "wf(edrel(A))"
  using wf_subset [of "trancl(Memrel(eclose(A)))"] edrel_sub_memrel
    wf_trancl wf_Memrel
  by auto

lemma ed_induction:
  assumes "\<And>x. \<lbrakk>\<And>y.  ed(y,x) \<Longrightarrow> Q(y) \<rbrakk> \<Longrightarrow> Q(x)"
  shows "Q(a)"
proof(induct rule: wf_induct2[OF wf_edrel[of "eclose({a})"] ,of a "eclose({a})"])
  case 1
  then show ?case using arg_into_eclose by simp
next
  case 2
  then show ?case using field_edrel .
next
  case (3 x)
  then
  show ?case
    using assms[of x] edrelI domain_trans[OF Transset_eclose 3(1)] by blast
qed

lemma dom_under_edrel_eclose: "edrel(eclose({x})) -`` {x} = domain(x)"
proof(intro equalityI)
  show "edrel(eclose({x})) -`` {x} \<subseteq> domain(x)"
    unfolding edrel_def Rrel_def ed_def
    by auto
next
  show "domain(x) \<subseteq> edrel(eclose({x})) -`` {x}"
    unfolding edrel_def Rrel_def
    using in_dom_in_eclose eclose_sing arg_into_eclose
    by blast
qed

lemma ed_eclose : "\<langle>y,z\<rangle> \<in> edrel(A) \<Longrightarrow> y \<in> eclose(z)"
  by(drule edrelD,auto simp add:domain_def in_dom_in_eclose)

lemma tr_edrel_eclose : "\<langle>y,z\<rangle> \<in> edrel(eclose({x}))^+ \<Longrightarrow> y \<in> eclose(z)"
  by(rule trancl_induct,(simp add: ed_eclose mem_eclose_trans)+)

lemma restrict_edrel_eq :
  assumes "z \<in> domain(x)"
  shows "edrel(eclose({x})) \<inter> eclose({z})\<times>eclose({z}) = edrel(eclose({z}))"
proof(intro equalityI subsetI)
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x) \<inter> ?ez \<times> ?ez"
  fix y
  assume "y \<in> ?rr"
  then
  obtain a b where "\<langle>a,b\<rangle> \<in> ?rr" "a \<in> ?ez" "b \<in> ?ez" "\<langle>a,b\<rangle> \<in> ?ec(x)" "y=\<langle>a,b\<rangle>"
    by blast
  moreover from this
  have "a \<in> domain(b)"
    using edrelD by blast
  ultimately
  show "y \<in> edrel(eclose({z}))"
    by blast
next
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x) \<inter> ?ez \<times> ?ez"
  fix y
  assume "y \<in> edrel(?ez)"
  then
  obtain a b where "a \<in> ?ez" "b \<in> ?ez" "y=\<langle>a,b\<rangle>" "a \<in> domain(b)"
    using edrelD by blast
  moreover
  from this assms
  have "z \<in> eclose(x)"
    using in_dom_in_eclose by simp
  moreover
  from assms calculation
  have "a \<in> eclose({x})" "b \<in> eclose({x})"
    using in_eclose_sing by simp_all
  moreover from calculation
  have "\<langle>a,b\<rangle> \<in> edrel(eclose({x}))"
    by blast
  ultimately
  show "y \<in> ?rr"
    by simp
qed

lemma tr_edrel_subset :
  assumes "z \<in> domain(x)"
  shows   "tr_down(edrel(eclose({x})),z) \<subseteq> eclose({z})"
proof(intro subsetI)
  let ?r="\<lambda> x . edrel(eclose({x}))"
  fix y
  assume "y \<in> tr_down(?r(x),z)"
  then
  have "\<langle>y,z\<rangle> \<in> ?r(x)^+"
    using tr_downD by simp
  with assms
  show "y \<in> eclose({z})"
    using tr_edrel_eclose eclose_sing by simp
qed

end