section\<open>Concepts involved in instances of Replacement\<close>
theory Fm_Definitions
  imports
    Transitive_Models.Renaming_Auto
    Transitive_Models.Aleph_Relative
    FrecR_Arities
begin

txt\<open>In this theory we put every concept that should be synthesized in a formula
to have an instance of replacement.

The automatic synthesis of a concept /foo/ requires that every concept used to
define /foo/ is already synthesized. We try to use our meta-programs to synthesize
concepts: given the absolute concept /foo/ we relativize in relational form
obtaining /is\_foo/ and the we synthesize the formula /is\_foo\_fm/.
The meta-program that synthesizes formulas also produce satisfactions lemmas.

Having one file to collect every formula needed for replacements breaks
the reading flow: we need to introduce the concept in this theory in order
to use the meta-programs; moreover there are some concepts for which we prove
here the satisfaction lemmas manually, while for others we prove them
on its theory.
\<close>

declare arity_subset_fm [simp del] arity_ordinal_fm[simp del, arity] arity_transset_fm[simp del]
  FOL_arities[simp del]

txt\<open>Formulas for particular replacement instances\<close>

text\<open>Now we introduce some definitions used in the definition of check; which
is defined by well-founded recursion using replacement in the recursive call.\<close>

\<comment> \<open>The well-founded relation for defining check.\<close>
definition
  rcheck :: "i \<Rightarrow> i" where
  "rcheck(x) \<equiv> Memrel(eclose({x}))^+"

relativize "rcheck" "is_rcheck"
synthesize "is_rcheck" from_definition
arity_theorem for "is_rcheck_fm"

\<comment> \<open>The function used for the replacement.\<close>
definition
  PHcheck :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "PHcheck(M,o,f,y,p) \<equiv> M(p) \<and> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> pair(M,fy,o,p))"

synthesize "PHcheck" from_definition assuming "nonempty"
arity_theorem for "PHcheck_fm"

\<comment> \<open>The recursive call for check. We could use the meta-program relationalize for
this; but it makes some proofs more involved.\<close>
definition
  is_Hcheck :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hcheck(M,o,z,f,hc)  \<equiv> is_Replace(M,z,PHcheck(M,o,f),hc)"

synthesize "is_Hcheck" from_definition assuming "nonempty"

lemma arity_is_Hcheck_fm:
  assumes "m\<in>nat" "n\<in>nat" "p\<in>nat" "o\<in>nat"
  shows "arity(is_Hcheck_fm(m,n,p,o)) = succ(o) \<union> succ(n) \<union> succ(p) \<union> succ(m) "
  unfolding is_Hcheck_fm_def
  using assms arity_Replace_fm[rule_format,OF PHcheck_fm_type _ _ _ arity_PHcheck_fm]
    pred_Un_distrib Un_assoc Un_nat_type
  by simp

\<comment> \<open>The relational version of check is hand-made because our automatic tool
does not handle \<^term>\<open>wfrec\<close>.\<close>
definition
  is_check :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_check(M,o,x,z) \<equiv> \<exists>rch[M]. is_rcheck(M,x,rch) \<and>
      is_wfrec(M,is_Hcheck(M,o),rch,x,z)"

\<comment> \<open>Finally, we internalize the formula.\<close>
definition
  check_fm :: "[i,i,i] \<Rightarrow> i" where
  "check_fm(x,o,z) \<equiv> Exists(And(is_rcheck_fm(1+\<^sub>\<omega>x,0),
                      is_wfrec_fm(is_Hcheck_fm(6+\<^sub>\<omega>o,2,1,0),0,1+\<^sub>\<omega>x,1+\<^sub>\<omega>z)))"

lemma check_fm_type[TC]: "x\<in>nat \<Longrightarrow> o\<in>nat \<Longrightarrow> z\<in>nat \<Longrightarrow> check_fm(x,o,z) \<in> formula"
  by (simp add:check_fm_def)

lemma sats_check_fm :
  assumes
    "o\<in>nat" "x\<in>nat" "z\<in>nat" "env\<in>list(M)" "0\<in>M"
  shows
    "(M , env \<Turnstile> check_fm(x,o,z)) \<longleftrightarrow> is_check(##M,nth(o,env),nth(x,env),nth(z,env))"
proof -
  have sats_is_Hcheck_fm:
    "\<And>a0 a1 a2 a3 a4 a6. \<lbrakk> a0\<in>M; a1\<in>M; a2\<in>M; a3\<in>M; a4\<in>M;a6 \<in>M\<rbrakk> \<Longrightarrow>
         is_Hcheck(##M,a6,a2, a1, a0) \<longleftrightarrow>
         (M , [a0,a1,a2,a3,a4,r,a6]@env \<Turnstile> is_Hcheck_fm(6,2,1,0))" if "r\<in>M" for r
    using that assms
    by simp
  then
  have "(M , [r]@env \<Turnstile> is_wfrec_fm(is_Hcheck_fm(6+\<^sub>\<omega>o,2,1,0),0,1+\<^sub>\<omega>x,1+\<^sub>\<omega>z))
        \<longleftrightarrow> is_wfrec(##M,is_Hcheck(##M,nth(o,env)),r,nth(x,env),nth(z,env))"
    if "r\<in>M" for r
    using that assms is_wfrec_iff_sats'[symmetric]
    by simp
  then
  show ?thesis
    unfolding is_check_def check_fm_def
    using assms is_rcheck_iff_sats[symmetric]
    by simp
qed

lemma iff_sats_check_fm[iff_sats] :
  assumes
    "nth(o, env) = oa" "nth(x, env) = xa" "nth(z, env) = za" "o \<in> nat" "x \<in> nat" "z \<in> nat" "env \<in> list(A)" "0 \<in> A"
  shows "is_check(##A, oa,xa, za) \<longleftrightarrow> A, env \<Turnstile> check_fm(x,o, z)"
  using assms sats_check_fm[symmetric]
  by auto

lemma arity_check_fm[arity]:
  assumes "m\<in>nat" "n\<in>nat" "o\<in>nat"
  shows "arity(check_fm(m,n,o)) = succ(o) \<union> succ(n) \<union> succ(m) "
  unfolding check_fm_def
  using assms arity_is_wfrec_fm[rule_format,OF _ _ _ _ _ arity_is_Hcheck_fm]
    pred_Un_distrib Un_assoc arity_tran_closure_fm
  by (auto simp add:arity)

notation check_fm (\<open>\<cdot>_\<^sup>v_ is _\<cdot>\<close>)

subsection\<open>Names for forcing the Axiom of Choice.\<close>
definition
  upair_name :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "upair_name(\<tau>,\<rho>,on) \<equiv> Upair(\<langle>\<tau>,on\<rangle>,\<langle>\<rho>,on\<rangle>)"

relativize "upair_name" "is_upair_name"
synthesize "upair_name" from_definition "is_upair_name"
arity_theorem for "upair_name_fm"

definition
  opair_name :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "opair_name(\<tau>,\<rho>,on) \<equiv> upair_name(upair_name(\<tau>,\<tau>,on),upair_name(\<tau>,\<rho>,on),on)"

relativize "opair_name" "is_opair_name"
synthesize "opair_name" from_definition "is_opair_name"
arity_theorem for "opair_name_fm"

definition
  is_opname_check :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_opname_check(M,on,s,x,y) \<equiv> \<exists>chx[M]. \<exists>sx[M]. is_check(M,on,x,chx) \<and>
        fun_apply(M,s,x,sx) \<and> is_opair_name(M,chx,sx,on,y)"

synthesize "is_opname_check" from_definition assuming "nonempty"
arity_theorem for "is_opname_check_fm"

\<comment> \<open>The pair of elements belongs to some set. The intended set is the preorder.\<close>
definition
  is_leq :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_leq(A,l,q,p) \<equiv> \<exists>qp[A]. (pair(A,q,p,qp) \<and> qp\<in>l)"

synthesize "is_leq" from_definition assuming "nonempty"
arity_theorem for "is_leq_fm"

abbreviation
  fm_leq :: "[i,i,i] \<Rightarrow> i" (\<open>\<cdot>_\<preceq>\<^bsup>_\<^esup>_\<cdot>\<close>) where
  "fm_leq(A,l,B) \<equiv> is_leq_fm(l,A,B)"

subsection\<open>Formulas used to prove some generic instances.\<close>

definition \<rho>_repl :: "i\<Rightarrow>i" where
  "\<rho>_repl(l) \<equiv> rsum({\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}, id(l), 2, 3, l)"

lemma f_type : "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>} \<in> 2 \<rightarrow> 3"
  using Pi_iff unfolding function_def by auto

\<comment> \<open>thm\<open>Internalize.sum_type\<close> clashes with thm\<open>Renaming.sum_type\<close>.\<close>
hide_fact Internalize.sum_type

lemma ren_type :
  assumes "l\<in>nat"
  shows "\<rho>_repl(l) : 2+\<^sub>\<omega>l \<rightarrow> 3+\<^sub>\<omega>l"
  using sum_type[of 2 3 l l "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}" "id(l)"] f_type assms id_type
  unfolding \<rho>_repl_def by auto

definition Lambda_in_M_fm where [simp]:"Lambda_in_M_fm(\<phi>,len) \<equiv>
  \<cdot>(\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and>
   ren(\<phi>) ` (2 +\<^sub>\<omega> len) ` (3 +\<^sub>\<omega> len) ` \<rho>_repl(len) \<cdot>\<cdot>) \<and> \<cdot>0 \<in> len +\<^sub>\<omega> 2\<cdot>\<cdot>"

lemma Lambda_in_M_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> len\<in>nat \<Longrightarrow> Lambda_in_M_fm(\<phi>,len) \<in>formula"
  using ren_tc[of \<phi> "2+\<^sub>\<omega>len" "3+\<^sub>\<omega>len" "\<rho>_repl(len)"] ren_type
  unfolding Lambda_in_M_fm_def
  by simp

definition \<rho>_pair_repl :: "i\<Rightarrow>i" where
  "\<rho>_pair_repl(l) \<equiv> rsum({\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>}, id(l), 3, 4, l)"

definition LambdaPair_in_M_fm where "LambdaPair_in_M_fm(\<phi>,len) \<equiv>
  \<cdot>(\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and>
             ren((\<cdot>\<exists>(\<cdot>\<exists>\<cdot>\<cdot>fst(2) is 0\<cdot> \<and> \<cdot>\<cdot>snd(2) is 1\<cdot> \<and> ren(\<phi>) ` (3 +\<^sub>\<omega> len) ` (4 +\<^sub>\<omega> len) ` \<rho>_pair_repl(len) \<cdot>\<cdot>\<cdot>)\<cdot>)) ` (2 +\<^sub>\<omega> len) `
             (3 +\<^sub>\<omega> len) `
             \<rho>_repl(len) \<cdot>\<cdot>) \<and>
          \<cdot>0 \<in> len +\<^sub>\<omega> 2\<cdot>\<cdot> "

lemma f_type' : "{\<langle>0,0 \<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>} \<in> 3 \<rightarrow> 4"
  using Pi_iff unfolding function_def by auto

lemma ren_type' :
  assumes "l\<in>nat"
  shows "\<rho>_pair_repl(l) : 3+\<^sub>\<omega>l \<rightarrow> 4+\<^sub>\<omega>l"
  using sum_type[of 3 4 l l "{\<langle>0, 0\<rangle>, \<langle>1, 1\<rangle>, \<langle>2, 3\<rangle>}" "id(l)"] f_type' assms id_type
  unfolding \<rho>_pair_repl_def by auto

lemma LambdaPair_in_M_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> len\<in>nat \<Longrightarrow> LambdaPair_in_M_fm(\<phi>,len) \<in>formula"
  using ren_tc[OF _ _ _ ren_type',of \<phi> "len"] Lambda_in_M_fm_type
  unfolding LambdaPair_in_M_fm_def
  by simp

subsection\<open>The relation \<^term>\<open>frecrel\<close>\<close>

definition
  frecrelP :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "frecrelP(M,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> is_frecR(M,x,y))"

synthesize "frecrelP" from_definition
arity_theorem for "frecrelP_fm"

definition
  is_frecrel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecrel(M,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2, frecrelP(M) ,r)"

synthesize "frecrel" from_definition "is_frecrel"
arity_theorem for "frecrel_fm"

definition
  names_below :: "i \<Rightarrow> i \<Rightarrow> i" where
  "names_below(P,x) \<equiv> 2\<times>ecloseN(x)\<times>ecloseN(x)\<times>P"

lemma names_belowsD:
  assumes "x \<in> names_below(P,z)"
  obtains f n1 n2 p where
    "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>P"
  using assms unfolding names_below_def by auto

synthesize "number2" from_definition

lemma number2_iff :
  "(A)(c) \<Longrightarrow> number2(A,c) \<longleftrightarrow> (\<exists>b[A]. \<exists>a[A]. successor(A, b, c) \<and> successor(A, a, b) \<and> empty(A, a))"
  unfolding number2_def number1_def by auto
arity_theorem for "number2_fm"

reldb_add "ecloseN" "is_ecloseN"
relativize "names_below" "is_names_below"
synthesize "is_names_below" from_definition
arity_theorem for "is_names_below_fm"

definition
  is_tuple :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_tuple(M,z,t1,t2,p,t) \<equiv> \<exists>t1t2p[M]. \<exists>t2p[M]. pair(M,t2,p,t2p) \<and> pair(M,t1,t2p,t1t2p) \<and>
                                                  pair(M,z,t1t2p,t)"

synthesize "is_tuple" from_definition
arity_theorem for "is_tuple_fm"

subsection\<open>Definition of Forces\<close>

subsubsection\<open>Definition of \<^term>\<open>forces\<close> for equality and membership\<close>
text\<open>$p\forces \tau = \theta$ if every $q\leqslant p$ both $q\forces \sigma \in \tau$
and $q\forces \sigma \in \theta$ for every $\sigma \in \dom(\tau)\cup \dom(\theta)$.\<close>
definition
  eq_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "eq_case(\<tau>,\<theta>,p,P,leq,f) \<equiv> \<forall>\<sigma>. \<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<longrightarrow>
      (\<forall>q. q\<in>P \<and> \<langle>q,p\<rangle>\<in>leq \<longrightarrow> (f`\<langle>1,\<sigma>,\<tau>,q\<rangle>=1  \<longleftrightarrow> f`\<langle>1,\<sigma>,\<theta>,q\<rangle> =1))"

relativize "eq_case" "is_eq_case"
synthesize "eq_case" from_definition "is_eq_case"

text\<open>$p\forces \tau \in \theta$ if for every $v\leqslant p$
  there exists $q$, $r$, and $\sigma$ such that
  $v\leqslant q$, $q\leqslant r$, $\langle \sigma,r\rangle \in \tau$, and
  $q\forces \pi = \sigma$.\<close>
definition
  mem_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "mem_case(\<tau>,\<theta>,p,P,leq,f) \<equiv> \<forall>v\<in>P. \<langle>v,p\<rangle>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>\<sigma>. \<exists>r. r\<in>P \<and> q\<in>P \<and> \<langle>q,v\<rangle>\<in>leq \<and> \<langle>\<sigma>,r\<rangle> \<in> \<theta> \<and> \<langle>q,r\<rangle>\<in>leq \<and>  f`\<langle>0,\<tau>,\<sigma>,q\<rangle> = 1)"

relativize "mem_case" "is_mem_case"
synthesize "mem_case" from_definition "is_mem_case"
arity_theorem intermediate for "eq_case_fm"
lemma arity_eq_case_fm[arity]:
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat"
  shows
    "arity(eq_case_fm(n1,n2,p,P,leq,f)) =
    succ(n1) \<union> succ(n2) \<union> succ(p) \<union> succ(P) \<union> succ(leq) \<union> succ(f)"
  using assms arity_eq_case_fm'
  by auto

arity_theorem intermediate for "mem_case_fm"
lemma arity_mem_case_fm[arity] :
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat"
  shows
    "arity(mem_case_fm(n1,n2,p,P,leq,f)) =
    succ(n1) \<union> succ(n2) \<union> succ(p) \<union> succ(P) \<union> succ(leq) \<union> succ(f)"
  using assms arity_mem_case_fm'
  by auto

definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>\<tau>. \<exists>\<theta>. \<exists>p. p\<in>P \<and> fnnc = \<langle>ft,\<tau>,\<theta>,p\<rangle> \<and>
     (  ft = 0 \<and>  eq_case(\<tau>,\<theta>,p,P,leq,f)
      \<or> ft = 1 \<and> mem_case(\<tau>,\<theta>,p,P,leq,f))"

relativize "Hfrc" "is_Hfrc"
synthesize "Hfrc" from_definition "is_Hfrc"

definition
  is_Hfrc_at :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc_at(M,P,leq,fnnc,f,b) \<equiv>
            (empty(M,b) \<and> \<not> is_Hfrc(M,P,leq,fnnc,f))
          \<or> (number1(M,b) \<and> is_Hfrc(M,P,leq,fnnc,f))"

synthesize "Hfrc_at" from_definition "is_Hfrc_at"
arity_theorem intermediate for "Hfrc_fm"

lemma arity_Hfrc_fm[arity] :
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat"
  shows
    "arity(Hfrc_fm(P,leq,fnnc,f)) = succ(P) \<union> succ(leq) \<union> succ(fnnc) \<union> succ(f)"
  using assms arity_Hfrc_fm'
  by auto

arity_theorem for "Hfrc_at_fm"

subsubsection\<open>The well-founded relation \<^term>\<open>forcerel\<close>\<close>
definition
  forcerel :: "i \<Rightarrow> i \<Rightarrow> i" where
  "forcerel(P,x) \<equiv> frecrel(names_below(P,x))^+"

definition
  is_forcerel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_forcerel(M,P,x,z) \<equiv> \<exists>r[M]. \<exists>nb[M]. tran_closure(M,r,z) \<and>
                        (is_names_below(M,P,x,nb) \<and> is_frecrel(M,nb,r))"
synthesize "is_forcerel" from_definition
arity_theorem for "is_forcerel_fm"

subsection\<open>\<^term>\<open>frc_at\<close>, forcing for atomic formulas\<close>
definition
  frc_at :: "[i,i,i] \<Rightarrow> i" where
  "frc_at(P,leq,fnnc) \<equiv> wfrec(frecrel(names_below(P,fnnc)),fnnc,
                              \<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"

\<comment> \<open>The relational form is defined manually because it uses \<^term>\<open>wfrec\<close>.\<close>
definition
  is_frc_at :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_frc_at(M,P,leq,x,z) \<equiv> \<exists>r[M]. is_forcerel(M,P,x,r) \<and>
                                    is_wfrec(M,is_Hfrc_at(M,P,leq),r,x,z)"

definition
  frc_at_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "frc_at_fm(p,l,x,z) \<equiv> Exists(And(is_forcerel_fm(succ(p),succ(x),0),
          is_wfrec_fm(Hfrc_at_fm(6+\<^sub>\<omega>p,6+\<^sub>\<omega>l,2,1,0),0,succ(x),succ(z))))"

lemma frc_at_fm_type [TC] :
  "\<lbrakk>p\<in>nat;l\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> frc_at_fm(p,l,x,z)\<in>formula"
  unfolding frc_at_fm_def by simp

lemma arity_frc_at_fm[arity] :
  assumes "p\<in>nat" "l\<in>nat" "x\<in>nat" "z\<in>nat"
  shows "arity(frc_at_fm(p,l,x,z)) = succ(p) \<union> succ(l) \<union> succ(x) \<union> succ(z)"
proof -
  let ?\<phi> = "Hfrc_at_fm(6 +\<^sub>\<omega> p, 6 +\<^sub>\<omega> l, 2, 1, 0)"
  note assms
  moreover from this
  have  "arity(?\<phi>) = (7+\<^sub>\<omega>p) \<union> (7+\<^sub>\<omega>l)" "?\<phi> \<in> formula"
    using arity_Hfrc_at_fm ord_simp_union
    by auto
  moreover from calculation
  have "arity(is_wfrec_fm(?\<phi>, 0, succ(x), succ(z))) = 2+\<^sub>\<omega>p \<union> (2+\<^sub>\<omega>l) \<union> (2+\<^sub>\<omega>x) \<union> (2+\<^sub>\<omega>z)"
    using arity_is_wfrec_fm[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = _\<close>] pred_Un_distrib pred_succ_eq
      union_abs1
    by auto
  moreover from assms
  have "arity(is_forcerel_fm(succ(p),succ(x),0)) = 2+\<^sub>\<omega>p \<union> (2+\<^sub>\<omega>x)"
    using arity_is_forcerel_fm ord_simp_union
    by auto
  ultimately
  show ?thesis
    unfolding frc_at_fm_def
    using arity_is_forcerel_fm pred_Un_distrib
    by (auto simp:FOL_arities)
qed

lemma sats_frc_at_fm :
  assumes
    "p\<in>nat" "l\<in>nat" "i\<in>nat" "j\<in>nat" "env\<in>list(A)" "i < length(env)" "j < length(env)"
  shows
    "(A , env \<Turnstile> frc_at_fm(p,l,i,j)) \<longleftrightarrow>
     is_frc_at(##A,nth(p,env),nth(l,env),nth(i,env),nth(j,env))"
proof -
  {
    fix r pp ll
    assume "r\<in>A"
    have "is_Hfrc_at(##A,nth(p,env),nth(l,env),a2, a1, a0) \<longleftrightarrow>
         (A, [a0,a1,a2,a3,a4,r]@env \<Turnstile> Hfrc_at_fm(6+\<^sub>\<omega>p,6+\<^sub>\<omega>l,2,1,0))"
      if "a0\<in>A" "a1\<in>A" "a2\<in>A" "a3\<in>A" "a4\<in>A" for a0 a1 a2 a3 a4
      using  that assms \<open>r\<in>A\<close>
        Hfrc_at_iff_sats[of "6+\<^sub>\<omega>p" "6+\<^sub>\<omega>l" 2 1 0 "[a0,a1,a2,a3,a4,r]@env" A]  by simp
    with \<open>r\<in>A\<close>
    have "(A,[r]@env \<Turnstile> is_wfrec_fm(Hfrc_at_fm(6+\<^sub>\<omega>p, 6+\<^sub>\<omega>l,2,1,0),0, i+\<^sub>\<omega>1, j+\<^sub>\<omega>1)) \<longleftrightarrow>
         is_wfrec(##A, is_Hfrc_at(##A, nth(p,env), nth(l,env)), r,nth(i, env), nth(j, env))"
      using assms sats_is_wfrec_fm
      by simp
  }
  moreover
  have "(A, Cons(r, env) \<Turnstile> is_forcerel_fm(succ(p), succ(i), 0)) \<longleftrightarrow>
        is_forcerel(##A,nth(p,env),nth(i,env),r)" if "r\<in>A" for r
    using assms sats_is_forcerel_fm that
    by simp
  ultimately
  show ?thesis
    unfolding is_frc_at_def frc_at_fm_def
    using assms
    by simp
qed

lemma frc_at_fm_iff_sats:
  assumes "nth(i,env) = w" "nth(j,env) = x" "nth(k,env) = y" "nth(l,env) = z"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "l\<in>nat" "env \<in> list(A)" "k<length(env)" "l<length(env)"
  shows "is_frc_at(##A, w, x, y,z) \<longleftrightarrow> (A , env \<Turnstile> frc_at_fm(i,j,k,l))"
  using assms sats_frc_at_fm
  by simp

declare frc_at_fm_iff_sats [iff_sats]

definition
  forces_eq' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_eq'(P,l,p,t1,t2) \<equiv> frc_at(P,l,\<langle>0,t1,t2,p\<rangle>) = 1"

definition
  forces_mem' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_mem'(P,l,p,t1,t2) \<equiv> frc_at(P,l,\<langle>1,t1,t2,p\<rangle>) = 1"

definition
  forces_neq' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_neq'(P,l,p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. \<langle>q,p\<rangle>\<in>l \<and> forces_eq'(P,l,q,t1,t2))"

definition
  forces_nmem' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_nmem'(P,l,p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. \<langle>q,p\<rangle>\<in>l \<and> forces_mem'(P,l,q,t1,t2))"

\<comment> \<open>The following definitions are explicitly defined to avoid the expansion
of concepts.\<close>
definition
  is_forces_eq' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_eq'(M,P,l,p,t1,t2) \<equiv> \<exists>o[M]. \<exists>z[M]. \<exists>t[M]. number1(M,o) \<and> empty(M,z) \<and>
                                is_tuple(M,z,t1,t2,p,t) \<and> is_frc_at(M,P,l,t,o)"

definition
  is_forces_mem' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_mem'(M,P,l,p,t1,t2) \<equiv> \<exists>o[M]. \<exists>t[M]. number1(M,o) \<and>
                                is_tuple(M,o,t1,t2,p,t) \<and> is_frc_at(M,P,l,t,o)"

definition
  is_forces_neq' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_neq'(M,P,l,p,t1,t2) \<equiv>
      \<not> (\<exists>q[M]. q\<in>P \<and> (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>l \<and> is_forces_eq'(M,P,l,q,t1,t2)))"

definition
  is_forces_nmem' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_nmem'(M,P,l,p,t1,t2) \<equiv>
      \<not> (\<exists>q[M]. \<exists>qp[M]. q\<in>P \<and> pair(M,q,p,qp) \<and> qp\<in>l \<and> is_forces_mem'(M,P,l,q,t1,t2))"

synthesize "forces_eq" from_definition "is_forces_eq'"
synthesize "forces_mem" from_definition "is_forces_mem'"
synthesize "forces_neq" from_definition "is_forces_neq'" assuming "nonempty"
synthesize "forces_nmem" from_definition "is_forces_nmem'" assuming "nonempty"

context
  notes Un_assoc[simp] Un_trasposition_aux2[simp]
begin
arity_theorem for "forces_eq_fm"
arity_theorem for "forces_mem_fm"
arity_theorem for "forces_neq_fm"
arity_theorem for "forces_nmem_fm"
end

subsection\<open>Forcing for general formulas\<close>

definition
  ren_forces_nand :: "i\<Rightarrow>i" where
  "ren_forces_nand(\<phi>) \<equiv> Exists(And(Equal(0,1),iterates(\<lambda>p. incr_bv(p)`1 , 2, \<phi>)))"

lemma ren_forces_nand_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_forces_nand(\<phi>) \<in>formula"
  unfolding ren_forces_nand_def
  by simp

lemma arity_ren_forces_nand :
  assumes "\<phi>\<in>formula"
  shows "arity(ren_forces_nand(\<phi>)) \<le> succ(arity(\<phi>))"
proof -
  consider (lt) "1<arity(\<phi>)" | (ge) "\<not> 1 < arity(\<phi>)"
    by auto
  then
  show ?thesis
  proof cases
    case lt
    with \<open>\<phi>\<in>_\<close>
    have "2 < succ(arity(\<phi>))" "2<arity(\<phi>)+\<^sub>\<omega>2"
      using succ_ltI by auto
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`1,2,\<phi>)) = 2+\<^sub>\<omega>arity(\<phi>)"
      using arity_incr_bv_lemma lt
      by auto
    with \<open>\<phi>\<in>_\<close>
    show ?thesis
      unfolding ren_forces_nand_def
      using lt pred_Un_distrib union_abs1 Un_assoc[symmetric] Un_le_compat
      by (simp add:FOL_arities)
  next
    case ge
    with \<open>\<phi>\<in>_\<close>
    have "arity(\<phi>) \<le> 1" "pred(arity(\<phi>)) \<le> 1"
      using not_lt_iff_le le_trans[OF le_pred]
      by simp_all
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`1,2,\<phi>)) = (arity(\<phi>))"
      using arity_incr_bv_lemma ge
      by simp
    with \<open>arity(\<phi>) \<le> 1\<close> \<open>\<phi>\<in>_\<close> \<open>pred(_) \<le> 1\<close>
    show ?thesis
      unfolding ren_forces_nand_def
      using  pred_Un_distrib union_abs1 Un_assoc[symmetric] union_abs2
      by (simp add:FOL_arities)
  qed
qed

lemma sats_ren_forces_nand:
  "[q,P,leq,o,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
   (M, [q,p,P,leq,o] @ env \<Turnstile> ren_forces_nand(\<phi>)) \<longleftrightarrow> (M, [q,P,leq,o] @ env \<Turnstile> \<phi>)"
  unfolding ren_forces_nand_def
  using sats_incr_bv_iff [of _ _ M _ "[q]"]
  by simp


definition
  ren_forces_forall :: "i\<Rightarrow>i" where
  "ren_forces_forall(\<phi>) \<equiv>
      Exists(Exists(Exists(Exists(Exists(
        And(Equal(0,6),And(Equal(1,7),And(Equal(2,8),And(Equal(3,9),
        And(Equal(4,5),iterates(\<lambda>p. incr_bv(p)`5 , 5, \<phi>)))))))))))"

lemma arity_ren_forces_all :
  assumes "\<phi>\<in>formula"
  shows "arity(ren_forces_forall(\<phi>)) = 5 \<union> arity(\<phi>)"
proof -
  consider (lt) "5<arity(\<phi>)" | (ge) "\<not> 5 < arity(\<phi>)"
    by auto
  then
  show ?thesis
  proof cases
    case lt
    with \<open>\<phi>\<in>_\<close>
    have "5 < succ(arity(\<phi>))" "5<arity(\<phi>)+\<^sub>\<omega>2"  "5<arity(\<phi>)+\<^sub>\<omega>3"  "5<arity(\<phi>)+\<^sub>\<omega>4"
      using succ_ltI by auto
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`5,5,\<phi>)) = 5+\<^sub>\<omega>arity(\<phi>)"
      using arity_incr_bv_lemma lt
      by simp
    with \<open>\<phi>\<in>_\<close>
    show ?thesis
      unfolding ren_forces_forall_def
      using pred_Un_distrib union_abs1 Un_assoc[symmetric] union_abs2
      by (simp add:FOL_arities)
  next
    case ge
    with \<open>\<phi>\<in>_\<close>
    have "arity(\<phi>) \<le> 5" "pred^5(arity(\<phi>)) \<le> 5"
      using not_lt_iff_le le_trans[OF le_pred]
      by simp_all
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`5,5,\<phi>)) = arity(\<phi>)"
      using arity_incr_bv_lemma ge
      by simp
    with \<open>arity(\<phi>) \<le> 5\<close> \<open>\<phi>\<in>_\<close> \<open>pred^5(_) \<le> 5\<close>
    show ?thesis
      unfolding ren_forces_forall_def
      using  pred_Un_distrib union_abs1 Un_assoc[symmetric] union_abs2
      by (simp add:FOL_arities)
  qed
qed

lemma ren_forces_forall_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_forces_forall(\<phi>) \<in>formula"
  unfolding ren_forces_forall_def by simp

lemma sats_ren_forces_forall :
  "[x,P,leq,o,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
    (M, [x,p,P,leq,o] @ env \<Turnstile> ren_forces_forall(\<phi>)) \<longleftrightarrow> (M, [p,P,leq,o,x] @ env \<Turnstile> \<phi>)"
  unfolding ren_forces_forall_def
  using sats_incr_bv_iff [of _ _ M _ "[p,P,leq,o,x]"]
  by simp

subsubsection\<open>The primitive recursion\<close>

consts forces' :: "i\<Rightarrow>i"
primrec
  "forces'(Member(x,y)) = forces_mem_fm(1,2,0,x+\<^sub>\<omega>4,y+\<^sub>\<omega>4)"
  "forces'(Equal(x,y))  = forces_eq_fm(1,2,0,x+\<^sub>\<omega>4,y+\<^sub>\<omega>4)"
  "forces'(Nand(p,q))   =
        Neg(Exists(And(Member(0,2),And(is_leq_fm(3,0,1),And(ren_forces_nand(forces'(p)),
                                         ren_forces_nand(forces'(q)))))))"
  "forces'(Forall(p))   = Forall(ren_forces_forall(forces'(p)))"


definition
  forces :: "i\<Rightarrow>i" where
  "forces(\<phi>) \<equiv> And(Member(0,1),forces'(\<phi>))"

lemma forces'_type [TC]:  "\<phi>\<in>formula \<Longrightarrow> forces'(\<phi>) \<in> formula"
  by (induct \<phi> set:formula; simp)

lemma forces_type[TC] : "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
  unfolding forces_def by simp

subsection\<open>The arity of \<^term>\<open>forces\<close>\<close>

lemma arity_forces_at:
  assumes  "x \<in> nat" "y \<in> nat"
  shows "arity(forces(Member(x, y))) = (succ(x) \<union> succ(y)) +\<^sub>\<omega> 4"
    "arity(forces(Equal(x, y))) = (succ(x) \<union> succ(y)) +\<^sub>\<omega> 4"
  unfolding forces_def
  using assms arity_forces_mem_fm arity_forces_eq_fm succ_Un_distrib ord_simp_union
  by (auto simp:FOL_arities,(rule_tac le_anti_sym,simp_all,(rule_tac not_le_anti_sym,simp_all))+)

lemma arity_forces':
  assumes "\<phi>\<in>formula"
  shows "arity(forces'(\<phi>)) \<le> arity(\<phi>) +\<^sub>\<omega> 4"
  using assms
proof (induct set:formula)
  case (Member x y)
  then
  show ?case
    using arity_forces_mem_fm succ_Un_distrib ord_simp_union leI not_le_iff_lt
    by simp
next
  case (Equal x y)
  then
  show ?case
    using arity_forces_eq_fm succ_Un_distrib ord_simp_union leI not_le_iff_lt
    by simp
next
  case (Nand \<phi> \<psi>)
  let ?\<phi>' = "ren_forces_nand(forces'(\<phi>))"
  let ?\<psi>' = "ren_forces_nand(forces'(\<psi>))"
  have "arity(is_leq_fm(3, 0, 1)) = 4"
    using arity_is_leq_fm succ_Un_distrib ord_simp_union
    by simp
  have "3 \<le> (4+\<^sub>\<omega>arity(\<phi>)) \<union> (4+\<^sub>\<omega>arity(\<psi>))" (is "_ \<le> ?rhs")
    using ord_simp_union by simp
  from \<open>\<phi>\<in>_\<close> Nand
  have "pred(arity(?\<phi>')) \<le> ?rhs"  "pred(arity(?\<psi>')) \<le> ?rhs"
  proof -
    from \<open>\<phi>\<in>_\<close> \<open>\<psi>\<in>_\<close>
    have A:"pred(arity(?\<phi>')) \<le> arity(forces'(\<phi>))"
      "pred(arity(?\<psi>')) \<le> arity(forces'(\<psi>))"
      using pred_mono[OF _  arity_ren_forces_nand] pred_succ_eq
      by simp_all
    from Nand
    have "3 \<union> arity(forces'(\<phi>)) \<le> arity(\<phi>) +\<^sub>\<omega> 4"
      "3 \<union> arity(forces'(\<psi>)) \<le> arity(\<psi>) +\<^sub>\<omega> 4"
      using Un_le by simp_all
    with Nand
    show "pred(arity(?\<phi>')) \<le> ?rhs"
      "pred(arity(?\<psi>')) \<le> ?rhs"
      using le_trans[OF A(1)] le_trans[OF A(2)] le_Un_iff
      by simp_all
  qed
  with Nand \<open>_=4\<close>
  show ?case
    using pred_Un_distrib Un_assoc[symmetric] succ_Un_distrib union_abs1 Un_leI3[OF \<open>3 \<le> ?rhs\<close>]
    by (simp add:FOL_arities)
next
  case (Forall \<phi>)
  let ?\<phi>' = "ren_forces_forall(forces'(\<phi>))"
  show ?case
  proof (cases "arity(\<phi>) = 0")
    case True
    with Forall
    show ?thesis
    proof -
      from Forall True
      have "arity(forces'(\<phi>)) \<le> 5"
        using le_trans[of _ 4 5] by auto
      with \<open>\<phi>\<in>_\<close>
      have "arity(?\<phi>') \<le> 5"
        using arity_ren_forces_all[OF forces'_type[OF \<open>\<phi>\<in>_\<close>]] union_abs2
        by auto
      with Forall True
      show ?thesis
        using pred_mono[OF _ \<open>arity(?\<phi>') \<le> 5\<close>]
        by simp
    qed
  next
    case False
    with Forall
    show ?thesis
    proof -
      from Forall False
      have "arity(?\<phi>') = 5 \<union> arity(forces'(\<phi>))"
        "arity(forces'(\<phi>)) \<le> 5 +\<^sub>\<omega> arity(\<phi>)"
        "4 \<le> 3+\<^sub>\<omega>arity(\<phi>)"
        using Ord_0_lt arity_ren_forces_all
          le_trans[OF _ add_le_mono[of 4 5, OF _ le_refl]]
        by auto
      with \<open>\<phi>\<in>_\<close>
      have "5 \<union> arity(forces'(\<phi>)) \<le> 5+\<^sub>\<omega>arity(\<phi>)"
        using ord_simp_union by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(?\<phi>') = 5 \<union> _\<close>
      show ?thesis
        using pred_Un_distrib succ_pred_eq[OF _ \<open>arity(\<phi>)\<noteq>0\<close>]
          pred_mono[OF _ Forall(2)] Un_le[OF \<open>4\<le>3+\<^sub>\<omega>arity(\<phi>)\<close>]
        by simp
    qed
  qed
qed

lemma arity_forces :
  assumes "\<phi>\<in>formula"
  shows "arity(forces(\<phi>)) \<le> 4+\<^sub>\<omega>arity(\<phi>)"
  unfolding forces_def
  using assms arity_forces' le_trans ord_simp_union FOL_arities by auto

lemma arity_forces_le :
  assumes "\<phi>\<in>formula" "n\<in>nat" "arity(\<phi>) \<le> n"
  shows "arity(forces(\<phi>)) \<le> 4+\<^sub>\<omega>n"
  using assms le_trans[OF _ add_le_mono[OF le_refl[of 5] \<open>arity(\<phi>)\<le>_\<close>]] arity_forces
  by auto

definition rename_split_fm where
  "rename_split_fm(\<phi>) \<equiv> (\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>\<cdot>\<cdot>snd(9) is 0\<cdot> \<and> \<cdot>\<cdot>fst(9) is 4\<cdot> \<and> \<cdot>\<cdot>1=11\<cdot> \<and>
    \<cdot>\<cdot>2=12\<cdot> \<and> \<cdot>\<cdot>3=13\<cdot> \<and> \<cdot>\<cdot>5=7\<cdot> \<and>
    (\<lambda>p. incr_bv(p)`6)^8(forces(\<phi>)) \<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)"

lemma rename_split_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> rename_split_fm(\<phi>)\<in>formula"
  unfolding rename_split_fm_def by simp

schematic_goal arity_rename_split_fm: "\<phi>\<in>formula \<Longrightarrow> arity(rename_split_fm(\<phi>)) = ?m"
  using arity_forces[of \<phi>] forces_type unfolding rename_split_fm_def
  by (simp add:arity Un_assoc[symmetric] union_abs1)

lemma arity_rename_split_fm_le:
  assumes "\<phi>\<in>formula"
  shows "arity(rename_split_fm(\<phi>)) \<le> 8 \<union> (6 +\<^sub>\<omega> arity(\<phi>))"
proof -
  from assms
  have arity_forces_6: "\<not> 1 < arity(\<phi>) \<Longrightarrow> 6 \<le> n \<Longrightarrow> arity(forces(\<phi>)) \<le> n" for n
    using le_trans lt_trans[of _ 5 n] not_lt_iff_le[of 1 "arity(\<phi>)"]
    by (auto intro!:le_trans[OF arity_forces])
  have pred1_arity_forces: "\<not> 1 < arity(\<phi>) \<Longrightarrow> pred^n(arity(forces(\<phi>))) \<le> 8" if "n\<in>nat" for n
    using that pred_le[of 7] le_succ[THEN [2] le_trans] arity_forces_6
    by (induct rule:nat_induct) auto
  have arity_forces_le_succ6: "pred^n(arity(forces(\<phi>))) \<le> succ(succ(succ(succ(succ(succ(arity(\<phi>)))))))"
    if "n\<in>nat" for n
    using that assms arity_forces[of \<phi>, THEN le_trans,
        OF _ le_succ, THEN le_trans, OF _ _ le_succ] le_trans[OF pred_le[OF _ le_succ]]
    by (induct rule:nat_induct) auto
  note trivial_arities = arity_forces_6
    arity_forces_le_succ6[of 1, simplified] arity_forces_le_succ6[of 2, simplified]
    arity_forces_le_succ6[of 3, simplified] arity_forces_le_succ6[of 4, simplified]
    arity_forces_le_succ6[of 5, simplified] arity_forces_le_succ6[of 6, simplified]
    pred1_arity_forces[of 1, simplified] pred1_arity_forces[of 2, simplified]
    pred1_arity_forces[of 3, simplified] pred1_arity_forces[of 4, simplified]
    pred1_arity_forces[of 5, simplified] pred1_arity_forces[of 6, simplified]
  show ?thesis
    using assms arity_forces[of \<phi>] arity_forces[of \<phi>, THEN le_trans, OF _ le_succ]
      arity_forces[of \<phi>, THEN le_trans, OF _ le_succ, THEN le_trans, OF _ _ le_succ]
    unfolding rename_split_fm_def
    by (simp add:arity Un_assoc[symmetric] union_abs1 arity_forces[of \<phi>] forces_type)
      ((subst arity_incr_bv_lemma; auto simp: arity ord_simp_union forces_type trivial_arities)+)
qed

definition body_ground_repl_fm where
  "body_ground_repl_fm(\<phi>) \<equiv> (\<cdot>\<exists>(\<cdot>\<exists>\<cdot>is_Vset_fm(2, 0) \<and> \<cdot>\<cdot>1 \<in> 0\<cdot> \<and> rename_split_fm(\<phi>) \<cdot>\<cdot>\<cdot>)\<cdot>)"

lemma body_ground_repl_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> body_ground_repl_fm(\<phi>)\<in>formula"
  unfolding body_ground_repl_fm_def by simp

lemma arity_body_ground_repl_fm_le:
  notes le_trans[trans]
  assumes "\<phi>\<in>formula"
  shows "arity(body_ground_repl_fm(\<phi>)) \<le> 6 \<union> (arity(\<phi>) +\<^sub>\<omega> 4)"
proof -
  from \<open>\<phi>\<in>formula\<close>
  have ineq: "n \<union> pred(pred(arity(rename_split_fm(\<phi>))))
    \<le> m \<union> pred(pred(8 \<union> (arity(\<phi>) +\<^sub>\<omega>6 )))" if "n \<le> m" "n\<in>nat" "m\<in>nat" for n m
    using that arity_rename_split_fm_le[of \<phi>, THEN [2] pred_mono, THEN [2] pred_mono,
        THEN [2] Un_mono[THEN subset_imp_le, OF _ le_imp_subset]] le_imp_subset
    by auto
  moreover
  have eq1: "pred(pred(pred(4 \<union> 2 \<union> pred(pred(pred(
    pred(pred(pred(pred(pred(9 \<union> 1 \<union> 3 \<union> 2))))))))))) = 1"
    by (auto simp:pred_Un_distrib)
  ultimately
  have "pred(pred(pred(4 \<union> 2 \<union> pred(pred(pred(
    pred(pred(pred(pred(pred(9 \<union> 1 \<union> 3 \<union> 2))))))))))) \<union>
    pred(pred(arity(rename_split_fm(\<phi>)))) \<le>
    1 \<union> pred(pred(8 \<union> (arity(\<phi>) +\<^sub>\<omega>6 )))"
    by auto
  also from \<open>\<phi>\<in>formula\<close>
  have "1 \<union> pred(pred(8 \<union> (arity(\<phi>) +\<^sub>\<omega>6 ))) \<le> 6 \<union> (4+\<^sub>\<omega>arity(\<phi>))"
    by (auto simp:pred_Un_distrib Un_assoc[symmetric] ord_simp_union)
  finally
  show ?thesis
    using  \<open>\<phi>\<in>formula\<close> unfolding body_ground_repl_fm_def
    by (simp add:arity pred_Un_distrib, subst arity_transrec_fm[of "is_HVfrom_fm(8,2,1,0)" 3 1])
      (simp add:arity pred_Un_distrib,simp_all,
        auto simp add:eq1 arity_is_HVfrom_fm[of 8 2 1 0])
qed

definition ground_repl_fm where
  "ground_repl_fm(\<phi>) \<equiv> least_fm(body_ground_repl_fm(\<phi>), 1)"

lemma ground_repl_fm_type[TC]:
  "\<phi>\<in>formula \<Longrightarrow> ground_repl_fm(\<phi>) \<in> formula"
  unfolding ground_repl_fm_def by simp

lemma arity_ground_repl_fm:
  assumes "\<phi>\<in>formula"
  shows "arity(ground_repl_fm(\<phi>)) \<le> 5 \<union> (3 +\<^sub>\<omega> arity(\<phi>))"
proof -
  from assms
  have "pred(arity(body_ground_repl_fm(\<phi>))) \<le> 5 \<union> (3 +\<^sub>\<omega> arity(\<phi>))"
    using arity_body_ground_repl_fm_le pred_mono succ_Un_distrib
    by (rule_tac pred_le) auto
  with assms
  have "2 \<union> pred(arity(body_ground_repl_fm(\<phi>))) \<le> 5 \<union> (3 +\<^sub>\<omega> arity(\<phi>))"
    using Un_le le_Un_iff by auto
  then
  show ?thesis
    using assms arity_forces arity_body_ground_repl_fm_le
    unfolding least_fm_def ground_repl_fm_def
    apply (auto simp add:arity Un_assoc[symmetric])
    apply (simp add: pred_Un Un_assoc, simp add: Un_assoc[symmetric] union_abs1 pred_Un)
    by(simp only: Un_commute, subst Un_commute, simp add:ord_simp_union,force)
qed

simple_rename "ren_F" src "[x_P, x_leq, x_o, x_f, y_c, x_bc, p, x, b]"
  tgt "[x_bc, y_c,b,x, x_P, x_leq, x_o, x_f, p]"

simple_rename "ren_G" src "[x,x_P, x_leq, x_one, x_f,x_p,y,x_B]"
  tgt "[x,y,x_P, x_leq, x_one, x_f,x_p,x_B]"

simple_rename "ren_F_aux" src "[q,x_P, x_leq, x_one, f_dot, x_a, x_bc,x_p,x_b]"
  tgt "[x_bc, q, x_b, x_P, x_leq, x_one, f_dot,x_a,x_p]"

simple_rename "ren_G_aux" src "[ x_b, x_P, x_leq, x_one, f_dot,x_a,x_p,y]"
  tgt "[ x_b, y, x_P, x_leq, x_one, f_dot,x_a,x_p]"

definition ccc_fun_closed_lemma_aux2_fm where [simp]:
  "ccc_fun_closed_lemma_aux2_fm \<equiv> ren(Collect_fm(1, (\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v5 is 0\<cdot> \<and> ren(\<cdot>\<cdot>0\<preceq>\<^bsup>2\<^esup>7\<cdot>
  \<and> forces(\<cdot>0`1 is 2\<cdot> ) \<cdot> ) ` 9 ` 9 ` ren_F_aux_fn\<cdot>\<cdot>), 7)) ` 8 ` 8 ` ren_G_aux_fn"

lemma ccc_fun_closed_lemma_aux2_fm_type [TC] :
  "ccc_fun_closed_lemma_aux2_fm \<in> formula"
proof -
  let ?\<psi>="\<cdot>\<cdot>0\<preceq>\<^bsup>2\<^esup>7\<cdot>  \<and> forces(\<cdot>0`1 is 2\<cdot> ) \<cdot> "
  let ?G="(\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v5 is 0\<cdot> \<and> ren(?\<psi>) ` 9 ` 9 ` ren_F_aux_fn\<cdot>\<cdot>)"
  have "ren(?\<psi>)`9`9`ren_F_aux_fn \<in> formula"
    using ren_tc ren_F_aux_thm check_fm_type is_leq_fm_type ren_F_aux_fn_def pred_le
    by simp_all
  then
  show ?thesis
    using ren_tc ren_G_aux_thm ren_G_aux_fn_def
    by simp
qed

definition ccc_fun_closed_lemma_fm where [simp]:
  "ccc_fun_closed_lemma_fm \<equiv> ren(Collect_fm(7, (\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v5 is 0\<cdot> \<and> (\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v6 is 0\<cdot> \<and>
   ren((\<cdot>\<exists>\<cdot>\<cdot>0 \<in> 1\<cdot> \<and> \<cdot>\<cdot>0\<preceq>\<^bsup>2\<^esup>7\<cdot> \<and> forces(\<cdot>0`1 is 2\<cdot> ) \<cdot>\<cdot>\<cdot>)) ` 9 ` 9 ` ren_F_fn\<cdot>\<cdot>)\<cdot>\<cdot>), 6))
   ` 8 ` 8 ` ren_G_fn"

lemma ccc_fun_closed_lemma_fm_type [TC] :
  "ccc_fun_closed_lemma_fm \<in> formula"
proof -
  let ?\<psi>="(\<cdot>\<exists>\<cdot>\<cdot>0 \<in> 1\<cdot> \<and> \<cdot> \<cdot>0 \<preceq>\<^bsup>2\<^esup> 7\<cdot> \<and> forces(\<cdot>0`1 is 2\<cdot> ) \<cdot>\<cdot>\<cdot>)"
  let ?G="(\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v5 is 0\<cdot> \<and> (\<cdot>\<exists>\<cdot>\<cdot>2\<^sup>v6 is 0\<cdot> \<and> ren(?\<psi>) ` 9 ` 9 ` ren_F_fn\<cdot>\<cdot>)\<cdot>\<cdot>)"
  have "ren(?\<psi>)`9`9`ren_F_fn \<in> formula"
    using ren_tc ren_F_thm check_fm_type is_leq_fm_type ren_F_fn_def pred_le
    by simp_all
  then
  show ?thesis
    using ren_tc ren_G_thm ren_G_fn_def
    by simp
qed

definition is_order_body
  where "is_order_body(M,X,x,z) \<equiv> \<exists>A[M]. cartprod(M,X,X,A) \<and> subset(M,x,A) \<and> M(z) \<and> M(x) \<and>
           is_well_ord(M,X, x) \<and> is_ordertype(M,X, x,z)"

synthesize "is_order_body" from_definition assuming "nonempty"

definition omap_wfrec_body where
  "omap_wfrec_body(A,r) \<equiv> (\<cdot>\<exists>\<cdot>image_fm(2, 0, 1) \<and> pred_set_fm(9+\<^sub>\<omega>A, 3,9+\<^sub>\<omega>r, 0) \<cdot>\<cdot>)"

lemma type_omap_wfrec_body_fm :"A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow> omap_wfrec_body(A,r)\<in>formula"
  unfolding omap_wfrec_body_def by simp

lemma arity_omap_wfrec_aux : "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow> arity(omap_wfrec_body(A,r)) = (9+\<^sub>\<omega>A) \<union> (9+\<^sub>\<omega>r)"
  unfolding omap_wfrec_body_def
  using arity_image_fm arity_pred_set_fm pred_Un_distrib union_abs2[of 3] union_abs1
  by (simp add:FOL_arities, auto simp add:Un_assoc[symmetric] union_abs1)

lemma arity_omap_wfrec: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>
  arity(is_wfrec_fm(omap_wfrec_body(A,r),r+\<^sub>\<omega>3, 1, 0)) = (4+\<^sub>\<omega>A) \<union> (4+\<^sub>\<omega>r)"
  using Arities.arity_is_wfrec_fm[OF _ _ _ _ _ arity_omap_wfrec_aux,of A r "3+\<^sub>\<omega>r" 1 0]
    pred_Un_distrib union_abs1 union_abs2 type_omap_wfrec_body_fm
  by auto

lemma arity_isordermap: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>d\<in>nat\<Longrightarrow>
   arity(is_ordermap_fm(A,r,d)) = succ(d) \<union> (succ(A) \<union> succ(r))"
  unfolding is_ordermap_fm_def
  using arity_lambda_fm[where i="(4+\<^sub>\<omega>A) \<union> (4+\<^sub>\<omega>r)",OF _ _ _ _ arity_omap_wfrec,
      unfolded omap_wfrec_body_def] pred_Un_distrib union_abs1
  by auto


lemma arity_is_ordertype: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>d\<in>nat\<Longrightarrow>
   arity(is_ordertype_fm(A,r,d)) = succ(d) \<union> (succ(A) \<union> succ(r))"
  unfolding is_ordertype_fm_def
  using arity_isordermap arity_image_fm pred_Un_distrib FOL_arities
  by auto

arity_theorem for "is_order_body_fm"

lemma arity_is_order_body: "arity(is_order_body_fm(2,0,1)) = 3"
  using arity_is_order_body_fm arity_is_ordertype ord_simp_union
  by (simp add:FOL_arities)

definition H_order_pred where
  "H_order_pred(A,r) \<equiv>  \<lambda>x f . f `` Order.pred(A, x, r)"

relationalize "H_order_pred" "is_H_order_pred"

synthesize "is_H_order_pred" from_definition assuming "nonempty"

definition order_pred_wfrec_body where
  "order_pred_wfrec_body(M,A,r,z,x) \<equiv> \<exists>y[M].
                pair(M, x, y, z) \<and>
                (\<exists>f[M].
                    (\<forall>z[M].
                        z \<in> f \<longleftrightarrow>
                        (\<exists>xa[M].
                            \<exists>y[M].
                               \<exists>xaa[M].
                                  \<exists>sx[M].
                                     \<exists>r_sx[M].
                                        \<exists>f_r_sx[M].
                                           pair(M, xa, y, z) \<and>
                                           pair(M, xa, x, xaa) \<and>
                                           upair(M, xa, xa, sx) \<and>
                                           pre_image(M, r, sx, r_sx) \<and>
                                           restriction(M, f, r_sx, f_r_sx) \<and>
                                           xaa \<in> r \<and> (\<exists>a[M]. image(M, f_r_sx, a, y) \<and> pred_set(M, A, xa, r, a)))) \<and>
                    (\<exists>a[M]. image(M, f, a, y) \<and> pred_set(M, A, x, r, a)))"


synthesize "order_pred_wfrec_body" from_definition
arity_theorem for "order_pred_wfrec_body_fm"

definition replacement_is_order_body_fm where "replacement_is_order_body_fm \<equiv> is_order_body_fm(2,0,1)"
definition wfrec_replacement_order_pred_fm where "wfrec_replacement_order_pred_fm \<equiv> order_pred_wfrec_body_fm(3,2,1,0)"
definition replacement_is_jump_cardinal_body_fm where "replacement_is_jump_cardinal_body_fm \<equiv> is_jump_cardinal_body'_fm(0,1)"
definition replacement_is_aleph_fm where "replacement_is_aleph_fm \<equiv> \<cdot>\<cdot>0 is ordinal\<cdot> \<and> \<cdot>\<aleph>(0) is 1\<cdot>\<cdot>"

definition
  funspace_succ_rep_intf where
  "funspace_succ_rep_intf \<equiv> \<lambda>p z n. \<exists>f b. p = <f,b> & z = {cons(<n,b>, f)}"

relativize functional "funspace_succ_rep_intf" "funspace_succ_rep_intf_rel"

\<comment> \<open>The definition obtained next uses \<^term>\<open>is_cons\<close> instead of \<^term>\<open>upair\<close>
  as in Paulson's \<^file>\<open>~~/src/ZF/Constructible/Relative.thy\<close>.\<close>
relationalize "funspace_succ_rep_intf_rel" "is_funspace_succ_rep_intf"

synthesize "is_funspace_succ_rep_intf" from_definition

arity_theorem for "is_funspace_succ_rep_intf_fm"

definition
  PHrank :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "PHrank(M,f,y,z) \<equiv> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> successor(M,fy,z))"

synthesize "PHrank" from_definition assuming "nonempty"

definition wfrec_Hfrc_at_fm where "wfrec_Hfrc_at_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(Hfrc_at_fm(8, 9, 2, 1, 0), 5, 1, 0) \<cdot>\<cdot>)"
definition list_repl1_intf_fm where "list_repl1_intf_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(iterates_MH_fm(list_functor_fm(13, 1, 0), 10, 2, 1, 0), 3, 1, 0) \<cdot>\<cdot>)"
definition list_repl2_intf_fm where "list_repl2_intf_fm \<equiv> \<cdot>\<cdot>0 \<in> 4\<cdot> \<and> is_iterates_fm(list_functor_fm(13, 1, 0), 3, 0, 1) \<cdot>"
definition formula_repl2_intf_fm where "formula_repl2_intf_fm \<equiv> \<cdot>\<cdot>0 \<in> 3\<cdot> \<and> is_iterates_fm(formula_functor_fm(1, 0), 2, 0, 1) \<cdot>"
definition eclose_repl2_intf_fm where "eclose_repl2_intf_fm \<equiv> \<cdot>\<cdot>0 \<in> 3\<cdot> \<and> is_iterates_fm(\<cdot>\<Union>1 is 0\<cdot>, 2, 0, 1) \<cdot>"
definition powapply_repl_fm where "powapply_repl_fm \<equiv> is_Powapply_fm(2,0,1)"
definition phrank_repl_fm where "phrank_repl_fm \<equiv> PHrank_fm(2,0,1)"
definition wfrec_rank_fm where "wfrec_rank_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(is_Hrank_fm(2, 1, 0), 3, 1, 0) \<cdot>\<cdot>)"
definition trans_repl_HVFrom_fm where "trans_repl_HVFrom_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(is_HVfrom_fm(8, 2, 1, 0), 4, 1, 0) \<cdot>\<cdot>)"
definition wfrec_Hcheck_fm where "wfrec_Hcheck_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(is_Hcheck_fm(8, 2, 1, 0), 4, 1, 0) \<cdot>\<cdot>) "
definition repl_PHcheck_fm where "repl_PHcheck_fm \<equiv> PHcheck_fm(2,3,0,1)"
definition check_replacement_fm where "check_replacement_fm \<equiv> \<cdot>check_fm(0,2,1) \<and> \<cdot>0 \<in> 3\<cdot>\<cdot>"
definition G_dot_in_M_fm where "G_dot_in_M_fm \<equiv>  \<cdot>(\<cdot>\<exists>\<cdot>\<cdot>1\<^sup>v3 is 0\<cdot> \<and> pair_fm(0, 1, 2) \<cdot>\<cdot>) \<and> \<cdot>0 \<in> 3\<cdot>\<cdot>"
definition repl_opname_check_fm where "repl_opname_check_fm \<equiv> \<cdot>is_opname_check_fm(3,2,0,1) \<and> \<cdot>0 \<in> 4\<cdot>\<cdot>"
definition tl_repl_intf_fm where "tl_repl_intf_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(iterates_MH_fm(tl_fm(1,0), 9, 2, 1, 0), 3, 1, 0) \<cdot>\<cdot>)"
definition formula_repl1_intf_fm where "formula_repl1_intf_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(iterates_MH_fm(formula_functor_fm(1,0), 9, 2, 1, 0), 3, 1, 0) \<cdot>\<cdot>)"
definition eclose_repl1_intf_fm where "eclose_repl1_intf_fm \<equiv> (\<cdot>\<exists>\<cdot>pair_fm(1, 0, 2) \<and> is_wfrec_fm(iterates_MH_fm(big_union_fm(1,0), 9, 2, 1, 0), 3, 1, 0) \<cdot>\<cdot>)"

definition replacement_assm where
  "replacement_assm(M,env,\<phi>) \<equiv> \<phi> \<in> formula \<longrightarrow> env \<in> list(M) \<longrightarrow>
  arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(env) \<longrightarrow>
    strong_replacement(##M,\<lambda>x y. (M , [x,y]@env \<Turnstile> \<phi>))"

definition ground_replacement_assm where
  "ground_replacement_assm(M,env,\<phi>) \<equiv> replacement_assm(M,env,ground_repl_fm(\<phi>))"

end
