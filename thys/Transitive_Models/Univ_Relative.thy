section\<open>Relativization of the cumulative hierarchy\<close>
theory Univ_Relative
  imports
    "ZF-Constructible.Rank"
    "ZF.Univ"
    Discipline_Cardinal

begin

declare arity_ordinal_fm[arity]

context M_trivial
begin
declare powerset_abs[simp]

lemma family_union_closed: "\<lbrakk>strong_replacement(M, \<lambda>x y. y = f(x)); M(A); \<forall>x\<in>A. M(f(x))\<rbrakk>
      \<Longrightarrow> M(\<Union>x\<in>A. f(x))"
  using RepFun_closed ..

lemma family_union_closed': "\<lbrakk>strong_replacement(M, \<lambda>x y. x\<in>A \<and> y = f(x)); M(A); \<forall>x\<in>A. M(f(x))\<rbrakk>
      \<Longrightarrow> M(\<Union>x\<in>A. f(x))"
  using RepFun_closed2
  by simp

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

definition
  Powapply :: "[i,i] \<Rightarrow> i"  where
  "Powapply(f,y) \<equiv> Pow(f`y)"

reldb_add functional "Pow" "Pow_rel"
reldb_add relational "Pow" "is_Pow"

declare Replace_iff_sats[iff_sats]
synthesize "is_Pow" from_definition assuming "nonempty"
arity_theorem for "is_Pow_fm"

relativize functional "Powapply" "Powapply_rel"
relationalize "Powapply_rel" "is_Powapply"
synthesize "is_Powapply" from_definition assuming "nonempty"
arity_theorem for "is_Powapply_fm"

notation Powapply_rel (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>)

context M_basic
begin

rel_closed for "Powapply"
  unfolding Powapply_rel_def
  by simp

is_iff_rel for "Powapply"
  using Pow_rel_iff
  unfolding is_Powapply_def Powapply_rel_def
  by simp

end \<comment>\<open>\<^locale>\<open>M_basic\<close>\<close>

definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply(f,y))"

relativize functional "HVfrom" "HVfrom_rel"
relationalize "HVfrom_rel" "is_HVfrom"
synthesize "is_HVfrom" from_definition assuming "nonempty"
arity_theorem intermediate for "is_HVfrom_fm"

lemma arity_is_HVfrom_fm:
  "A \<in> nat \<Longrightarrow>
    x \<in> nat \<Longrightarrow>
    f \<in> nat \<Longrightarrow>
    d \<in> nat \<Longrightarrow>
    arity(is_HVfrom_fm(A, x, f, d)) = succ(A) \<union> succ(d) \<union> (succ(x) \<union> succ(f))"
  using arity_is_HVfrom_fm' arity_is_Powapply_fm
  by(simp,subst arity_Replace_fm[of "is_Powapply_fm(succ(succ(succ(succ(f)))), 0, 1)" "succ(succ(x))" 1])
    (simp_all, auto simp add:arity pred_Un_distrib)

notation HVfrom_rel (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>)

locale M_HVfrom = M_eclose +
  assumes
    Powapply_replacement:
    "M(f) \<Longrightarrow> strong_replacement(M,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y))"
begin

is_iff_rel for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)" "M(res)"
  then
  have "is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that Powapply_rel_closed
      Replace_abs[of x r "\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y)"] transM[of _ x]
    by simp
  moreover
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow>
        is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r)" if "M(r)" for r
    using assms that is_Powapply_iff is_Replace_cong
    by simp
  ultimately
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that assms
    by simp
  moreover
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})"
    using assms strong_replacement_closed[OF Powapply_replacement]
      Powapply_rel_closed transM[of _ x]
    by simp
  moreover from assms
    \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}"
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
    unfolding is_HVfrom_def HVfrom_rel_def
    by (auto dest:transM)
qed

rel_closed for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)"
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})"
    using assms strong_replacement_closed[OF Powapply_replacement]
      Powapply_rel_closed transM[of _ x]
    by simp
  then
  have "M(A \<union> \<Union>({z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}))"
    using assms
    by simp
  moreover from assms
    \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}"
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
    unfolding HVfrom_rel_def
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_HVfrom\<close>\<close>

definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Vfrom\<^bsup>M\<^esup>(A,i) = transrec(i, HVfrom_rel(M,A))"

definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_transrec(M,is_HVfrom(M,A),i,z)"

definition
  Hrank :: "[i,i] \<Rightarrow> i" where
  "Hrank(x,f) \<equiv> (\<Union>y\<in>x. succ(f`y))"

definition
  rrank :: "i \<Rightarrow> i" where
  "rrank(a) \<equiv> Memrel(eclose({a}))^+"

relativize functional "Hrank" "Hrank_rel"
relationalize "Hrank_rel" "is_Hrank"
synthesize "is_Hrank" from_definition assuming "nonempty"

lemma arity_is_Hrank_fm : "x \<in> nat \<Longrightarrow>
    f \<in> nat \<Longrightarrow>
    d \<in> nat \<Longrightarrow>
    arity(is_Hrank_fm(x, f, d)) =
    succ(d) \<union> succ(x) \<union> succ(f)"
  unfolding is_Hrank_fm_def
  using  arity_fun_apply_fm arity_big_union_fm
    arity_fun_apply_fm arity_succ_fm arity_And arity_Exists
    arity_Replace_fm[of
      "(\<cdot>\<exists>\<cdot>\<cdot>succ(0) is 2\<cdot> \<and> \<cdot> succ(succ(succ(succ(f))))`1 is 0\<cdot>\<cdot>\<cdot>)"
      "succ(x)" 0 "4+\<^sub>\<omega>f"]
  by(simp_all add:Un_assoc pred_Un,simp add:ord_simp_union)

locale M_Vfrom = M_HVfrom +
  assumes
    trepl_HVfrom : "\<lbrakk> M(A);M(i) \<rbrakk> \<Longrightarrow> transrec_replacement(M,is_HVfrom(M,A),i)"
    and
    Hrank_replacement : "M(f) \<Longrightarrow> strong_replacement(M,\<lambda>x y . y = succ(f`x))"
    and
    is_Hrank_replacement : "M(x) \<Longrightarrow> wfrec_replacement(M,is_Hrank(M),rrank(x))"
    and
    HVfrom_replacement : "\<lbrakk> M(i) ; M(A) \<rbrakk> \<Longrightarrow>
                          transrec_replacement(M,is_HVfrom(M,A),i)"

begin

lemma Vfrom_rel_iff :
  assumes "M(A)" "M(i)" "M(z)" "Ord(i)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom\<^bsup>M\<^esup>(A,i)"
proof -
  have "relation2(M, is_HVfrom(M, A), HVfrom_rel(M, A))"
    using assms is_HVfrom_iff
    unfolding relation2_def
    by simp
  then
  show ?thesis
    using assms HVfrom_rel_closed trepl_HVfrom
      transrec_abs[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)" z]
    unfolding is_Vfrom_def Vfrom_rel_def
    by simp
qed

lemma relation2_HVfrom: "M(A) \<Longrightarrow> relation2(M,is_HVfrom(M,A),HVfrom_rel(M,A))"
  using is_HVfrom_iff
  unfolding relation2_def
  by auto

lemma HVfrom_closed :
  "M(A) \<Longrightarrow> \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(HVfrom_rel(M,A,x,g))"
  using HVfrom_rel_closed by simp

lemma Vfrom_rel_closed:
  assumes "M(A)" "M(i)" "Ord(i)"
  shows "M(transrec(i, HVfrom_rel(M, A)))"
  using is_HVfrom_iff HVfrom_closed HVfrom_replacement assms trepl_HVfrom relation2_HVfrom
    transrec_closed[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)"]
  by simp

lemma transrec_HVfrom:
  assumes "M(A)"
  shows "Ord(i) \<Longrightarrow> M(i) \<Longrightarrow> {x\<in>Vfrom(A,i). M(x)} = transrec(i,HVfrom_rel(M,A))"
proof (induct rule:trans_induct)
  have eq:"(\<Union>x\<in>i. {x \<in> Pow(transrec(x, HVfrom_rel(M, A))) . M(x)}) =  \<Union>{y . x \<in> i, y = Pow\<^bsup>M\<^esup>(transrec(x, HVfrom_rel(M, A)))}"
    if "Ord(i)" "M(i)" for i
    using assms Pow_rel_char[OF Vfrom_rel_closed[OF \<open>M(A)\<close> transM[of _ i]]] Ord_in_Ord' that
    by auto
  case (step i)
  then
  have 0: "M(Pow\<^bsup>M\<^esup>(transrec(x, HVfrom_rel(M, A))))" if "x\<in>i" for x
    using assms that transM[of _ i] Ord_in_Ord
      transrec_closed[of "is_HVfrom(M,A)" _ "HVfrom_rel(M,A)"] trepl_HVfrom relation2_HVfrom
    by auto
  have "Vfrom(A,i) = A \<union> (\<Union>y\<in>i. Pow((\<lambda>x\<in>i. Vfrom(A, x)) ` y))"
    using def_transrec[OF Vfrom_def, of A i] by simp
  then
  have "Vfrom(A,i) = A \<union> (\<Union>y\<in>i. Pow(Vfrom(A, y)))"
    by simp
  then
  have "{x\<in>Vfrom(A,i). M(x)} = {x\<in>A. M(x)} \<union> (\<Union>y\<in>i. {x\<in>Pow(Vfrom(A, y)). M(x)})"
    by auto
  with \<open>M(A)\<close>
  have "{x\<in>Vfrom(A,i). M(x)} = A \<union> (\<Union>y\<in>i. {x\<in>Pow(Vfrom(A, y)). M(x)})"
    by (auto intro:transM)
  also
  have "... = A \<union> (\<Union>y\<in>i. {x\<in>Pow({z\<in>Vfrom(A,y). M(z)}). M(x)})"
  proof -
    have "{x\<in>Pow(Vfrom(A, y)). M(x)} = {x\<in>Pow({z\<in>Vfrom(A,y). M(z)}). M(x)}"
      if "y\<in>i" for y by (auto intro:transM)
    then
    show ?thesis by simp
  qed
  also from step
  have " ... = A \<union> (\<Union>y\<in>i. {x\<in>Pow(transrec(y, HVfrom_rel(M, A))). M(x)})"
    using transM[of _ i]
    by auto
  also
  have " ... = transrec(i, HVfrom_rel(M, A))"
    using 0 step assms transM[of _ i] eq
      def_transrec[of "\<lambda>y. transrec(y, HVfrom_rel(M, A))" "HVfrom_rel(M, A)" i]
    unfolding Powapply_rel_def HVfrom_rel_def
    by auto
  finally
  show ?case .
qed

lemma Vfrom_abs: "\<lbrakk> M(A); M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vfrom(M,A,i,V) \<longleftrightarrow> V = {x\<in>Vfrom(A,i). M(x)}"
  unfolding is_Vfrom_def
  using is_HVfrom_iff
    transrec_abs[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)"] trepl_HVfrom relation2_HVfrom
    transrec_HVfrom
  by simp

lemma Vfrom_closed: "\<lbrakk> M(A); M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vfrom(A,i). M(x)})"
  unfolding is_Vfrom_def
  using is_HVfrom_iff HVfrom_closed HVfrom_replacement
    transrec_closed[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)"] trepl_HVfrom relation2_HVfrom
    transrec_HVfrom
  by simp

end \<comment> \<open>\<^locale>\<open>M_Vfrom\<close>\<close>

subsection\<open>Formula synthesis\<close>

context M_Vfrom
begin

rel_closed for "Hrank"
  unfolding Hrank_rel_def
  using Hrank_replacement
  by simp

is_iff_rel for "Hrank"
proof -
  assume "M(f)" "M(x)" "M(res)"
  moreover from this
  have "{a . y \<in> x, M(a) \<and> M(y) \<and> a = succ(f ` y)} = {a . y \<in> x,  a = succ(f ` y)}"
    using transM[of _ x]
    by auto
  ultimately
  show ?thesis
    unfolding is_Hrank_def Hrank_rel_def
    using Replace_abs transM[of _ x] Hrank_replacement
    by auto
qed

lemma relation2_Hrank :
  "relation2(M,is_Hrank(M),Hrank)"
  unfolding  relation2_def
proof(clarify)
  fix x f res
  assume "M(x)" "M(f)" "M(res)"
  moreover from this
  have "{a . y \<in> x, M(a) \<and> M(y) \<and> a = succ(f ` y)} = {a . y \<in> x,  a = succ(f ` y)}"
    using transM[of _ x]
    by auto
  ultimately
  show "is_Hrank(M, x, f, res) \<longleftrightarrow> res = Hrank(x, f)"
    unfolding  Hrank_def relation2_def
    using is_Hrank_iff[unfolded Hrank_rel_def]
    by auto
qed

lemma Hrank_closed :
  "\<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(Hrank(x,g))"
proof(clarify)
  fix x g
  assume "M(x)" "M(g)"
  then
  show "M(Hrank(x,g))"
    using RepFun_closed[OF Hrank_replacement] transM[of _ x]
    unfolding Hrank_def
    by auto
qed

end \<comment>\<open>\<^locale>\<open>M_basic\<close>\<close>

context M_eclose
begin

lemma wf_rrank : "M(x) \<Longrightarrow> wf(rrank(x))"
  unfolding rrank_def using wf_trancl[OF wf_Memrel] .

lemma trans_rrank : "M(x) \<Longrightarrow> trans(rrank(x))"
  unfolding rrank_def using trans_trancl .

lemma relation_rrank : "M(x) \<Longrightarrow> relation(rrank(x))"
  unfolding rrank_def using relation_trancl .

lemma rrank_in_M : "M(x) \<Longrightarrow> M(rrank(x))"
  unfolding rrank_def by simp

end \<comment> \<open>\<^locale>\<open>M_eclose\<close>\<close>

lemma Hrank_trancl:"Hrank(y, restrict(f,Memrel(eclose({x}))-``{y}))
                  = Hrank(y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  unfolding Hrank_def
  using restrict_trans_eq by simp

lemma rank_trancl: "rank(x) = wfrec(rrank(x), x, Hrank)"
proof -
  have "rank(x) =  wfrec(Memrel(eclose({x})), x, Hrank)"
    (is "_ = wfrec(?r,_,_)")
    unfolding rank_def transrec_def Hrank_def by simp
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. Hrank(y, restrict(f,?r-``{y})))"
    unfolding wfrec_def ..
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. Hrank(y, restrict(f,(?r^+)-``{y})))"
    using Hrank_trancl by simp
  also
  have " ... =  wfrec(?r^+, x, Hrank)"
    unfolding wfrec_def using trancl_eq_r[OF relation_trancl trans_trancl] by simp
  finally
  show ?thesis unfolding rrank_def .
qed

definition
  Vset' :: "[i] \<Rightarrow> i" where
  "Vset'(A) \<equiv> Vfrom(0,A)"

reldb_add relational "Vfrom" "is_Vfrom"
reldb_add functional "Vfrom" "Vfrom_rel"
relativize functional "Vset'" "Vset_rel"
relationalize "Vset_rel" "is_Vset"
reldb_rem relational "Vset"
reldb_rem functional "Vset_rel"
reldb_add relational "Vset" "is_Vset"
reldb_add functional "Vset" "Vset_rel"

schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env)) \<longleftrightarrow> sats(A,?ivs_fm(i,v),env)"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

synthesize "is_Vset" from_schematic "sats_is_Vset_fm_auto"
arity_theorem for "is_Vset_fm"
context M_Vfrom
begin

lemma Vset_abs: "\<lbrakk> M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vset(M,i,V) \<longleftrightarrow> V = {x\<in>Vset(i). M(x)}"
  using Vfrom_abs unfolding is_Vset_def by simp

lemma Vset_closed: "\<lbrakk> M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vset(i). M(x)})"
  using Vfrom_closed unfolding is_Vset_def by simp

lemma rank_closed: "M(a) \<Longrightarrow> M(rank(a))"
  unfolding rank_trancl
  using Hrank_closed is_Hrank_replacement relation2_Hrank
    wf_rrank relation_rrank trans_rrank rrank_in_M
    trans_wfrec_closed[of "rrank(a)" a "is_Hrank(M)"]
    transM[of _ a]
  by auto

lemma M_into_Vset:
  assumes "M(a)"
  shows "\<exists>i[M]. \<exists>V[M]. ordinal(M,i) \<and> is_Vset(M,i,V) \<and> a\<in>V"
proof -
  let ?i="succ(rank(a))"
  from assms
  have "a\<in>{x\<in>Vfrom(0,?i). M(x)}" (is "a\<in>?V")
    using Vset_Ord_rank_iff by simp
  moreover from assms
  have "M(?i)"
    using rank_closed by simp
  moreover
  note \<open>M(a)\<close>
  moreover from calculation
  have "M(?V)"
    using Vfrom_closed by simp
  moreover from calculation
  have "ordinal(M,?i) \<and> is_Vfrom(M, 0, ?i, ?V) \<and> a \<in> ?V"
    using Ord_rank Vfrom_abs by simp
  ultimately
  show ?thesis
    using nonempty empty_abs
    unfolding is_Vset_def
    by blast
qed

end \<comment> \<open>\<^locale>\<open>M_HVfrom\<close>\<close>

end