section\<open>Names and generic extensions\<close>

theory Names
  imports
    Forcing_Data
    FrecR_Arities
    ZF_Trans_Interpretations
begin

definition
  Hv :: "[i,i,i]\<Rightarrow>i" where
  "Hv(G,x,f) \<equiv> { z . y\<in> domain(x), (\<exists>p\<in>G. \<langle>y,p\<rangle> \<in> x) \<and> z=f`y}"

text\<open>The funcion \<^term>\<open>val\<close> interprets a name in \<^term>\<open>M\<close>
according to a (generic) filter \<^term>\<open>G\<close>. Note the definition
in terms of the well-founded recursor.\<close>

definition
  val :: "[i,i]\<Rightarrow>i" where
  "val(G,\<tau>) \<equiv> wfrec(edrel(eclose({\<tau>})), \<tau> ,Hv(G))"

definition
  GenExt :: "[i,i]\<Rightarrow>i"     ("_[_]" [71,1])
  where "M[G] \<equiv> {val(G,\<tau>). \<tau> \<in> M}"

lemma map_val_in_MG:
  assumes
    "env\<in>list(M)"
  shows
    "map(val(G),env)\<in>list(M[G])"
  unfolding GenExt_def using assms map_type2 by simp

subsection\<open>Values and check-names\<close>
context forcing_data1
begin

lemma name_components_in_M:
  assumes "\<langle>\<sigma>,p\<rangle>\<in>\<theta>" "\<theta> \<in> M"
  shows   "\<sigma>\<in>M" "p\<in>M"
  using assms transitivity pair_in_M_iff
  by auto

definition
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  \<equiv> { \<langle>f`y,\<one>\<rangle> . y \<in> z}"

definition
  check :: "i \<Rightarrow> i" where
  "check(x) \<equiv> transrec(x , Hcheck)"

lemma checkD:
  "check(x) =  wfrec(Memrel(eclose({x})), x, Hcheck)"
  unfolding check_def transrec_def ..

lemma Hcheck_trancl:"Hcheck(y, restrict(f,Memrel(eclose({x}))-``{y}))
                   = Hcheck(y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  unfolding Hcheck_def
  using restrict_trans_eq by simp

lemma check_trancl: "check(x) = wfrec(rcheck(x), x, Hcheck)"
  using checkD wf_eq_trancl Hcheck_trancl unfolding rcheck_def by simp

lemma rcheck_in_M : "x \<in> M \<Longrightarrow> rcheck(x) \<in> M"
  unfolding rcheck_def by (simp flip: setclass_iff)

lemma rcheck_subset_M : "x \<in> M \<Longrightarrow> field(rcheck(x)) \<subseteq> eclose({x})"
  unfolding rcheck_def using field_Memrel field_trancl by auto

lemma  aux_def_check: "x \<in> y \<Longrightarrow>
  wfrec(Memrel(eclose({y})), x, Hcheck) =
  wfrec(Memrel(eclose({x})), x, Hcheck)"
  by (rule wfrec_eclose_eq,auto simp add: arg_into_eclose eclose_sing)

lemma def_check : "check(y) = { \<langle>check(w),\<one>\<rangle> . w \<in> y}"
proof -
  let
    ?r="\<lambda>y. Memrel(eclose({y}))"
  have wfr:   "\<forall>w . wf(?r(w))"
    using wf_Memrel ..
  then
  have "check(y)= Hcheck( y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck))"
    using wfrec[of "?r(y)" y "Hcheck"] checkD by simp
  also
  have " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    using under_Memrel_eclose arg_into_eclose by simp
  also
  have " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check checkD by simp
  finally
  show ?thesis
    using Hcheck_def by simp
qed

lemma def_checkS :
  fixes n
  assumes "n \<in> nat"
  shows "check(succ(n)) = check(n) \<union> {\<langle>check(n),\<one>\<rangle>}"
proof -
  have "check(succ(n)) = {\<langle>check(i),\<one>\<rangle> . i \<in> succ(n)} "
    using def_check by blast
  also
  have "... = {\<langle>check(i),\<one>\<rangle> . i \<in> n} \<union> {\<langle>check(n),\<one>\<rangle>}"
    by blast
  also
  have "... = check(n) \<union> {\<langle>check(n),\<one>\<rangle>}"
    using def_check[of n,symmetric] by simp
  finally
  show ?thesis .
qed

lemma field_Memrel2 :
  assumes "x \<in> M"
  shows "field(Memrel(eclose({x}))) \<subseteq> M"
proof -
  have "field(Memrel(eclose({x}))) \<subseteq> eclose({x})" "eclose({x}) \<subseteq> M"
    using Ordinal.Memrel_type field_rel_subset assms eclose_least[OF trans_M] by auto
  then
  show ?thesis
    using subset_trans by simp
qed

lemma aux_def_val:
  assumes "z \<in> domain(x)"
  shows "wfrec(edrel(eclose({x})),z,Hv(G)) = wfrec(edrel(eclose({z})),z,Hv(G))"
proof -
  let ?r="\<lambda>x . edrel(eclose({x}))"
  have "z\<in>eclose({z})"
    using arg_in_eclose_sing .
  moreover
  have "relation(?r(x))"
    using relation_edrel .
  moreover
  have "wf(?r(x))"
    using wf_edrel .
  moreover from assms
  have "tr_down(?r(x),z) \<subseteq> eclose({z})"
    using tr_edrel_subset by simp
  ultimately
  have "wfrec(?r(x),z,Hv(G)) = wfrec[eclose({z})](?r(x),z,Hv(G))"
    using wfrec_restr by simp
  also from \<open>z\<in>domain(x)\<close>
  have "... = wfrec(?r(z),z,Hv(G))"
    using restrict_edrel_eq wfrec_restr_eq by simp
  finally
  show ?thesis .
qed

text\<open>The next lemma provides the usual recursive expresion for the definition of \<^term>\<open>val\<close>.\<close>

lemma def_val:  "val(G,x) = {z . t\<in>domain(x) , (\<exists>p\<in>G .  \<langle>t,p\<rangle>\<in>x) \<and> z=val(G,t)}"
proof -
  let
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(x)-``{x}. wfrec(?r(x),z,Hv(G))"
  have "\<forall>\<tau>. wf(?r(\<tau>))"
    using wf_edrel by simp
  with wfrec [of _ x]
  have "val(G,x) = Hv(G,x,?f)"
    using val_def by simp
  also
  have " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r(x),z,Hv(G)))"
    using dom_under_edrel_eclose by simp
  also
  have " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    using aux_def_val val_def by simp
  finally
  show ?thesis
    using Hv_def by simp
qed

lemma val_mono : "x\<subseteq>y \<Longrightarrow> val(G,x) \<subseteq> val(G,y)"
  by (subst (1 2) def_val, force)

text\<open>Check-names are the canonical names for elements of the
ground model. Here we show that this is the case.\<close>

lemma val_check : "\<one> \<in> G \<Longrightarrow>  \<one> \<in> \<bbbP> \<Longrightarrow> val(G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -
    have "check(y) = { \<langle>check(w), \<one>\<rangle> . w \<in> y}"  (is "_ = ?C")
      using def_check .
    then
    have "val(G,check(y)) = val(G, {\<langle>check(w), \<one>\<rangle> . w \<in> y})"
      by simp
    also
    have " ...  = {z . t\<in>domain(?C) , (\<exists>p\<in>G .  \<langle>t, p\<rangle>\<in>?C ) \<and> z=val(G,t) }"
      using def_val by blast
    also
    have " ... =  {z . t\<in>domain(?C) , (\<exists>w\<in>y. t=check(w)) \<and> z=val(G,t) }"
      using 1 by simp
    also
    have " ... = {val(G,check(w)) . w\<in>y }"
      by force
    finally
    show "val(G,check(y)) = y"
      using 1 by simp
  qed
qed

lemma val_of_name :
  "val(G,{x\<in>A\<times>\<bbbP>. Q(x)}) = {z . t\<in>A , (\<exists>p\<in>\<bbbP> .  Q(\<langle>t,p\<rangle>) \<and> p \<in> G) \<and> z=val(G,t)}"
proof -
  let
    ?n="{x\<in>A\<times>\<bbbP>. Q(x)}" and
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(?n)-``{?n}. val(G,z)"
  have
    wfR : "wf(?r(\<tau>))" for \<tau>
    by (simp add: wf_edrel)
  have "domain(?n) \<subseteq> A" by auto
  { fix t
    assume H:"t \<in> domain({x \<in> A \<times> \<bbbP> . Q(x)})"
    then have "?f ` t = (if t \<in> ?r(?n)-``{?n} then val(G,t) else 0)"
      by simp
    moreover have "... = val(G,t)"
      using dom_under_edrel_eclose H if_P by auto
  }
  then
  have Eq1: "t \<in> domain({x \<in> A \<times> \<bbbP> . Q(x)}) \<Longrightarrow> val(G,t) = ?f` t"  for t
    by simp
  have "val(G,?n) = {z . t\<in>domain(?n), (\<exists>p \<in> G . \<langle>t,p\<rangle> \<in> ?n) \<and> z=val(G,t)}"
    by (subst def_val,simp)
  also
  have "... = {z . t\<in>domain(?n), (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=?f`t}"
    unfolding Hv_def
    by (auto simp add:Eq1)
  also
  have "... = {z . t\<in>domain(?n), (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=(if t\<in>?r(?n)-``{?n} then val(G,t) else 0)}"
    by (simp)
  also
  have "... = { z . t\<in>domain(?n), (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(G,t)}"
  proof -
    have "domain(?n) \<subseteq> ?r(?n)-``{?n}"
      using dom_under_edrel_eclose by simp
    then
    have "\<forall>t\<in>domain(?n). (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then
    show "{ z . t\<in>domain(?n), (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=(if t\<in>?r(?n)-``{?n} then val(G,t) else 0)} =
          { z . t\<in>domain(?n), (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(G,t)}"
      by auto
  qed
  also
  have " ... = { z . t\<in>A, (\<exists>p\<in>\<bbbP> . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(G,t)}"
    by force
  finally
  show " val(G,?n)  = { z . t\<in>A, (\<exists>p\<in>\<bbbP> . Q(\<langle>t,p\<rangle>) \<and> p\<in>G) \<and> z=val(G,t)}"
    by auto
qed

lemma val_of_name_alt :
  "val(G,{x\<in>A\<times>\<bbbP>. Q(x)}) = {z . t\<in>A , (\<exists>p\<in>\<bbbP>\<inter>G .  Q(\<langle>t,p\<rangle>)) \<and> z=val(G,t) }"
  using val_of_name by force

lemma val_only_names: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>F. x=\<langle>t,p\<rangle>})"
  (is "_ = val(F,?name)")
proof -
  have "val(F,?name) = {z . t\<in>domain(?name), (\<exists>p\<in>F. \<langle>t, p\<rangle> \<in> ?name) \<and> z=val(F, t)}"
    using def_val by blast
  also
  have " ... = {val(F, t). t\<in>{y\<in>domain(\<tau>). \<exists>p\<in>F. \<langle>y, p\<rangle> \<in> \<tau> }}"
    by blast
  also
  have " ... = {z . t\<in>domain(\<tau>), (\<exists>p\<in>F. \<langle>t, p\<rangle> \<in> \<tau>) \<and> z=val(F, t)}"
    by blast
  also
  have " ... = val(F, \<tau>)"
    using def_val[symmetric] by blast
  finally
  show ?thesis ..
qed

lemma val_only_pairs: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
proof
  have "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>F. x=\<langle>t,p\<rangle>})" (is "_ = val(F,?name)")
    using val_only_names .
  also
  have "... \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
    using val_mono[of ?name "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
  finally
  show "val(F,\<tau>) \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})" by simp
next
  show "val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}) \<subseteq> val(F,\<tau>)"
    using val_mono[of "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
qed

lemma val_subset_domain_times_range: "val(F,\<tau>) \<subseteq> val(F,domain(\<tau>)\<times>range(\<tau>))"
  using val_only_pairs[THEN equalityD1]
    val_mono[of "{x \<in> \<tau> . \<exists>t p. x = \<langle>t, p\<rangle>}" "domain(\<tau>)\<times>range(\<tau>)"] by blast

lemma val_of_elem: "\<langle>\<theta>,p\<rangle> \<in> \<pi> \<Longrightarrow> p\<in>G \<Longrightarrow> val(G,\<theta>) \<in> val(G,\<pi>)"
proof -
  assume "\<langle>\<theta>,p\<rangle> \<in> \<pi>"
  then
  have "\<theta>\<in>domain(\<pi>)"
    by auto
  assume "p\<in>G"
  with \<open>\<theta>\<in>domain(\<pi>)\<close> \<open>\<langle>\<theta>,p\<rangle> \<in> \<pi>\<close>
  have "val(G,\<theta>) \<in> {z . t\<in>domain(\<pi>) , (\<exists>p\<in>G .  \<langle>t, p\<rangle>\<in>\<pi>) \<and> z=val(G,t) }"
    by auto
  then
  show ?thesis
    by (subst def_val)
qed

lemma elem_of_val: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair':
  assumes "\<pi>\<in>M" "x\<in>val(G,\<pi>)"
  shows "\<exists>\<theta>\<in>M. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x"
proof -
  from assms
  obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle>\<in>\<pi>" "val(G,\<theta>) = x"
    using elem_of_val_pair by blast
  moreover from this \<open>\<pi>\<in>M\<close>
  have "\<theta>\<in>M"
    using pair_in_M_iff[THEN iffD1, THEN conjunct1, simplified]
      transitivity by blast
  ultimately
  show ?thesis
    by blast
qed

lemma GenExtD: "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  by (simp add:GenExt_def)

lemma GenExtI: "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)

lemma Transset_MG : "Transset(M[G])"
proof -
  { fix vc y
    assume "vc \<in> M[G]" and "y \<in> vc"
    then
    obtain c where "c\<in>M" "val(G,c)\<in>M[G]" "y \<in> val(G,c)"
      using GenExtD by auto
    from \<open>y \<in> val(G,c)\<close>
    obtain \<theta> where "\<theta>\<in>domain(c)" "val(G,\<theta>) = y"
      using elem_of_val by blast
    with trans_M \<open>c\<in>M\<close>
    have "y \<in> M[G]"
      using domain_trans GenExtI by blast
  }
  then
  show ?thesis
    using Transset_def by auto
qed

lemmas transitivity_MG = Transset_intf[OF Transset_MG]

text\<open>This lemma can be proved before having \<^term>\<open>check_in_M\<close>. At some point Miguel naïvely
thought that the \<^term>\<open>check_in_M\<close> could be proved using this argument.\<close>
lemma check_nat_M :
  assumes "n \<in> nat"
  shows "check(n) \<in> M"
  using assms
proof (induct n)
  case 0
  then
  show ?case
    using zero_in_M by (subst def_check,simp)
next
  case (succ x)
  have "\<one> \<in> M"
    using one_in_P P_sub_M subsetD by simp
  with \<open>check(x)\<in>M\<close>
  have "\<langle>check(x),\<one>\<rangle> \<in> M"
    using pair_in_M_iff by simp
  then
  have "{\<langle>check(x),\<one>\<rangle>} \<in> M"
    using singleton_closed by simp
  with \<open>check(x)\<in>M\<close>
  have "check(x) \<union> {\<langle>check(x),\<one>\<rangle>} \<in> M"
    using Un_closed by simp
  then
  show ?case
    using \<open>x\<in>nat\<close> def_checkS by simp
qed

lemma def_PHcheck:
  assumes
    "z\<in>M" "f\<in>M"
  shows
    "Hcheck(z,f) = Replace(z,PHcheck(##M,\<one>,f))"
proof -
  from assms
  have "\<langle>f`x,\<one>\<rangle> \<in> M" "f`x\<in>M" if "x\<in>z" for x
    using pair_in_M_iff transitivity that apply_closed by simp_all
  then
  have "{y . x \<in> z, y = \<langle>f ` x, \<one>\<rangle>} =  {y . x \<in> z, y = \<langle>f ` x, \<one>\<rangle> \<and> y\<in>M \<and> f`x\<in>M}"
    by simp
  then
  show ?thesis
    using \<open>z\<in>M\<close> \<open>f\<in>M\<close> transitivity
    unfolding Hcheck_def PHcheck_def RepFun_def
    by auto
qed

(* instance of replacement for hcheck *)
lemma wfrec_Hcheck :
  assumes "X\<in>M"
  shows "wfrec_replacement(##M,is_Hcheck(##M,\<one>),rcheck(X))"
proof -
  let ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0)))"
  have "is_Hcheck(##M,\<one>,a,b,c) \<longleftrightarrow>
        sats(M,is_Hcheck_fm(8,2,1,0),[c,b,a,d,e,y,x,z,\<one>,rcheck(x)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
    for a b c d e y x z
    using that \<open>X\<in>M\<close> rcheck_in_M is_Hcheck_iff_sats zero_in_M
    by simp
  then
  have "sats(M,is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0), [y,x,z,\<one>,rcheck(X)])
        \<longleftrightarrow> is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using that sats_is_wfrec_fm \<open>X\<in>M\<close> rcheck_in_M zero_in_M
    by simp
  moreover from this
  have satsf:"sats(M, ?f, [x,z,\<one>,rcheck(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that \<open>X\<in>M\<close> rcheck_in_M
    by (simp del:pair_abs)
  moreover
  have artyf:"arity(?f) = 4"
    using arity_wfrec_replacement_fm[where p="is_Hcheck_fm(8, 2, 1, 0)" and i=9]
      arity_is_Hcheck_fm ord_simp_union
    by simp
  ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,\<one>,rcheck(X)]))"
    using ZF_ground_replacements(2) artyf \<open>X\<in>M\<close> rcheck_in_M
    unfolding replacement_assm_def wfrec_Hcheck_fm_def by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y))"
    using repl_sats[of M ?f "[\<one>,rcheck(X)]"] satsf by (simp del:pair_abs)
  then
  show ?thesis
    unfolding wfrec_replacement_def by simp
qed

lemma Hcheck_closed' : "f\<in>M \<Longrightarrow> z\<in>M \<Longrightarrow> {f ` x . x \<in> z} \<in> M"
  using RepFun_closed[OF lam_replacement_imp_strong_replacement]
          lam_replacement_apply apply_closed transM[of _ z]
  by simp

lemma repl_PHcheck :
  assumes "f\<in>M"
  shows "lam_replacement(##M,\<lambda>x. Hcheck(x,f))"
proof -
  have "Hcheck(x,f) = {f`y . y\<in>x}\<times>{\<one>}" for x
    unfolding Hcheck_def by auto
  moreover
  note assms
  moreover from this
  have 1:"lam_replacement(##M, \<lambda>x . {f`y . y\<in>x}\<times>{\<one>})"
    using lam_replacement_RepFun_apply
      lam_replacement_constant lam_replacement_fst lam_replacement_snd
      singleton_closed cartprod_closed fst_snd_closed Hcheck_closed'
    by (rule_tac lam_replacement_CartProd[THEN [5] lam_replacement_hcomp2],simp_all)
  ultimately
  show ?thesis
    using singleton_closed cartprod_closed Hcheck_closed'
    by(rule_tac lam_replacement_cong[OF 1],auto)
qed

lemma univ_PHcheck : "\<lbrakk> z\<in>M ; f\<in>M \<rbrakk> \<Longrightarrow> univalent(##M,z,PHcheck(##M,\<one>,f))"
  unfolding univalent_def PHcheck_def
  by simp

lemma PHcheck_closed : "\<lbrakk>z\<in>M ; f\<in>M ; x\<in>z; PHcheck(##M,\<one>,f,x,y) \<rbrakk> \<Longrightarrow> (##M)(y)"
  unfolding PHcheck_def by simp

lemma relation2_Hcheck : "relation2(##M,is_Hcheck(##M,\<one>),Hcheck)"
proof -
  have "is_Replace(##M,z,PHcheck(##M,\<one>,f),hc) \<longleftrightarrow> hc = Replace(z,PHcheck(##M,\<one>,f))"
    if "z\<in>M" "f\<in>M" "hc\<in>M" for z f hc
    using that Replace_abs[OF _ _ univ_PHcheck] PHcheck_closed[of z f]
    by simp
  with def_PHcheck
  show ?thesis
    unfolding relation2_def is_Hcheck_def Hcheck_def
    by simp
qed

lemma Hcheck_closed : "\<forall>y\<in>M. \<forall>g\<in>M.  Hcheck(y,g)\<in>M"
proof -
  have eq:"Hcheck(x,f) = {f`y . y\<in>x}\<times>{\<one>}" for f x
    unfolding Hcheck_def by auto
  then
  have "Hcheck(y,g)\<in>M" if "y\<in>M" "g\<in>M" for y g
    using eq that Hcheck_closed' cartprod_closed singleton_closed
    by simp
  then
  show ?thesis
    by auto
qed

lemma wf_rcheck : "x\<in>M \<Longrightarrow> wf(rcheck(x))"
  unfolding rcheck_def using wf_trancl[OF wf_Memrel] .

lemma trans_rcheck : "x\<in>M \<Longrightarrow> trans(rcheck(x))"
  unfolding rcheck_def using trans_trancl .

lemma relation_rcheck : "x\<in>M \<Longrightarrow> relation(rcheck(x))"
  unfolding rcheck_def using relation_trancl .

lemma check_in_M : "x\<in>M \<Longrightarrow> check(x) \<in> M"
  using wfrec_Hcheck[of x] check_trancl wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
    Hcheck_closed relation2_Hcheck trans_wfrec_closed[of "rcheck(x)"]
  by simp

(* Internalization and absoluteness of rcheck\<close> *)
lemma rcheck_abs[Rel] : "\<lbrakk> x\<in>M ; r\<in>M \<rbrakk> \<Longrightarrow> is_rcheck(##M,x,r) \<longleftrightarrow> r = rcheck(x)"
  unfolding rcheck_def is_rcheck_def
  using singleton_closed trancl_closed Memrel_closed eclose_closed zero_in_M
  by simp

lemma check_abs[Rel] :
  assumes "x\<in>M" "z\<in>M"
  shows "is_check(##M,\<one>,x,z) \<longleftrightarrow> z = check(x)"
proof -
  have "is_check(##M,\<one>,x,z) \<longleftrightarrow> is_wfrec(##M,is_Hcheck(##M,\<one>),rcheck(x),x,z)"
    unfolding is_check_def
    using assms rcheck_abs rcheck_in_M zero_in_M
    unfolding check_trancl is_check_def
    by simp
  then
  show ?thesis
    unfolding check_trancl
    using assms wfrec_Hcheck[of x] wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
      Hcheck_closed relation2_Hcheck trans_wfrec_abs[of "rcheck(x)" x z "is_Hcheck(##M,\<one>)" Hcheck]
    by (simp flip: setclass_iff)
qed

lemma check_lam_replacement: "lam_replacement(##M,check)"
proof -
  have "arity(check_fm(2,0,1)) = 3"
    by (simp add:ord_simp_union arity)
  then
  have "Lambda(A, check) \<in> M" if "A\<in>M" for A
    using that check_in_M transitivity[of _ A]
      sats_check_fm check_abs zero_in_M
      check_fm_type ZF_ground_replacements(3)
    by(rule_tac Lambda_in_M [of "check_fm(2,0,1)" "[\<one>]"],simp_all)
  then
  show ?thesis
    using check_in_M lam_replacement_iff_lam_closed[THEN iffD2]
    by simp
qed

lemma check_replacement: "{check(x). x\<in>\<bbbP>} \<in> M"
  using lam_replacement_imp_strong_replacement_aux[OF check_lam_replacement]
    transitivity check_in_M RepFun_closed
    by simp_all

lemma M_subset_MG : "\<one> \<in> G \<Longrightarrow> M \<subseteq> M[G]"
  using check_in_M GenExtI
  by (intro subsetI, subst val_check [of G,symmetric], auto)

text\<open>The name for the generic filter\<close>
definition
  G_dot :: "i" where
  "G_dot \<equiv> {\<langle>check(p),p\<rangle> . p\<in>\<bbbP>}"

lemma G_dot_in_M : "G_dot \<in> M"
  using lam_replacement_Pair[THEN [5] lam_replacement_hcomp2,OF
    check_lam_replacement lam_replacement_identity]
    check_in_M lam_replacement_imp_strong_replacement_aux
    transitivity check_in_M RepFun_closed pair_in_M_iff
  unfolding G_dot_def
  by simp

lemma zero_in_MG : "0 \<in> M[G]"
proof -
  have "0 = val(G,0)"
    using zero_in_M elem_of_val by auto
  also
  have "... \<in> M[G]"
    using GenExtI zero_in_M by simp
  finally
  show ?thesis .
qed

declare check_in_M [simp,intro]

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

context G_generic1
begin

lemma val_G_dot : "val(G,G_dot) = G"
proof (intro equalityI subsetI)
  fix x
  assume "x\<in>val(G,G_dot)"
  then obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle> \<in> G_dot" "val(G,\<theta>) = x" "\<theta> = check(p)"
    unfolding G_dot_def using elem_of_val_pair G_dot_in_M
    by force
  then
  show "x \<in> G"
    using G_subset_P one_in_G val_check P_sub_M by auto
next
  fix p
  assume "p\<in>G"
  have "\<langle>check(q),q\<rangle> \<in> G_dot" if "q\<in>\<bbbP>" for q
    unfolding G_dot_def using that by simp
  with \<open>p\<in>G\<close>
  have "val(G,check(p)) \<in> val(G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close>
  show "p \<in> val(G,G_dot)"
    using one_in_G G_subset_P P_sub_M val_check by auto
qed

lemma G_in_Gen_Ext : "G \<in> M[G]"
  using G_subset_P one_in_G val_G_dot GenExtI[of _ G] G_dot_in_M
  by force

lemmas generic_simps = val_check[OF one_in_G one_in_P]
  M_subset_MG[OF one_in_G, THEN subsetD]
  GenExtI P_in_M

lemmas generic_dests = M_genericD M_generic_compatD

bundle G_generic1_lemmas = generic_simps[simp] generic_dests[dest]

end  \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

sublocale G_generic1 \<subseteq> ext: M_trans "##M[G]"
  using generic transitivity_MG zero_in_MG
  by unfold_locales force+

end