section\<open>Names and generic extensions\<close>

theory Names
  imports
    Forcing_Data
    FrecR_Arities
begin

definition
  Hv :: "[i,i,i,i]\<Rightarrow>i" where
  "Hv(P,G,x,f) \<equiv> { z . y\<in> domain(x), (\<exists>p\<in>P. \<langle>y,p\<rangle> \<in> x \<and> p \<in> G) \<and> z=f`y}"

text\<open>The funcion \<^term>\<open>val\<close> interprets a name in \<^term>\<open>M\<close>
according to a (generic) filter \<^term>\<open>G\<close>. Note the definition
in terms of the well-founded recursor.\<close>

definition
  val :: "[i,i,i]\<Rightarrow>i" where
  "val(P,G,\<tau>) \<equiv> wfrec(edrel(eclose({\<tau>})), \<tau> ,Hv(P,G))"

definition
  GenExt :: "[i,i,i]\<Rightarrow>i"     ("_\<^bsup>_\<^esup>[_]" [71,1])
  where "M\<^bsup>P\<^esup>[G] \<equiv> {val(P,G,\<tau>). \<tau> \<in> M}"

abbreviation (in forcing_notion)
  GenExt_at_P :: "i\<Rightarrow>i\<Rightarrow>i"     ("_[_]" [71,1])
  where "M[G] \<equiv> M\<^bsup>P\<^esup>[G]"

subsection\<open>Values and check-names\<close>
context forcing_data1
begin

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
  shows "wfrec(edrel(eclose({x})),z,Hv(P,G)) = wfrec(edrel(eclose({z})),z,Hv(P,G))"
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
  have "wfrec(?r(x),z,Hv(P,G)) = wfrec[eclose({z})](?r(x),z,Hv(P,G))"
    using wfrec_restr by simp
  also from \<open>z\<in>domain(x)\<close>
  have "... = wfrec(?r(z),z,Hv(P,G))"
    using restrict_edrel_eq wfrec_restr_eq by simp
  finally
  show ?thesis .
qed

text\<open>The next lemma provides the usual recursive expresion for the definition of term\<open>val\<close>.\<close>

lemma def_val:  "val(P,G,x) = {z . t\<in>domain(x) , (\<exists>p\<in>P .  \<langle>t,p\<rangle>\<in>x \<and> p \<in> G) \<and> z=val(P,G,t)}"
proof -
  let
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(x)-``{x}. wfrec(?r(x),z,Hv(P,G))"
  have "\<forall>\<tau>. wf(?r(\<tau>))"
    using wf_edrel by simp
  with wfrec [of _ x]
  have "val(P,G,x) = Hv(P,G,x,?f)"
    using val_def by simp
  also
  have " ... = Hv(P,G,x,\<lambda>z\<in>domain(x). wfrec(?r(x),z,Hv(P,G)))"
    using dom_under_edrel_eclose by simp
  also
  have " ... = Hv(P,G,x,\<lambda>z\<in>domain(x). val(P,G,z))"
    using aux_def_val val_def by simp
  finally
  show ?thesis
    using Hv_def by simp
qed

lemma val_mono : "x\<subseteq>y \<Longrightarrow> val(P,G,x) \<subseteq> val(P,G,y)"
  by (subst (1 2) def_val, force)

text\<open>Check-names are the canonical names for elements of the
ground model. Here we show that this is the case.\<close>

lemma valcheck : "\<one> \<in> G \<Longrightarrow>  \<one> \<in> P \<Longrightarrow> val(P,G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -
    have "check(y) = { \<langle>check(w), \<one>\<rangle> . w \<in> y}"  (is "_ = ?C")
      using def_check .
    then
    have "val(P,G,check(y)) = val(P,G, {\<langle>check(w), \<one>\<rangle> . w \<in> y})"
      by simp
    also
    have " ...  = {z . t\<in>domain(?C) , (\<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>?C \<and> p \<in> G) \<and> z=val(P,G,t) }"
      using def_val by blast
    also
    have " ... =  {z . t\<in>domain(?C) , (\<exists>w\<in>y. t=check(w)) \<and> z=val(P,G,t) }"
      using 1 by simp
    also
    have " ... = {val(P,G,check(w)) . w\<in>y }"
      by force
    finally
    show "val(P,G,check(y)) = y"
      using 1 by simp
  qed
qed

lemma val_of_name :
  "val(P,G,{x\<in>A\<times>P. Q(x)}) = {z . t\<in>A , (\<exists>p\<in>P .  Q(\<langle>t,p\<rangle>) \<and> p \<in> G) \<and> z=val(P,G,t)}"
proof -
  let
    ?n="{x\<in>A\<times>P. Q(x)}" and
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(?n)-``{?n}. val(P,G,z)"
  have
    wfR : "wf(?r(\<tau>))" for \<tau>
    by (simp add: wf_edrel)
  have "domain(?n) \<subseteq> A" by auto
  { fix t
    assume H:"t \<in> domain({x \<in> A \<times> P . Q(x)})"
    then have "?f ` t = (if t \<in> ?r(?n)-``{?n} then val(P,G,t) else 0)"
      by simp
    moreover have "... = val(P,G,t)"
      using dom_under_edrel_eclose H if_P by auto
  }
  then
  have Eq1: "t \<in> domain({x \<in> A \<times> P . Q(x)}) \<Longrightarrow> val(P,G,t) = ?f` t"  for t
    by simp
  have "val(P,G,?n) = {z . t\<in>domain(?n), (\<exists>p \<in> P . \<langle>t,p\<rangle> \<in> ?n \<and> p \<in> G) \<and> z=val(P,G,t)}"
    by (subst def_val,simp)
  also
  have "... = {z . t\<in>domain(?n), (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=?f`t}"
    unfolding Hv_def
    by (auto simp add:Eq1)
  also
  have "... = {z . t\<in>domain(?n), (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=(if t\<in>?r(?n)-``{?n} then val(P,G,t) else 0)}"
    by (simp)
  also
  have "... = { z . t\<in>domain(?n), (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(P,G,t)}"
  proof -
    have "domain(?n) \<subseteq> ?r(?n)-``{?n}"
      using dom_under_edrel_eclose by simp
    then
    have "\<forall>t\<in>domain(?n). (if t\<in>?r(?n)-``{?n} then val(P,G,t) else 0) = val(P,G,t)"
      by auto
    then
    show "{ z . t\<in>domain(?n), (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=(if t\<in>?r(?n)-``{?n} then val(P,G,t) else 0)} =
          { z . t\<in>domain(?n), (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(P,G,t)}"
      by auto
  qed
  also
  have " ... = { z . t\<in>A, (\<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G) \<and> z=val(P,G,t)}"
    by force
  finally
  show " val(P,G,?n)  = { z . t\<in>A, (\<exists>p\<in>P . Q(\<langle>t,p\<rangle>) \<and> p\<in>G) \<and> z=val(P,G,t)}"
    by auto
qed

lemma val_of_name_alt :
  "val(P,G,{x\<in>A\<times>P. Q(x)}) = {z . t\<in>A , (\<exists>p\<in>P\<inter>G .  Q(\<langle>t,p\<rangle>)) \<and> z=val(P,G,t) }"
  using val_of_name by force

lemma val_only_names: "val(P,F,\<tau>) = val(P,F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>})"
  (is "_ = val(P,F,?name)")
proof -
  have "val(P,F,?name) = {z . t\<in>domain(?name), (\<exists>p\<in>P. \<langle>t, p\<rangle> \<in> ?name \<and> p \<in> F) \<and> z=val(P,F, t)}"
    using def_val by blast
  also
  have " ... = {val(P,F, t). t\<in>{y\<in>domain(\<tau>). \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> \<tau> \<and> p \<in> F}}"
    by blast
  also
  have " ... = {z . t\<in>domain(\<tau>), (\<exists>p\<in>P. \<langle>t, p\<rangle> \<in> \<tau> \<and> p \<in> F) \<and> z=val(P,F, t)}"
    by blast
  also
  have " ... = val(P,F, \<tau>)"
    using def_val[symmetric] by blast
  finally
  show ?thesis ..
qed

lemma val_only_pairs: "val(P,F,\<tau>) = val(P,F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
proof
  have "val(P,F,\<tau>) = val(P,F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>})" (is "_ = val(P,F,?name)")
    using val_only_names .
  also
  have "... \<subseteq> val(P,F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
    using val_mono[of ?name "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
  finally
  show "val(P,F,\<tau>) \<subseteq> val(P,F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})" by simp
next
  show "val(P,F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}) \<subseteq> val(P,F,\<tau>)"
    using val_mono[of "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
qed

lemma val_subset_domain_times_range: "val(P,F,\<tau>) \<subseteq> val(P,F,domain(\<tau>)\<times>range(\<tau>))"
  using val_only_pairs[THEN equalityD1]
    val_mono[of "{x \<in> \<tau> . \<exists>t p. x = \<langle>t, p\<rangle>}" "domain(\<tau>)\<times>range(\<tau>)"] by blast

lemma val_subset_domain_times_P: "val(P,F,\<tau>) \<subseteq> val(P,F,domain(\<tau>)\<times>P)"
  using val_only_names[of F \<tau>] val_mono[of "{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>}" "domain(\<tau>)\<times>P" F]
  by auto

lemma val_of_elem: "\<langle>\<theta>,p\<rangle> \<in> \<pi> \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> val(P,G,\<theta>) \<in> val(P,G,\<pi>)"
proof -
  assume "\<langle>\<theta>,p\<rangle> \<in> \<pi>"
  then
  have "\<theta>\<in>domain(\<pi>)"
    by auto
  assume "p\<in>G" "p\<in>P"
  with \<open>\<theta>\<in>domain(\<pi>)\<close> \<open>\<langle>\<theta>,p\<rangle> \<in> \<pi>\<close>
  have "val(P,G,\<theta>) \<in> {z . t\<in>domain(\<pi>) , (\<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G) \<and> z=val(P,G,t) }"
    by auto
  then
  show ?thesis
    by (subst def_val)
qed

lemma elem_of_val: "x\<in>val(P,G,\<pi>) \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(P,G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair: "x\<in>val(P,G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(P,G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair':
  assumes "\<pi>\<in>M" "x\<in>val(P,G,\<pi>)"
  shows "\<exists>\<theta>\<in>M. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(P,G,\<theta>) = x"
proof -
  from assms
  obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle>\<in>\<pi>" "val(P,G,\<theta>) = x"
    using elem_of_val_pair by blast
  moreover from this \<open>\<pi>\<in>M\<close>
  have "\<theta>\<in>M"
    using pair_in_M_iff[THEN iffD1, THEN conjunct1, simplified]
      transitivity by blast
  ultimately
  show ?thesis
    by blast
qed


lemma GenExtD: "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(P,G,\<tau>)"
  by (simp add:GenExt_def)

lemma GenExtI: "x \<in> M \<Longrightarrow> val(P,G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)

lemma Transset_MG : "Transset(M[G])"
proof -
  { fix vc y
    assume "vc \<in> M[G]" and "y \<in> vc"
    then
    obtain c where "c\<in>M" "val(P,G,c)\<in>M[G]" "y \<in> val(P,G,c)"
      using GenExtD by auto
    from \<open>y \<in> val(P,G,c)\<close>
    obtain \<theta> where "\<theta>\<in>domain(c)" "val(P,G,\<theta>) = y"
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
    using pair_in_M_iff one_in_M transitivity that apply_closed by simp_all
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
    using that one_in_M \<open>X\<in>M\<close> rcheck_in_M is_Hcheck_iff_sats zero_in_M
    by simp
  then
  have "sats(M,is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0), [y,x,z,\<one>,rcheck(X)])
        \<longleftrightarrow> is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that sats_is_wfrec_fm \<open>X\<in>M\<close> rcheck_in_M one_in_M zero_in_M
    by simp
  moreover from this
  have satsf:"sats(M, ?f, [x,z,\<one>,rcheck(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that \<open>X\<in>M\<close> rcheck_in_M one_in_M
    by (simp del:pair_abs)
  moreover
  have artyf:"arity(?f) = 4"
    using arity_wfrec_replacement_fm[where p="is_Hcheck_fm(8, 2, 1, 0)" and i=9]
      arity_is_Hcheck_fm ord_simp_union
    by simp
  ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,\<one>,rcheck(X)]))"
    using replacement_ax1(10) artyf \<open>X\<in>M\<close> rcheck_in_M one_in_M
    unfolding replacement_assm_def by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(##M,\<one>),rcheck(X), x, y))"
    using repl_sats[of M ?f "[\<one>,rcheck(X)]"] satsf by (simp del:pair_abs)
  then
  show ?thesis
    unfolding wfrec_replacement_def by simp
qed

lemma repl_PHcheck :
  assumes "f\<in>M"
  shows "strong_replacement(##M,PHcheck(##M,\<one>,f))"
proof -
  from \<open>f\<in>M\<close>
  have "strong_replacement(##M,\<lambda>x y. sats(M,PHcheck_fm(2,3,0,1),[x,y,\<one>,f]))"
    using replacement_ax1(11) one_in_M unfolding replacement_assm_def
    by (simp add:arity ord_simp_union)
  with \<open>f\<in>M\<close>
  show ?thesis
    using one_in_M zero_in_M
    unfolding strong_replacement_def univalent_def
    by simp
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

lemma Hcheck_closed : "\<forall>y\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> Hcheck(y,g)\<in>M"
proof -
  have "Replace(y,PHcheck(##M,\<one>,f))\<in>M" if "f\<in>M" "y\<in>M" for f y
    using that repl_PHcheck  PHcheck_closed[of y f] univ_PHcheck
      strong_replacement_closed
    by (simp flip: setclass_iff)
  then
  show ?thesis
    using def_PHcheck by auto
qed

lemma wf_rcheck : "x\<in>M \<Longrightarrow> wf(rcheck(x))"
  unfolding rcheck_def using wf_trancl[OF wf_Memrel] .

lemma trans_rcheck : "x\<in>M \<Longrightarrow> trans(rcheck(x))"
  unfolding rcheck_def using trans_trancl .

lemma relation_rcheck : "x\<in>M \<Longrightarrow> relation(rcheck(x))"
  unfolding rcheck_def using relation_trancl .

lemma check_in_M : "x\<in>M \<Longrightarrow> check(x) \<in> M"
  unfolding transrec_def
  using wfrec_Hcheck[of x] check_trancl wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
    Hcheck_closed relation2_Hcheck trans_wfrec_closed[of "rcheck(x)" x "is_Hcheck(##M,\<one>)" Hcheck]
  by (simp flip: setclass_iff)

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

lemma check_replacement: "{check(x). x\<in>P} \<in> M"
proof -
  have "arity(check_fm(0,2,1)) = 3"
    by (simp add:ord_simp_union arity)
  then
  show ?thesis
    using sats_check_fm check_abs P_in_M check_in_M one_in_M transitivity zero_in_M
      Replace_relativized_in_M[of "check_fm(0,2,1)" "[\<one>]" _ "is_check(##M,\<one>)" check]
      check_fm_type replacement_ax1(12)
    by simp
qed

lemma M_subset_MG :  "\<one> \<in> G \<Longrightarrow> M \<subseteq> M[G]"
  using check_in_M one_in_P GenExtI
  by (intro subsetI, subst valcheck [of G,symmetric], auto)

text\<open>The name for the generic filter\<close>
definition
  G_dot :: "i" where
  "G_dot \<equiv> {\<langle>check(p),p\<rangle> . p\<in>P}"

lemma G_dot_in_M : "G_dot \<in> M"
proof -
  let ?is_pcheck = "\<lambda>x y. \<exists>ch\<in>M. is_check(##M,\<one>,x,ch) \<and> pair(##M,ch,x,y)"
  let ?pcheck_fm = "Exists(And(check_fm(1,3,0),pair_fm(0,1,2)))"
  have "sats(M,?pcheck_fm,[x,y,\<one>]) \<longleftrightarrow> ?is_pcheck(x,y)" if "x\<in>M" "y\<in>M" for x y
    using sats_check_fm that one_in_M zero_in_M by simp
  moreover
  have "?is_pcheck(x,y) \<longleftrightarrow> y = \<langle>check(x),x\<rangle>" if "x\<in>M" "y\<in>M" for x y
    using that check_abs check_in_M by simp
  moreover
  have "?pcheck_fm\<in>formula"
    by simp
  moreover
  have "arity(?pcheck_fm)=3"
    by (simp add:ord_simp_union arity)
  moreover
  from P_in_M check_in_M pair_in_M_iff P_sub_M
  have "\<langle>check(p),p\<rangle> \<in> M" if "p\<in>P" for p
    using that by auto
  ultimately
  show ?thesis
    unfolding G_dot_def
    using one_in_M P_in_M transitivity Replace_relativized_in_M[of ?pcheck_fm "[\<one>]"]
      replacement_ax1(13)
    by simp
qed

lemma val_G_dot :
  assumes "G \<subseteq> P" "\<one> \<in> G"
  shows "val(P,G,G_dot) = G"
proof (intro equalityI subsetI)
  fix x
  assume "x\<in>val(P,G,G_dot)"
  then obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle> \<in> G_dot" "val(P,G,\<theta>) = x" "\<theta> = check(p)"
    unfolding G_dot_def using elem_of_val_pair G_dot_in_M
    by force
  with \<open>\<one>\<in>G\<close> \<open>G\<subseteq>P\<close>
  show "x \<in> G"
    using valcheck P_sub_M by auto
next
  fix p
  assume "p\<in>G"
  have "\<langle>check(q),q\<rangle> \<in> G_dot" if "q\<in>P" for q
    unfolding G_dot_def using that by simp
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close>
  have "val(P,G,check(p)) \<in> val(P,G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>\<one>\<in>G\<close>
  show "p \<in> val(P,G,G_dot)"
    using P_sub_M valcheck by auto
qed

lemma G_in_Gen_Ext :
  assumes "G \<subseteq> P" "\<one> \<in> G"
  shows   "G \<in> M[G]"
  using assms val_G_dot GenExtI[of _ G] G_dot_in_M
  by force

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

locale G_generic1 = forcing_data1 +
  fixes G :: "i"
  assumes generic : "M_generic(G)"
begin

lemma zero_in_MG :
  "0 \<in> M[G]"
proof -
  have "0 = val(P,G,0)"
    using zero_in_M elem_of_val by auto
  also
  have "... \<in> M[G]"
    using GenExtI zero_in_M by simp
  finally
  show ?thesis .
qed

lemma G_nonempty: "G\<noteq>0"
  using generic subset_refl[of P] P_in_M P_dense
  unfolding M_generic_def
  by auto

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

locale G_generic1_AC = G_generic1 + M_ctm1_AC

end