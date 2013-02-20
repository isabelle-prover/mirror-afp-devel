(*  Title:      Down.ty
    Author:     Franz Regensburger
    Author:     Brian Huffman
    Author:     Joachim Breitner
*)

header {* The type of lifted values *}

theory Down
imports "HOLCF-Top" "HOLCF-Join"
begin

default_sort cpo

datatype 'a d = Itop | Idown 'a

type_notation (xsymbols)
  u  ("(_\<^sub>\<top>)" [1000] 999)

primrec Ifdown :: "('a \<rightarrow> 'b::Top_cpo) \<Rightarrow> 'a d \<Rightarrow> 'b" where
    "Ifdown f Itop = \<top>"
 |  "Ifdown f (Idown x) = f\<cdot>x"

subsection {* Ordering on lifted cpo *}

instantiation d :: (cpo) below
begin

definition
  below_down_def:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. case y of Itop \<Rightarrow> True | Idown a \<Rightarrow>
      (case x of Itop \<Rightarrow> False | Idown b \<Rightarrow> b \<sqsubseteq> a))"

instance ..
end

lemma maximal_down [iff]: "z \<sqsubseteq> Itop"
by (simp add: below_down_def)

lemma not_Idown_above [iff]: "Itop \<notsqsubseteq> Idown x "
by (simp add: below_down_def)

lemma Idown_below [iff]: "(Idown x \<sqsubseteq> Idown y) = (x \<sqsubseteq> y)"
by (simp add: below_down_def)

subsection {* Lifted cpo is a partial order *}

instance d :: (cpo) po
proof
  fix x :: "'a d"
  show "x \<sqsubseteq> x"
    unfolding below_down_def by (simp split: d.split)
next
  fix x y :: "'a d"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding below_down_def
    by (auto split: d.split_asm intro: below_antisym)
next
  fix x y z :: "'a d"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding below_down_def
    by (auto split: d.split_asm intro: below_trans)
qed

subsection {* Lifted cpo is a cpo *}

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (\<lambda>i. Idown (S i)) <<| Idown x"
unfolding is_lub_def is_ub_def ball_simps
by (auto simp add: below_down_def split: d.split)

lemma down_chain_lemma:
  assumes Y: "chain Y" obtains
    i where "Y i = Itop"
  | A where "\<forall>i. Idown (A i) = Y i" and "chain A" and "range Y <<| Idown (\<Squnion>i. A i)"
proof (cases "\<forall>k. Y k \<noteq> Itop")
  case True
  def A \<equiv> "\<lambda>i. THE a. Idown a = Y i"
  have Idown_A: "\<forall>i. Idown (A i) = Y i"
  proof
    fix i :: nat
    have "Y i \<noteq> Itop" using True by (auto)
    thus "Idown (A i) = Y i"
      by (cases "Y i", simp_all add: A_def)
  qed
  from Y have chain_A: "chain A"
    unfolding chain_def Idown_below [symmetric]
    by (simp add: Idown_A)
  hence "range A <<| (\<Squnion>i. A i)"
    by (rule cpo_lubI)
  hence "range (\<lambda>i. Idown (A i)) <<| Idown (\<Squnion>i. A i)"
    by (rule is_lub_Iup)
  hence "range (\<lambda>i. Y i) <<| Idown (\<Squnion>i. A i)"
    by (simp only: Idown_A)
  with Idown_A chain_A show ?thesis ..
next
  case False
  then obtain i where "Y i = Itop" by auto
  then show ?thesis ..
qed

lemma is_lub_maximal_Itop: "Y i = Itop \<Longrightarrow> range Y <<| Itop"
    by (metis  is_lub_maximal is_ubI  maximal_down rangeI)

instance d :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a d"
  assume S: "chain S"
  thus "\<exists>x. range (\<lambda>i. S i) <<| x"
  proof (rule down_chain_lemma)
    fix i
    assume "S i = Itop"
    hence "range (\<lambda>i. S i) <<| Itop"
      by (rule is_lub_maximal_Itop)
    thus ?thesis ..
  next
    fix A :: "nat \<Rightarrow> 'a"
    assume "range S <<| Idown (\<Squnion>i. A i)"
    thus ?thesis ..
  qed
qed


subsection {* Lifted cpo is pointed *}

instance d :: (cpo) Top_cpo
by intro_classes fast

text {* for compatibility with old HOLCF-Version *}
lemma inst_down_Top_cpo: "\<top> = Itop"
by (rule maximal_down [THEN topI, symmetric])

subsection {* Continuity of \emph{Idown} and \emph{Ifdown} *}

text {* continuity for @{term Idown} *}

lemma cont_Idown: "cont Idown"
apply (rule contI)
apply (rule is_lub_Iup)
apply (erule cpo_lubI)
done

text {* continuity for @{term Ifdown} *}

lemma cont_Ifdown1: "cont (\<lambda>f. Ifdown f x)"
by (induct x, simp_all)

lemma monofun_Ifdown2: "monofun (\<lambda>x. Ifdown f x)"
apply (rule monofunI)
apply (case_tac y, simp)
apply (case_tac x, simp)
apply (simp add: monofun_cfun_arg)
done

lemma cont_Ifdown2: "cont (\<lambda>x. Ifdown f x)"
proof (rule contI2)
  fix Y assume Y: "chain Y" and Y': "chain (\<lambda>i. Ifdown f (Y i))"
  from Y show "Ifdown f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. Ifdown f (Y i))"
  proof (rule down_chain_lemma)
    fix A
    assume A: "\<forall>i. Idown (A i) = Y i"
    assume "chain A" and "range Y <<| Idown (\<Squnion>i. A i)"
    hence "Ifdown f (\<Squnion>i. Y i) = (\<Squnion>i. Ifdown f (Idown (A i)))"
      by (simp add: lub_eqI contlub_cfun_arg)
    also have "\<dots> = (\<Squnion>i. Ifdown f (Y i))"
      by (simp add: A)
    finally show ?thesis by simp
  next
    fix i
    assume "Y i = Itop"
    hence "range Y <<| Itop"
      by (rule is_lub_maximal_Itop)
    hence "(\<Squnion>i. Y i) = Itop"
      by (metis lub_eqI)
    moreover
    assume "Y i = Itop"
    hence "Ifdown f (Y i) = \<top>" by simp
    hence "range (\<lambda>i. Ifdown f (Y i)) <<| \<top>"
      by (metis (mono_tags) Y' above_top_iff cpo_class.thelubE is_ub_thelub)
    hence "(\<Squnion>i. Ifdown f (Y i)) = \<top>"
      by (metis lub_eqI)
    ultimately
    show ?thesis by simp
  qed
qed (rule monofun_Ifdown2)

subsection {* Continuous versions of constants *}

definition
  down  :: "'a \<rightarrow> 'a d" where
  "down = (\<Lambda> x. Idown x)"

definition
  fdown :: "('a \<rightarrow> 'b::Top_cpo) \<rightarrow> 'a d \<rightarrow> 'b" where
  "fdown = (\<Lambda> f p. Ifdown f p)"

translations
  "case l of XCONST down\<cdot>x \<Rightarrow> t" == "CONST fdown\<cdot>(\<Lambda> x. t)\<cdot>l"
  "case l of (XCONST down :: 'a)\<cdot>x \<Rightarrow> t" => "CONST fdown\<cdot>(\<Lambda> x. t)\<cdot>l"
  "\<Lambda>(XCONST down\<cdot>x). t" == "CONST fdown\<cdot>(\<Lambda> x. t)"

text {* continuous versions of lemmas for @{typ "('a)d"} *}

lemma Exh_Down: "z = \<top> \<or> (\<exists>x. z = down\<cdot>x)"
apply (induct z)
apply (simp add: inst_down_Top_cpo)
apply (simp add: down_def cont_Idown)
done

lemma down_eq [simp]: "(down\<cdot>x = down\<cdot>y) = (x = y)"
by (simp add: down_def cont_Idown)

lemma down_inject: "down\<cdot>x = down\<cdot>y \<Longrightarrow> x = y"
by simp

lemma down_defined [simp]: "down\<cdot>x \<noteq> \<top>"
by (simp add: down_def cont_Idown inst_down_Top_cpo)

lemma not_down_less_UU: "\<top> \<notsqsubseteq> down\<cdot>x "
by simp (* FIXME: remove? *)

lemma down_above [simp]: "down\<cdot>x \<sqsubseteq> down\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
by (simp add: down_def cont_Idown)

lemma downE [case_names top down, cases type: d]:
  "\<lbrakk>p = \<top> \<Longrightarrow> Q; \<And>x. p = down\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp add: inst_down_Top_cpo)
apply (simp add: down_def cont_Idown)
done

lemma down_induct [case_names top down, induct type: d]:
  "\<lbrakk>P \<top>; \<And>x. P (down\<cdot>x)\<rbrakk> \<Longrightarrow> P x"
by (cases x, simp_all)

(*
text {* lifting preserves chain-finiteness *}

lemma up_chain_cases:
  assumes Y: "chain Y" obtains "\<forall>i. Y i = \<bottom>"
  | A k where "\<forall>i. up\<cdot>(A i) = Y (i + k)" and "chain A" and "(\<Squnion>i. Y i) = up\<cdot>(\<Squnion>i. A i)"
apply (rule up_chain_lemma [OF Y])
apply (simp_all add: inst_up_pcpo up_def cont_Iup lub_eqI)
done

lemma compact_up: "compact x \<Longrightarrow> compact (up\<cdot>x)"
apply (rule compactI2)
apply (erule up_chain_cases)
apply simp
apply (drule (1) compactD2, simp)
apply (erule exE)
apply (drule_tac f="up" and x="x" in monofun_cfun_arg)
apply (simp, erule exI)
done

lemma compact_upD: "compact (up\<cdot>x) \<Longrightarrow> compact x"
unfolding compact_def
by (drule adm_subst [OF cont_Rep_cfun2 [where f=up]], simp)

lemma compact_up_iff [simp]: "compact (up\<cdot>x) = compact x"
by (safe elim!: compact_up compact_upD)

instance u :: (chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (rule_tac p="\<Squnion>i. Y i" in upE, simp_all)
done
*)

text {* properties of fup *}

lemma fdown1 [simp]: "fdown\<cdot>f\<cdot>\<top> = \<top>"
by (simp add: fdown_def cont_Ifdown1 cont_Ifdown2 inst_down_Top_cpo cont2cont_LAM)

lemma fdown2 [simp]: "fdown\<cdot>f\<cdot>(down\<cdot>x) = f\<cdot>x"
by (simp add: down_def fdown_def cont_Idown cont_Ifdown1 cont_Ifdown2 cont2cont_LAM)

lemma fdown3 [simp]: "fdown\<cdot>down\<cdot>x = x"
by (cases x, simp_all)

(* End of dual of Up.thy, now various lemmas of later HOLCF theories follow. *)


subsection {* Map function for top-adjoint cpo *}

definition
  d_map :: "('a -> 'b) -> 'a d -> 'b d"
where
  "d_map = (\<Lambda> f. fdown\<cdot>(down oo f))"

lemma d_map_strict [simp]: "d_map\<cdot>f\<cdot>\<top> = \<top>"
unfolding d_map_def by simp

lemma d_map_up [simp]: "d_map\<cdot>f\<cdot>(down\<cdot>x) = down\<cdot>(f\<cdot>x)"
unfolding d_map_def by simp

lemma d_map_ID: "d_map\<cdot>ID = ID"
unfolding d_map_def by (simp add: cfun_eq_iff eta_cfun)

lemma d_map_map: "d_map\<cdot>f\<cdot>(d_map\<cdot>g\<cdot>p) = d_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>p"
by (induct p) simp_all

lemma d_map_oo: "d_map\<cdot>(f oo g) = d_map\<cdot>f oo d_map\<cdot>g"
by (simp add: cfcomp1 d_map_map eta_cfun)

lemma ep_pair_d_map: "ep_pair e p \<Longrightarrow> ep_pair (d_map\<cdot>e) (d_map\<cdot>p)"
apply default
apply (case_tac x, simp, simp add: ep_pair.e_inverse)
apply (case_tac y, simp, simp add: ep_pair.e_p_below)
done

lemma deflation_d_map: "deflation d \<Longrightarrow> deflation (d_map\<cdot>d)"
apply default
apply (case_tac x, simp, simp add: deflation.idem)
apply (case_tac x, simp, simp add: deflation.below)
done

lemma finite_deflation_d_map:
  assumes "finite_deflation d" shows "finite_deflation (d_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (d_map\<cdot>d)" by (rule deflation_d_map)
  have "{x. d_map\<cdot>d\<cdot>x = x} \<subseteq> insert \<top> ((\<lambda>x. down\<cdot>x) ` {x. d\<cdot>x = x})"
    by (rule subsetI, case_tac x, simp_all)
  thus "finite {x. d_map\<cdot>d\<cdot>x = x}"
    by (rule finite_subset, simp add: d.finite_fixes)
qed

subsubsection {* top-adjoint cpo *}

lemma approx_chain_d_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. d_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP d_map_ID finite_deflation_d_map)


instance d :: (pcpo) pcpo
  apply default
  apply (rule_tac x = "Idown \<bottom>" in exI)
  apply rule
  apply (case_tac y rule:d.exhaust)
  apply auto
  done

instance d :: (bifinite) bifinite
  apply default
  using bifinite
  by (auto dest: approx_chain_d_map)

definition "d_emb = udom_emb (\<lambda>i. d_map\<cdot>(udom_approx i))"
definition "d_prj = udom_prj (\<lambda>i. d_map\<cdot>(udom_approx i))"

lemma ep_pair_d: "ep_pair d_emb d_prj"
  unfolding d_emb_def d_prj_def
  by (simp add: ep_pair_udom approx_chain_d_map)

definition d_defl :: "udom defl \<rightarrow> udom defl"
  where "d_defl = defl_fun1 d_emb d_prj d_map"

lemma cast_d_defl:
  "cast\<cdot>(d_defl\<cdot>A) =
    d_emb oo d_map\<cdot>(cast\<cdot>A) oo d_prj"
using ep_pair_d finite_deflation_d_map
unfolding d_defl_def by (rule cast_defl_fun1)

instantiation d :: ("domain") "domain"
begin

definition
  "emb = d_emb oo d_map \<cdot> emb"

definition
  "prj = d_map \<cdot> prj oo d_prj"

definition
  "defl (t::'a d itself) = d_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a d u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a d u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a d itself) = liftdefl_of\<cdot>DEFL('a d)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a d)"
    unfolding emb_d_def prj_d_def
    by (intro ep_pair_comp ep_pair_d ep_pair_d_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a d) = emb oo (prj :: udom \<rightarrow> 'a d)"
    unfolding emb_d_def prj_d_def defl_d_def cast_d_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff d_map_map)
qed (fact liftemb_d_def liftprj_d_def liftdefl_d_def)+

end

lemma DEFL_d:
  "DEFL(('a::domain) d) = d_defl\<cdot>DEFL('a)"
by (rule defl_d_def)

lemma isodefl_d:
  "isodefl d1 t1  \<Longrightarrow>  isodefl (d_map\<cdot>d1) (d_defl\<cdot>t1)"
apply (rule isodeflI)
apply (simp add: cast_d_defl cast_isodefl)
apply (simp add: emb_d_def prj_d_def)
apply (simp add: d_map_map isodefl_strict)
done


lemmas [domain_defl_simps] = DEFL_d

lemmas [domain_map_ID] = d_map_ID

lemmas [domain_isodefl] = isodefl_d

lemmas [domain_deflation] = deflation_d_map


setup {*
  Domain_Take_Proofs.add_rec_type (@{type_name "d"}, [true])
*}


(* Complete cpos; Meet is sufficient *)

class Meet_cpo = Top_cpo + Nonempty_Meet_cpo
begin
  lemma  meet_exists: "\<exists>x. S >>| (x::'a)"
  using [[show_types]] [[show_sorts]]
   apply (cases "S = {}")
   thm nonempty_meet_exists maximal top_def
   apply (rule_tac x = "\<top>" in exI)
   apply (rule is_glbI)
   apply (rule is_lbI)
   apply auto[1]
   apply (rule maximal)
   apply (metis nonempty_meet_exists)
   done

  text {* Properties of the glb *}  

  lemma glbI: "S >>| (\<Sqinter>S :: 'a)"
    by (metis meet_exists is_glb_glb)

  lemma thelubE: "\<lbrakk>(\<Sqinter>S) = l\<rbrakk> \<Longrightarrow> S  >>| (l::'a)"
    by (metis meet_exists is_glb_glb)

  lemma is_lb_theglb: "x \<in> S \<Longrightarrow> \<Sqinter> S \<sqsubseteq> x"
    by (metis meet_exists is_lbD is_glb_glb[THEN is_glbD1])
  
  lemma is_glb_theglb:
    "[|S >| x|] ==> x \<sqsubseteq> (\<Sqinter>S)"
    by (metis meet_exists is_glb_glb[THEN is_glbD2])
  
  lemma glb_above_iff: "x \<sqsubseteq> (\<Sqinter>S) <-> (\<forall>y \<in> S. x \<sqsubseteq> y)"
    by (simp add: is_glb_above_iff [OF glbI] is_lb_def)
  
  lemma glb_above: "[| \<And>y. y \<in> S \<Longrightarrow> x \<sqsubseteq> y|] ==> x \<sqsubseteq> (\<Sqinter>S)"
    by (simp add: glb_above_iff)
  
  lemma above_glb: "[|y \<in> S ; y \<sqsubseteq> x|] ==> (\<Sqinter>S) \<sqsubseteq> y"
    by (metis is_lb_theglb)

end 

class complete_cpo = Meet_cpo + Join_cpo

instance Meet_cpo \<subseteq> Join_cpo
  apply default
  apply (rule_tac x = "lub {}" in exI)
  apply (metis is_lub_thelub_ex is_ub_empty ub_implies_lub_exists)
  apply (metis is_lubI is_ubI glb_above is_ubD is_lb_theglb mem_Collect_eq)
  done

lemma (in Top_cpo) meet_empty[simp]: "\<Sqinter>{} = (\<top>::'a)"
    by (metis glb_eqI is_glbI is_lb_empty maximal)


(* Stuff for the down type *)

lemma down_set_cases:
  fixes S  :: "'a d set"
  obtains Stop and  Sbelow
  where "Stop \<subseteq> {Itop}" and "Stop \<union> Idown ` Sbelow = S"
proof-
  have "S \<inter> {Itop} \<subseteq> {Itop}" by auto
  moreover
  have "Idown ` ((\<lambda>x. THE z. x = Idown z) ` (S - {Itop})) = S - {Itop}" 
    apply (intro set_eqI)
    apply (case_tac x rule:d.exhaust)
    apply auto[1]

    apply rule

    apply (erule imageE)
    apply auto[1]
    apply (rule classical)
    apply (erule notE)
    apply (rule the1I2)
    apply auto[1]
    apply (metis d.exhaust)
    apply simp

    apply (simp only:)
    apply (rule imageI)
    apply (erule rev_image_eqI)
    apply (rule the1I2)
    apply auto
    done
  hence "(S \<inter> {Itop}) \<union> Idown ` ((\<lambda>x. THE z. x = Idown z) ` (S - {Itop})) = S" by auto
  ultimately
  show thesis ..
qed

instance d :: (Nonempty_Meet_cpo) Nonempty_Meet_cpo
proof(default)
  fix S :: "'a d set"
  assume "S \<noteq> {}"
  
  obtain S1 S2 where "S1 \<subseteq> {Itop}" and "S1 \<union> Idown ` S2 = S" by (rule down_set_cases)
  
  show "\<exists> x. S >>| x"
  proof (cases "S2 = {}")
  case True
    hence "S = S1" using `_ \<union> _ = _` by (metis Un_empty_right image_empty)
    hence "S = {Itop}" using  `S \<noteq> {}` `S1 \<subseteq> _` by (metis subset_singletonD)
    hence "S >>| Itop"
      by (metis is_glb_singleton)
    thus ?thesis..
  next
  case False
    then obtain u where "S2 >>| u" by (metis nonempty_meet_exists)
  
    from `S2 \<noteq> {}` obtain a where "Idown a \<in> S"  using `_ \<union> _ = _` by auto
  
    have lb: "S >| Idown u"
      using `_ \<union> _ = _` `S1 \<subseteq> _` is_lbD[OF is_glbD1[OF `S2 >>| u`]]
      by (auto intro: is_lbI)
  
    have "S >>| Idown u"
      apply(rule is_glbI[OF lb])
      apply (case_tac ua rule:d.exhaust)  
      apply (drule is_lbD[OF _ `Idown a \<in> S`])
      apply simp
      apply simp
      apply (rule is_glbD2[OF `S2 >>| u`])
      apply (rule is_lbI)
      apply (drule is_lbD)
      using  `_ \<union> _ = _`
      apply auto
      done
    thus ?thesis ..
  qed
qed

class Finite_Meet_bifinite_cpo = Finite_Meet_cpo + bifinite

lemma is_ub_range:
     "S >| u \<Longrightarrow> Rep_cfun f ` S >| f \<cdot> u"
  apply (rule is_lbI)
  apply (erule imageE)
  by (metis monofun_cfun_arg is_lbD)

lemma (in approx_chain) lub_approx_arg: "(\<Squnion>i. approx i \<cdot> u ) = u"
  by (metis chain_approx lub_ID_reach lub_approx)

instance Finite_Meet_bifinite_cpo \<subseteq> Nonempty_Meet_cpo
proof (default)
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" by auto
  fix S
  assume "(S :: 'a set) \<noteq> {}"
  have "\<And>i. \<exists> l . Rep_cfun (approx i) ` S >>|l"
    apply (rule finite_meet_exists)
    using `S \<noteq> {}` apply auto[1]
    using  finite_deflation.finite_range[OF approx_chain.finite_deflation_approx[OF `approx_chain approx`]]
    by (metis (full_types) image_mono rev_finite_subset top_greatest)
  then obtain Y where Y_is_glb: "\<And>i. Rep_cfun (approx i) ` S >>| Y i" by metis
  
  have "chain Y"
    apply (rule chainI)
    apply (subst is_glb_above_iff[OF Y_is_glb])
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule rev_below_trans[OF monofun_cfun_fun[OF chainE[OF approx_chain.chain_approx[OF `approx_chain approx`]]]])
    apply (rule is_lbD[OF is_glbD1[OF Y_is_glb]])
    apply (erule imageI)
    done
  
  have "S >| Lub Y"
  proof(rule is_lbI, rule lub_below[OF `chain Y`])
    fix x i
    assume "x \<in> S"
    hence "Y i \<sqsubseteq> approx i \<cdot> x"
      by (rule imageI[THEN is_lbD[OF is_glbD1[OF Y_is_glb]]])
    also have "approx i \<cdot> x \<sqsubseteq> x"
      by (rule  approx_chain.approx_below[OF `approx_chain approx`])
    finally
    show "Y i \<sqsubseteq> x".
  qed

  have "S >>| Lub Y"
  proof (rule is_glbI[OF `S >| Lub Y`])
    fix u
    assume "S >| u"
    hence "\<And> i. Rep_cfun (approx i) ` S >| approx i \<cdot> u"
      by (rule is_ub_range)
    hence "\<And> i.  approx i \<cdot> u \<sqsubseteq> Y i"
      by (rule is_glbD2[OF Y_is_glb])
    hence "(\<Squnion>i. approx i \<cdot> u ) \<sqsubseteq> Lub Y" 
      by (rule lub_mono[OF
            ch2ch_Rep_cfunL[OF approx_chain.chain_approx[OF `approx_chain approx`]]
            `chain Y`
            ])
    thus "u \<sqsubseteq> Lub Y" 
      by (metis approx_chain.lub_approx_arg[OF `approx_chain approx`])
  qed
  thus "\<exists>x. S >>| x"..
qed

end
