section {* Functor Class *}

theory Functor
imports TypeApp Coerce
keywords "tycondef" :: thy_decl and "\<cdot>"
begin

subsection {* Class definition *}

text {* Here we define the @{text functor} class, which models the
Haskell class \texttt{Functor}. For technical reasons, we split the
definition of @{text functor} into two separate classes: First, we
introduce @{text prefunctor}, which only requires @{text fmap} to
preserve the identity function, and not function composition. *}

text {* The Haskell class \texttt{Functor f} fixes a polymorphic
function \texttt{fmap :: (a -> b) -> f a -> f b}. Since functions in
Isabelle type classes can only mention one type variable, we have the
@{text prefunctor} class fix a function @{text fmapU} that fixes both
of the polymorphic types to be the universal domain. We will use the
coercion operator to recover a polymorphic @{text fmap}. *}

text {* The single axiom of the @{text prefunctor} class is stated in
terms of the HOLCF constant @{text isodefl}, which relates a function
@{text "f :: 'a \<rightarrow> 'a"} with a deflation @{text "t :: udom defl"}:
@{thm isodefl_def [of f t, no_vars]}. *}

class prefunctor = "tycon" +
  fixes fmapU :: "(udom \<rightarrow> udom) \<rightarrow> udom\<cdot>'a \<rightarrow> udom\<cdot>'a::tycon"
  assumes isodefl_fmapU:
    "isodefl (fmapU\<cdot>(cast\<cdot>t)) (TC('a::tycon)\<cdot>t)"

text {* The @{text functor} class extends @{text prefunctor} with an
axiom stating that @{text fmapU} preserves composition. *}

class "functor" = prefunctor +
  assumes fmapU_fmapU [coerce_simp]:
    "\<And>f g (xs::udom\<cdot>'a::tycon).
      fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"

text {* We define the polymorphic @{text fmap} by coercion from @{text
fmapU}, then we proceed to derive the polymorphic versions of the
functor laws. *}

definition fmap :: "('a \<rightarrow> 'b) \<rightarrow> 'a\<cdot>'f \<rightarrow> 'b\<cdot>'f::functor"
  where "fmap = coerce\<cdot>(fmapU :: _ \<rightarrow> udom\<cdot>'f \<rightarrow> udom\<cdot>'f)"

subsection {* Polymorphic functor laws *}

lemma fmapU_eq_fmap: "fmapU = fmap"
by (simp add: fmap_def eta_cfun)

lemma fmap_eq_fmapU: "fmap = fmapU"
  by (simp only: fmapU_eq_fmap)

lemma cast_TC:
  "cast\<cdot>(TC('f)\<cdot>t) = emb oo fmapU\<cdot>(cast\<cdot>t) oo PRJ(udom\<cdot>'f::prefunctor)"
by (rule isodefl_fmapU [unfolded isodefl_def])

lemma isodefl_cast: "isodefl (cast\<cdot>t) t"
by (simp add: isodefl_def)

lemma cast_cast_below1: "A \<sqsubseteq> B \<Longrightarrow> cast\<cdot>A\<cdot>(cast\<cdot>B\<cdot>x) = cast\<cdot>A\<cdot>x"
by (intro deflation_below_comp1 deflation_cast monofun_cfun_arg)

lemma cast_cast_below2: "A \<sqsubseteq> B \<Longrightarrow> cast\<cdot>B\<cdot>(cast\<cdot>A\<cdot>x) = cast\<cdot>A\<cdot>x"
by (intro deflation_below_comp2 deflation_cast monofun_cfun_arg)

lemma isodefl_fmap:
  assumes "isodefl d t"
  shows "isodefl (fmap\<cdot>d :: 'a\<cdot>'f \<rightarrow> _) (TC('f::functor)\<cdot>t)"
proof -
  have deflation_d: "deflation d"
    using assms by (rule isodefl_imp_deflation)
  have cast_t: "cast\<cdot>t = emb oo d oo prj"
    using assms unfolding isodefl_def .
  have t_below: "t \<sqsubseteq> DEFL('a)"
    apply (rule cast_below_imp_below)
    apply (simp only: cast_t cast_DEFL)
    apply (simp add: cfun_below_iff deflation.below [OF deflation_d])
    done
  have fmap_eq: "fmap\<cdot>d = PRJ('a\<cdot>'f) oo cast\<cdot>(TC('f)\<cdot>t) oo emb"
    by (simp add: fmap_def coerce_cfun cast_TC cast_t prj_emb cfcomp1)
  show ?thesis
    apply (simp add: fmap_eq isodefl_def cfun_eq_iff emb_prj)
    apply (simp add: DEFL_app)
    apply (simp add: cast_cast_below1 monofun_cfun t_below)
    apply (simp add: cast_cast_below2 monofun_cfun t_below)
    done
qed

lemma fmap_ID [simp]: "fmap\<cdot>ID = ID"
apply (rule isodefl_DEFL_imp_ID)
apply (subst DEFL_app)
apply (rule isodefl_fmap)
apply (rule isodefl_ID_DEFL)
done

lemma fmap_ident [simp]: "fmap\<cdot>(\<Lambda> x. x) = ID"
by (simp add: ID_def [symmetric])

lemma coerce_coerce_eq_fmapU_cast [coerce_simp]:
  fixes xs :: "udom\<cdot>'f::functor"
  shows "COERCE('a\<cdot>'f, udom\<cdot>'f)\<cdot>(COERCE(udom\<cdot>'f, 'a\<cdot>'f)\<cdot>xs) =
    fmapU\<cdot>(cast\<cdot>DEFL('a))\<cdot>xs"
by (simp add: coerce_def emb_prj DEFL_app cast_TC)

lemma fmap_fmap:
  fixes xs :: "'a\<cdot>'f::functor" and g :: "'a \<rightarrow> 'b" and f :: "'b \<rightarrow> 'c"
  shows "fmap\<cdot>f\<cdot>(fmap\<cdot>g\<cdot>xs) = fmap\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
unfolding fmap_def
by (simp add: coerce_simp)

lemma fmap_cfcomp: "fmap\<cdot>(f oo g) = fmap\<cdot>f oo fmap\<cdot>g"
by (simp add: cfcomp1 fmap_fmap eta_cfun)

subsection {* Derived properties of @{text fmap} *}

text {* Other theorems about @{text fmap} can be derived using only
the abstract functor laws. *}

lemma deflation_fmap:
  "deflation d \<Longrightarrow> deflation (fmap\<cdot>d)"
 apply (rule deflation.intro)
  apply (simp add: fmap_fmap deflation.idem eta_cfun)
 apply (subgoal_tac "fmap\<cdot>d\<cdot>x \<sqsubseteq> fmap\<cdot>ID\<cdot>x", simp)
 apply (rule monofun_cfun_fun, rule monofun_cfun_arg)
 apply (erule deflation.below_ID)
done

lemma ep_pair_fmap:
  "ep_pair e p \<Longrightarrow> ep_pair (fmap\<cdot>e) (fmap\<cdot>p)"
 apply (rule ep_pair.intro)
  apply (simp add: fmap_fmap ep_pair.e_inverse)
 apply (simp add: fmap_fmap)
 apply (rule_tac y="fmap\<cdot>ID\<cdot>y" in below_trans)
  apply (rule monofun_cfun_fun)
  apply (rule monofun_cfun_arg)
  apply (rule cfun_belowI, simp)
  apply (erule ep_pair.e_p_below)
 apply simp
done

lemma fmap_strict:
  fixes f :: "'a \<rightarrow> 'b"
  assumes "f\<cdot>\<bottom> = \<bottom>" shows "fmap\<cdot>f\<cdot>\<bottom> = (\<bottom>::'b\<cdot>'f::functor)"
proof (rule bottomI)
  have "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>'f) \<sqsubseteq> fmap\<cdot>f\<cdot>(fmap\<cdot>\<bottom>\<cdot>(\<bottom>::'b\<cdot>'f))"
    by (simp add: monofun_cfun)
  also have "... = fmap\<cdot>(\<Lambda> x. f\<cdot>(\<bottom>\<cdot>x))\<cdot>(\<bottom>::'b\<cdot>'f)"
    by (simp add: fmap_fmap)
  also have "... \<sqsubseteq> fmap\<cdot>ID\<cdot>\<bottom>"
    by (simp add: monofun_cfun assms del: fmap_ID)
  also have "... = \<bottom>"
    by simp
  finally show "fmap\<cdot>f\<cdot>\<bottom> \<sqsubseteq> (\<bottom>::'b\<cdot>'f::functor)" .
qed

subsection {* Proving that @{text "fmap\<cdot>coerce = coerce"} *}

lemma fmapU_cast_eq:
  "fmapU\<cdot>(cast\<cdot>A) =
    PRJ(udom\<cdot>'f) oo cast\<cdot>(TC('f::functor)\<cdot>A) oo emb"
by (subst cast_TC, rule cfun_eqI, simp)

lemma fmapU_cast_DEFL:
  "fmapU\<cdot>(cast\<cdot>DEFL('a)) =
    PRJ(udom\<cdot>'f) oo cast\<cdot>DEFL('a\<cdot>'f::functor) oo emb"
by (simp add: fmapU_cast_eq DEFL_app)

lemma coerce_functor: "COERCE('a\<cdot>'f, 'b\<cdot>'f::functor) = fmap\<cdot>coerce"
apply (rule cfun_eqI, rename_tac xs)
apply (simp add: fmap_def coerce_cfun)
apply (simp add: coerce_def)
apply (simp add: cfcomp1)
apply (simp only: emb_prj)
apply (subst fmapU_fmapU [symmetric])
apply (simp add: fmapU_cast_DEFL)
apply (simp add: emb_prj)
apply (simp add: cast_cast_below1 cast_cast_below2)
done

subsection {* Lemmas for reasoning about coercion *}

lemma fmapU_cast_coerce [coerce_simp]:
  fixes m :: "'a\<cdot>'f::functor"
  shows "fmapU\<cdot>(cast\<cdot>DEFL('a))\<cdot>(COERCE('a\<cdot>'f, udom\<cdot>'f)\<cdot>m) =
    COERCE('a\<cdot>'f, udom\<cdot>'f)\<cdot>m"
by (simp add: coerce_functor cast_DEFL fmapU_eq_fmap fmap_fmap eta_cfun)

lemma coerce_fmap [coerce_simp]:
  fixes xs :: "'a\<cdot>'f::functor" and f :: "'a \<rightarrow> 'b"
  shows "COERCE('b\<cdot>'f, 'c\<cdot>'f)\<cdot>(fmap\<cdot>f\<cdot>xs) = fmap\<cdot>(\<Lambda> x. COERCE('b,'c)\<cdot>(f\<cdot>x))\<cdot>xs"
by (simp add: coerce_functor fmap_fmap)

lemma fmap_coerce [coerce_simp]:
  fixes xs :: "'a\<cdot>'f::functor" and f :: "'b \<rightarrow> 'c"
  shows "fmap\<cdot>f\<cdot>(COERCE('a\<cdot>'f, 'b\<cdot>'f)\<cdot>xs) = fmap\<cdot>(\<Lambda> x. f\<cdot>(COERCE('a,'b)\<cdot>x))\<cdot>xs"
by (simp add: coerce_functor fmap_fmap)

subsection {* Configuration of Domain package *}

text {* We make various theorem declarations to enable Domain
  package definitions that involve @{text "tycon"} application. *}

setup {* Domain_Take_Proofs.add_rec_type (@{type_name app}, [true, false]) *}

declare DEFL_app [domain_defl_simps]
declare fmap_ID [domain_map_ID]
declare deflation_fmap [domain_deflation]
declare isodefl_fmap [domain_isodefl]

subsection {* Configuration of the Tycon package *}

text {* We now set up a new type definition command, which is used for
  defining new @{text tycon} instances. The @{text tycondef} command
  is implemented using much of the same code as the Domain package,
  and supports a similar input syntax. It automatically generates a
  @{text prefunctor} instance for each new type. (The user must
  provide a proof of the composition law to obtain a @{text functor}
  class instance.) *}

ML_file "tycondef.ML"

end
