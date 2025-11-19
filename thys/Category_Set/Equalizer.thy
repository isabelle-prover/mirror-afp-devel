section \<open>Equalizers and Subobjects\<close>

theory Equalizer
  imports Terminal
begin

subsection \<open>Equalizers\<close>

definition equalizer :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> bool" where
  "equalizer E m f g \<longleftrightarrow> (\<exists> X Y. (f : X \<rightarrow> Y) \<and> (g : X \<rightarrow> Y) \<and> (m : E \<rightarrow> X)
    \<and> (f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"

lemma equalizer_def2:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y" "m : E \<rightarrow> X"
  shows "equalizer E m f g \<longleftrightarrow> ((f \<circ>\<^sub>c m = g \<circ>\<^sub>c m)
    \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h)))"
  using assms unfolding equalizer_def by (auto simp add: cfunc_type_def)

lemma equalizer_eq:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y" "m : E \<rightarrow> X"
  assumes "equalizer E m f g"
  shows "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
  using assms equalizer_def2 by auto

lemma similar_equalizers:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y" "m : E \<rightarrow> X"
  assumes "equalizer E m f g"
  assumes "h : F \<rightarrow> X" "f \<circ>\<^sub>c h = g \<circ>\<^sub>c h"
  shows "\<exists>! k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h"
  using assms equalizer_def2 by auto

text \<open>The definition above and the axiomatization below correspond to Axiom 4 (Equalizers) in Halvorson.\<close>
axiomatization where
  equalizer_exists: "f : X \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Y \<Longrightarrow> \<exists> E m. equalizer E m f g"

lemma equalizer_exists2:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> Y"
  shows "\<exists> E m. m : E \<rightarrow> X \<and> f \<circ>\<^sub>c m = g \<circ>\<^sub>c m \<and> (\<forall> h F. ((h : F \<rightarrow> X) \<and> (f \<circ>\<^sub>c h = g \<circ>\<^sub>c h)) \<longrightarrow> (\<exists>! k. (k : F \<rightarrow> E) \<and> m \<circ>\<^sub>c k = h))"
proof -
  obtain E m where "equalizer E m f g"
    using assms equalizer_exists by blast
  then show ?thesis
    unfolding equalizer_def
  proof (intro exI[where x=E], intro exI[where x=m], safe)
    fix X' Y'
    assume f_type2: "f : X' \<rightarrow> Y'"
    assume g_type2: "g : X' \<rightarrow> Y'"
    assume m_type: "m : E \<rightarrow> X'"
    assume fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
    assume equalizer_unique: "\<forall>h F. h : F \<rightarrow> X' \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h)"

    show m_type2: "m : E \<rightarrow> X"
      using assms(2) cfunc_type_def g_type2 m_type by auto

    show "\<And> h F. h : F \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<Longrightarrow> \<exists>k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h"
      by (metis m_type2 cfunc_type_def equalizer_unique m_type)

    show "\<And> F k y. m \<circ>\<^sub>c k : F \<rightarrow> X \<Longrightarrow> f \<circ>\<^sub>c m \<circ>\<^sub>c k = g \<circ>\<^sub>c m \<circ>\<^sub>c k \<Longrightarrow> k : F \<rightarrow> E \<Longrightarrow> y : F \<rightarrow> E
        \<Longrightarrow> m \<circ>\<^sub>c y = m \<circ>\<^sub>c k \<Longrightarrow> k = y"
      using comp_type equalizer_unique m_type by blast
  qed
qed 

text \<open>The lemma below corresponds to Exercise 2.1.31 in Halvorson.\<close>
lemma equalizers_isomorphic:
  assumes "equalizer E m f g" "equalizer E' m' f g"
  shows "\<exists> k. k : E \<rightarrow> E' \<and> isomorphism k \<and> m = m' \<circ>\<^sub>c k"
proof -
  have fm_eq_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
    using assms(1) equalizer_def by blast
  have fm'_eq_gm': "f \<circ>\<^sub>c m' = g \<circ>\<^sub>c m'"
    using assms(2) equalizer_def by blast

  obtain X Y where f_type: "f : X \<rightarrow> Y" and g_type: "g : X \<rightarrow> Y" and m_type: "m : E \<rightarrow> X"
    using assms(1) unfolding equalizer_def by auto

  obtain k where k_type: "k : E' \<rightarrow> E" and mk_eq_m': "m \<circ>\<^sub>c k = m'"
    by (metis assms cfunc_type_def equalizer_def)
  obtain k' where k'_type: "k' : E \<rightarrow> E'" and m'k_eq_m: "m' \<circ>\<^sub>c k' = m"
    by (metis assms cfunc_type_def equalizer_def)

  have "f \<circ>\<^sub>c m \<circ>\<^sub>c k \<circ>\<^sub>c k' = g \<circ>\<^sub>c m \<circ>\<^sub>c k \<circ>\<^sub>c k'"
    using comp_associative2 m_type fm_eq_gm k'_type k_type m'k_eq_m mk_eq_m' by auto

  have "k \<circ>\<^sub>c k' : E \<rightarrow> E \<and> m \<circ>\<^sub>c k \<circ>\<^sub>c k' = m"
    using comp_associative2 comp_type k'_type k_type m_type m'k_eq_m mk_eq_m' by auto
  then have kk'_eq_id: "k \<circ>\<^sub>c k' = id E"
    using assms(1) equalizer_def id_right_unit2 id_type by blast

  have "k' \<circ>\<^sub>c k : E' \<rightarrow> E' \<and> m' \<circ>\<^sub>c k' \<circ>\<^sub>c k = m'"
    by (smt comp_associative2 comp_type k'_type k_type m'k_eq_m m_type mk_eq_m')
  then have k'k_eq_id: "k' \<circ>\<^sub>c k = id E'"
    using assms(2) equalizer_def id_right_unit2 id_type by blast

  show "\<exists>k. k : E \<rightarrow> E' \<and> isomorphism k \<and> m = m' \<circ>\<^sub>c k"
    using cfunc_type_def isomorphism_def k'_type k'k_eq_id k_type kk'_eq_id m'k_eq_m by (intro exI[where x=k'], auto)
qed

lemma isomorphic_to_equalizer_is_equalizer:
  assumes "\<phi>: E' \<rightarrow> E"
  assumes "isomorphism \<phi>"
  assumes "equalizer E m f g" 
  assumes "f : X \<rightarrow> Y"
  assumes "g : X \<rightarrow> Y"
  assumes "m : E \<rightarrow> X"
  shows   "equalizer E' (m \<circ>\<^sub>c \<phi>) f g"
proof - 
  obtain \<phi>_inv where \<phi>_inv_type[type_rule]: "\<phi>_inv : E \<rightarrow> E'" and \<phi>_inv_\<phi>: "\<phi>_inv \<circ>\<^sub>c \<phi> = id(E')" and \<phi>\<phi>_inv: "\<phi> \<circ>\<^sub>c \<phi>_inv = id(E)"
    using assms(1,2) cfunc_type_def isomorphism_def by auto

  have equalizes: "f \<circ>\<^sub>c m \<circ>\<^sub>c \<phi> = g \<circ>\<^sub>c m \<circ>\<^sub>c \<phi>"
    using assms comp_associative2 equalizer_def by force
  have "\<forall>h F. h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k = h)"
  proof(safe)
    fix h F
    assume h_type[type_rule]: "h : F \<rightarrow> X"
    assume h_equalizes: "f \<circ>\<^sub>c h = g \<circ>\<^sub>c h"
    have k_exists_uniquely: "\<exists>! k. k: F  \<rightarrow> E \<and> m \<circ>\<^sub>c k = h"
      using assms equalizer_def2 h_equalizes by (typecheck_cfuncs, auto)
    then obtain k where k_type[type_rule]: "k: F  \<rightarrow> E" and k_def: "m \<circ>\<^sub>c k = h"
      by blast
    then show "\<exists>k. k : F \<rightarrow> E' \<and> (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k = h"
      using assms by (typecheck_cfuncs, smt (z3) \<phi>\<phi>_inv \<phi>_inv_type comp_associative2 comp_type id_right_unit2 k_exists_uniquely)
  next
    fix F k y
    assume "(m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k : F \<rightarrow> X"
    assume "f \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k = g \<circ>\<^sub>c (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k"
    assume k_type[type_rule]: "k : F \<rightarrow> E'"
    assume y_type[type_rule]: "y : F \<rightarrow> E'"
    assume "(m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c y = (m \<circ>\<^sub>c \<phi>) \<circ>\<^sub>c k"
    then show "k = y"
      by (typecheck_cfuncs, smt (verit, ccfv_threshold) assms(1,2,3) cfunc_type_def comp_associative comp_type equalizer_def id_left_unit2 isomorphism_def)
  qed
  then show ?thesis
    by (smt (verit, best) assms(1,4,5,6) comp_type equalizer_def equalizes)
qed

text \<open>The lemma below corresponds to Exercise 2.1.34 in Halvorson.\<close>
lemma equalizer_is_monomorphism:
  "equalizer E m f g \<Longrightarrow>  monomorphism(m)"
  unfolding equalizer_def monomorphism_def
proof clarify
  fix h1 h2 X Y
  assume f_type: "f : X \<rightarrow> Y"
  assume g_type: "g : X \<rightarrow> Y"
  assume m_type: "m : E \<rightarrow> X"
  assume fm_gm: "f \<circ>\<^sub>c m = g \<circ>\<^sub>c m"
  assume uniqueness: "\<forall>h F. h : F \<rightarrow> X \<and> f \<circ>\<^sub>c h = g \<circ>\<^sub>c h \<longrightarrow> (\<exists>!k. k : F \<rightarrow> E \<and> m \<circ>\<^sub>c k = h)"
  assume relation_ga: "codomain h1 = domain m"
  assume relation_h: "codomain h2 = domain m" 
  assume m_ga_mh: "m \<circ>\<^sub>c h1 = m \<circ>\<^sub>c h2"   
  have  "f \<circ>\<^sub>c m \<circ>\<^sub>c h1 =  g \<circ>\<^sub>c m \<circ>\<^sub>c h2"
    using cfunc_type_def comp_associative f_type fm_gm g_type m_ga_mh m_type relation_h by auto
  then obtain z where "z: domain(h1) \<rightarrow> E \<and> m \<circ>\<^sub>c z = m \<circ>\<^sub>c h1 \<and> 
    (\<forall> j. j:domain(h1) \<rightarrow> E \<and>  m \<circ>\<^sub>c j = m \<circ>\<^sub>c h1 \<longrightarrow> j = z)"
    using uniqueness by (smt cfunc_type_def codomain_comp domain_comp m_ga_mh m_type relation_ga)
  then show "h1 = h2"
    by (metis cfunc_type_def domain_comp m_ga_mh m_type relation_ga relation_h)
qed

text \<open>The definition below corresponds to Definition 2.1.35 in Halvorson.\<close>
definition regular_monomorphism :: "cfunc \<Rightarrow> bool"
  where "regular_monomorphism f  \<longleftrightarrow>  
          (\<exists> g h. domain g = codomain f \<and> domain h = codomain f \<and> equalizer (domain f) f g h)"

text \<open>The lemma below corresponds to Exercise 2.1.36 in Halvorson.\<close>
lemma epi_regmon_is_iso:
  assumes "epimorphism f" "regular_monomorphism f"
  shows "isomorphism f"
proof -
  obtain g h where g_type: "domain g = codomain f" and
                   h_type: "domain h = codomain f" and
                   f_equalizer: "equalizer (domain f) f g h"
    using assms(2) regular_monomorphism_def by auto
  then have "g \<circ>\<^sub>c f = h \<circ>\<^sub>c f"
    using equalizer_def by blast
  then have "g = h"
    using assms(1) cfunc_type_def epimorphism_def equalizer_def f_equalizer by auto
  then have "g \<circ>\<^sub>c id(codomain f) = h \<circ>\<^sub>c id(codomain f)"
    by simp
  then obtain k where k_type: "f \<circ>\<^sub>c k = id(codomain(f)) \<and> codomain k = domain f"
    by (metis cfunc_type_def equalizer_def f_equalizer id_type)
  then have "f \<circ>\<^sub>c id(domain(f)) = f \<circ>\<^sub>c (k \<circ>\<^sub>c f)"
    by (metis comp_associative domain_comp id_domain id_left_unit id_right_unit)
  then have "monomorphism f \<Longrightarrow> k \<circ>\<^sub>c f = id(domain f)"
    by (metis (mono_tags) codomain_comp domain_comp id_codomain id_domain k_type monomorphism_def)
  then have "k \<circ>\<^sub>c f = id(domain f)"
    using equalizer_is_monomorphism f_equalizer by blast
  then show "isomorphism f"
    by (metis domain_comp id_domain isomorphism_def k_type)  
qed

subsection \<open>Subobjects\<close>

text \<open>The definition below corresponds to Definition 2.1.32 in Halvorson.\<close>
definition factors_through :: "cfunc  \<Rightarrow> cfunc \<Rightarrow> bool" (infix "factorsthru" 90)
  where "g factorsthru f \<longleftrightarrow> (\<exists> h. (h: domain(g)\<rightarrow> domain(f)) \<and> f \<circ>\<^sub>c h = g)"

lemma factors_through_def2:
  assumes "g : X \<rightarrow> Z" "f : Y \<rightarrow> Z"
  shows "g factorsthru f \<longleftrightarrow> (\<exists> h. h: X \<rightarrow> Y \<and> f \<circ>\<^sub>c h = g)"
  unfolding factors_through_def using assms by (simp add: cfunc_type_def)

text \<open>The lemma below corresponds to Exercise 2.1.33 in Halvorson.\<close>
lemma xfactorthru_equalizer_iff_fx_eq_gx:
  assumes "f: X\<rightarrow> Y" "g:X \<rightarrow> Y" "equalizer E m f g" "x\<in>\<^sub>c X"
  shows "x factorsthru m \<longleftrightarrow> f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
proof safe
  assume LHS: "x factorsthru m"
  then show "f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
    using assms(3) cfunc_type_def comp_associative equalizer_def factors_through_def by auto
next
  assume RHS: "f \<circ>\<^sub>c x = g  \<circ>\<^sub>c x"
  then show "x factorsthru m"
    unfolding cfunc_type_def factors_through_def
    by (metis RHS assms(1,3,4) cfunc_type_def equalizer_def)
qed

text \<open>The definition below corresponds to Definition 2.1.37 in Halvorson.\<close>
definition subobject_of :: "cset \<times> cfunc \<Rightarrow> cset \<Rightarrow> bool" (infix "\<subseteq>\<^sub>c" 50)
  where "B \<subseteq>\<^sub>c X \<longleftrightarrow> (snd B : fst B \<rightarrow> X \<and> monomorphism (snd B))"

lemma subobject_of_def2:
  "(B,m) \<subseteq>\<^sub>c X = (m : B \<rightarrow> X \<and> monomorphism m)"
  by (simp add: subobject_of_def)

definition relative_subset :: "cset \<times> cfunc \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" ("_\<subseteq>\<^bsub>_\<^esub>_" [51,50,51]50)
  where "B \<subseteq>\<^bsub>X\<^esub> A  \<longleftrightarrow> 
    (snd B : fst B \<rightarrow> X \<and> monomorphism (snd B) \<and> snd A : fst A \<rightarrow> X \<and> monomorphism (snd A)
          \<and> (\<exists> k. k: fst B \<rightarrow> fst A \<and> snd A \<circ>\<^sub>c k = snd B))"

lemma relative_subset_def2: 
  "(B,m) \<subseteq>\<^bsub>X\<^esub> (A,n) = (m : B \<rightarrow> X \<and> monomorphism m \<and> n : A \<rightarrow> X \<and> monomorphism n
          \<and> (\<exists> k. k: B \<rightarrow> A \<and> n \<circ>\<^sub>c k = m))"
  unfolding relative_subset_def by auto

lemma subobject_is_relative_subset: "(B,m) \<subseteq>\<^sub>c A \<longleftrightarrow> (B,m) \<subseteq>\<^bsub>A\<^esub> (A, id(A))"
  unfolding relative_subset_def2 subobject_of_def2
  using cfunc_type_def id_isomorphism id_left_unit id_type iso_imp_epi_and_monic by auto

text \<open>The definition below corresponds to Definition 2.1.39 in Halvorson.\<close>
definition relative_member :: "cfunc \<Rightarrow> cset \<Rightarrow> cset \<times> cfunc \<Rightarrow> bool" ("_ \<in>\<^bsub>_\<^esub> _" [51,50,51]50) where
  "x \<in>\<^bsub>X\<^esub> B \<longleftrightarrow> (x \<in>\<^sub>c X \<and> monomorphism (snd B) \<and> snd B : fst B \<rightarrow> X \<and> x factorsthru (snd B))"

lemma relative_member_def2:
  "x \<in>\<^bsub>X\<^esub> (B, m) = (x \<in>\<^sub>c X \<and> monomorphism m \<and> m : B \<rightarrow> X \<and> x factorsthru m)"
  unfolding relative_member_def by auto

text \<open>The lemma below corresponds to Proposition 2.1.40 in Halvorson.\<close>
lemma relative_subobject_member:
  assumes "(A,n) \<subseteq>\<^bsub>X\<^esub> (B,m)" "x \<in>\<^sub>c X"
  shows "x \<in>\<^bsub>X\<^esub> (A,n) \<Longrightarrow> x \<in>\<^bsub>X\<^esub> (B,m)"
  using assms unfolding relative_member_def2 relative_subset_def2
proof clarify
  fix k
  assume m_type: "m : B \<rightarrow> X"
  assume k_type: "k : A \<rightarrow> B"
  assume m_monomorphism: "monomorphism m"
  assume mk_monomorphism: "monomorphism (m \<circ>\<^sub>c k)"
  assume n_eq_mk: "n = m \<circ>\<^sub>c k"
  assume factorsthru_mk: "x factorsthru (m \<circ>\<^sub>c k)"
  
  obtain a where a_assms: "a \<in>\<^sub>c A \<and> (m \<circ>\<^sub>c k) \<circ>\<^sub>c a = x"
    using assms(2) cfunc_type_def domain_comp factors_through_def factorsthru_mk k_type m_type by auto
  then show "x factorsthru m "
    unfolding factors_through_def 
    using cfunc_type_def comp_type k_type m_type comp_associative
    by (intro exI[where x="k \<circ>\<^sub>c a"], auto)
qed

subsection \<open>Inverse Image\<close>

text\<open>The definition below corresponds to a definition given by a diagram between Definition 2.1.37 and Proposition 2.1.38 in Halvorson.\<close>
definition inverse_image :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cset" ("_\<^sup>-\<^sup>1\<lparr>_\<rparr>\<^bsub>_\<^esub>" [101,0,0]100) where
  "inverse_image f B m = (SOME A. \<exists> X Y k. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer A k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B))"

lemma inverse_image_is_equalizer:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "\<exists>k. equalizer (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
proof -
  obtain A k where "equalizer A k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    by (meson assms(1,2) comp_type equalizer_exists left_cart_proj_type right_cart_proj_type)
  then show "\<exists>k. equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    unfolding inverse_image_def using assms cfunc_type_def by (subst someI2_ex, auto)
qed

definition inverse_image_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc"  where
  "inverse_image_mapping f B m = (SOME k. \<exists> X Y. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B))"

lemma inverse_image_is_equalizer2:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
proof -
  obtain k where "equalizer (inverse_image f B m) k (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    using assms inverse_image_is_equalizer by blast
  then have "\<exists> X Y. f : X \<rightarrow> Y \<and> m : B \<rightarrow> Y \<and> monomorphism m \<and>
    equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    unfolding inverse_image_mapping_def using assms by (subst someI_ex, auto)
  then show "equalizer (inverse_image f B m) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B)"
    using assms(2) cfunc_type_def by auto
qed

lemma inverse_image_mapping_type[type_rule]:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "inverse_image_mapping f B m : (inverse_image f B m) \<rightarrow> X \<times>\<^sub>c B"
  using assms cfunc_type_def domain_comp equalizer_def inverse_image_is_equalizer2 left_cart_proj_type by auto

lemma inverse_image_mapping_eq:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m
      = m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m"
  using assms cfunc_type_def comp_associative equalizer_def inverse_image_is_equalizer2
  by (typecheck_cfuncs, smt (verit))

lemma inverse_image_mapping_monomorphism:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism (inverse_image_mapping f B m)"
  using assms equalizer_is_monomorphism inverse_image_is_equalizer2 by blast

text \<open>The lemma below is the dual of Proposition 2.1.38 in Halvorson.\<close>
lemma inverse_image_monomorphism:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "monomorphism (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
  using assms
proof (typecheck_cfuncs, unfold monomorphism_def3, clarify)
  fix g h A
  assume g_type: "g : A \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
  assume h_type: "h : A \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
  assume left_eq: "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
  then have "f \<circ>\<^sub>c (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = f \<circ>\<^sub>c (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    by auto
  then have "m \<circ>\<^sub>c (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = m \<circ>\<^sub>c (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms g_type h_type
    by (typecheck_cfuncs, smt cfunc_type_def codomain_comp comp_associative domain_comp inverse_image_mapping_eq left_cart_proj_type) 
  then have right_eq: "(right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c g
    = (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms g_type h_type monomorphism_def3 by (typecheck_cfuncs, auto)
  then have "inverse_image_mapping f B m \<circ>\<^sub>c g = inverse_image_mapping f B m \<circ>\<^sub>c h"
    using assms g_type h_type cfunc_type_def comp_associative left_eq left_cart_proj_type right_cart_proj_type
    by (typecheck_cfuncs, subst cart_prod_eq, auto)
  then show "g = h"
    using assms g_type h_type inverse_image_mapping_monomorphism inverse_image_mapping_type monomorphism_def3
    by blast
qed

definition inverse_image_subobject_mapping :: "cfunc \<Rightarrow> cset \<Rightarrow> cfunc \<Rightarrow> cfunc" ("[_\<^sup>-\<^sup>1\<lparr>_\<rparr>\<^bsub>_\<^esub>]map" [101,0,0]100) where
  "[f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map = left_cart_proj (domain f) B \<circ>\<^sub>c inverse_image_mapping f B m"

lemma inverse_image_subobject_mapping_def2:
  assumes "f : X \<rightarrow> Y"
  shows "[f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map = left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m"
  using assms unfolding inverse_image_subobject_mapping_def cfunc_type_def by auto

lemma inverse_image_subobject_mapping_type[type_rule]:
  assumes "f : X \<rightarrow> Y" "m : B \<rightarrow> Y" "monomorphism m"
  shows "[f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map : f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub> \<rightarrow> X"
  by (smt (verit, best) assms comp_type inverse_image_mapping_type inverse_image_subobject_mapping_def2 left_cart_proj_type)

lemma inverse_image_subobject_mapping_mono:
  assumes "f : X \<rightarrow> Y" "m : B \<rightarrow> Y" "monomorphism m"
  shows "monomorphism ([f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map)"
  using assms cfunc_type_def inverse_image_monomorphism inverse_image_subobject_mapping_def by fastforce

lemma inverse_image_subobject:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "(f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>, [f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>]map) \<subseteq>\<^sub>c X"
  unfolding subobject_of_def2
  using assms inverse_image_subobject_mapping_mono inverse_image_subobject_mapping_type
  by force

lemma inverse_image_pullback:
  assumes "m : B \<rightarrow> Y" "f : X \<rightarrow> Y" "monomorphism m"
  shows "is_pullback (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) B X Y 
    (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) m
    (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) f"
  unfolding is_pullback_def using assms
proof safe
  show right_type: "right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m : f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub> \<rightarrow> B"
    using assms cfunc_type_def codomain_comp domain_comp inverse_image_mapping_type
      right_cart_proj_type by auto
  show left_type: "left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m : f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub> \<rightarrow> X"
    using assms fst_conv inverse_image_subobject subobject_of_def by (typecheck_cfuncs)

  show "m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m =
      f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m"
    using assms inverse_image_mapping_eq by auto
next
  fix Z k h
  assume k_type: "k : Z \<rightarrow> B" and h_type: "h : Z \<rightarrow> X"
  assume mk_eq_fh: "m \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "equalizer (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) (inverse_image_mapping f B m) (f \<circ>\<^sub>c left_cart_proj X B) (m \<circ>\<^sub>c right_cart_proj X B )"
    using assms inverse_image_is_equalizer2 by blast
  then have "\<forall>h F. h : F \<rightarrow> (X \<times>\<^sub>c B) 
            \<and> (f \<circ>\<^sub>c left_cart_proj X B) \<circ>\<^sub>c h = (m \<circ>\<^sub>c right_cart_proj X B) \<circ>\<^sub>c h \<longrightarrow>
          (\<exists>!u. u : F \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) \<and> inverse_image_mapping f B m \<circ>\<^sub>c u = h)"
    unfolding equalizer_def using assms(2) cfunc_type_def domain_comp left_cart_proj_type by auto
  then have "\<langle>h,k\<rangle> : Z \<rightarrow> X \<times>\<^sub>c B  \<Longrightarrow>
      (f \<circ>\<^sub>c left_cart_proj X B) \<circ>\<^sub>c \<langle>h,k\<rangle> = (m \<circ>\<^sub>c right_cart_proj X B) \<circ>\<^sub>c \<langle>h,k\<rangle> \<Longrightarrow>
      (\<exists>!u. u : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) \<and> inverse_image_mapping f B m \<circ>\<^sub>c u = \<langle>h,k\<rangle>)"
    by auto
  then have "\<exists>!u. u : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) \<and> inverse_image_mapping f B m \<circ>\<^sub>c u = \<langle>h,k\<rangle>"
    using k_type h_type assms
    by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod left_cart_proj_type
        mk_eq_fh right_cart_proj_cfunc_prod right_cart_proj_type)
  then show "\<exists>j. j : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) \<and>
         (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = k \<and>
         (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = h"
  proof (clarify)
    fix u
    assume u_type[type_rule]: "u : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
    assume u_eq: "inverse_image_mapping f B m \<circ>\<^sub>c u = \<langle>h,k\<rangle>"

    show "\<exists>j. j : Z \<rightarrow> f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub> \<and>
             (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = k \<and>
             (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = h"
    proof (rule exI[where x=u], typecheck_cfuncs, safe)

      show "(right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c u = k"
        using assms u_type h_type k_type u_eq
        by (typecheck_cfuncs, metis (full_types) comp_associative2 right_cart_proj_cfunc_prod)
  
      show "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c u = h"
        using assms u_type h_type k_type u_eq
        by (typecheck_cfuncs, metis (full_types) comp_associative2 left_cart_proj_cfunc_prod)
    qed
  qed
next
  fix Z j y
  assume j_type: "j : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
  assume y_type: "y : Z \<rightarrow> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
  assume "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c y =
       (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j"
  then show "j = y"
    using assms j_type y_type inverse_image_mapping_type comp_type
    by (smt (verit, ccfv_threshold) inverse_image_monomorphism left_cart_proj_type monomorphism_def3)
qed

text \<open>The lemma below corresponds to Proposition 2.1.41 in Halvorson.\<close>
lemma in_inverse_image:
  assumes "f : X \<rightarrow> Y" "(B,m) \<subseteq>\<^sub>c Y" "x \<in>\<^sub>c X"
  shows "(x \<in>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>, left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)) = (f \<circ>\<^sub>c x \<in>\<^bsub>Y\<^esub> (B,m))"
proof
  have m_type: "m : B \<rightarrow> Y" "monomorphism m"
    using assms(2) unfolding subobject_of_def2 by auto

  assume "x \<in>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>, left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
  then obtain h where h_type: "h \<in>\<^sub>c (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>)"
      and h_def: "(left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h = x"
    unfolding relative_member_def2 factors_through_def by (auto simp add: cfunc_type_def)
  then have "f \<circ>\<^sub>c x = f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m \<circ>\<^sub>c h"
    using assms m_type by (typecheck_cfuncs, simp add: comp_associative2 h_def)
  then have "f \<circ>\<^sub>c x = (f \<circ>\<^sub>c left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms m_type h_type h_def comp_associative2 by (typecheck_cfuncs, blast)
  then have "f \<circ>\<^sub>c x = (m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c h"
    using assms h_type m_type by (typecheck_cfuncs, simp add: inverse_image_mapping_eq m_type)
  then have "f \<circ>\<^sub>c x = m \<circ>\<^sub>c right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m \<circ>\<^sub>c h"
    using assms m_type h_type by (typecheck_cfuncs, smt cfunc_type_def comp_associative domain_comp)
  then have "(f \<circ>\<^sub>c x) factorsthru m"
    unfolding factors_through_def using assms h_type m_type
    by (intro exI[where x="right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m \<circ>\<^sub>c h"],
        typecheck_cfuncs, auto simp add: cfunc_type_def)
  then show "f \<circ>\<^sub>c x \<in>\<^bsub>Y\<^esub> (B, m)"
    unfolding relative_member_def2 using assms m_type by (typecheck_cfuncs, auto)
next
  have m_type: "m : B \<rightarrow> Y" "monomorphism m"
    using assms(2) unfolding subobject_of_def2 by auto

  assume "f \<circ>\<^sub>c x \<in>\<^bsub>Y\<^esub> (B, m)"
  then have "\<exists>h. h : domain (f \<circ>\<^sub>c x) \<rightarrow> domain m \<and> m \<circ>\<^sub>c h = f \<circ>\<^sub>c x"
    unfolding relative_member_def2 factors_through_def by auto
  then obtain h where h_type: "h \<in>\<^sub>c B" and h_def: "m \<circ>\<^sub>c h = f \<circ>\<^sub>c x"
    unfolding relative_member_def2 factors_through_def 
    using assms cfunc_type_def domain_comp m_type by auto
  then have "\<exists>j. j \<in>\<^sub>c (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>) \<and>
         (right_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = h \<and>
         (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m) \<circ>\<^sub>c j = x"
    using inverse_image_pullback assms m_type unfolding is_pullback_def by blast
  then have "x factorsthru (left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
    using m_type assms cfunc_type_def by (typecheck_cfuncs, unfold factors_through_def, auto)
  then show "x \<in>\<^bsub>X\<^esub> (f\<^sup>-\<^sup>1\<lparr>B\<rparr>\<^bsub>m\<^esub>, left_cart_proj X B \<circ>\<^sub>c inverse_image_mapping f B m)"
    unfolding relative_member_def2 using m_type assms
    by (typecheck_cfuncs, simp add: inverse_image_monomorphism)
qed

subsection \<open>Fibered Products\<close>

text \<open>The definition below corresponds to Definition 2.1.42 in Halvorson.\<close>
definition fibered_product :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset" ("_ \<^bsub>_\<^esub>\<times>\<^sub>c\<^bsub>_\<^esub> _" [66,50,50,65]65) where
  "X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y = (SOME E. \<exists> Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer E m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y))"

lemma fibered_product_equalizer:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "\<exists> m. equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
proof -
  obtain E m where "equalizer E m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using assms equalizer_exists by (typecheck_cfuncs, blast)
  then have "\<exists>x Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
      equalizer x m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using assms by blast
  then have "\<exists> Z m. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and> 
      equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    unfolding fibered_product_def by (rule someI_ex)
  then show "\<exists>m. equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    by auto
qed

definition fibered_product_morphism :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_morphism X f g Y = (SOME m. \<exists> Z. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) m (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y))"

lemma fibered_product_morphism_equalizer:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
proof -
  have "\<exists>x Z. f : X \<rightarrow> Z \<and>
      g : Y \<rightarrow> Z \<and> equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) x (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using assms fibered_product_equalizer by blast
  then have "\<exists>Z. f : X \<rightarrow> Z \<and> g : Y \<rightarrow> Z \<and>
    equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    unfolding fibered_product_morphism_def by (rule someI_ex)
  then show "equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    by auto
qed

lemma fibered_product_morphism_type[type_rule]:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_morphism X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> X \<times>\<^sub>c Y"
  using assms cfunc_type_def domain_comp equalizer_def fibered_product_morphism_equalizer left_cart_proj_type by auto

lemma fibered_product_morphism_monomorphism:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "monomorphism (fibered_product_morphism X f g Y)"
  using assms equalizer_is_monomorphism fibered_product_morphism_equalizer by blast

definition fibered_product_left_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_left_proj X f g Y = (left_cart_proj X Y) \<circ>\<^sub>c (fibered_product_morphism X f g Y)"

lemma fibered_product_left_proj_type[type_rule]:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_left_proj X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> X"
  by (metis assms comp_type fibered_product_left_proj_def fibered_product_morphism_type left_cart_proj_type)

definition fibered_product_right_proj :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cfunc" where
  "fibered_product_right_proj X f g Y = (right_cart_proj X Y) \<circ>\<^sub>c (fibered_product_morphism X f g Y)"

lemma fibered_product_right_proj_type[type_rule]:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "fibered_product_right_proj X f g Y : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<rightarrow> Y"
  by (metis assms comp_type fibered_product_right_proj_def fibered_product_morphism_type right_cart_proj_type)

lemma pair_factorsthru_fibered_product_morphism:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z" "x : A \<rightarrow> X" "y : A \<rightarrow> Y"
  shows "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y \<Longrightarrow> \<langle>x,y\<rangle> factorsthru fibered_product_morphism X f g Y"
  unfolding factors_through_def
proof -
  have equalizer: "equalizer (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) (fibered_product_morphism X f g Y) (f \<circ>\<^sub>c left_cart_proj X Y) (g \<circ>\<^sub>c right_cart_proj X Y)"
    using fibered_product_morphism_equalizer assms by (typecheck_cfuncs, auto)

  assume "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
  then have "(f \<circ>\<^sub>c left_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle> = (g \<circ>\<^sub>c right_cart_proj X Y) \<circ>\<^sub>c \<langle>x,y\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  then have "\<exists>! h. h : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and> fibered_product_morphism X f g Y \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    using assms similar_equalizers by (typecheck_cfuncs, smt (verit, del_insts)  cfunc_type_def equalizer equalizer_def)
  then show "\<exists>h. h : domain \<langle>x,y\<rangle> \<rightarrow> domain (fibered_product_morphism X f g Y) \<and>
        fibered_product_morphism X f g Y \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    by (metis assms(1,2) cfunc_type_def domain_comp fibered_product_morphism_type)
qed

lemma fibered_product_is_pullback:
  assumes f_type[type_rule]: "f : X \<rightarrow> Z" and g_type[type_rule]: "g : Y \<rightarrow> Z"
  shows "is_pullback (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y) Y X Z  (fibered_product_right_proj X f g Y) g (fibered_product_left_proj X f g Y) f"
  unfolding is_pullback_def
  using assms fibered_product_left_proj_type fibered_product_right_proj_type
proof safe
  show "g \<circ>\<^sub>c fibered_product_right_proj X f g Y = f \<circ>\<^sub>c fibered_product_left_proj X f g Y"
    unfolding fibered_product_right_proj_def fibered_product_left_proj_def
    using cfunc_type_def comp_associative2 equalizer_def fibered_product_morphism_equalizer
    by (typecheck_cfuncs, auto)
next
  fix A k h
  assume k_type: "k : A \<rightarrow> Y" and h_type: "h : A \<rightarrow> X"
  assume k_h_commutes: "g \<circ>\<^sub>c k = f \<circ>\<^sub>c h"

  have "\<langle>h,k\<rangle> factorsthru fibered_product_morphism X f g Y"
    using assms h_type k_h_commutes k_type pair_factorsthru_fibered_product_morphism by auto
  then have f1: "\<exists>j. j : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and> fibered_product_morphism X f g Y \<circ>\<^sub>c j = \<langle>h,k\<rangle>"
    by (meson assms cfunc_prod_type factors_through_def2 fibered_product_morphism_type h_type k_type)
  then show "\<exists>j. j : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and>
           fibered_product_right_proj X f g Y \<circ>\<^sub>c j = k \<and> fibered_product_left_proj X f g Y \<circ>\<^sub>c j = h"
    unfolding fibered_product_right_proj_def fibered_product_left_proj_def 
  proof (clarify, safe)
    fix j
    assume j_type: "j : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y"

    show "\<exists>j. j : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and>
           (right_cart_proj X Y \<circ>\<^sub>c fibered_product_morphism X f g Y) \<circ>\<^sub>c j = k \<and> (left_cart_proj X Y \<circ>\<^sub>c fibered_product_morphism X f g Y) \<circ>\<^sub>c j = h"
      by (typecheck_cfuncs, smt (verit, best) f1 comp_associative2 h_type k_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  qed
next
  fix A j y
  assume j_type: "j : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y" and y_type: "y : A \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y"
  assume "fibered_product_right_proj X f g Y \<circ>\<^sub>c y = fibered_product_right_proj X f g Y \<circ>\<^sub>c j"
  then have right_eq: "right_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c y) =
      right_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c j)"
    unfolding fibered_product_right_proj_def using assms j_type y_type
    by (typecheck_cfuncs, simp add: comp_associative2)
  assume "fibered_product_left_proj X f g Y \<circ>\<^sub>c y = fibered_product_left_proj X f g Y \<circ>\<^sub>c j"
  then have left_eq: "left_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c y) =
      left_cart_proj X Y \<circ>\<^sub>c (fibered_product_morphism X f g Y \<circ>\<^sub>c j)"
    unfolding fibered_product_left_proj_def  using assms j_type y_type
    by (typecheck_cfuncs, simp add: comp_associative2)

  have mono: "monomorphism (fibered_product_morphism X f g Y)"
    using assms fibered_product_morphism_monomorphism by auto

  have "fibered_product_morphism X f g Y \<circ>\<^sub>c y = fibered_product_morphism X f g Y \<circ>\<^sub>c j"
    using right_eq left_eq cart_prod_eq fibered_product_morphism_type y_type j_type assms comp_type
    by (subst cart_prod_eq[where Z=A, where X=X, where Y=Y], auto)
  then show "j = y"
    using mono assms cfunc_type_def fibered_product_morphism_type j_type y_type
    unfolding monomorphism_def
    by auto 
qed

lemma fibered_product_proj_eq:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z"
  shows "f \<circ>\<^sub>c fibered_product_left_proj X f g Y = g \<circ>\<^sub>c fibered_product_right_proj X f g Y"
    using fibered_product_is_pullback assms
    unfolding is_pullback_def by auto

lemma fibered_product_pair_member:
  assumes "f : X \<rightarrow> Z" "g : Y \<rightarrow> Z" "x \<in>\<^sub>c X" "y \<in>\<^sub>c Y"
  shows "(\<langle>x, y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub>Y,  fibered_product_morphism X f g Y)) = (f \<circ>\<^sub>c x = g \<circ>\<^sub>c y)"
proof
  assume "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y)"
  then obtain h where
    h_type: "h \<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub>Y" and h_eq: "fibered_product_morphism X f g Y \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    unfolding relative_member_def2 factors_through_def
    using assms(3,4) cfunc_prod_type cfunc_type_def by auto
  
  have left_eq: "fibered_product_left_proj X f g Y \<circ>\<^sub>c h = x"
    unfolding fibered_product_left_proj_def
    using assms h_type
    by (typecheck_cfuncs, smt comp_associative2 h_eq left_cart_proj_cfunc_prod)

  have right_eq: "fibered_product_right_proj X f g Y \<circ>\<^sub>c h = y"
    unfolding fibered_product_right_proj_def
    using assms h_type
    by (typecheck_cfuncs, smt comp_associative2 h_eq right_cart_proj_cfunc_prod)

  have "f \<circ>\<^sub>c fibered_product_left_proj X f g Y \<circ>\<^sub>c h = g \<circ>\<^sub>c fibered_product_right_proj X f g Y \<circ>\<^sub>c h"
    using assms h_type by (typecheck_cfuncs, simp add: comp_associative2 fibered_product_proj_eq)
  then show "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    using left_eq right_eq by auto
next
  assume f_g_eq: "f \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
  show "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c Y\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y)"
    unfolding relative_member_def factors_through_def
  proof (safe)
    show "\<langle>x,y\<rangle> \<in>\<^sub>c X \<times>\<^sub>c Y"
      using assms by typecheck_cfuncs
    show "monomorphism (snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y))"
      using assms(1,2) fibered_product_morphism_monomorphism by auto
    show "snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y) : fst (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y) \<rightarrow> X \<times>\<^sub>c Y"
      using assms(1,2) fibered_product_morphism_type by force
    have j_exists: "\<And> Z k h. k : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<Longrightarrow> g \<circ>\<^sub>c k = f \<circ>\<^sub>c h \<Longrightarrow>
      (\<exists>!j. j : Z \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y \<and>
            fibered_product_right_proj X f g Y \<circ>\<^sub>c j = k \<and>
            fibered_product_left_proj X f g Y \<circ>\<^sub>c j = h)"
      using fibered_product_is_pullback assms unfolding is_pullback_def by auto

    obtain j where j_type: "j \<in>\<^sub>c X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y" and 
      j_projs: "fibered_product_right_proj X f g Y \<circ>\<^sub>c j = y" "fibered_product_left_proj X f g Y \<circ>\<^sub>c j = x"
      using j_exists[where Z=\<one>, where k=y, where h=x] assms f_g_eq by auto
    show "\<exists>h. h : domain \<langle>x,y\<rangle> \<rightarrow> domain (snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y)) \<and>
           snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y) \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    proof (intro exI[where x=j], safe)
      show "j : domain \<langle>x,y\<rangle> \<rightarrow> domain (snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y))"
        using assms j_type cfunc_type_def by (typecheck_cfuncs, auto)

      have left_eq: "left_cart_proj X Y \<circ>\<^sub>c fibered_product_morphism X f g Y \<circ>\<^sub>c j = x"
        using j_projs assms j_type comp_associative2
        unfolding fibered_product_left_proj_def by (typecheck_cfuncs, auto)

      have right_eq: "right_cart_proj X Y \<circ>\<^sub>c fibered_product_morphism X f g Y \<circ>\<^sub>c j = y"
        using j_projs assms j_type comp_associative2
        unfolding fibered_product_right_proj_def by (typecheck_cfuncs, auto)

      show "snd (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>g\<^esub> Y, fibered_product_morphism X f g Y) \<circ>\<^sub>c j = \<langle>x,y\<rangle>"
        using left_eq right_eq assms j_type by (typecheck_cfuncs, simp add: cfunc_prod_unique)
    qed
  qed
qed

lemma fibered_product_pair_member2:
  assumes "f : X \<rightarrow> Y" "g : X \<rightarrow> E" "x \<in>\<^sub>c X" "y \<in>\<^sub>c X"
  assumes "g \<circ>\<^sub>c fibered_product_left_proj X f f X = g \<circ>\<^sub>c fibered_product_right_proj X f f X"
  shows "\<forall>x y. x \<in>\<^sub>c X \<longrightarrow> y \<in>\<^sub>c X \<longrightarrow> \<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) \<longrightarrow> g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
proof(clarify)
  fix x y  
  assume x_type[type_rule]: "x \<in>\<^sub>c X"
  assume y_type[type_rule]: "y \<in>\<^sub>c X"
  assume a3: "\<langle>x,y\<rangle> \<in>\<^bsub>X \<times>\<^sub>c X\<^esub> (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X)"
  then obtain h where
    h_type: "h \<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub>X" and h_eq: "fibered_product_morphism X f f X \<circ>\<^sub>c h = \<langle>x,y\<rangle>"
    by (meson factors_through_def2 relative_member_def2)

  have left_eq: "fibered_product_left_proj X f f X \<circ>\<^sub>c h = x"
      unfolding fibered_product_left_proj_def
      by (typecheck_cfuncs, smt (z3) assms(1) comp_associative2 h_eq h_type left_cart_proj_cfunc_prod y_type)
    
  have right_eq: "fibered_product_right_proj X f f X \<circ>\<^sub>c h = y"
    unfolding fibered_product_right_proj_def
    by (typecheck_cfuncs, metis (full_types) a3 comp_associative2 h_eq h_type relative_member_def2 right_cart_proj_cfunc_prod x_type)

  then show "g \<circ>\<^sub>c x = g \<circ>\<^sub>c y"
    using assms(1,2,5) cfunc_type_def comp_associative fibered_product_left_proj_type fibered_product_right_proj_type h_type left_eq right_eq by fastforce
qed

lemma kernel_pair_subset:
  assumes "f: X \<rightarrow> Y"
  shows "(X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X, fibered_product_morphism X f f X) \<subseteq>\<^sub>c X \<times>\<^sub>c X"
  using assms fibered_product_morphism_monomorphism fibered_product_morphism_type subobject_of_def2 by auto

text \<open>The three lemmas below correspond to Exercise 2.1.44 in Halvorson.\<close>
lemma kern_pair_proj_iso_TFAE1:
  assumes "f: X \<rightarrow> Y" "monomorphism f"
  shows "(fibered_product_left_proj X f f X) = (fibered_product_right_proj X f f X)"
proof (cases "\<exists>x. x\<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub>X", clarify)
  fix x
  assume x_type: "x\<in>\<^sub>c X\<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub>X"
  then have "(f \<circ>\<^sub>c (fibered_product_left_proj X f f X))\<circ>\<^sub>c x = (f\<circ>\<^sub>c (fibered_product_right_proj X f f X))\<circ>\<^sub>c x"
    using assms cfunc_type_def comp_associative equalizer_def fibered_product_morphism_equalizer
    unfolding fibered_product_right_proj_def fibered_product_left_proj_def
    by (typecheck_cfuncs, smt (verit))
  then have "f \<circ>\<^sub>c (fibered_product_left_proj X f f X) = f\<circ>\<^sub>c (fibered_product_right_proj X f f X)"
    using assms fibered_product_is_pullback is_pullback_def by auto
  then show "(fibered_product_left_proj X f f X) = (fibered_product_right_proj X f f X)"
    using assms cfunc_type_def fibered_product_left_proj_type fibered_product_right_proj_type monomorphism_def by auto
next
  assume "\<nexists>x. x \<in>\<^sub>c X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
  then show "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
    using assms fibered_product_left_proj_type fibered_product_right_proj_type one_separator by blast
qed

lemma kern_pair_proj_iso_TFAE2:
  assumes "f: X \<rightarrow> Y" "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
  shows "monomorphism f \<and> isomorphism (fibered_product_left_proj X f f X) \<and> isomorphism (fibered_product_right_proj X f f X)"
  using assms
proof safe
  have "injective f"
    unfolding injective_def
  proof clarify
    fix x y
    assume x_type: "x \<in>\<^sub>c domain f" and y_type: "y \<in>\<^sub>c domain f"
    then have x_type2: "x \<in>\<^sub>c X" and y_type2: "y \<in>\<^sub>c X"
      using assms(1) cfunc_type_def by auto

    have x_y_type: "\<langle>x,y\<rangle> : \<one> \<rightarrow> X \<times>\<^sub>c X"
      using x_type2 y_type2 by (typecheck_cfuncs)
    have fibered_product_type: "fibered_product_morphism X f f X : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X \<times>\<^sub>c X"
      using assms by typecheck_cfuncs

    assume "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    then have factorsthru: "\<langle>x,y\<rangle> factorsthru fibered_product_morphism X f f X"
      using assms(1) pair_factorsthru_fibered_product_morphism x_type2 y_type2 by auto
    then obtain xy where xy_assms: "xy : \<one> \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" "fibered_product_morphism X f f X \<circ>\<^sub>c xy = \<langle>x,y\<rangle>"
      using factors_through_def2 fibered_product_type x_y_type by blast

    have left_proj: "fibered_product_left_proj X f f X \<circ>\<^sub>c xy = x"
      unfolding fibered_product_left_proj_def using assms xy_assms
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative left_cart_proj_cfunc_prod x_type2 xy_assms(2) y_type2)
    have right_proj: "fibered_product_right_proj X f f X \<circ>\<^sub>c xy = y"
      unfolding fibered_product_right_proj_def using assms xy_assms
      by (typecheck_cfuncs, metis cfunc_type_def comp_associative right_cart_proj_cfunc_prod x_type2 xy_assms(2) y_type2)
      
    show "x = y"
      using assms(2) left_proj right_proj by auto
  qed
  then show "monomorphism f"
    using injective_imp_monomorphism by blast
next
  have "diagonal X factorsthru fibered_product_morphism X f f X"
    using assms(1) diagonal_def id_type pair_factorsthru_fibered_product_morphism by fastforce
  then obtain xx where xx_assms: "xx : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" "diagonal X = fibered_product_morphism X f f X \<circ>\<^sub>c xx"
    using assms(1) cfunc_type_def diagonal_type factors_through_def fibered_product_morphism_type by fastforce
  have eq1: "fibered_product_right_proj X f f X \<circ>\<^sub>c xx = id X"
    by (smt assms(1) comp_associative2 diagonal_def fibered_product_morphism_type fibered_product_right_proj_def id_type right_cart_proj_cfunc_prod right_cart_proj_type xx_assms)

  have eq2: "xx \<circ>\<^sub>c fibered_product_right_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
  proof (rule one_separator[where X="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X", where Y="X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"])
    show "xx \<circ>\<^sub>c fibered_product_right_proj X f f X : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      using assms(1) comp_type fibered_product_right_proj_type xx_assms by blast
    show "id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) : X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      by (simp add: id_type)
  next
    fix x
    assume x_type: "x \<in>\<^sub>c X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
    then obtain a where a_assms: "\<langle>a,a\<rangle> = fibered_product_morphism X f f X \<circ>\<^sub>c x" "a \<in>\<^sub>c X"
      by (smt assms cfunc_prod_comp cfunc_prod_unique comp_type fibered_product_left_proj_def
          fibered_product_morphism_type fibered_product_right_proj_def fibered_product_right_proj_type)

    have "(xx \<circ>\<^sub>c fibered_product_right_proj X f f X) \<circ>\<^sub>c x = xx \<circ>\<^sub>c right_cart_proj X X \<circ>\<^sub>c \<langle>a,a\<rangle>"
      using xx_assms x_type a_assms assms comp_associative2
      unfolding fibered_product_right_proj_def
      by (typecheck_cfuncs, auto)
    also have "... = xx \<circ>\<^sub>c a"
      using a_assms(2) right_cart_proj_cfunc_prod by auto
    also have "... = x"
    proof -
      have f2: "\<forall>c. c : \<one> \<rightarrow> X \<longrightarrow> fibered_product_morphism X f f X \<circ>\<^sub>c xx \<circ>\<^sub>c c = diagonal X \<circ>\<^sub>c c"
      proof safe
        fix c
        assume "c \<in>\<^sub>c X"
        then show "fibered_product_morphism X f f X \<circ>\<^sub>c xx \<circ>\<^sub>c c = diagonal X \<circ>\<^sub>c c"
          using assms xx_assms by (typecheck_cfuncs, simp add: comp_associative2 xx_assms(2))
      qed
      have f4: "xx : X \<rightarrow> codomain xx"
        using cfunc_type_def xx_assms by presburger
      have f5: "diagonal X \<circ>\<^sub>c a = \<langle>a,a\<rangle>"
        using a_assms diag_on_elements by blast
      have f6: "codomain (xx \<circ>\<^sub>c a) = codomain xx"
        using f4 by (meson a_assms cfunc_type_def comp_type)
      then have f9: "x : domain x \<rightarrow> codomain xx"
        using cfunc_type_def x_type xx_assms by auto
      have f10: "\<forall>c ca. domain (ca \<circ>\<^sub>c a) = \<one> \<or> \<not> ca : X \<rightarrow> c"
        by (meson a_assms cfunc_type_def comp_type)
      then have "domain \<langle>a,a\<rangle> = \<one>"
        using diagonal_type f5 by force
      then have f11: "domain x = \<one>"
        using cfunc_type_def x_type by blast
      have "xx \<circ>\<^sub>c a \<in>\<^sub>c codomain xx"
        using a_assms comp_type f4 by auto
      then show ?thesis
        using f11 f9 f5 f2 a_assms assms(1) cfunc_type_def fibered_product_morphism_monomorphism 
              fibered_product_morphism_type monomorphism_def x_type
        by auto
    qed
    also have "... = id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c x"
      by (metis cfunc_type_def id_left_unit x_type)
    finally show "(xx \<circ>\<^sub>c fibered_product_right_proj X f f X) \<circ>\<^sub>c x = id\<^sub>c (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X) \<circ>\<^sub>c x".
  qed

  show "isomorphism (fibered_product_left_proj X f f X)"
    unfolding isomorphism_def
    by (metis assms cfunc_type_def eq1 eq2 fibered_product_right_proj_type xx_assms(1))

  then show "isomorphism (fibered_product_right_proj X f f X)"
    unfolding isomorphism_def
    using assms(2) isomorphism_def by auto
qed

lemma kern_pair_proj_iso_TFAE3:
  assumes "f: X \<rightarrow> Y"
  assumes "isomorphism (fibered_product_left_proj X f f X)" "isomorphism (fibered_product_right_proj X f f X)"
  shows "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
proof -
  obtain q0 where 
    q0_assms: "q0 : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      "fibered_product_left_proj X f f X \<circ>\<^sub>c q0 = id X"
      "q0 \<circ>\<^sub>c fibered_product_left_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using assms(1,2) cfunc_type_def isomorphism_def by (typecheck_cfuncs, force)

  obtain q1 where 
    q1_assms: "q1 : X \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X"
      "fibered_product_right_proj X f f X \<circ>\<^sub>c q1 = id X"
      "q1 \<circ>\<^sub>c fibered_product_right_proj X f f X = id (X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X)"
    using assms(1,3) cfunc_type_def isomorphism_def by (typecheck_cfuncs, force)

  have "\<And>x. x \<in>\<^sub>c domain f \<Longrightarrow> q0 \<circ>\<^sub>c x = q1 \<circ>\<^sub>c x"
  proof -
    fix x 
    have fxfx:  "f\<circ>\<^sub>c x = f\<circ>\<^sub>c x"
       by simp
    assume x_type: "x \<in>\<^sub>c domain f"
    have factorsthru: "\<langle>x,x\<rangle> factorsthru fibered_product_morphism X f f X"
      using assms(1) cfunc_type_def fxfx pair_factorsthru_fibered_product_morphism x_type  by auto
    then obtain xx where xx_assms: "xx : \<one> \<rightarrow> X \<^bsub>f\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> X" "\<langle>x,x\<rangle> = fibered_product_morphism X f f X \<circ>\<^sub>c xx"
      by (smt assms(1) cfunc_type_def diag_on_elements diagonal_type domain_comp factors_through_def factorsthru fibered_product_morphism_type x_type)
      
    have projection_prop: "q0 \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx) = 
                               q1 \<circ>\<^sub>c ((fibered_product_right_proj X f f X)\<circ>\<^sub>c xx)"
      using q0_assms q1_assms xx_assms assms by (typecheck_cfuncs, simp add: comp_associative2)
    then have fun_fact: "x = ((fibered_product_left_proj X f f X) \<circ>\<^sub>c q1)\<circ>\<^sub>c (((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx))"
      by (smt assms(1) cfunc_type_def comp_associative2 fibered_product_left_proj_def
          fibered_product_left_proj_type fibered_product_morphism_type fibered_product_right_proj_def
          fibered_product_right_proj_type id_left_unit2 left_cart_proj_cfunc_prod left_cart_proj_type
          q1_assms right_cart_proj_cfunc_prod right_cart_proj_type x_type xx_assms)
    then have "q1  \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx) = 
             q0  \<circ>\<^sub>c ((fibered_product_left_proj X f f X)\<circ>\<^sub>c xx)"
      using q0_assms q1_assms xx_assms assms 
      by (typecheck_cfuncs, smt cfunc_type_def comp_associative2 fibered_product_left_proj_def
          fibered_product_morphism_type fibered_product_right_proj_def left_cart_proj_cfunc_prod
          left_cart_proj_type projection_prop right_cart_proj_cfunc_prod right_cart_proj_type x_type xx_assms(2))
    then show "q0 \<circ>\<^sub>c x = q1 \<circ>\<^sub>c x"      
      by (smt assms(1) cfunc_type_def codomain_comp comp_associative fibered_product_left_proj_type
          fun_fact id_left_unit2 q0_assms q1_assms xx_assms)
  qed
  then have "q0 = q1"
    by (metis assms(1) cfunc_type_def one_separator_contrapos q0_assms(1) q1_assms(1))
  then show "fibered_product_left_proj X f f X = fibered_product_right_proj X f f X"
    by (smt assms(1) comp_associative2 fibered_product_left_proj_type fibered_product_right_proj_type
        id_left_unit2 id_right_unit2 q0_assms q1_assms)
qed

lemma terminal_fib_prod_iso:
  assumes "terminal_object(T)"
  assumes f_type: "f : Y \<rightarrow> T" 
  assumes g_type: "g : X \<rightarrow> T"
  shows "(X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) \<cong> X \<times>\<^sub>c Y"
proof - 
  have "(is_pullback (X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) Y X T (fibered_product_right_proj X g f Y) f (fibered_product_left_proj X g f Y) g)"
    using assms pullback_iff_product fibered_product_is_pullback by (typecheck_cfuncs, blast)
  then have "(is_cart_prod (X \<^bsub>g\<^esub>\<times>\<^sub>c\<^bsub>f\<^esub> Y) (fibered_product_left_proj X g f Y) (fibered_product_right_proj X g f Y)  X Y)"
    using assms by (meson one_terminal_object pullback_iff_product terminal_func_type)
  then show ?thesis
    using assms by (metis canonical_cart_prod_is_cart_prod cart_prods_isomorphic fst_conv is_isomorphic_def snd_conv)
qed

end