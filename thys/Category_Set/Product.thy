section \<open>Cartesian Products of Sets\<close>

theory Product
  imports Cfunc
begin

text \<open>The axiomatization below corresponds to Axiom 2 (Cartesian Products) in Halvorson.\<close>
axiomatization
  cart_prod :: "cset \<Rightarrow> cset \<Rightarrow> cset" (infixr "\<times>\<^sub>c" 65) and
  left_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  right_cart_proj :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" and
  cfunc_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" ("\<langle>_,_\<rangle>")
where
  left_cart_proj_type[type_rule]: "left_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> X" and
  right_cart_proj_type[type_rule]: "right_cart_proj X Y : X \<times>\<^sub>c Y \<rightarrow> Y" and
  cfunc_prod_type[type_rule]: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> \<langle>f,g\<rangle> : Z \<rightarrow> X \<times>\<^sub>c Y" and
  left_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> left_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = f" and
  right_cart_proj_cfunc_prod: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c \<langle>f,g\<rangle> = g" and
  cfunc_prod_unique: "f : Z \<rightarrow> X \<Longrightarrow> g : Z \<rightarrow> Y \<Longrightarrow> h : Z \<rightarrow> X \<times>\<^sub>c Y \<Longrightarrow> 
    left_cart_proj X Y \<circ>\<^sub>c h = f \<Longrightarrow> right_cart_proj X Y \<circ>\<^sub>c h = g \<Longrightarrow> h = \<langle>f,g\<rangle>"

definition is_cart_prod :: "cset \<Rightarrow> cfunc \<Rightarrow> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" where
  "is_cart_prod W \<pi>\<^sub>0 \<pi>\<^sub>1 X Y \<longleftrightarrow> 
    (\<pi>\<^sub>0 : W \<rightarrow> X \<and> \<pi>\<^sub>1 : W \<rightarrow> Y \<and>
    (\<forall> f g Z. (f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y) \<longrightarrow> 
      (\<exists> h. h : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h = g \<and>
        (\<forall> h2. (h2 : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h))))"

lemma is_cart_prod_def2:
  assumes "\<pi>\<^sub>0 : W \<rightarrow> X" "\<pi>\<^sub>1 : W \<rightarrow> Y"
  shows "is_cart_prod W \<pi>\<^sub>0 \<pi>\<^sub>1 X Y \<longleftrightarrow> 
    (\<forall> f g Z. (f : Z \<rightarrow> X \<and> g : Z \<rightarrow> Y) \<longrightarrow> 
      (\<exists> h. h : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h = g \<and>
        (\<forall> h2. (h2 : Z \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = f \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = g) \<longrightarrow> h2 = h)))"
  unfolding is_cart_prod_def using assms by auto

abbreviation is_cart_prod_triple :: "cset \<times> cfunc \<times> cfunc \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> bool" where
  "is_cart_prod_triple W\<pi> X Y \<equiv> is_cart_prod (fst W\<pi>) (fst (snd W\<pi>)) (snd (snd W\<pi>)) X Y"

lemma canonical_cart_prod_is_cart_prod:
 "is_cart_prod (X \<times>\<^sub>c Y) (left_cart_proj X Y) (right_cart_proj X Y) X Y"
  unfolding is_cart_prod_def
proof (typecheck_cfuncs)
  fix f g Z
  assume f_type: "f: Z \<rightarrow> X"
  assume g_type: "g: Z \<rightarrow> Y"
  show "\<exists>h. h : Z \<rightarrow> X \<times>\<^sub>c Y \<and>
           left_cart_proj X Y \<circ>\<^sub>c h = f \<and>
           right_cart_proj X Y \<circ>\<^sub>c h = g \<and>
           (\<forall>h2. h2 : Z \<rightarrow> X \<times>\<^sub>c Y \<and>
                 left_cart_proj X Y \<circ>\<^sub>c h2 = f \<and> right_cart_proj X Y \<circ>\<^sub>c h2 = g \<longrightarrow>
                 h2 = h)"
       using f_type g_type left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod cfunc_prod_unique
       by (intro exI[where x="\<langle>f,g\<rangle>"], simp add: cfunc_prod_type)
qed

text \<open>The lemma below corresponds to Proposition 2.1.8 in Halvorson.\<close>
lemma cart_prods_isomorphic:
  assumes W_cart_prod:  "is_cart_prod_triple (W, \<pi>\<^sub>0, \<pi>\<^sub>1) X Y"
  assumes W'_cart_prod: "is_cart_prod_triple (W', \<pi>'\<^sub>0, \<pi>'\<^sub>1) X Y"
  shows "\<exists> f. f : W \<rightarrow> W' \<and> isomorphism f \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
proof -
  obtain f where f_def: "f : W \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by (metis fstI sndI)

  obtain g where g_def: "g : W' \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c g = \<pi>'\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c g = \<pi>'\<^sub>1"
      using W'_cart_prod W_cart_prod unfolding is_cart_prod_def by (metis fstI sndI)

  have fg0: "\<pi>'\<^sub>0 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>0"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have fg1: "\<pi>'\<^sub>1 \<circ>\<^sub>c (f \<circ>\<^sub>c g) = \<pi>'\<^sub>1"
    using W'_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW' where "idW' : W' \<rightarrow> W' \<and> (\<forall> h2. (h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1) \<longrightarrow> h2 = idW')"
    using W'_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have fg: "f \<circ>\<^sub>c g = id W'"
  proof clarify
    assume idW'_unique: "\<forall>h2. h2 : W' \<rightarrow> W' \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c h2 = \<pi>'\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c h2 = \<pi>'\<^sub>1 \<longrightarrow> h2 = idW'"
    have 1: "f \<circ>\<^sub>c g = idW'"
      using comp_type f_def fg0 fg1 g_def idW'_unique by blast
    have 2: "id W' = idW'"
      using W'_cart_prod idW'_unique id_right_unit2 id_type is_cart_prod_def by auto
    from 1 2 show "f \<circ>\<^sub>c g = id W'"
      by auto
  qed

  have gf0: "\<pi>\<^sub>0 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>0"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto
  have gf1: "\<pi>\<^sub>1 \<circ>\<^sub>c (g \<circ>\<^sub>c f) = \<pi>\<^sub>1"
    using W_cart_prod comp_associative2 f_def g_def is_cart_prod_def by auto

  obtain idW where "idW : W \<rightarrow> W \<and> (\<forall> h2. (h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1) \<longrightarrow> h2 = idW)"
    using W_cart_prod unfolding is_cart_prod_def by (metis fst_conv snd_conv)
  then have gf: "g \<circ>\<^sub>c f = id W"
  proof clarify
    assume idW_unique: "\<forall>h2. h2 : W \<rightarrow> W \<and> \<pi>\<^sub>0 \<circ>\<^sub>c h2 = \<pi>\<^sub>0 \<and> \<pi>\<^sub>1 \<circ>\<^sub>c h2 = \<pi>\<^sub>1 \<longrightarrow> h2 = idW"
    have 1: "g \<circ>\<^sub>c f = idW"
      using idW_unique cfunc_type_def codomain_comp domain_comp f_def gf0 gf1 g_def by auto
    have 2: "id W = idW"
      using idW_unique W_cart_prod id_right_unit2 id_type is_cart_prod_def by auto
    from 1 2 show "g \<circ>\<^sub>c f = id W"
      by auto
  qed

  have f_iso: "isomorphism f"
    using f_def fg g_def gf isomorphism_def3 by blast
  from f_iso f_def show "\<exists>f. f : W \<rightarrow> W' \<and> isomorphism f \<and> \<pi>'\<^sub>0 \<circ>\<^sub>c f = \<pi>\<^sub>0 \<and> \<pi>'\<^sub>1 \<circ>\<^sub>c f = \<pi>\<^sub>1"
    by auto
qed

lemma product_commutes:
  "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
proof -
  have id_AB: "\<langle>right_cart_proj B A, left_cart_proj B A\<rangle> \<circ>\<^sub>c \<langle>right_cart_proj A B, left_cart_proj A B\<rangle> = id(A \<times>\<^sub>c B)"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_unique comp_associative2 id_right_unit2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  have id_BA: "\<langle>right_cart_proj A B, left_cart_proj A B\<rangle> \<circ>\<^sub>c \<langle>right_cart_proj B A, left_cart_proj B A\<rangle> = id(B \<times>\<^sub>c A)"
    by (typecheck_cfuncs, smt (z3) cfunc_prod_unique comp_associative2 id_right_unit2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  show "A \<times>\<^sub>c B \<cong> B \<times>\<^sub>c A"
    by (smt (verit, ccfv_threshold) canonical_cart_prod_is_cart_prod cfunc_prod_unique cfunc_type_def id_AB id_BA is_cart_prod_def is_isomorphic_def isomorphism_def)
qed

lemma cart_prod_eq:
  assumes "a : Z \<rightarrow> X \<times>\<^sub>c Y" "b : Z \<rightarrow>  X \<times>\<^sub>c Y"
  shows "a = b \<longleftrightarrow> 
    (left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  by (metis (full_types) assms cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type)

lemma cart_prod_eqI:
  assumes "a : Z \<rightarrow> X \<times>\<^sub>c Y" "b : Z \<rightarrow>  X \<times>\<^sub>c Y"
  assumes "(left_cart_proj X Y \<circ>\<^sub>c a = left_cart_proj X Y \<circ>\<^sub>c b 
      \<and> right_cart_proj X Y \<circ>\<^sub>c a = right_cart_proj X Y \<circ>\<^sub>c b)"
  shows "a = b"
  using assms cart_prod_eq by blast

lemma cart_prod_eq2:
  assumes "a : Z \<rightarrow> X" "b : Z \<rightarrow> Y" "c : Z \<rightarrow>  X" "d : Z \<rightarrow>  Y"
  shows "\<langle>a, b\<rangle> = \<langle>c,d\<rangle> \<longleftrightarrow> (a = c \<and> b = d)"
  by (metis assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

lemma cart_prod_decomp:
  assumes "a : A \<rightarrow> X \<times>\<^sub>c Y"
  shows "\<exists> x y. a = \<langle>x, y\<rangle> \<and> x : A \<rightarrow> X \<and> y : A \<rightarrow> Y"
proof (rule exI[where x="left_cart_proj X Y \<circ>\<^sub>c a"], intro exI [where x="right_cart_proj X Y \<circ>\<^sub>c a"], safe)
  show "a = \<langle>left_cart_proj X Y \<circ>\<^sub>c a,right_cart_proj X Y \<circ>\<^sub>c a\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_unique)
  show "left_cart_proj X Y \<circ>\<^sub>c a : A \<rightarrow>  X"
    using assms by typecheck_cfuncs
  show "right_cart_proj X Y \<circ>\<^sub>c a : A \<rightarrow> Y"
    using assms by typecheck_cfuncs
qed

subsection \<open>Diagonal Functions\<close>

text \<open>The definition below corresponds to Definition 2.1.9 in Halvorson.\<close>
definition diagonal :: "cset \<Rightarrow> cfunc" where
  "diagonal X = \<langle>id X,id X\<rangle>"

lemma diagonal_type[type_rule]:
  "diagonal X : X \<rightarrow> X \<times>\<^sub>c X"
  unfolding diagonal_def by (simp add: cfunc_prod_type id_type)

lemma diag_mono:
"monomorphism(diagonal X)"
proof - 
  have "left_cart_proj X X \<circ>\<^sub>c diagonal X = id X"
    by (metis diagonal_def id_type left_cart_proj_cfunc_prod)
  then show "monomorphism(diagonal X)"
    by (metis cfunc_type_def comp_monic_imp_monic diagonal_type id_isomorphism iso_imp_epi_and_monic left_cart_proj_type)
qed

subsection \<open>Products of Functions\<close>

text \<open>The definition below corresponds to Definition 2.1.10 in Halvorson.\<close>
definition cfunc_cross_prod :: "cfunc \<Rightarrow> cfunc \<Rightarrow> cfunc" (infixr "\<times>\<^sub>f" 55) where
  "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj (domain f) (domain g), g \<circ>\<^sub>c right_cart_proj (domain f) (domain g)\<rangle>"

lemma cfunc_cross_prod_def2: 
  assumes "f : X \<rightarrow> Y" "g : V\<rightarrow> W"
  shows "f \<times>\<^sub>f g = \<langle>f \<circ>\<^sub>c left_cart_proj X V, g \<circ>\<^sub>c right_cart_proj X V\<rangle>"
  using assms cfunc_cross_prod_def cfunc_type_def by auto
    
lemma cfunc_cross_prod_type[type_rule]:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> f \<times>\<^sub>f g : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z"
  unfolding cfunc_cross_prod_def
  using cfunc_prod_type cfunc_type_def comp_type left_cart_proj_type right_cart_proj_type by auto

lemma left_cart_proj_cfunc_cross_prod:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> left_cart_proj Y Z \<circ>\<^sub>c f \<times>\<^sub>f g = f \<circ>\<^sub>c left_cart_proj W X"
  unfolding cfunc_cross_prod_def
  using cfunc_type_def comp_type left_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type by (smt (verit))

lemma right_cart_proj_cfunc_cross_prod:
  "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> right_cart_proj Y Z \<circ>\<^sub>c f \<times>\<^sub>f g = g \<circ>\<^sub>c right_cart_proj W X"
  unfolding cfunc_cross_prod_def
  using cfunc_type_def comp_type right_cart_proj_cfunc_prod left_cart_proj_type right_cart_proj_type by (smt (verit))

lemma cfunc_cross_prod_unique: "f : W \<rightarrow> Y \<Longrightarrow> g : X \<rightarrow> Z \<Longrightarrow> h : W \<times>\<^sub>c X \<rightarrow> Y \<times>\<^sub>c Z \<Longrightarrow>
    left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c left_cart_proj W X \<Longrightarrow>
    right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c right_cart_proj W X \<Longrightarrow> h = f \<times>\<^sub>f g"
  unfolding cfunc_cross_prod_def
  using cfunc_prod_unique cfunc_type_def comp_type left_cart_proj_type right_cart_proj_type by auto

text \<open>The lemma below corresponds to Proposition 2.1.11 in Halvorson.\<close>
lemma identity_distributes_across_composition:
  assumes f_type: "f : A \<rightarrow> B" and g_type: "g : B \<rightarrow> C"
  shows "id X \<times>\<^sub>f (g  \<circ>\<^sub>c f) = (id X \<times>\<^sub>f g) \<circ>\<^sub>c (id X \<times>\<^sub>f f)"
proof -
  from cfunc_cross_prod_unique
  have uniqueness: "\<forall>h. h : X \<times>\<^sub>c A \<rightarrow> X \<times>\<^sub>c C \<and>
    left_cart_proj X C \<circ>\<^sub>c h = id\<^sub>c X \<circ>\<^sub>c left_cart_proj X A \<and>
    right_cart_proj X C \<circ>\<^sub>c h = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj X A \<longrightarrow>
    h = id\<^sub>c X \<times>\<^sub>f (g \<circ>\<^sub>c f)"
    by (meson comp_type f_type g_type id_type)

  have left_eq: "left_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = id\<^sub>c X \<circ>\<^sub>c left_cart_proj X A"
    using assms by (typecheck_cfuncs, smt comp_associative2 id_left_unit2 left_cart_proj_cfunc_cross_prod left_cart_proj_type)
  have right_eq: "right_cart_proj X C \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c (id\<^sub>c X \<times>\<^sub>f f) = (g \<circ>\<^sub>c f) \<circ>\<^sub>c right_cart_proj X A"
    using assms by(typecheck_cfuncs, smt comp_associative2 right_cart_proj_cfunc_cross_prod right_cart_proj_type)
  show "id\<^sub>c X \<times>\<^sub>f g \<circ>\<^sub>c f = (id\<^sub>c X \<times>\<^sub>f g) \<circ>\<^sub>c id\<^sub>c X \<times>\<^sub>f f"
    using assms left_eq right_eq uniqueness by (typecheck_cfuncs, auto)
qed

lemma cfunc_cross_prod_comp_cfunc_prod:
  assumes a_type: "a : A \<rightarrow> W" and b_type: "b : A \<rightarrow> X"
  assumes f_type: "f : W \<rightarrow> Y" and g_type: "g : X \<rightarrow> Z"
  shows "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
proof -
  from cfunc_prod_unique have uniqueness:
    "\<forall>h. h : A \<rightarrow> Y \<times>\<^sub>c Z \<and> left_cart_proj Y Z \<circ>\<^sub>c h = f \<circ>\<^sub>c a \<and> right_cart_proj Y Z \<circ>\<^sub>c h = g \<circ>\<^sub>c b \<longrightarrow> 
      h = \<langle>f \<circ>\<^sub>c a, g \<circ>\<^sub>c b\<rangle>"
    using assms comp_type by blast

  have "left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c left_cart_proj W X \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_cross_prod)
  then have left_eq: "left_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = f \<circ>\<^sub>c a"
    using a_type b_type left_cart_proj_cfunc_prod by auto
  
  have "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c right_cart_proj W X \<circ>\<^sub>c \<langle>a, b\<rangle>"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 right_cart_proj_cfunc_cross_prod)
  then have right_eq: "right_cart_proj Y Z \<circ>\<^sub>c (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, b\<rangle> = g \<circ>\<^sub>c b"
    using a_type b_type right_cart_proj_cfunc_prod by auto

  show "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a,b\<rangle> = \<langle>f \<circ>\<^sub>c a,g \<circ>\<^sub>c b\<rangle>"
    using uniqueness left_eq right_eq assms by (meson cfunc_cross_prod_type cfunc_prod_type comp_type uniqueness)
qed

lemma cfunc_prod_comp:
  assumes f_type: "f : X \<rightarrow> Y"
  assumes a_type: "a : Y \<rightarrow> A" and b_type: "b : Y \<rightarrow> B"
  shows "\<langle>a, b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
proof -
  have same_left_proj: "left_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = a \<circ>\<^sub>c f"
    using assms by (typecheck_cfuncs, simp add: comp_associative2 left_cart_proj_cfunc_prod)
  have same_right_proj: "right_cart_proj A B \<circ>\<^sub>c \<langle>a, b\<rangle> \<circ>\<^sub>c f = b \<circ>\<^sub>c f"
    using assms comp_associative2 right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
  show "\<langle>a,b\<rangle> \<circ>\<^sub>c f = \<langle>a \<circ>\<^sub>c f, b \<circ>\<^sub>c f\<rangle>"
    by (typecheck_cfuncs, metis a_type b_type cfunc_prod_unique f_type same_left_proj same_right_proj)
qed

text \<open>The lemma below corresponds to Exercise 2.1.12 in Halvorson.\<close>
lemma id_cross_prod: "id(X) \<times>\<^sub>f id(Y) = id(X \<times>\<^sub>c Y)"
  by (typecheck_cfuncs, smt (z3) cfunc_cross_prod_unique id_left_unit2 id_right_unit2 left_cart_proj_type right_cart_proj_type)

text \<open>The lemma below corresponds to Exercise 2.1.14 in Halvorson.\<close>
lemma cfunc_cross_prod_comp_diagonal:
  assumes "f: X \<rightarrow> Y" 
  shows "(f \<times>\<^sub>f f) \<circ>\<^sub>c diagonal(X) = diagonal(Y) \<circ>\<^sub>c f"
  unfolding diagonal_def
proof -
  have "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id\<^sub>c X, id\<^sub>c X\<rangle> = \<langle>f \<circ>\<^sub>c id\<^sub>c X, f \<circ>\<^sub>c id\<^sub>c X\<rangle>"
    using assms cfunc_cross_prod_comp_cfunc_prod id_type by blast
  also have "... = \<langle>f, f\<rangle>"
    using assms cfunc_type_def id_right_unit by auto
  also have "... = \<langle>id\<^sub>c Y \<circ>\<^sub>c f, id\<^sub>c Y \<circ>\<^sub>c f\<rangle>"
    using assms cfunc_type_def id_left_unit by auto
  also have "... = \<langle>id\<^sub>c Y, id\<^sub>c Y\<rangle> \<circ>\<^sub>c f"
    using assms cfunc_prod_comp id_type by fastforce
  finally show "(f \<times>\<^sub>f f) \<circ>\<^sub>c \<langle>id\<^sub>c X,id\<^sub>c X\<rangle> = \<langle>id\<^sub>c Y,id\<^sub>c Y\<rangle> \<circ>\<^sub>c f".
qed

lemma cfunc_cross_prod_comp_cfunc_cross_prod:
  assumes "a : A \<rightarrow> X" "b : B \<rightarrow> Y" "x : X \<rightarrow> Z" "y : Y \<rightarrow> W"
  shows "(x \<times>\<^sub>f y) \<circ>\<^sub>c (a \<times>\<^sub>f b) = (x \<circ>\<^sub>c a) \<times>\<^sub>f (y \<circ>\<^sub>c b)"
proof -
  have "(x \<times>\<^sub>f y) \<circ>\<^sub>c \<langle>a \<circ>\<^sub>c left_cart_proj A B , b \<circ>\<^sub>c right_cart_proj A B\<rangle>
      = \<langle>x \<circ>\<^sub>c a \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c b \<circ>\<^sub>c right_cart_proj A B\<rangle>"
    by (meson assms cfunc_cross_prod_comp_cfunc_prod comp_type left_cart_proj_type right_cart_proj_type)
  then show "(x \<times>\<^sub>f y) \<circ>\<^sub>c a \<times>\<^sub>f b = (x \<circ>\<^sub>c a) \<times>\<^sub>f y \<circ>\<^sub>c b"
    by (typecheck_cfuncs,smt (z3) assms cfunc_cross_prod_def2 comp_associative2 left_cart_proj_type right_cart_proj_type)
qed

lemma cfunc_cross_prod_mono:
  assumes type_assms: "f : X \<rightarrow> Y" "g : Z \<rightarrow> W"
  assumes f_mono: "monomorphism f" and g_mono: "monomorphism g"
  shows "monomorphism (f \<times>\<^sub>f g)"
  using type_assms
proof (typecheck_cfuncs, unfold monomorphism_def3, clarify)
  fix x y A
  assume x_type: "x : A \<rightarrow> X \<times>\<^sub>c Z"
  assume y_type: "y : A \<rightarrow> X \<times>\<^sub>c Z"

  obtain x1 x2 where x_expand: "x = \<langle>x1, x2\<rangle>" and x1_x2_type: "x1 : A \<rightarrow> X" "x2 : A \<rightarrow> Z"
    using cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type x_type by blast
  obtain y1 y2 where y_expand: "y = \<langle>y1, y2\<rangle>" and y1_y2_type: "y1 : A \<rightarrow> X" "y2 : A \<rightarrow> Z"
    using cfunc_prod_unique comp_type left_cart_proj_type right_cart_proj_type y_type by blast

  assume "(f \<times>\<^sub>f g) \<circ>\<^sub>c x = (f \<times>\<^sub>f g) \<circ>\<^sub>c y"
  then have "(f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>x1, x2\<rangle> = (f \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>y1, y2\<rangle>"
    using x_expand y_expand by blast
  then have "\<langle>f \<circ>\<^sub>c x1, g \<circ>\<^sub>c x2\<rangle> = \<langle>f \<circ>\<^sub>c y1, g \<circ>\<^sub>c y2\<rangle>"
    using cfunc_cross_prod_comp_cfunc_prod type_assms x1_x2_type y1_y2_type by auto
  then have "f \<circ>\<^sub>c x1 = f \<circ>\<^sub>c y1 \<and> g \<circ>\<^sub>c x2 = g \<circ>\<^sub>c y2"
    by (meson cart_prod_eq2 comp_type type_assms x1_x2_type y1_y2_type)
  then have "x1 = y1 \<and> x2 = y2"
    using cfunc_type_def f_mono g_mono monomorphism_def type_assms x1_x2_type y1_y2_type by auto
  then have "\<langle>x1, x2\<rangle> = \<langle>y1, y2\<rangle>"
    by blast
  then show "x = y"
    by (simp add: x_expand y_expand)
qed

subsection \<open>Useful Cartesian Product Permuting Functions\<close>

subsubsection \<open>Swapping a Cartesian Product\<close>

definition swap :: "cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "swap X Y = \<langle>right_cart_proj X Y, left_cart_proj X Y\<rangle>"

lemma swap_type[type_rule]: "swap X Y : X \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c X"
  unfolding swap_def by (simp add: cfunc_prod_type left_cart_proj_type right_cart_proj_type)

lemma swap_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y"
  shows "swap X Y \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>y, x\<rangle>"
proof -
  have "swap X Y \<circ>\<^sub>c \<langle>x, y\<rangle> = \<langle>right_cart_proj X Y,left_cart_proj X Y\<rangle> \<circ>\<^sub>c \<langle>x,y\<rangle>"
    unfolding swap_def by auto
  also have "... = \<langle>right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, left_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
    by (meson assms cfunc_prod_comp cfunc_prod_type left_cart_proj_type right_cart_proj_type)
  also have "... = \<langle>y, x\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  finally show ?thesis.
qed

lemma swap_cross_prod:
  assumes "x : A \<rightarrow> X" "y : B \<rightarrow> Y"
  shows "swap X Y \<circ>\<^sub>c (x \<times>\<^sub>f y) = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap A B"
proof -
  have "swap X Y \<circ>\<^sub>c (x \<times>\<^sub>f y) = swap X Y \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c right_cart_proj A B\<rangle>"
    using assms unfolding cfunc_cross_prod_def cfunc_type_def by auto
  also have "... = \<langle>y \<circ>\<^sub>c right_cart_proj A B, x \<circ>\<^sub>c left_cart_proj A B\<rangle>"
    by (meson assms comp_type left_cart_proj_type right_cart_proj_type swap_ap)
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c \<langle>right_cart_proj A B, left_cart_proj A B\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (y \<times>\<^sub>f x) \<circ>\<^sub>c swap A B"
    unfolding swap_def by auto
  finally show ?thesis.
qed

lemma swap_idempotent:
  "swap Y X \<circ>\<^sub>c swap X Y = id (X \<times>\<^sub>c Y)"
  by (metis swap_def cfunc_prod_unique id_right_unit2 id_type left_cart_proj_type
      right_cart_proj_type swap_ap)

lemma swap_mono:
  "monomorphism(swap X Y)"
  by (metis cfunc_type_def iso_imp_epi_and_monic isomorphism_def swap_idempotent swap_type)

subsubsection \<open>Permuting a Cartesian Product to Associate to the Right\<close>

definition associate_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_right X Y Z =
    \<langle>
      left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, 
      \<langle>
        right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z,
        right_cart_proj (X \<times>\<^sub>c Y) Z
      \<rangle>
    \<rangle>"

lemma associate_right_type[type_rule]: "associate_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  unfolding associate_right_def by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type)

lemma associate_right_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "associate_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, \<langle>y, z\<rangle>\<rangle>"
proof -
  have "associate_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>(left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z) \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>, 
    \<langle>(right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z) \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>, right_cart_proj (X \<times>\<^sub>c Y) Z \<circ>\<^sub>c \<langle>\<langle>x,y\<rangle>,z\<rangle>\<rangle>\<rangle>"
    by (typecheck_cfuncs, smt (verit, best) assms associate_right_def cfunc_prod_comp cfunc_prod_type)
  also have "... = \<langle>left_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, \<langle>right_cart_proj X Y \<circ>\<^sub>c \<langle>x,y\<rangle>, z\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, smt comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... =\<langle>x, \<langle>y, z\<rangle>\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  finally show ?thesis.
qed

lemma associate_right_crossprod_ap:
  assumes "x : A \<rightarrow> X" "y : B \<rightarrow> Y" "z : C \<rightarrow> Z"
  shows "associate_right X Y Z \<circ>\<^sub>c ((x \<times>\<^sub>f y) \<times>\<^sub>f z) = (x \<times>\<^sub>f (y\<times>\<^sub>f z)) \<circ>\<^sub>c  associate_right A B C"
proof-
  have "associate_right X Y Z \<circ>\<^sub>c ((x \<times>\<^sub>f y) \<times>\<^sub>f z) =
        associate_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x  \<circ>\<^sub>c left_cart_proj A B, y \<circ>\<^sub>c right_cart_proj A B\<rangle> \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C, z \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) C\<rangle>"
    using assms unfolding cfunc_cross_prod_def2 by(typecheck_cfuncs, unfold cfunc_cross_prod_def2, auto) 
  also have "... = associate_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x  \<circ>\<^sub>c left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C, y  \<circ>\<^sub>c right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C\<rangle>, z \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) C\<rangle>"
    using assms  cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = \<langle>x  \<circ>\<^sub>c left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C, \<langle>y \<circ>\<^sub>c right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C, z \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) C\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: associate_right_ap)
  also have "... = \<langle>x  \<circ>\<^sub>c left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C, (y \<times>\<^sub>f z)\<circ>\<^sub>c \<langle>right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C,right_cart_proj (A \<times>\<^sub>c B) C\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (x \<times>\<^sub>f (y\<times>\<^sub>f z)) \<circ>\<^sub>c \<langle>left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C,\<langle>right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A\<times>\<^sub>cB) C,right_cart_proj (A \<times>\<^sub>c B) C\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = (x \<times>\<^sub>f (y\<times>\<^sub>f z)) \<circ>\<^sub>c  associate_right A B C"   
    unfolding associate_right_def by auto
  finally show ?thesis.
qed

subsubsection \<open>Permuting a Cartesian Product to Associate to the Left\<close>

definition associate_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "associate_left X Y Z =
    \<langle>
      \<langle>
        left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
      \<rangle>,
      right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)
    \<rangle>"

lemma associate_left_type[type_rule]: "associate_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  unfolding associate_left_def
  by (meson cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type)

lemma associate_left_ap:
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "associate_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
proof -
  have "associate_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>  = \<langle>\<langle>left_cart_proj X (Y \<times>\<^sub>c Z),
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle> \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
        right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)  \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using assms associate_left_def cfunc_prod_comp cfunc_type_def comp_associative comp_type by (typecheck_cfuncs, auto)
  also have "... = \<langle> \<langle>left_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>,
        left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z) \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>,
        right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)  \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>\<langle>x, left_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>, right_cart_proj Y Z \<circ>\<^sub>c \<langle>y, z\<rangle>\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by (typecheck_cfuncs, auto)
  also have "... = \<langle>\<langle>x, y\<rangle>, z\<rangle>"
    using assms left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod by auto
  finally show ?thesis.
qed

lemma right_left: 
 "associate_right A B C \<circ>\<^sub>c associate_left A B C = id (A \<times>\<^sub>c (B \<times>\<^sub>c C))"
  by (typecheck_cfuncs, smt (verit, ccfv_threshold) associate_left_def associate_right_ap cfunc_prod_unique comp_type id_right_unit2 left_cart_proj_type right_cart_proj_type)

lemma left_right: 
 "associate_left A B C \<circ>\<^sub>c associate_right A B C = id ((A \<times>\<^sub>c B) \<times>\<^sub>c C)"
    by (smt associate_left_ap associate_right_def cfunc_cross_prod_def cfunc_prod_unique comp_type id_cross_prod id_domain id_left_unit2 left_cart_proj_type right_cart_proj_type)

lemma product_associates:
  "A \<times>\<^sub>c (B \<times>\<^sub>c C)  \<cong> (A \<times>\<^sub>c B) \<times>\<^sub>c C"
    by (metis associate_left_type associate_right_type cfunc_type_def is_isomorphic_def isomorphism_def left_right right_left) 

lemma associate_left_crossprod_ap:
  assumes "x : A \<rightarrow> X" "y : B \<rightarrow> Y" "z : C \<rightarrow> Z"
  shows "associate_left X Y Z \<circ>\<^sub>c (x \<times>\<^sub>f (y\<times>\<^sub>f z)) = ((x \<times>\<^sub>f y)\<times>\<^sub>f z) \<circ>\<^sub>c  associate_left A B C"
proof-
  have "associate_left X Y Z \<circ>\<^sub>c (x \<times>\<^sub>f (y\<times>\<^sub>f z)) =
        associate_left X Y Z \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj A (B\<times>\<^sub>cC), \<langle>y \<circ>\<^sub>c left_cart_proj B C, z \<circ>\<^sub>c right_cart_proj B C\<rangle> \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>"
    using assms unfolding cfunc_cross_prod_def2 by(typecheck_cfuncs, unfold cfunc_cross_prod_def2, auto) 
  also have "... = associate_left X Y Z \<circ>\<^sub>c \<langle>x \<circ>\<^sub>c left_cart_proj A (B\<times>\<^sub>cC), \<langle>y \<circ>\<^sub>c left_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC), z \<circ>\<^sub>c right_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>\<rangle>"
    using assms  cfunc_prod_comp comp_associative2 by (typecheck_cfuncs, auto)
  also have "... = \<langle>\<langle>x \<circ>\<^sub>c left_cart_proj A (B\<times>\<^sub>cC), y \<circ>\<^sub>c left_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>,z \<circ>\<^sub>c right_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: associate_left_ap)
  also have "... = \<langle>(x \<times>\<^sub>f y)\<circ>\<^sub>c \<langle> left_cart_proj A (B\<times>\<^sub>cC), left_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>,z \<circ>\<^sub>c right_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = ((x \<times>\<^sub>f y)\<times>\<^sub>f z) \<circ>\<^sub>c \<langle>\<langle>left_cart_proj A (B\<times>\<^sub>cC), left_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>,right_cart_proj B C \<circ>\<^sub>c right_cart_proj A (B\<times>\<^sub>cC)\<rangle>"
    using assms by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
  also have "... = ((x \<times>\<^sub>f y)\<times>\<^sub>f z) \<circ>\<^sub>c associate_left A B C"   
    unfolding associate_left_def by auto
  finally show ?thesis.
qed
  
subsubsection \<open>Distributing over a Cartesian Product from the Right\<close>

definition distribute_right_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_left X Y Z = 
    \<langle>left_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle>"

lemma distribute_right_left_type[type_rule]:
  "distribute_right_left X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> X \<times>\<^sub>c Z"
  unfolding distribute_right_left_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_right_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right_left X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>x, z\<rangle>"
  unfolding distribute_right_left_def 
  by (typecheck_cfuncs, smt (verit, best) assms cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

definition distribute_right_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right_right X Y Z = 
    \<langle>right_cart_proj X Y \<circ>\<^sub>c left_cart_proj (X \<times>\<^sub>c Y) Z, right_cart_proj (X \<times>\<^sub>c Y) Z\<rangle>"

lemma distribute_right_right_type[type_rule]:
  "distribute_right_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> Y \<times>\<^sub>c Z"
  unfolding distribute_right_right_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_right_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>y, z\<rangle>"
  unfolding distribute_right_right_def  
  by (typecheck_cfuncs, smt (z3) assms cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

definition distribute_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_right X Y Z = \<langle>distribute_right_left X Y Z, distribute_right_right X Y Z\<rangle>"

lemma distribute_right_type[type_rule]:
  "distribute_right X Y Z : (X \<times>\<^sub>c Y) \<times>\<^sub>c Z \<rightarrow> (X \<times>\<^sub>c Z) \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  unfolding distribute_right_def
  by (simp add: cfunc_prod_type distribute_right_left_type distribute_right_right_type)

lemma distribute_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>x, y\<rangle>, z\<rangle> = \<langle>\<langle>x, z\<rangle>, \<langle>y, z\<rangle>\<rangle>"
  using assms unfolding distribute_right_def  
  by (typecheck_cfuncs, simp add: cfunc_prod_comp distribute_right_left_ap distribute_right_right_ap)

lemma distribute_right_mono:
  "monomorphism (distribute_right X Y Z)"
proof (typecheck_cfuncs, unfold monomorphism_def3, clarify)
  fix g h A
  assume "g : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  then obtain g1 g2 g3 where g_expand: "g = \<langle>\<langle>g1, g2\<rangle>, g3\<rangle>"
      and g1_g2_g3_types: "g1 : A \<rightarrow> X" "g2 : A \<rightarrow> Y" "g3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 
  assume "h : A \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c Z"
  then obtain h1 h2 h3 where h_expand: "h = \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
      and h1_h2_h3_types: "h1 : A \<rightarrow> X" "h2 : A \<rightarrow> Y" "h3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 

  assume "distribute_right X Y Z \<circ>\<^sub>c g = distribute_right X Y Z \<circ>\<^sub>c h"
  then have "distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>g1, g2\<rangle>, g3\<rangle> = distribute_right X Y Z \<circ>\<^sub>c \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
    using g_expand h_expand by auto
  then have "\<langle>\<langle>g1, g3\<rangle>, \<langle>g2, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h3\<rangle>, \<langle>h2, h3\<rangle>\<rangle>"
    using distribute_right_ap g1_g2_g3_types h1_h2_h3_types by auto
  then have "\<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle> \<and> \<langle>g2, g3\<rangle> = \<langle>h2, h3\<rangle>"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by (typecheck_cfuncs, auto)
  then have "g1 = h1 \<and> g2 = h2 \<and> g3 = h3"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by auto
  then have "\<langle>\<langle>g1, g2\<rangle>, g3\<rangle> = \<langle>\<langle>h1, h2\<rangle>, h3\<rangle>"
    by simp
  then show "g = h"
    by (simp add: g_expand h_expand)
qed

subsubsection \<open>Distributing over a Cartesian Product from the Left\<close>

definition distribute_left_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_left X Y Z = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), left_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_left_type[type_rule]:
  "distribute_left_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Y"
  unfolding distribute_left_left_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_left_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, y\<rangle>"
  using assms distribute_left_left_def  
  by (typecheck_cfuncs, smt (z3) associate_left_ap associate_left_def cart_prod_decomp cart_prod_eq2 cfunc_prod_comp comp_associative2 distribute_left_left_def right_cart_proj_cfunc_prod right_cart_proj_type)

definition distribute_left_right :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left_right X Y Z = 
    \<langle>left_cart_proj X (Y \<times>\<^sub>c Z), right_cart_proj Y Z \<circ>\<^sub>c right_cart_proj X (Y \<times>\<^sub>c Z)\<rangle>"

lemma distribute_left_right_type[type_rule]:
  "distribute_left_right X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> X \<times>\<^sub>c Z"
  unfolding distribute_left_right_def
  using cfunc_prod_type comp_type left_cart_proj_type right_cart_proj_type by blast

lemma distribute_left_right_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left_right X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>x, z\<rangle>"
  using assms unfolding distribute_left_right_def  
  by (typecheck_cfuncs, smt (z3) cfunc_prod_comp comp_associative2 left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)

definition distribute_left :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "distribute_left X Y Z = \<langle>distribute_left_left X Y Z, distribute_left_right X Y Z\<rangle>"

lemma distribute_left_type[type_rule]:
  "distribute_left X Y Z : X \<times>\<^sub>c (Y \<times>\<^sub>c Z) \<rightarrow> (X \<times>\<^sub>c Y) \<times>\<^sub>c (X \<times>\<^sub>c Z)"
  unfolding distribute_left_def
  by (simp add: cfunc_prod_type distribute_left_left_type distribute_left_right_type)

lemma distribute_left_ap: 
  assumes "x : A \<rightarrow> X" "y : A \<rightarrow> Y" "z : A \<rightarrow> Z"
  shows "distribute_left X Y Z \<circ>\<^sub>c \<langle>x, \<langle>y, z\<rangle>\<rangle> = \<langle>\<langle>x, y\<rangle>, \<langle>x, z\<rangle>\<rangle>"
  using assms unfolding distribute_left_def 
  by (typecheck_cfuncs, simp add: cfunc_prod_comp distribute_left_left_ap distribute_left_right_ap)

lemma distribute_left_mono:
  "monomorphism (distribute_left X Y Z)"
proof (typecheck_cfuncs, unfold monomorphism_def3, clarify)
  fix g h A
  assume g_type: "g : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  then obtain g1 g2 g3 where g_expand: "g = \<langle>g1, \<langle>g2, g3\<rangle>\<rangle>"
      and g1_g2_g3_types: "g1 : A \<rightarrow> X" "g2 : A \<rightarrow> Y" "g3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 
  assume h_type: "h : A \<rightarrow> X \<times>\<^sub>c (Y \<times>\<^sub>c Z)"
  then obtain h1 h2 h3 where h_expand: "h = \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
      and h1_h2_h3_types: "h1 : A \<rightarrow> X" "h2 : A \<rightarrow> Y" "h3 : A \<rightarrow> Z"
    using cart_prod_decomp by blast 

  assume "distribute_left X Y Z \<circ>\<^sub>c g = distribute_left X Y Z \<circ>\<^sub>c h"
  then have "distribute_left X Y Z \<circ>\<^sub>c \<langle>g1, \<langle>g2, g3\<rangle>\<rangle> = distribute_left X Y Z \<circ>\<^sub>c \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
    using g_expand h_expand by auto
  then have "\<langle>\<langle>g1, g2\<rangle>, \<langle>g1, g3\<rangle>\<rangle> = \<langle>\<langle>h1, h2\<rangle>, \<langle>h1, h3\<rangle>\<rangle>"
    using distribute_left_ap g1_g2_g3_types h1_h2_h3_types by auto
  then have "\<langle>g1, g2\<rangle> = \<langle>h1, h2\<rangle> \<and> \<langle>g1, g3\<rangle> = \<langle>h1, h3\<rangle>"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by (typecheck_cfuncs, auto)
  then have "g1 = h1 \<and> g2 = h2 \<and> g3 = h3"
    using g1_g2_g3_types h1_h2_h3_types cart_prod_eq2 by auto
  then have "\<langle>g1, \<langle>g2, g3\<rangle>\<rangle> = \<langle>h1, \<langle>h2, h3\<rangle>\<rangle>"
    by simp
  then show "g = h"
    by (simp add: g_expand h_expand)
qed

subsubsection \<open>Selecting Pairs from a Pair of Pairs\<close>

definition outers :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "outers A B C D = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma outers_type[type_rule]: "outers A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c D)"
  unfolding outers_def by typecheck_cfuncs

lemma outers_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "outers A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> = \<langle>a,d\<rangle>"
proof -
  have "outers A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c,d\<rangle>\<rangle> = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>
    \<rangle>"
    unfolding outers_def  using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>left_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>a, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  finally show ?thesis.
qed

definition inners :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "inners A B C D = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma inners_type[type_rule]: "inners A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c C)"
  unfolding inners_def by typecheck_cfuncs
    
lemma inners_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "inners A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b,c\<rangle>"
proof -
  have "inners A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>,
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    unfolding inners_def using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>right_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>b, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  finally show ?thesis.
qed

definition lefts :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "lefts A B C D = \<langle>
      left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma lefts_type[type_rule]: "lefts A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (A \<times>\<^sub>c C)"
  unfolding lefts_def by typecheck_cfuncs

lemma lefts_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "lefts A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>a,c\<rangle>"
proof -
  have "lefts A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>left_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>, left_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    unfolding lefts_def using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>left_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, left_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>a, c\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
  finally show ?thesis.
qed

definition rights :: "cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cset \<Rightarrow> cfunc" where
  "rights A B C D = \<langle>
      right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D),
      right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D)
    \<rangle>"

lemma rights_type[type_rule]: "rights A B C D : (A \<times>\<^sub>c B) \<times>\<^sub>c (C \<times>\<^sub>c D) \<rightarrow> (B \<times>\<^sub>c D)"
  unfolding rights_def by typecheck_cfuncs

lemma rights_apply:
  assumes "a : Z \<rightarrow> A" "b : Z \<rightarrow> B" "c : Z \<rightarrow> C" "d : Z \<rightarrow> D"
  shows "rights A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>b,d\<rangle>"
proof -
  have "rights A B C D \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle> = \<langle>right_cart_proj A B \<circ>\<^sub>c left_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>, right_cart_proj C D \<circ>\<^sub>c right_cart_proj (A \<times>\<^sub>c B) (C \<times>\<^sub>c D) \<circ>\<^sub>c \<langle>\<langle>a,b\<rangle>, \<langle>c, d\<rangle>\<rangle>\<rangle>"
    unfolding rights_def using assms by (typecheck_cfuncs, simp add: cfunc_prod_comp comp_associative2)
  also have "... = \<langle>right_cart_proj A B \<circ>\<^sub>c \<langle>a,b\<rangle>, right_cart_proj C D \<circ>\<^sub>c \<langle>c,d\<rangle>\<rangle>"
    using assms by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod right_cart_proj_cfunc_prod)
  also have "... = \<langle>b, d\<rangle>"
    using assms by (typecheck_cfuncs, simp add: right_cart_proj_cfunc_prod)
  finally show ?thesis.
qed

end