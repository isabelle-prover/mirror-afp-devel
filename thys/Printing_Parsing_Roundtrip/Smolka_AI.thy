theory Smolka_AI
  imports Main
begin

section \<open>AI-Authored proof formalization of the roundtrip algorithm\<close>

text \<open>
  Formalization of the Smolka-Blanchette printing--parsing roundtrip algorithm for Isabelle.

  The algorithm takes a fully-typed term and selects a locally minimal and complete
  set of type annotations so the term can be unambiguously re-parsed via
  Hindley--Milner type inference.
\<close>

subsection \<open>Types and Type Substitutions\<close>

text \<open>Types are built from type variables and
  type constructors with a fixed arity (implicit in the list length).\<close>

datatype ty =
  TVar string
| TCons string "ty list"

text \<open>We define the function type constructor as a distinguished binary constructor.\<close>

definition fun_ty :: "ty \<Rightarrow> ty \<Rightarrow> ty" (infixr "\<rightarrow>" 65) where
  "fun_ty \<tau>\<^sub>1 \<tau>\<^sub>2 = TCons ''fun'' [\<tau>\<^sub>1, \<tau>\<^sub>2]"

text \<open>Type variables occurring in a type.\<close>

fun tvars_ty :: "ty \<Rightarrow> string set" where
  "tvars_ty (TVar v) = {v}"
| "tvars_ty (TCons _ ts) = \<Union>(set (map tvars_ty ts))"

text \<open>Definition (Type Substitution). A type substitution is a function
  from variable names to types. It extends homomorphically to types.\<close>

fun subst_ty :: "(string \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> ty" where
  "subst_ty \<sigma> (TVar v) = \<sigma> v"
| "subst_ty \<sigma> (TCons k ts) = TCons k (map (subst_ty \<sigma>) ts)"

text \<open>The arrow type \<open>\<tau> \<rightarrow> \<tau>\<close> is strictly larger than \<open>\<tau>\<close>,
  hence \<open>\<tau> \<rightarrow> \<tau> \<noteq> \<tau>\<close>. This is used in the minimality proof.
  The proof uses the built-in \<open>size\<close> function from the datatype package.\<close>

lemma arrow_neq_self: "\<tau> \<rightarrow> \<tau> \<noteq> \<tau>"
proof
  assume "\<tau> \<rightarrow> \<tau> = \<tau>"
  then have "size (\<tau> \<rightarrow> \<tau>) = size \<tau>" by simp
  then show False by (simp add: fun_ty_def)
qed

text \<open>Lemma (Uniqueness of Type Matching). If two substitutions agree
  when applied to a type, they agree on all type variables of that type.\<close>

lemma unique_type_match:
  "subst_ty \<sigma>\<^sub>1 \<tau> = subst_ty \<sigma>\<^sub>2 \<tau> \<Longrightarrow> \<alpha> \<in> tvars_ty \<tau> \<Longrightarrow> \<sigma>\<^sub>1 \<alpha> = \<sigma>\<^sub>2 \<alpha>"
  by (induction \<tau>) auto

text \<open>Substitution on type variables: the domain is precisely \<^term>\<open>tvars_ty \<tau>\<close>.\<close>

lemma tvars_subst_ty: "tvars_ty (subst_ty \<sigma> \<tau>) = \<Union>(tvars_ty ` \<sigma> ` tvars_ty \<tau>)"
  by (induction \<tau>) auto

lemma subst_ty_id:
  "(\<And>v. v \<in> tvars_ty \<tau> \<Longrightarrow> \<sigma> v = TVar v) \<Longrightarrow> subst_ty \<sigma> \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma subst_ty_agree:
  "(\<And>v. v \<in> tvars_ty \<tau> \<Longrightarrow> \<sigma>\<^sub>1 v = \<sigma>\<^sub>2 v) \<Longrightarrow> subst_ty \<sigma>\<^sub>1 \<tau> = subst_ty \<sigma>\<^sub>2 \<tau>"
  by (induction \<tau>) auto

lemma subst_ty_compose:
  "subst_ty \<sigma>\<^sub>1 (subst_ty \<sigma>\<^sub>2 \<tau>) = subst_ty (\<lambda>v. subst_ty \<sigma>\<^sub>1 (\<sigma>\<^sub>2 v)) \<tau>"
  by (induction \<tau>) auto

subsection \<open>Contexts\<close>

text \<open>A context is a finite partial function from variable names to types.\<close>

type_synonym ctx = "string \<rightharpoonup> ty"

text \<open>Type variables of a context.\<close>

definition tvars_ctx :: "ctx \<Rightarrow> string set" where
  "tvars_ctx \<Gamma> = \<Union>(tvars_ty ` ran \<Gamma>)"

text \<open>Applying a type substitution to a context.\<close>

definition subst_ctx :: "(string \<Rightarrow> ty) \<Rightarrow> ctx \<Rightarrow> ctx" where
  "subst_ctx \<sigma> \<Gamma> = map_option (subst_ty \<sigma>) \<circ> \<Gamma>"

lemma subst_ctx_dom [simp]: "dom (subst_ctx \<sigma> \<Gamma>) = dom \<Gamma>"
  by (auto simp: subst_ctx_def dom_def)

lemma subst_ctx_app: "x \<in> dom \<Gamma> \<Longrightarrow> subst_ctx \<sigma> \<Gamma> x = Some (subst_ty \<sigma> (the (\<Gamma> x)))"
  by (auto simp: subst_ctx_def dom_def)

lemma subst_ctx_update:
  "subst_ctx \<sigma> (\<Gamma>(x \<mapsto> \<tau>)) = (subst_ctx \<sigma> \<Gamma>)(x \<mapsto> subst_ty \<sigma> \<tau>)"
  by (auto simp: subst_ctx_def)

lemma subst_ctx_id:
  "(\<And>v. v \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma> v = TVar v) \<Longrightarrow> subst_ctx \<sigma> \<Gamma> = \<Gamma>"
  using ranI by (fastforce intro!: map_option_idI subst_ty_id simp: subst_ctx_def tvars_ctx_def)

subsection \<open>Terms\<close>

subsubsection \<open>Raw Terms\<close>

text \<open>Raw terms include type constraints and binder constraints as annotations.\<close>

datatype raw_term =
  RConst string
| RVar string
| RAbs string raw_term
| RAbsT string ty raw_term
| RApp raw_term raw_term
| RConstrain raw_term ty

text \<open>The function \<open>strip\<close> removes all constraints from a raw term.\<close>

fun strip :: "raw_term \<Rightarrow> raw_term" where
  "strip (RConst c) = RConst c"
| "strip (RVar x) = RVar x"
| "strip (RAbs x t) = RAbs x (strip t)"
| "strip (RAbsT x _ t) = RAbs x (strip t)"
| "strip (RApp t\<^sub>1 t\<^sub>2) = RApp (strip t\<^sub>1) (strip t\<^sub>2)"
| "strip (RConstrain t _) = strip t"

text \<open>A term is constraint-free if stripping is the identity.\<close>

fun constraint_free :: "raw_term \<Rightarrow> bool" where
  "constraint_free (RConst _) = True"
| "constraint_free (RVar _) = True"
| "constraint_free (RAbs _ t) = constraint_free t"
| "constraint_free (RAbsT _ _ _) = False"
| "constraint_free (RApp t\<^sub>1 t\<^sub>2) = (constraint_free t\<^sub>1 \<and> constraint_free t\<^sub>2)"
| "constraint_free (RConstrain _ _) = False"

lemma strip_idem [simp]: "strip (strip t) = strip t"
  by (induction t) auto

lemma strip_constraint_free: "constraint_free (strip t)"
  by (induction t) auto

subsubsection \<open>Annotated Terms\<close>

text \<open>Definition (Annotated Terms). Every node carries exactly one type annotation.\<close>

datatype aterm =
  AConst string ty
| AVar string ty
| AAbs string ty aterm ty
| AApp aterm aterm ty

text \<open>Definition (Type of an Annotated Term). Reads the outermost type.\<close>

fun typeof_aterm :: "aterm \<Rightarrow> ty" where
  "typeof_aterm (AConst _ \<tau>) = \<tau>"
| "typeof_aterm (AVar _ \<tau>) = \<tau>"
| "typeof_aterm (AAbs _ _ _ \<tau>') = \<tau>'"
| "typeof_aterm (AApp _ _ \<tau>) = \<tau>"

text \<open>Definition (Erasure). Strips all types from an annotated term,
  producing a constraint-free raw term.\<close>

fun erase :: "aterm \<Rightarrow> raw_term" where
  "erase (AConst c _) = RConst c"
| "erase (AVar x _) = RVar x"
| "erase (AAbs x _ a _) = RAbs x (erase a)"
| "erase (AApp a\<^sub>1 a\<^sub>2 _) = RApp (erase a\<^sub>1) (erase a\<^sub>2)"

lemma erase_constraint_free: "constraint_free (erase a)"
  by (induction a) auto

lemma strip_erase [simp]: "strip (erase a) = erase a"
  by (induction a) auto

text \<open>Definition (Type Substitution on Annotated Terms).\<close>

fun subst_aterm :: "(string \<Rightarrow> ty) \<Rightarrow> aterm \<Rightarrow> aterm" where
  "subst_aterm \<sigma> (AConst c \<tau>) = AConst c (subst_ty \<sigma> \<tau>)"
| "subst_aterm \<sigma> (AVar x \<tau>) = AVar x (subst_ty \<sigma> \<tau>)"
| "subst_aterm \<sigma> (AAbs x \<tau> a \<tau>') = AAbs x (subst_ty \<sigma> \<tau>) (subst_aterm \<sigma> a) (subst_ty \<sigma> \<tau>')"
| "subst_aterm \<sigma> (AApp a\<^sub>1 a\<^sub>2 \<tau>) = AApp (subst_aterm \<sigma> a\<^sub>1) (subst_aterm \<sigma> a\<^sub>2) (subst_ty \<sigma> \<tau>)"

text \<open>Key property: erasure is invariant under type substitution.\<close>

lemma erase_subst [simp]: "erase (subst_aterm \<sigma> a) = erase a"
  by (induction a) auto

text \<open>Key property: \<^term>\<open>typeof_aterm\<close> commutes with type substitution.\<close>

lemma typeof_subst [simp]: "typeof_aterm (subst_aterm \<sigma> a) = subst_ty \<sigma> (typeof_aterm a)"
  by (cases a) auto

text \<open>Type variables of an annotated term.\<close>

fun tvars_aterm :: "aterm \<Rightarrow> string set" where
  "tvars_aterm (AConst _ \<tau>) = tvars_ty \<tau>"
| "tvars_aterm (AVar _ \<tau>) = tvars_ty \<tau>"
| "tvars_aterm (AAbs _ \<tau> a \<tau>') = tvars_ty \<tau> \<union> tvars_aterm a \<union> tvars_ty \<tau>'"
| "tvars_aterm (AApp a\<^sub>1 a\<^sub>2 \<tau>) = tvars_aterm a\<^sub>1 \<union> tvars_aterm a\<^sub>2 \<union> tvars_ty \<tau>"

text \<open>If two substitutions agree on the type variables of a term, they give the same result.\<close>

lemma subst_aterm_agree:
  "(\<And>v. v \<in> tvars_aterm a \<Longrightarrow> \<sigma>\<^sub>1 v = \<sigma>\<^sub>2 v) \<Longrightarrow> subst_aterm \<sigma>\<^sub>1 a = subst_aterm \<sigma>\<^sub>2 a"
  by (induction a) (auto intro: subst_ty_agree)

text \<open>Converse: if two substitutions give the same annotated term, they agree on the
  type variables of that term. This is ``injectivity'' of substitution on annotated terms.\<close>

lemma subst_aterm_injective:
  "subst_aterm \<sigma>\<^sub>1 a = subst_aterm \<sigma>\<^sub>2 a \<Longrightarrow> \<alpha> \<in> tvars_aterm a \<Longrightarrow> \<sigma>\<^sub>1 \<alpha> = \<sigma>\<^sub>2 \<alpha>"
  using unique_type_match by (induction a arbitrary: \<alpha>) auto

lemma subst_ty_TVar [simp]: "subst_ty TVar \<tau> = \<tau>"
  by (induction \<tau>) (auto simp: map_idI)

lemma subst_aterm_id:
  "(\<And>v. v \<in> tvars_aterm a \<Longrightarrow> \<sigma> v = TVar v) \<Longrightarrow> subst_aterm \<sigma> a = a"
  by (induction a) (auto intro: subst_ty_id)

subsubsection \<open>Well-Typedness\<close>

text \<open>We parameterize the development by a function giving the declared type scheme
  of each constant. This is the type scheme that must be instantiated at each use site.\<close>

text \<open>An annotated term is well-typed in a context
  if each node satisfies the appropriate typing constraint.\<close>

inductive well_typed :: "(string \<Rightarrow> ty) \<Rightarrow> ctx \<Rightarrow> aterm \<Rightarrow> bool" where
  wt_const: "\<exists>\<rho>. \<tau> = subst_ty \<rho> (const_type c) \<Longrightarrow>
    well_typed const_type \<Gamma> (AConst c \<tau>)"
| wt_var: "\<Gamma> x = Some \<tau> \<Longrightarrow>
    well_typed const_type \<Gamma> (AVar x \<tau>)"
| wt_abs: "well_typed const_type (\<Gamma>(x \<mapsto> \<tau>)) a \<Longrightarrow>
    \<tau>' = \<tau> \<rightarrow> typeof_aterm a \<Longrightarrow>
    well_typed const_type \<Gamma> (AAbs x \<tau> a \<tau>')"
| wt_app: "well_typed const_type \<Gamma> a\<^sub>1 \<Longrightarrow>
    well_typed const_type \<Gamma> a\<^sub>2 \<Longrightarrow>
    typeof_aterm a\<^sub>1 = typeof_aterm a\<^sub>2 \<rightarrow> \<tau> \<Longrightarrow>
    well_typed const_type \<Gamma> (AApp a\<^sub>1 a\<^sub>2 \<tau>)"

text \<open>Lemma (Substitution Preserves Well-Typedness). If \<^term>\<open>a\<close> is well-typed in \<^term>\<open>\<Gamma>\<close>, 
  then \<^term>\<open>subst_aterm \<sigma> a\<close> is well-typed in \<^term>\<open>subst_ctx \<sigma> \<Gamma>\<close>.\<close>

lemma subst_preserves_wt:
  "well_typed ct \<Gamma> a \<Longrightarrow> well_typed ct (subst_ctx \<sigma> \<Gamma>) (subst_aterm \<sigma> a)"
proof (induction rule: well_typed.induct)
  case (wt_const \<tau> ct c \<Gamma>)
  then obtain \<rho> where "\<tau> = subst_ty \<rho> (ct c)" by auto
  then have "subst_ty \<sigma> \<tau> = subst_ty (\<lambda>v. subst_ty \<sigma> (\<rho> v)) (ct c)"
    by (simp add: subst_ty_compose)
  then show ?case by (auto intro: well_typed.wt_const)
next
  case (wt_var \<Gamma> x \<tau> ct)
  then show ?case by (auto simp: subst_ctx_def intro: well_typed.wt_var)
next
  case (wt_abs ct \<Gamma> x \<tau> a \<tau>')
  then have ih: "well_typed ct ((subst_ctx \<sigma> \<Gamma>)(x \<mapsto> subst_ty \<sigma> \<tau>)) (subst_aterm \<sigma> a)"
    using subst_ctx_update by metis
  from wt_abs.hyps(2) have "subst_ty \<sigma> \<tau>' = subst_ty \<sigma> \<tau> \<rightarrow> typeof_aterm (subst_aterm \<sigma> a)"
    by (simp add: fun_ty_def)
  with ih show ?case by (auto intro: well_typed.wt_abs)
next
  case (wt_app ct \<Gamma> a\<^sub>1 a\<^sub>2 \<tau>)
  from wt_app.hyps(3) have
    "typeof_aterm (subst_aterm \<sigma> a\<^sub>1) = typeof_aterm (subst_aterm \<sigma> a\<^sub>2) \<rightarrow> subst_ty \<sigma> \<tau>"
    by (simp add: fun_ty_def)
  with wt_app.IH show ?case by (auto intro: well_typed.wt_app)
qed

text \<open>Corollary: if \<^term>\<open>\<sigma>\<close> is the identity on \<^term>\<open>tvars_ctx \<Gamma>\<close>, then \<^term>\<open>subst_ctx \<sigma> \<Gamma> = \<Gamma>\<close>, 
  so \<^term>\<open>subst_aterm \<sigma> a\<close> is well-typed in \<^term>\<open>\<Gamma>\<close>.\<close>

corollary subst_wt_identity_ctx:
  "well_typed ct \<Gamma> a \<Longrightarrow> (\<And>v. v \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma> v = TVar v) \<Longrightarrow>
   well_typed ct \<Gamma> (subst_aterm \<sigma> a)"
  using subst_preserves_wt[of ct \<Gamma> a \<sigma>] subst_ctx_id[of \<Gamma> \<sigma>] by simp

subsection \<open>Positions and Post-Order Enumeration\<close>

text \<open>Definition (Post-Order Enumeration). For a fully annotated term \<^term>\<open>a\<close>,
  the function \<open>enum_aterm a\<close> returns a list of triples \<^term>\<open>(p, s, \<tau>)\<close>
  where \<^term>\<open>p\<close> is a position number (in post-order), \<^term>\<open>s\<close> is the raw subterm,
  and \<^term>\<open>\<tau>\<close> is the type at that position.

  The helper \<open>shift_enum k L\<close> adds \<^term>\<open>k\<close> to all position numbers in \<^term>\<open>L\<close>.\<close>

definition shift_enum :: "nat \<Rightarrow> (nat \<times> raw_term \<times> ty) list \<Rightarrow> (nat \<times> raw_term \<times> ty) list" where
  "shift_enum k L = map (\<lambda>(p, s, \<tau>). (k + p, s, \<tau>)) L"

fun enum_aterm :: "aterm \<Rightarrow> (nat \<times> raw_term \<times> ty) list" where
  "enum_aterm (AConst c \<tau>) = [(0, RConst c, \<tau>)]"
| "enum_aterm (AVar x \<tau>) = [(0, RVar x, \<tau>)]"
| "enum_aterm (AAbs x \<tau> a\<^sub>1 \<tau>') =
    (let L = enum_aterm a\<^sub>1; n = length L in
     [(0, RVar x, \<tau>)] @ shift_enum 1 L @ [(1 + n, RAbs x (erase a\<^sub>1), \<tau>')])"
| "enum_aterm (AApp a\<^sub>1 a\<^sub>2 \<tau>) =
    (let L\<^sub>1 = enum_aterm a\<^sub>1; n\<^sub>1 = length L\<^sub>1;
         L\<^sub>2 = enum_aterm a\<^sub>2; n\<^sub>2 = length L\<^sub>2 in
     L\<^sub>1 @ shift_enum n\<^sub>1 L\<^sub>2 @ [(n\<^sub>1 + n\<^sub>2, RApp (erase a\<^sub>1) (erase a\<^sub>2), \<tau>)])"

text \<open>The set of positions.\<close>

definition pos_set :: "aterm \<Rightarrow> nat set" where
  "pos_set a = fst ` set (enum_aterm a)"

text \<open>The type at a given position in the enumeration.\<close>

definition type_at_pos :: "aterm \<Rightarrow> nat \<Rightarrow> ty" where
  "type_at_pos a p = (THE \<tau>. \<exists>s. (p, s, \<tau>) \<in> set (enum_aterm a))"

text \<open>The subterm at a given position in the enumeration.\<close>

definition subterm_at_pos :: "aterm \<Rightarrow> nat \<Rightarrow> raw_term" where
  "subterm_at_pos a p = (THE s. \<exists>\<tau>. (p, s, \<tau>) \<in> set (enum_aterm a))"

subsubsection \<open>Basic Properties of Enumeration\<close>

lemma length_shift_enum [simp]: "length (shift_enum k L) = length L"
  by (simp add: shift_enum_def)

lemma set_shift_enum: "set (shift_enum k L) = (\<lambda>(p, s, \<tau>). (k + p, s, \<tau>)) ` set L"
  by (auto simp: shift_enum_def)

lemma in_shift_enum_iff:
  "(p, s, \<tau>) \<in> set (shift_enum k L) \<longleftrightarrow> (\<exists>p'. p = k + p' \<and> (p', s, \<tau>) \<in> set L)"
  by (auto simp: shift_enum_def image_iff split: prod.splits)

lemma shift_enum_shift_enum:
  "shift_enum k\<^sub>1 (shift_enum k\<^sub>2 L) = shift_enum (k\<^sub>1 + k\<^sub>2) L"
  by (induction L) (auto simp: shift_enum_def)

text \<open>The length of the enumeration equals the number of nodes in the term.
  For an annotated term, each node produces one entry, with abstractions
  additionally producing a binder position.\<close>

fun aterm_node_count :: "aterm \<Rightarrow> nat" where
  "aterm_node_count (AConst _ _) = 1"
| "aterm_node_count (AVar _ _) = 1"
| "aterm_node_count (AAbs _ _ a _) = 2 + aterm_node_count a"
| "aterm_node_count (AApp a\<^sub>1 a\<^sub>2 _) = 1 + aterm_node_count a\<^sub>1 + aterm_node_count a\<^sub>2"

lemma length_enum_aterm: "length (enum_aterm a) = aterm_node_count a"
  by (induction a) (auto simp: Let_def)

text \<open>Every annotated term has at least one position.\<close>

lemma enum_aterm_nonempty: "enum_aterm a \<noteq> []"
  by (cases a) (auto simp: Let_def)

lemma aterm_node_count_pos: "aterm_node_count a \<ge> 1"
  by (cases a) auto

subsubsection \<open>Substitution Distributes to Positions\<close>

text \<open>Lemma (Substitution Distributes to Positions).
  The enumeration of \<^term>\<open>subst_aterm \<sigma> a\<close> is obtained from the enumeration
  of \<^term>\<open>a\<close> by applying \<^term>\<open>\<sigma>\<close> to each type, leaving position numbers and
  subterms unchanged.

  We first define the operation that applies a substitution to the types in an
  enumeration list.\<close>

definition map_enum_ty :: 
  "(string \<Rightarrow> ty) \<Rightarrow> (nat \<times> raw_term \<times> ty) list \<Rightarrow> (nat \<times> raw_term \<times> ty) list" where
  "map_enum_ty \<sigma> L = map (\<lambda>(p, s, \<tau>). (p, s, subst_ty \<sigma> \<tau>)) L"

lemma length_map_enum_ty [simp]: "length (map_enum_ty \<sigma> L) = length L"
  by (simp add: map_enum_ty_def)

lemma map_enum_ty_shift: "map_enum_ty \<sigma> (shift_enum k L) = shift_enum k (map_enum_ty \<sigma> L)"
  by (induction L) (auto simp: map_enum_ty_def shift_enum_def)

lemma map_enum_ty_append: "map_enum_ty \<sigma> (L\<^sub>1 @ L\<^sub>2) = map_enum_ty \<sigma> L\<^sub>1 @ map_enum_ty \<sigma> L\<^sub>2"
  by (simp add: map_enum_ty_def)

text \<open>The main lemma: the enumeration commutes with type substitution.\<close>

lemma enum_subst_aterm:
  "enum_aterm (subst_aterm \<sigma> a) = map_enum_ty \<sigma> (enum_aterm a)"
  by (induction a) (auto simp: map_enum_ty_def shift_enum_def Let_def split: prod.splits)

corollary type_at_pos_subst_iff:
  "(p, s, \<tau>') \<in> set (enum_aterm (subst_aterm \<sigma> a)) \<longleftrightarrow>
   (\<exists>\<tau>. (p, s, \<tau>) \<in> set (enum_aterm a) \<and> \<tau>' = subst_ty \<sigma> \<tau>)"
  by (auto simp: enum_subst_aterm map_enum_ty_def image_iff split: prod.splits)

corollary type_at_pos_subst:
  "(p, s, \<tau>) \<in> set (enum_aterm a) \<Longrightarrow> (p, s, subst_ty \<sigma> \<tau>) \<in> set (enum_aterm (subst_aterm \<sigma> a))"
  using type_at_pos_subst_iff by auto

text \<open>The node count is invariant under type substitution.\<close>

lemma aterm_node_count_subst [simp]:
  "aterm_node_count (subst_aterm \<sigma> a) = aterm_node_count a"
  by (induction a) auto

text \<open>The position set is invariant under type substitution,
  and more generally, is the same for any two terms with the same erasure.
  We prove the substitution case first.\<close>

lemma pos_set_subst [simp]: "pos_set (subst_aterm \<sigma> a) = pos_set a"
  unfolding pos_set_def
  by (force simp: map_enum_ty_def enum_subst_aterm)

text \<open>All type variables of \<^term>\<open>a\<close> appear in some type annotation at a position.\<close>

lemma tvars_aterm_subset_enum:
  "\<alpha> \<in> tvars_aterm a \<Longrightarrow> \<exists>p s \<tau>. (p, s, \<tau>) \<in> set (enum_aterm a) \<and> \<alpha> \<in> tvars_ty \<tau>"
  by (induction a) (auto simp: Let_def in_shift_enum_iff)

text \<open>Converse: every type at an enumeration position contributes to the term's type variables.\<close>

lemma enum_tvars_subset_aterm:
  "(p, s, \<tau>) \<in> set (enum_aterm a) \<Longrightarrow> tvars_ty \<tau> \<subseteq> tvars_aterm a"
  by (induction a arbitrary: p s \<tau>) (fastforce simp: Let_def in_shift_enum_iff)+

subsubsection \<open>Distinctness and Range of Position Numbers\<close>

text \<open>Position numbers in the enumeration form a contiguous range starting from 0.
  This gives distinctness of positions as an immediate corollary.\<close>

lemma map_fst_shift_enum: "map fst (shift_enum k L) = map ((+) k) (map fst L)"
  by (induction L) (auto simp: shift_enum_def)

lemma map_fst_enum_aterm: "map fst (enum_aterm a) = [0..<aterm_node_count a]"
  using upt_add_eq_append[symmetric] map_add_upt
  by (induction a) 
    (auto simp: upt_conv_Cons Let_def map_fst_shift_enum length_enum_aterm add.commute)
 
text \<open>Corollary: position numbers are distinct.\<close>

lemma distinct_enum_fst: "distinct (map fst (enum_aterm a))"
  by (simp add: map_fst_enum_aterm)

text \<open>Corollary: the position set is exactly the range \<^term>\<open>{0..<aterm_node_count a}\<close>.\<close>

lemma pos_set_range: "pos_set a = {0..<aterm_node_count a}"
  unfolding pos_set_def
  by (metis map_fst_enum_aterm set_map set_upt)

text \<open>A useful corollary: if \<^term>\<open>(p, s, \<tau>)\<close> and \<^term>\<open>(p, s', \<tau>')\<close> are both
  in the enumeration, then \<^term>\<open>s = s'\<close> and \<^term>\<open>\<tau> = \<tau>'\<close> (positions are unique keys).\<close>

lemma enum_aterm_unique:
  assumes "(p, s, \<tau>) \<in> set (enum_aterm a)" "(p, s', \<tau>') \<in> set (enum_aterm a)"
  shows "s = s'" "\<tau> = \<tau>'"
  using assms eq_key_imp_eq_value distinct_enum_fst 
  by fastforce+

text \<open>Note: The coverage lemma is proved below in
  \<open>annotation_problem\<close> locale as \<open>coverage_initial\<close>. The locale
  instantiation connecting the reverse-greedy algorithm to \<open>annotation_selection\<close>
  is also done below via the \<open>rg\<close> interpretation.\<close>

subsection \<open>The Annotation Algorithm\<close>

subsubsection \<open>Type Inference Assumption\<close>

text \<open>Assumption (Type Inference). We work in a locale that fixes:
  - \<^term>\<open>const_type\<close>: the type scheme of each constant
  - \<^term>\<open>\<Gamma>\<close>: a fixed context
  - \<^term>\<open>a\<close>: a fully annotated, well-typed term in \<^term>\<open>\<Gamma>\<close>
  - \<^term>\<open>a_star\<close>: the principal typing (generalized term)
  - \<^term>\<open>\<sigma>\<close>: the matching substitution with \<^term>\<open>\<sigma> a_star = a\<close>:\<close>

locale annotation_problem =
  fixes const_type :: "string \<Rightarrow> ty"
    and \<Gamma> :: ctx
    and a :: aterm
    and a_star :: aterm
    and \<sigma> :: "string \<Rightarrow> ty"
  assumes a_wt: "well_typed const_type \<Gamma> a"
    and a_star_wt: "well_typed const_type \<Gamma> a_star"
    and same_erasure: "erase a_star = erase a"
    and matching: "subst_aterm \<sigma> a_star = a"
    and freshness: "\<And>\<alpha>. \<alpha> \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma> \<alpha> = TVar \<alpha>"
begin

text \<open>Definition (Inference Variables). The type variables introduced by
  inference that are not present in the context.\<close>

definition V :: "string set" where
  "V = tvars_aterm a_star - tvars_ctx \<Gamma>"

text \<open>Definition (Key). The inference variables visible at a position.
  We define \<open>key p\<close> as the set of inference variables that appear in any type
  annotation at position \<^term>\<open>p\<close> in the enumeration of \<^term>\<open>a_star\<close>, intersected with \<^term>\<open>V\<close>.
  This avoids the need to show that position numbers are unique in the
  enumeration.\<close>

definition key :: "nat \<Rightarrow> string set" where
  "key p = {\<alpha>. \<exists>s \<tau>. (p, s, \<tau>) \<in> set (enum_aterm a_star) \<and> \<alpha> \<in> tvars_ty \<tau>} \<inter> V"

text \<open>The \<^term>\<open>\<sigma>\<close> is the identity on \<^term>\<open>tvars_ctx \<Gamma>\<close>, hence moves only
  variables in \<^term>\<open>V\<close>.\<close>

lemma sigma_id_on_ctx: "\<alpha> \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma> \<alpha> = TVar \<alpha>"
  using freshness by simp

text \<open>Positions of \<^term>\<open>a_star\<close> and \<^term>\<open>a\<close> coincide.\<close>

lemma pos_set_eq: "pos_set a = pos_set a_star"
  using matching pos_set_subst[of \<sigma> a_star] by simp

text \<open>Lemma (Coverage). Every inference variable appears in the key of some position.
  This follows directly from the fact that every type variable of \<^term>\<open>a_star\<close> appears at some
  position in the enumeration, and \<^term>\<open>V\<close> is a subset of \<^term>\<open>tvars_aterm a_star\<close>.\<close>

lemma coverage_initial:
  assumes "\<alpha> \<in> V"
  shows "\<exists>p \<in> pos_set a_star. \<alpha> \<in> key p"
  using assms tvars_aterm_subset_enum unfolding pos_set_def key_def V_def by force

text \<open>Consistency of a term \<^term>\<open>a'\<close> with annotations at a set of positions \<^term>\<open>P'\<close>:
  for every position \<^term>\<open>p \<in> P'\<close>, the type at position \<^term>\<open>p\<close> in \<^term>\<open>a'\<close> agrees with
  the type at position \<^term>\<open>p\<close> in \<^term>\<open>a\<close> (i.e., with \<^term>\<open>subst_ty \<sigma> \<tau>\<close> where
  \<^term>\<open>\<tau>\<close> is the type at position \<^term>\<open>p\<close> in \<^term>\<open>a_star\<close>).

  This directly follows the paper's definition: since \<^term>\<open>erase a' = erase a_star\<close>,
  position sets coincide, and consistency means that for each \<^term>\<open>p \<in> P'\<close> the
  type at position \<^term>\<open>p\<close> in \<^term>\<open>a'\<close> equals \<^term>\<open>subst_ty \<sigma> \<tau>\<close> where
  \<^term>\<open>(p, s, \<tau>) \<in> set (enum_aterm a_star)\<close>.\<close>

definition consistent_with :: "aterm \<Rightarrow> nat set \<Rightarrow> bool" where
  "consistent_with a' P' \<equiv>
    \<forall>p s \<tau>. p \<in> P' \<longrightarrow> (p, s, \<tau>) \<in> set (enum_aterm a_star) \<longrightarrow>
      (\<exists>\<tau>'. (p, s, \<tau>') \<in> set (enum_aterm a') \<and> \<tau>' = subst_ty \<sigma> \<tau>)"

lemma consistent_withI:
  "(\<And>p s \<tau>. p \<in> P' \<Longrightarrow> (p, s, \<tau>) \<in> set (enum_aterm a_star) \<Longrightarrow>
      \<exists>\<tau>'. (p, s, \<tau>') \<in> set (enum_aterm a') \<and> \<tau>' = subst_ty \<sigma> \<tau>)
   \<Longrightarrow> consistent_with a' P'"
  unfolding consistent_with_def by auto

lemma consistent_withE:
  assumes "consistent_with a' P'" "p \<in> P'" "(p, s, \<tau>) \<in> set (enum_aterm a_star)"
  obtains \<tau>' where "(p, s, \<tau>') \<in> set (enum_aterm a')" "\<tau>' = subst_ty \<sigma> \<tau>"
  using assms unfolding consistent_with_def by auto

lemma consistent_with_mono:
  "consistent_with a' P' \<Longrightarrow> Q \<subseteq> P' \<Longrightarrow> consistent_with a' Q"
  unfolding consistent_with_def by auto

text \<open>When \<^term>\<open>a'\<close> is a substitution instance of \<^term>\<open>a_star\<close>, i.e.,
  \<^term>\<open>a' = subst_aterm \<sigma>' a_star\<close>, consistency at \<^term>\<open>P'\<close> reduces to
  type agreement: \<^term>\<open>subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>\<close> for all positions
  \<^term>\<open>p \<in> P'\<close>. This is the form used in the completeness proof.\<close>

lemma consistent_with_substI:
  assumes "\<And>p s \<tau>. p \<in> P' \<Longrightarrow> (p, s, \<tau>) \<in> set (enum_aterm a_star) \<Longrightarrow>
             subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>"
  shows "consistent_with (subst_aterm \<sigma>' a_star) P'"
proof (rule consistent_withI)
  fix p s \<tau>
  assume "p \<in> P'" "(p, s, \<tau>) \<in> set (enum_aterm a_star)"
  then have "subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>" using assms by auto
  moreover have "(p, s, subst_ty \<sigma>' \<tau>) \<in> set (enum_aterm (subst_aterm \<sigma>' a_star))"
    using \<open>(p, s, \<tau>) \<in> set (enum_aterm a_star)\<close> type_at_pos_subst by auto
  ultimately show "\<exists>\<tau>'. (p, s, \<tau>') \<in> set (enum_aterm (subst_aterm \<sigma>' a_star)) \<and> \<tau>' = subst_ty \<sigma> \<tau>"
    by auto
qed

lemma consistent_with_substD:
  assumes "consistent_with (subst_aterm \<sigma>' a_star) P'"
    "p \<in> P'" "(p, s, \<tau>) \<in> set (enum_aterm a_star)"
  shows "subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>"
  using consistent_withE[OF assms] assms enum_aterm_unique type_at_pos_subst
  by metis

end

text \<open>An annotation selection extends the annotation problem with a finite set of
  positions \<^term>\<open>P\<close> that covers all inference variables and where each position has a witness
  variable (a variable in its key not appearing in any other position's key in \<^term>\<open>P\<close>).
  We separate the proof of the main theorems from the algorithm that produces \<^term>\<open>P\<close>.\<close>

locale annotation_selection = annotation_problem +
  fixes P :: "nat set"
  assumes P_subset: "P \<subseteq> pos_set a_star"
    and coverage: "\<Union>(key ` P) = V"
    and witness: "\<And>p. p \<in> P \<Longrightarrow> \<exists>\<alpha> \<in> key p. \<forall>p' \<in> P. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'"
begin

text \<open>Every inference variable appears in the key of some kept position.\<close>

lemma coverage_mem: "\<alpha> \<in> V \<Longrightarrow> \<exists>p \<in> P. \<alpha> \<in> key p"
  using coverage by blast

subsubsection \<open>Annotations determine the substitution\<close>

lemma sigma_agree_on_V:
  assumes agreement: "\<And>p s \<tau>. p \<in> P \<Longrightarrow> (p, s, \<tau>) \<in> set (enum_aterm a_star) \<Longrightarrow> subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>"
  and \<open>\<alpha> \<in> V\<close>
shows "\<sigma>' \<alpha> = \<sigma> \<alpha>"
proof -
  obtain p where "p \<in> P" "\<alpha> \<in> key p" using coverage_mem \<open>\<alpha> \<in> V\<close> by blast
  from \<open>\<alpha> \<in> key p\<close> obtain s \<tau> where
    mem: "(p, s, \<tau>) \<in> set (enum_aterm a_star)" and var: "\<alpha> \<in> tvars_ty \<tau>"
    unfolding key_def by auto
  from \<open>p \<in> P\<close> mem have "subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>" using agreement by auto
  with var show "\<sigma>' \<alpha> = \<sigma> \<alpha>" using unique_type_match by blast
qed

text \<open>The main result:\<close>

lemma annotations_determine_subst:
  assumes agreement: "\<And>p s \<tau>. p \<in> P \<Longrightarrow> (p, s, \<tau>) \<in> set (enum_aterm a_star) \<Longrightarrow>
                    subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>"
    and fresh': "\<And>\<alpha>. \<alpha> \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma>' \<alpha> = TVar \<alpha>"
  shows "subst_aterm \<sigma>' a_star = a"
proof -
  text \<open>We show \<^term>\<open>\<sigma>' = \<sigma>\<close> on \<^term>\<open>tvars_aterm a_star\<close>, then conclude
    by @{thm subst_aterm_agree} and @{thm matching}.\<close>
  have agree: "\<sigma>' \<alpha> = \<sigma> \<alpha>" if "\<alpha> \<in> tvars_aterm a_star" for \<alpha>
  proof (cases "\<alpha> \<in> V")
    case True
    then show ?thesis
      using sigma_agree_on_V[OF agreement] by simp
  next
    case False
    with that have "\<alpha> \<in> tvars_ctx \<Gamma>" unfolding V_def by auto
    then have "\<sigma>' \<alpha> = TVar \<alpha>" using fresh' by auto
    moreover have "\<sigma> \<alpha> = TVar \<alpha>" using \<open>\<alpha> \<in> tvars_ctx \<Gamma>\<close> freshness by auto
    ultimately show ?thesis by simp
  qed
  have "subst_aterm \<sigma>' a_star = subst_aterm \<sigma> a_star"
    by (intro subst_aterm_agree agree)
  also have "... = a" using matching by simp
  finally show ?thesis .
qed

subsubsection \<open>Completeness\<close>

text \<open>Theorem (Completeness). Any well-typed \<^term>\<open>a'\<close> with
  \<^term>\<open>erase a' = erase a\<close> and consistent with the constraints at \<^term>\<open>P\<close> satisfies \<open>a' = a\<close>.

  The principality assumption gives: any well-typed term with the same erasure
  is a substitution instance of \<^term>\<open>a_star\<close>, where the substitution is identity on
  context variables.\<close>

theorem completeness:
  assumes a'_wt: "well_typed const_type \<Gamma> a'"
    and a'_erase: "erase a' = erase a"
    and principality: "\<exists>\<sigma>'. subst_aterm \<sigma>' a_star = a'
                          \<and> (\<forall>\<alpha> \<in> tvars_ctx \<Gamma>. \<sigma>' \<alpha> = TVar \<alpha>)"
    and consist: "consistent_with a' P"
  shows "a' = a"
proof -
  from principality obtain \<sigma>' where
    inst: "subst_aterm \<sigma>' a_star = a'" and
    fresh': "\<forall>\<alpha> \<in> tvars_ctx \<Gamma>. \<sigma>' \<alpha> = TVar \<alpha>"
    by blast
  have "a' = subst_aterm \<sigma>' a_star" using inst by simp
  also have "... = a"
  proof (rule annotations_determine_subst)
    fix p s \<tau>
    assume "p \<in> P" "(p, s, \<tau>) \<in> set (enum_aterm a_star)"
    then show "subst_ty \<sigma>' \<tau> = subst_ty \<sigma> \<tau>"
      using consistent_with_substD[OF consist[folded inst] \<open>p \<in> P\<close> \<open>(p, s, \<tau>) \<in> set (enum_aterm a_star)\<close>] by auto
  next
    fix \<alpha>
    assume "\<alpha> \<in> tvars_ctx \<Gamma>"
    then show "\<sigma>' \<alpha> = TVar \<alpha>" using fresh' by auto
  qed
  finally show "a' = a" .
qed

subsubsection \<open>Local Minimality\<close>

text \<open>Theorem (Local Minimality). For every \<^term>\<open>p \<in> P\<close>, removing the annotation
  at position \<^term>\<open>p\<close> makes the typing non-unique: there exists \<^term>\<open>a'\<close> different from \<^term>\<open>a\<close>
  that is well-typed in \<open>\<Gamma>\<close> with \<^term>\<open>erase a' = erase a\<close> and consistent with
  the annotations at \<^term>\<open>P - {p}\<close>.\<close>

theorem local_minimality:
  assumes "p \<in> P"
  shows "\<exists>a'. a' \<noteq> a
    \<and> well_typed const_type \<Gamma> a'
    \<and> erase a' = erase a
    \<and> consistent_with a' (P - {p})"
proof -
  text \<open>Step 1: Obtain witness variable.\<close>
  from witness[OF \<open>p \<in> P\<close>] obtain \<alpha> where
    \<alpha>_in_key: "\<alpha> \<in> key p" and
    \<alpha>_unique: "\<forall>p' \<in> P. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'"
    by blast

  text \<open>Step 2: Define the altered substitution.\<close>
  define \<sigma>_star where "\<sigma>_star = (\<lambda>v. if v = \<alpha> then \<sigma> \<alpha> \<rightarrow> \<sigma> \<alpha> else \<sigma> v)"

  text \<open>Step 3: Define \<open>a'\<close> and show it satisfies all four properties.\<close>
  define a' where "a' = subst_aterm \<sigma>_star a_star"

  text \<open>Property 1: \<^term>\<open>a'\<close> differs from \<^term>\<open>a\<close>.\<close>
  have \<sigma>_star_diff: "\<sigma>_star \<alpha> \<noteq> \<sigma> \<alpha>"
    unfolding \<sigma>_star_def using arrow_neq_self by simp

  have "\<alpha> \<in> V" using \<alpha>_in_key unfolding key_def by auto
  then have "\<alpha> \<in> tvars_aterm a_star" unfolding V_def by auto

  have "a' \<noteq> a"
  proof
    assume "a' = a"
    then have "subst_aterm \<sigma>_star a_star = subst_aterm \<sigma> a_star" using matching a'_def by simp
    then have "\<sigma>_star \<alpha> = \<sigma> \<alpha>"
      using \<open>\<alpha> \<in> tvars_aterm a_star\<close> subst_aterm_injective by blast
    with \<sigma>_star_diff show False by contradiction
  qed

  text \<open>Property 2: \<^term>\<open>a'\<close> is well-typed.\<close>
  have fresh_star: "\<alpha>' \<in> tvars_ctx \<Gamma> \<Longrightarrow> \<sigma>_star \<alpha>' = TVar \<alpha>'" for \<alpha>'
  proof -
    assume "\<alpha>' \<in> tvars_ctx \<Gamma>"
    then have "\<alpha>' \<notin> V" unfolding V_def by auto
    then have "\<alpha>' \<noteq> \<alpha>" using \<open>\<alpha> \<in> V\<close> by auto
    then have "\<sigma>_star \<alpha>' = \<sigma> \<alpha>'" unfolding \<sigma>_star_def by simp
    also have "... = TVar \<alpha>'" using \<open>\<alpha>' \<in> tvars_ctx \<Gamma>\<close> freshness by auto
    finally show "\<sigma>_star \<alpha>' = TVar \<alpha>'" .
  qed
  have "well_typed const_type \<Gamma> a'"
    unfolding a'_def using subst_wt_identity_ctx[OF a_star_wt fresh_star] .

  text \<open>Property 3: \<^term>\<open>erase a' = erase a\<close>.\<close>
  have "erase a' = erase a"
    unfolding a'_def using erase_subst same_erasure by simp

  text \<open>Property 4: \<^term>\<open>a'\<close> is consistent with \<^term>\<open>P - {p}\<close>.\<close>
  have consistent_minus_p: "consistent_with a' (P - {p})"
    unfolding a'_def
  proof (rule consistent_with_substI)
    fix p' s \<tau>
    assume "p' \<in> P - {p}" "(p', s, \<tau>) \<in> set (enum_aterm a_star)"
    then have "p' \<in> P" "p' \<noteq> p" by auto
    text \<open>Step 1: \<^term>\<open>\<alpha>\<close> is not in \<^term>\<open>tvars_ty \<tau>\<close>.\<close>
    have "\<alpha> \<notin> tvars_ty \<tau>"
    proof
      assume "\<alpha> \<in> tvars_ty \<tau>"
      then have "\<alpha> \<in> key p'"
        using \<open>(p', s, \<tau>) \<in> set (enum_aterm a_star)\<close> \<open>\<alpha> \<in> V\<close>
        unfolding key_def by auto
      with \<alpha>_unique \<open>p' \<in> P\<close> \<open>p' \<noteq> p\<close> show False by auto
    qed
    text \<open>Step 2: \<^term>\<open>\<sigma>_star = \<sigma>\<close> on \<^term>\<open>tvars_ty \<tau>\<close>.\<close>
    have "\<sigma>_star \<beta> = \<sigma> \<beta>" if "\<beta> \<in> tvars_ty \<tau>" for \<beta>
    proof -
      from that \<open>\<alpha> \<notin> tvars_ty \<tau>\<close> have "\<beta> \<noteq> \<alpha>" by auto
      then show ?thesis unfolding \<sigma>_star_def by simp
    qed
    then show "subst_ty \<sigma>_star \<tau> = subst_ty \<sigma> \<tau>"
      by (rule subst_ty_agree)
  qed

  from \<open>a' \<noteq> a\<close> \<open>well_typed const_type \<Gamma> a'\<close> \<open>erase a' = erase a\<close> consistent_minus_p
  show ?thesis by blast
qed

end

subsection \<open>Annotation Insertion\<close>

text \<open>Definition (Annotation Insertion).
  Given the matching substitution \<^term>\<open>\<sigma>\<close>, the generalized term \<^term>\<open>a_star\<close>,
  the selected positions \<^term>\<open>P\<close>, and a starting position counter \<^term>\<open>k\<close>,
  the function \<^term>\<open>ins\<close> traverses the raw term and the annotated term in lockstep,
  inserting type constraints at positions in \<^term>\<open>P\<close>.

  Returns a pair (annotated raw term, number of positions traversed).\<close>

fun ins :: "(string \<Rightarrow> ty) \<Rightarrow> aterm \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> raw_term \<times> nat" where
  "ins \<sigma> (AConst c \<tau>) P k =
    (if k \<in> P then RConstrain (RConst c) (subst_ty \<sigma> \<tau>) else RConst c, 1)"
| "ins \<sigma> (AVar x \<tau>) P k =
    (if k \<in> P then RConstrain (RVar x) (subst_ty \<sigma> \<tau>) else RVar x, 1)"
| "ins \<sigma> (AAbs x \<tau> a\<^sub>1 \<tau>') P k =
    (let (t\<^sub>1', n\<^sub>1) = ins \<sigma> a\<^sub>1 P (k + 1);
         t_binder = (if k \<in> P then RAbsT x (subst_ty \<sigma> \<tau>) t\<^sub>1'
                     else RAbs x t\<^sub>1');
         t' = (if k + 1 + n\<^sub>1 \<in> P then RConstrain t_binder (subst_ty \<sigma> \<tau>')
               else t_binder)
     in (t', n\<^sub>1 + 2))"
| "ins \<sigma> (AApp a\<^sub>1 a\<^sub>2 \<tau>) P k =
    (let (t\<^sub>1', n\<^sub>1) = ins \<sigma> a\<^sub>1 P k;
         (t\<^sub>2', n\<^sub>2) = ins \<sigma> a\<^sub>2 P (k + n\<^sub>1);
         t_app = RApp t\<^sub>1' t\<^sub>2';
         t' = (if k + n\<^sub>1 + n\<^sub>2 \<in> P then RConstrain t_app (subst_ty \<sigma> \<tau>)
               else t_app)
     in (t', n\<^sub>1 + n\<^sub>2 + 1))"

text \<open>The top-level annotation function.\<close>

definition annotate :: "(string \<Rightarrow> ty) \<Rightarrow> aterm \<Rightarrow> nat set \<Rightarrow> raw_term" where
  "annotate \<sigma> a_star P = fst (ins \<sigma> a_star P 0)"

text \<open>The number of positions traversed equals the node count.\<close>

lemma ins_count: "snd (ins \<sigma> a P k) = aterm_node_count a"
  by (induction a arbitrary: k) (auto simp: Let_def case_prod_unfold)

text \<open>Stripping constraints from the output of ins recovers the erasure.\<close>

lemma strip_ins: "strip (fst (ins \<sigma> a P k)) = erase a"
  by (induction a arbitrary: k) (auto simp: Let_def case_prod_unfold)

text \<open>Corollary: annotate preserves the raw term under stripping.\<close>

corollary strip_annotate: "strip (annotate \<sigma> a P) = erase a"
  unfolding annotate_def using strip_ins by simp

subsection \<open>The Reverse-Greedy Algorithm\<close>

text \<open>Definition (Reverse-Greedy Selection).
  The algorithm processes candidate positions in decreasing cost order.
  A position is dropped if every variable in its key has count \<open>> 1\<close> (i.e.,
  is covered by at least one other remaining candidate); otherwise it is kept.

  We model the algorithm as a fold over the candidate list (sorted by decreasing cost).
  The state is a count function tracking how many undropped candidates cover each variable.
  
  The fold processes from head (highest cost) to tail (lowest cost).
  When a position is kept, the count is unchanged.
  When a position is dropped, the count is decremented for each variable in its key.\<close>

text \<open>One step: a position with key \<^term>\<open>K\<close> is kept iff some variable in \<^term>\<open>K\<close> has count \<open>\<le> 1\<close>.\<close>

definition rg_keep :: "(string \<Rightarrow> nat) \<Rightarrow> string set \<Rightarrow> bool" where
  "rg_keep cnt K = (\<exists>\<alpha> \<in> K. cnt \<alpha> \<le> 1)"

text \<open>The fold: processes a list of (position, key) pairs. Returns (kept set, final count).\<close>

fun rg_fold :: "(nat \<times> string set) list \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> nat set \<times> (string \<Rightarrow> nat)" where
  "rg_fold [] cnt = ({}, cnt)"
| "rg_fold ((p, K) # rest) cnt =
    (if rg_keep cnt K then
       let (P', cnt') = rg_fold rest cnt in (insert p P', cnt')
     else
       let cnt' = (\<lambda>\<alpha>. if \<alpha> \<in> K then cnt \<alpha> - 1 else cnt \<alpha>) in
       let (P', cnt'') = rg_fold rest cnt' in (P', cnt''))"

text \<open>Initialize the count for each variable.\<close>

definition init_count :: "(nat \<times> string set) list \<Rightarrow> string \<Rightarrow> nat" where
  "init_count cands \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) cands)"

text \<open>The full algorithm.\<close>

definition reverse_greedy :: "(nat \<times> string set) list \<Rightarrow> nat set" where
  "reverse_greedy cands = fst (rg_fold cands (init_count cands))"

subsubsection \<open>Basic Properties of the Fold\<close>

text \<open>The kept set is a subset of the candidates.\<close>

lemma rg_fold_subset: "fst (rg_fold cands cnt) \<subseteq> fst ` set cands"
  by (induction cands arbitrary: cnt) (fastforce split: if_splits simp: case_prod_unfold Let_def)+

text \<open>If a variable is not in any candidate's key, the count is unchanged by the fold.\<close>

lemma rg_fold_cnt_unchanged:
  "\<forall>(p, K) \<in> set cands. \<alpha> \<notin> K \<Longrightarrow> snd (rg_fold cands cnt) \<alpha> = cnt \<alpha>"
  by (induction cands arbitrary: cnt) (auto simp: case_prod_unfold Let_def)

text \<open>The count never increases during the fold.\<close>

lemma rg_fold_cnt_mono: "snd (rg_fold cands cnt) \<alpha> \<le> cnt \<alpha>"
proof (induction cands arbitrary: cnt) 
  case (Cons pc rest)
  thus ?case
    using order.trans[OF Cons]
    by (cases pc) (auto simp: Let_def case_prod_unfold)
qed simp

text \<open>If no kept position has \<^term>\<open>\<alpha>\<close> in its key, then the final count for \<^term>\<open>\<alpha>\<close> equals \<^term>\<open>0\<close>
  (assuming the initial count equals the number of candidates covering \<^term>\<open>\<alpha>\<close>).\<close>

lemma rg_fold_no_kept_zero:
  assumes no_kept: "\<forall>p K. (p, K) \<in> set cands \<longrightarrow> \<alpha> \<in> K \<longrightarrow> p \<notin> fst (rg_fold cands cnt)"
    and cnt_eq: "cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) cands)"
  shows "snd (rg_fold cands cnt) \<alpha> = 0"
  using assms
  by (induction cands arbitrary: cnt) (auto simp: case_prod_unfold Let_def)

subsubsection \<open>Coverage\<close>

text \<open>Lemma (Reverse-Greedy Preserves Full Coverage).
  The key invariant: the fold maintains \<^term>\<open>cnt \<alpha> \<ge> 1\<close> for every \<^term>\<open>\<alpha>\<close>
  that appears in some candidate's key. This is because:
  - At a keep step: count is unchanged (passes to recursive call as-is).
  - At a drop step: we only drop when all counts in \<open>key p\<close> are \<open>> 1\<close>, so after
    decrementing they are \<open>\<ge> 1\<close>. For variables NOT in \<open>key p\<close>, the count is unchanged.

  At termination, \<^term>\<open>cnt \<alpha> \<ge> 1\<close> means at least one undropped candidate covers
  \<^term>\<open>\<alpha>\<close>. But there are no more candidates to process, so every undropped candidate
  is a kept position. Hence \<^term>\<open>\<alpha>\<close> is covered by a kept position.

  The formal proof combines this invariant with the fact that the final count equals
  the number of kept positions covering \<^term>\<open>\<alpha>\<close>.\<close>

text \<open>The key invariant: if all counts are non-zero, they remain non-zero after the fold.
  This is because a position is only dropped when all variables in its key have count \<open>> 1\<close>.\<close>

lemma rg_fold_preserves_ge1:
  assumes "\<And>\<alpha>. cnt \<alpha> \<ge> 1"
  shows "snd (rg_fold cands cnt) \<alpha> \<ge> 1"
  using assms
proof (induction cands arbitrary: cnt)
next
  case (Cons pc rest)
  thus ?case
    by (cases pc) (fastforce simp: case_prod_unfold Let_def rg_keep_def intro!: Cons[simplified])
qed simp

text \<open>The fold result depends only on the count values for variables in candidate keys.\<close>

lemma rg_fold_cnt_agree:
  assumes "\<forall>\<alpha>. (\<exists>(p, K) \<in> set cands. \<alpha> \<in> K) \<longrightarrow> cnt1 \<alpha> = cnt2 \<alpha>"
  shows "fst (rg_fold cands cnt1) = fst (rg_fold cands cnt2)"
    and "\<forall>\<alpha>. (\<exists>(p, K) \<in> set cands. \<alpha> \<in> K) \<longrightarrow> 
           snd (rg_fold cands cnt1) \<alpha> = snd (rg_fold cands cnt2) \<alpha>"
proof -
  have both: "fst (rg_fold cands cnt1) = fst (rg_fold cands cnt2) \<and>
    (\<forall>\<alpha>. (\<exists>(p, K) \<in> set cands. \<alpha> \<in> K) \<longrightarrow> 
           snd (rg_fold cands cnt1) \<alpha> = snd (rg_fold cands cnt2) \<alpha>)"
    using assms
  proof (induction cands arbitrary: cnt1 cnt2)
    case Nil then show ?case by simp
next
  case (Cons pc rest)
  obtain p K where [simp]: "pc = (p, K)" by (cases pc)
  have key_eq: "\<forall>\<alpha> \<in> K. cnt1 \<alpha> = cnt2 \<alpha>"
    using Cons.prems by auto
  then have keep_eq: "rg_keep cnt1 K = rg_keep cnt2 K"
    unfolding rg_keep_def by auto
  show ?case
  proof (cases "rg_keep cnt1 K")
    case True
    have rest_agree: "\<forall>\<alpha>. (\<exists>(p, K) \<in> set rest. \<alpha> \<in> K) \<longrightarrow> cnt1 \<alpha> = cnt2 \<alpha>"
      using Cons.prems by auto
    from Cons.IH[OF rest_agree] have IH: 
      "fst (rg_fold rest cnt1) = fst (rg_fold rest cnt2)"
      "\<forall>\<alpha>. (\<exists>(p, K) \<in> set rest. \<alpha> \<in> K) \<longrightarrow> 
             snd (rg_fold rest cnt1) \<alpha> = snd (rg_fold rest cnt2) \<alpha>"
      by auto
    have snd_eq: "\<forall>\<beta>. (\<exists>(p, K) \<in> set (pc # rest). \<beta> \<in> K) \<longrightarrow> 
           snd (rg_fold (pc # rest) cnt1) \<beta> = snd (rg_fold (pc # rest) cnt2) \<beta>"
    proof (intro allI impI)
      fix \<beta> assume ex: "\<exists>(p, K) \<in> set (pc # rest). \<beta> \<in> K"
      obtain P1 c1 P2 c2 where 
        r1: "rg_fold rest cnt1 = (P1, c1)" and r2: "rg_fold rest cnt2 = (P2, c2)" 
        by (cases "rg_fold rest cnt1"; cases "rg_fold rest cnt2")
      from IH(1) r1 r2 have "P1 = P2" by simp
      have fold1: "rg_fold (pc # rest) cnt1 = (insert p P1, c1)"
        using \<open>rg_keep cnt1 K\<close> r1 by (simp add: Let_def)
      have fold2: "rg_fold (pc # rest) cnt2 = (insert p P2, c2)"
        using \<open>rg_keep cnt1 K\<close> keep_eq r2 by (simp add: Let_def)
      show "snd (rg_fold (pc # rest) cnt1) \<beta> = snd (rg_fold (pc # rest) cnt2) \<beta>"
      proof (cases "\<exists>(p, K) \<in> set rest. \<beta> \<in> K")
        case True
        from IH(2) True have "c1 \<beta> = c2 \<beta>" using r1 r2 by auto
        then show ?thesis using fold1 fold2 by simp
      next
        case False
        then have nk1: "\<forall>(p, K) \<in> set rest. \<beta> \<notin> K" by auto
        have "snd (rg_fold rest cnt1) \<beta> = cnt1 \<beta>" using rg_fold_cnt_unchanged[OF nk1] by simp
        then have "c1 \<beta> = cnt1 \<beta>" using r1 by simp
        moreover have "snd (rg_fold rest cnt2) \<beta> = cnt2 \<beta>" using rg_fold_cnt_unchanged[OF nk1] by simp
        then have "c2 \<beta> = cnt2 \<beta>" using r2 by simp

        moreover from ex False have "\<beta> \<in> K" by auto
        then have "cnt1 \<beta> = cnt2 \<beta>" using key_eq by auto
        ultimately show ?thesis using fold1 fold2 by simp
      qed
    qed
    from IH(1) snd_eq True keep_eq
    show ?thesis by (auto simp: Let_def split: prod.splits)

  next
    case False
    define cnt1' where "cnt1' = (\<lambda>\<alpha>. if \<alpha> \<in> K then cnt1 \<alpha> - 1 else cnt1 \<alpha>)"
    define cnt2' where "cnt2' = (\<lambda>\<alpha>. if \<alpha> \<in> K then cnt2 \<alpha> - 1 else cnt2 \<alpha>)"
    have rest_agree: "\<forall>\<alpha>. (\<exists>(p, K) \<in> set rest. \<alpha> \<in> K) \<longrightarrow> cnt1' \<alpha> = cnt2' \<alpha>"
      using Cons.prems key_eq unfolding cnt1'_def cnt2'_def by auto
    from Cons.IH[OF rest_agree] have IH:
      "fst (rg_fold rest cnt1') = fst (rg_fold rest cnt2')"
      "\<forall>\<alpha>. (\<exists>(p, K) \<in> set rest. \<alpha> \<in> K) \<longrightarrow> 
             snd (rg_fold rest cnt1') \<alpha> = snd (rg_fold rest cnt2') \<alpha>"
      by auto
    have snd_eq: "\<forall>\<alpha>. (\<exists>(p, K) \<in> set (pc # rest). \<alpha> \<in> K) \<longrightarrow> 
           snd (rg_fold (pc # rest) cnt1) \<alpha> = snd (rg_fold (pc # rest) cnt2) \<alpha>"
    proof (intro allI impI)
      fix \<beta> assume "\<exists>(p, K) \<in> set (pc # rest). \<beta> \<in> K"
      then have "\<beta> \<in> K \<or> (\<exists>(p, K) \<in> set rest. \<beta> \<in> K)" by auto
      then show "snd (rg_fold (pc # rest) cnt1) \<beta> = snd (rg_fold (pc # rest) cnt2) \<beta>"
      proof
        assume "\<beta> \<in> K"
        show ?thesis
        proof (cases "\<exists>(p, K) \<in> set rest. \<beta> \<in> K")
          case True
          then show ?thesis using IH(2) False keep_eq cnt1'_def cnt2'_def
            by (simp add: Let_def rg_keep_def split: prod.splits)
        next
          case Falser: False
          then have nk2: "\<forall>(p, K) \<in> set rest. \<beta> \<notin> K" by auto
          have "snd (rg_fold rest cnt1') \<beta> = cnt1' \<beta>"
            using rg_fold_cnt_unchanged[OF nk2] by simp
          moreover have "snd (rg_fold rest cnt2') \<beta> = cnt2' \<beta>"
            using rg_fold_cnt_unchanged[OF nk2] by simp
          moreover have "cnt1' \<beta> = cnt2' \<beta>" 
            using key_eq \<open>\<beta> \<in> K\<close> unfolding cnt1'_def cnt2'_def by auto
          ultimately show ?thesis using False keep_eq cnt1'_def cnt2'_def
            by (simp add: Let_def rg_keep_def split: prod.splits)

        qed
      next
        assume "\<exists>(p, K) \<in> set rest. \<beta> \<in> K"
        then show ?thesis using IH(2) False keep_eq cnt1'_def cnt2'_def
          by (simp add: Let_def rg_keep_def split: prod.splits)
      qed
    qed
    from IH(1) snd_eq False keep_eq cnt1'_def cnt2'_def
    show ?thesis by (simp add: Let_def rg_keep_def split: prod.splits)
  qed
  qed
  from both show "fst (rg_fold cands cnt1) = fst (rg_fold cands cnt2)" by simp
  from both show "\<forall>\<alpha>. (\<exists>(p, K) \<in> set cands. \<alpha> \<in> K) \<longrightarrow> 
           snd (rg_fold cands cnt1) \<alpha> = snd (rg_fold cands cnt2) \<alpha>" by simp
qed

text \<open>Corollary: the fold preserves count \<open>\<ge> 1\<close> for variables in candidate keys.
  We prove this by using @{thm rg_fold_cnt_agree} to relate the fold with \<^term>\<open>init_count\<close>
  to the fold with a count that is \<open>\<ge> 1\<close> everywhere.\<close>

lemma rg_fold_preserves_ge1_on_keys:
  assumes "\<forall>\<alpha>. (\<exists>(p, K) \<in> set cands. \<alpha> \<in> K) \<longrightarrow> cnt \<alpha> \<ge> 1"
    and "(\<exists>(p, K) \<in> set cands. \<alpha> \<in> K)"
  shows "snd (rg_fold cands cnt) \<alpha> \<ge> 1"
proof -
  define cnt' where "cnt' \<beta> = (if \<exists>(p, K) \<in> set cands. \<beta> \<in> K then cnt \<beta> else 1)" for \<beta>
  have ge1: "\<forall>\<beta>. cnt' \<beta> \<ge> 1" unfolding cnt'_def using assms(1) by auto
  have agree: "\<forall>\<beta>. (\<exists>(p, K) \<in> set cands. \<beta> \<in> K) \<longrightarrow> cnt \<beta> = cnt' \<beta>"
    unfolding cnt'_def by auto
  from rg_fold_cnt_agree(2)[OF agree] assms(2) 
  have "snd (rg_fold cands cnt) \<alpha> = snd (rg_fold cands cnt') \<alpha>" by auto
  then have "snd (rg_fold cands cnt) \<alpha> = snd (rg_fold cands cnt') \<alpha>" by simp
  also have "\<dots> \<ge> 1" using rg_fold_preserves_ge1 ge1 by auto
  finally show ?thesis .
qed

subsubsection \<open>Witness Property\<close>

text \<open>Lemma (Witness Variable). For every kept position \<^term>\<open>p\<close>, there exists a variable
  \<^term>\<open>\<alpha>\<close> in its key such that \<^term>\<open>\<alpha>\<close> does not appear in the key of any other kept position.

  The proof proceeds by induction on the candidate list, using a generalized invariant
  that tracks an extra count (representing kept positions from the prefix that are no
  longer in the candidate list). The key insight: in the keep case, the extra count
  being zero for the witness variable automatically excludes it from the current head's
  key, since the extra count absorbs the head's contribution.\<close>

text \<open>Auxiliary generalized lemma: the count function may over-count by an extra amount.
  The conclusion finds a witness \<^term>\<open>\<alpha>\<close> whose extra contribution is zero, meaning \<^term>\<open>\<alpha>\<close> only
  appears in candidates from the current list (not from any prior kept positions).\<close>

lemma rg_fold_witness_aux:
  assumes dist: "distinct (map fst cands)"
    and cnt_eq: "\<forall>\<alpha>. cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) cands) + extra \<alpha>"
    and mem: "(p, K) \<in> set cands"
    and kept: "p \<in> fst (rg_fold cands cnt)"
  shows "\<exists>\<alpha> \<in> K. extra \<alpha> = 0 \<and>
    (\<forall>p' K'. (p', K') \<in> set cands \<longrightarrow> p' \<in> fst (rg_fold cands cnt) \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K')"
  using assms
proof (induction cands arbitrary: cnt extra p K)
  case Nil
  then show ?case by simp
next
  case (Cons pc rest)
  obtain ph Kh where pc_def: "pc = (ph, Kh)" by (cases pc)
  from Cons.prems(1) pc_def have dist_rest: "distinct (map fst rest)"
    and ph_notin: "ph \<notin> fst ` set rest" by auto
  show ?case
  proof (cases "p = ph")
    case True
    text \<open>Target is the head. First establish \<^term>\<open>K = Kh\<close> using distinctness.\<close>
    from Cons.prems(3) pc_def \<open>p = ph\<close> have "(ph, K) \<in> set ((ph, Kh) # rest)" by simp
    then have "K = Kh \<or> (ph, K) \<in> set rest" by auto
    with ph_notin have K_eq: "K = Kh" by (auto simp: image_iff)
    show ?thesis
    proof (cases "rg_keep cnt Kh")
      case True
      text \<open>Head is kept:\<close>
      from True obtain \<alpha> where \<alpha>_in: "\<alpha> \<in> Kh" and cnt_le: "cnt \<alpha> \<le> 1"
        unfolding rg_keep_def by auto
      from Cons.prems(2) pc_def \<alpha>_in have
        cnt_eq_\<alpha>: "cnt \<alpha> = 1 + length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra \<alpha>"
        by simp
      from cnt_le cnt_eq_\<alpha> have rest_empty: "length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) = 0"
        and extra_zero: "extra \<alpha> = 0" by arith+
      from rest_empty have no_\<alpha>_rest: "\<forall>(p', K') \<in> set rest. \<alpha> \<notin> K'"
        by (auto simp: filter_empty_conv)
      text \<open>Show the witness property for \<^term>\<open>\<alpha>\<close>.\<close>
      have wit: "\<forall>p' K'. (p', K') \<in> set (pc # rest) \<longrightarrow> 
        p' \<in> fst (rg_fold (pc # rest) cnt) \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K'"
      proof (intro allI impI)
        fix p' K' 
        assume p'_in: "(p', K') \<in> set (pc # rest)"
          and p'_kept: "p' \<in> fst (rg_fold (pc # rest) cnt)"
          and p'_ne: "p' \<noteq> p"
        from p'_ne \<open>p = ph\<close> have "p' \<noteq> ph" by simp
        from p'_in pc_def \<open>p' \<noteq> ph\<close> have "(p', K') \<in> set rest" by auto
        with no_\<alpha>_rest show "\<alpha> \<notin> K'" by auto
      qed
      from \<alpha>_in K_eq extra_zero wit show ?thesis 
        by (intro bexI[of _ \<alpha>]) auto
    next
      case False
      text \<open>Head is dropped but \<^term>\<open>p = ph\<close>, so \<^term>\<open>p\<close> must be in the result of the recursive call.
        This leads to a contradiction since \<^term>\<open>ph\<close> cannot be in \<^term>\<open>fst\<close> of \<^term>\<open>rest\<close>'s result.\<close>
      define cnt' where "cnt' = (\<lambda>\<alpha>. if \<alpha> \<in> Kh then cnt \<alpha> - 1 else cnt \<alpha>)"
      from False pc_def have fold_eq: "rg_fold (pc # rest) cnt = 
        (let (P', cnt'') = rg_fold rest cnt' in (P', cnt''))"
        by (simp add: Let_def cnt'_def)
      obtain P' cnt'' where rec: "rg_fold rest cnt' = (P', cnt'')" 
        by (cases "rg_fold rest cnt'")
      from fold_eq rec have "fst (rg_fold (pc # rest) cnt) = P'" by (simp add: Let_def)
      with Cons.prems(4) \<open>p = ph\<close> have "ph \<in> P'" by simp
      from rg_fold_subset[of rest cnt'] rec have "P' \<subseteq> fst ` set rest" by simp
      with \<open>ph \<in> P'\<close> ph_notin show ?thesis by auto
    qed
  next
    case False
    text \<open>Target \<^term>\<open>p\<close> is in the tail.\<close>
    from Cons.prems(3) pc_def \<open>p \<noteq> ph\<close> have p_in_rest: "(p, K) \<in> set rest" by auto
    show ?thesis
    proof (cases "rg_keep cnt Kh")
      case True
      text \<open>Head is kept. The recursive call uses the same \<^term>\<open>cnt\<close>.
        The extra count for rest includes the head's contribution.\<close>
      obtain P' cnt_out where rec: "rg_fold rest cnt = (P', cnt_out)" 
        by (cases "rg_fold rest cnt")
      from True pc_def rec have fold_eq: 
        "fst (rg_fold (pc # rest) cnt) = insert ph P'"
        by (simp add: Let_def)
      from Cons.prems(4) fold_eq \<open>p \<noteq> ph\<close> have p_kept_rest: "p \<in> P'" by simp
      with rec have p_in_fold: "p \<in> fst (rg_fold rest cnt)" by simp
      text \<open>Define the extra count for rest:\<close>
      define extra' where "extra' \<alpha> = (if \<alpha> \<in> Kh then 1 else 0) + extra \<alpha>" for \<alpha>
      have cnt_rest: "\<forall>\<alpha>. cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra' \<alpha>"
      proof
        fix \<alpha>
        from Cons.prems(2) pc_def have 
          "cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) (pc # rest)) + extra \<alpha>" by simp
        then show "cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra' \<alpha>"
          unfolding extra'_def pc_def by simp
      qed
      text \<open>Apply IH on rest.\<close>
      from Cons.IH[OF dist_rest cnt_rest p_in_rest p_in_fold]
      obtain \<alpha> where \<alpha>_in: "\<alpha> \<in> K" 
        and extra'_zero: "extra' \<alpha> = 0"
        and wit_rest: "\<forall>p' K'. (p', K') \<in> set rest \<longrightarrow> 
          p' \<in> fst (rg_fold rest cnt) \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K'"
        by auto
      text \<open>From \<^term>\<open>extra' \<alpha> = 0\<close>, deduce \<^term>\<open>\<alpha> \<notin> Kh\<close> and \<^term>\<open>extra \<alpha> = 0\<close>.\<close>
      from extra'_zero extra'_def have \<alpha>_notin_Kh: "\<alpha> \<notin> Kh" and extra_zero: "extra \<alpha> = 0"
        by (auto split: if_splits)
      text \<open>Extend the witness property to the full list.\<close>
      have wit_full: "\<forall>p' K'. (p', K') \<in> set (pc # rest) \<longrightarrow> 
        p' \<in> fst (rg_fold (pc # rest) cnt) \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K'"
      proof (intro allI impI)
        fix p' K' 
        assume p'_in: "(p', K') \<in> set (pc # rest)"
          and p'_kept: "p' \<in> fst (rg_fold (pc # rest) cnt)"
          and p'_ne: "p' \<noteq> p"
        show "\<alpha> \<notin> K'"
          using \<alpha>_notin_Kh p'_in pc_def ph_notin fold_eq rec p'_kept 
          by (fastforce simp: image_iff p'_ne wit_rest)
      qed
      from \<alpha>_in extra_zero wit_full show ?thesis by (intro bexI[of _ \<alpha>]) auto
    next
      case False
      text \<open>Head is dropped. Decrement count for variables in \<^term>\<open>Kh\<close>.\<close>
      define cnt' where "cnt' = (\<lambda>\<alpha>. if \<alpha> \<in> Kh then cnt \<alpha> - 1 else cnt \<alpha>)"
      obtain P' cnt'' where rec: "rg_fold rest cnt' = (P', cnt'')" 
        by (cases "rg_fold rest cnt'")
      from False pc_def cnt'_def rec have fold_eq:
        "fst (rg_fold (pc # rest) cnt) = P'"
        by (simp add: Let_def rg_keep_def split: prod.splits)
      from Cons.prems(4) fold_eq have p_kept_rest: "p \<in> P'" by simp
      with rec have p_in_fold: "p \<in> fst (rg_fold rest cnt')" by simp
      text \<open>Compute the \<^term>\<open>cnt'\<close> equation for rest.\<close>
      have cnt_rest: "\<forall>\<alpha>. cnt' \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra \<alpha>"
      proof
        fix \<alpha>
        from Cons.prems(2) pc_def have 
          cnt_full: "cnt \<alpha> = (if \<alpha> \<in> Kh then 1 else 0) + length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra \<alpha>"
          by simp
        show "cnt' \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) rest) + extra \<alpha>"
        proof (cases "\<alpha> \<in> Kh")
          case True
          then have "cnt \<alpha> \<ge> 1" using cnt_full by simp
          with True show ?thesis unfolding cnt'_def using cnt_full by simp
        next
          case False\<alpha>: False
          then show ?thesis unfolding cnt'_def using cnt_full by simp
        qed
      qed
      text \<open>Apply IH on rest with extra unchanged.\<close>
      from Cons.IH[OF dist_rest cnt_rest p_in_rest p_in_fold]
      obtain \<alpha> where \<alpha>_in: "\<alpha> \<in> K"
        and extra_zero: "extra \<alpha> = 0"
        and wit_rest: "\<forall>p' K'. (p', K') \<in> set rest \<longrightarrow> 
          p' \<in> fst (rg_fold rest cnt') \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K'"
        by auto
      text \<open>Extend witness property to full list. The head was dropped, so \<^term>\<open>ph \<notin> P'\<close>.\<close>
      from rg_fold_subset[of rest cnt'] rec have "P' \<subseteq> fst ` set rest" by simp
      with ph_notin have ph_notin_P: "ph \<notin> P'" by auto
      have wit_full: "\<forall>p' K'. (p', K') \<in> set (pc # rest) \<longrightarrow> 
        p' \<in> fst (rg_fold (pc # rest) cnt) \<longrightarrow> p' \<noteq> p \<longrightarrow> \<alpha> \<notin> K'"
      proof (intro allI impI)
        fix p' K' 
        assume p'_in: "(p', K') \<in> set (pc # rest)"
          and p'_kept: "p' \<in> fst (rg_fold (pc # rest) cnt)"
          and p'_ne: "p' \<noteq> p"
        from p'_kept fold_eq have "p' \<in> P'" by simp
        with ph_notin_P have "p' \<noteq> ph" by auto
        from p'_in pc_def \<open>p' \<noteq> ph\<close> have "(p', K') \<in> set rest" by auto
        from \<open>p' \<in> P'\<close> rec have "p' \<in> fst (rg_fold rest cnt')" by simp
        from wit_rest \<open>(p', K') \<in> set rest\<close> this p'_ne
        show "\<alpha> \<notin> K'" by auto
      qed
      from \<alpha>_in extra_zero wit_full show ?thesis by (intro bexI[of _ \<alpha>]) auto
    qed
  qed
qed

text \<open>The main witness lemma: specialization with \<^term>\<open>extra = 0\<close>.\<close>

lemma rg_fold_witness:
  assumes "distinct (map fst cands)"
    and "\<forall>\<alpha>. cnt \<alpha> = length (filter (\<lambda>(_, K). \<alpha> \<in> K) cands)"
    and "(p, K) \<in> set cands" and "p \<in> fst (rg_fold cands cnt)"
  shows "\<exists>\<alpha> \<in> K. \<forall>p' \<in> fst (rg_fold cands cnt). p' \<noteq> p \<longrightarrow>
    (\<forall>K'. (p', K') \<in> set cands \<longrightarrow> \<alpha> \<notin> K')"
  using rg_fold_witness_aux[OF assms(1) _ assms(3,4)] assms(2)
  by fastforce

subsubsection \<open>Connecting the Algorithm to the Locale\<close>

text \<open>We now connect the reverse-greedy algorithm to the locale-based proofs.
  The candidate list is constructed from the enumeration of \<^term>\<open>a_star\<close>, filtering
  for positions with non-empty keys. The reverse-greedy produces a set \<^term>\<open>P\<close>
  satisfying coverage and witness properties.\<close>

context annotation_problem
begin

text \<open>Candidate list: positions paired with their keys, derived from the post-order
  enumeration of \<^term>\<open>a_star\<close>. 
  Candidates are processed in the \<^term>\<open>enum_aterm\<close> order (generalization to other orders is easy).
  Positions with empty keys are included
  but are always dropped by the reverse-greedy (the keep condition is vacuously false).\<close>

definition candidates :: "(nat \<times> string set) list" where
  "candidates = map (\<lambda>(p, s, \<tau>). (p, tvars_ty \<tau> \<inter> V)) (enum_aterm a_star)"

text \<open>The candidate positions have distinct first components.\<close>

lemma candidates_distinct: "distinct (map fst candidates)"
  unfolding candidates_def by (simp add: comp_def case_prod_beta distinct_enum_fst)

text \<open>For \<^term>\<open>\<alpha> \<in> V\<close>, the initial count is at least 1.\<close>

lemma candidates_count_ge1:
  assumes "\<alpha> \<in> V"
  shows "init_count candidates \<alpha> \<ge> 1"                                                 
proof -
  from coverage_initial[OF assms] obtain p where
    "p \<in> pos_set a_star" "\<alpha> \<in> key p" by auto
  from \<open>\<alpha> \<in> key p\<close> obtain s \<tau> where
    mem: "(p, s, \<tau>) \<in> set (enum_aterm a_star)" and tv: "\<alpha> \<in> tvars_ty \<tau>" and "\<alpha> \<in> V"
    unfolding key_def by auto
  then have mem_cand: "(p, tvars_ty \<tau> \<inter> V) \<in> set candidates"
    unfolding candidates_def by force
  have "\<alpha> \<in> tvars_ty \<tau> \<inter> V" using tv assms by auto
  with mem_cand have "(p, tvars_ty \<tau> \<inter> V) \<in> set (filter (\<lambda>(_, K). \<alpha> \<in> K) candidates)"
    by auto
  then have "0 < length (filter (\<lambda>(_, K). \<alpha> \<in> K) candidates)"
    by (rule length_pos_if_in_set)
  then have "length (filter (\<lambda>(_, K). \<alpha> \<in> K) candidates) \<ge> 1" by linarith
  then show ?thesis unfolding init_count_def by simp
qed

text \<open>The kept set from the reverse-greedy is a subset of candidate positions,
  which are positions in \<^term>\<open>pos_set a_star\<close>.\<close>

lemma rg_result_subset: "reverse_greedy candidates \<subseteq> pos_set a_star"
proof -
  have "reverse_greedy candidates \<subseteq> fst ` set candidates"
    unfolding reverse_greedy_def using rg_fold_subset by auto
  also have "\<dots> \<subseteq> pos_set a_star"
    unfolding candidates_def pos_set_def by force
  finally show ?thesis .
qed

text \<open>Key in the candidate list matches key in the locale.\<close>

lemma candidates_key_eq:
  assumes "(p, K) \<in> set candidates"
  shows "K = key p"
  using assms
  unfolding key_def candidates_def
  by (fastforce dest: enum_aterm_unique)

text \<open>Coverage property: the kept positions cover all inference variables.\<close>

lemma rg_coverage: "\<Union>(key ` reverse_greedy candidates) = V"
proof (intro equalityI subsetI)
  fix \<alpha> assume "\<alpha> \<in> \<Union>(key ` reverse_greedy candidates)"
  then obtain p where "p \<in> reverse_greedy candidates" "\<alpha> \<in> key p" by auto
  then show "\<alpha> \<in> V" unfolding key_def by auto
next
  fix \<alpha> assume \<alpha>_V: "\<alpha> \<in> V"
  text \<open>By @{thm rg_fold_preserves_ge1_on_keys}, the final count for \<^term>\<open>\<alpha>\<close> is \<open>\<ge> 1\<close>.
    This means at least one candidate covering \<^term>\<open>\<alpha>\<close> was not dropped.\<close>
  from coverage_initial[OF \<alpha>_V] obtain p0 where
    "p0 \<in> pos_set a_star" "\<alpha> \<in> key p0" by auto
  from \<open>\<alpha> \<in> key p0\<close> obtain s0 \<tau>0 where 
    mem0: "(p0, s0, \<tau>0) \<in> set (enum_aterm a_star)" and "\<alpha> \<in> tvars_ty \<tau>0" "\<alpha> \<in> V"
    unfolding key_def by auto
  then have "(p0, tvars_ty \<tau>0 \<inter> V) \<in> set candidates"
    unfolding candidates_def by force
  then have ex_cand: "\<exists>(p, K) \<in> set candidates. \<alpha> \<in> K"
    using \<open>\<alpha> \<in> tvars_ty \<tau>0\<close> \<open>\<alpha> \<in> V\<close> by (intro bexI[of _ "(p0, tvars_ty \<tau>0 \<inter> V)"]) auto
  have cnt_ge1: "\<forall>\<beta>. (\<exists>(p, K) \<in> set candidates. \<beta> \<in> K) \<longrightarrow> init_count candidates \<beta> \<ge> 1"
  proof (intro allI impI)
    fix \<beta> assume "\<exists>(p, K) \<in> set candidates. \<beta> \<in> K"
    then obtain p1 K1 where "(p1, K1) \<in> set candidates" "\<beta> \<in> K1" by auto
    from candidates_key_eq[OF this(1)] \<open>\<beta> \<in> K1\<close> have "\<beta> \<in> key p1" by auto
    then have "\<beta> \<in> V" unfolding key_def by auto
    then show "init_count candidates \<beta> \<ge> 1" using candidates_count_ge1 by auto
  qed
  from rg_fold_preserves_ge1_on_keys[OF cnt_ge1 ex_cand]
  have final_ge1: "snd (rg_fold candidates (init_count candidates)) \<alpha> \<ge> 1" .
  text \<open>Final count \<open>\<ge> 1\<close> means at least one position covering \<^term>\<open>\<alpha>\<close> was kept.
    Since final count \<open>\<ge> 1\<close>, at least one candidate with \<^term>\<open>\<alpha>\<close> was kept.\<close>
  from rg_fold_cnt_mono[of candidates "init_count candidates" \<alpha>]
  have "snd (rg_fold candidates (init_count candidates)) \<alpha> \<le> init_count candidates \<alpha>" .

  have "\<exists>(pk, Kk) \<in> set candidates. \<alpha> \<in> Kk \<and> pk \<in> fst (rg_fold candidates (init_count candidates))"
  proof (rule ccontr)
    assume "\<not> (\<exists>(pk, Kk) \<in> set candidates. \<alpha> \<in> Kk \<and> pk \<in> fst (rg_fold candidates (init_count candidates)))"
    then have no_kept: "\<forall>(pk, Kk) \<in> set candidates. \<alpha> \<in> Kk \<longrightarrow> pk \<notin> fst (rg_fold candidates (init_count candidates))"
      by auto
    text \<open>If no kept position covers \<^term>\<open>\<alpha>\<close>, the count must drop to \<^term>\<open>0\<close>:\<close>
    have nk: "\<forall>p K. (p, K) \<in> set candidates \<longrightarrow> \<alpha> \<in> K \<longrightarrow>
        p \<notin> fst (rg_fold candidates (init_count candidates))"
      using no_kept by auto
    have "snd (rg_fold candidates (init_count candidates)) \<alpha> = 0"
      by (rule rg_fold_no_kept_zero[OF nk]) (simp add: init_count_def)
    with final_ge1 show False by simp
  qed
  then obtain pk Kk where pk_mem: "(pk, Kk) \<in> set candidates"
    and "\<alpha> \<in> Kk" and pk_kept: "pk \<in> fst (rg_fold candidates (init_count candidates))"
    by auto
  from pk_kept have "pk \<in> reverse_greedy candidates" unfolding reverse_greedy_def by simp
  from candidates_key_eq[OF pk_mem] \<open>\<alpha> \<in> Kk\<close> have "\<alpha> \<in> key pk" by auto
  from \<open>pk \<in> reverse_greedy candidates\<close> \<open>\<alpha> \<in> key pk\<close>
  show "\<alpha> \<in> \<Union>(key ` reverse_greedy candidates)" by auto
qed

text \<open>Witness property: each kept position has a witness variable.\<close>

lemma rg_witness:
  assumes "p \<in> reverse_greedy candidates"
  shows "\<exists>\<alpha> \<in> key p. \<forall>p' \<in> reverse_greedy candidates. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'"
proof -
  from assms have p_in: "p \<in> fst (rg_fold candidates (init_count candidates))"
    unfolding reverse_greedy_def by simp
  have "p \<in> fst ` set candidates"
    using p_in rg_fold_subset[of candidates "init_count candidates"] by auto
  then obtain K where pK1: "(p, K) \<in> set candidates"
    by (force simp: candidates_def)
  note pK = pK1 p_in

  from rg_fold_witness[OF candidates_distinct _ pK]
  have wit: "\<exists>\<alpha> \<in> K. \<forall>p' \<in> fst (rg_fold candidates (init_count candidates)). p' \<noteq> p \<longrightarrow>
    (\<forall>K'. (p', K') \<in> set candidates \<longrightarrow> \<alpha> \<notin> K')"
    by (simp add: init_count_def)
  then obtain \<alpha> where "\<alpha> \<in> K" and
    excl: "\<forall>p' \<in> fst (rg_fold candidates (init_count candidates)). p' \<noteq> p \<longrightarrow>
      (\<forall>K'. (p', K') \<in> set candidates \<longrightarrow> \<alpha> \<notin> K')" by auto
  from candidates_key_eq[OF pK(1)] \<open>\<alpha> \<in> K\<close> have "\<alpha> \<in> key p" by simp
  moreover have "\<forall>p' \<in> reverse_greedy candidates. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'"
  proof (intro ballI impI)
    fix p' assume "p' \<in> reverse_greedy candidates" "p' \<noteq> p"
    then have p'_in: "p' \<in> fst (rg_fold candidates (init_count candidates))"
      unfolding reverse_greedy_def by simp
    from rg_fold_subset have "p' \<in> fst ` set candidates"
      using p'_in by (metis in_mono)
    then obtain K' where "(p', K') \<in> set candidates" by auto
    from excl p'_in \<open>p' \<noteq> p\<close> this have "\<alpha> \<notin> K'" by auto
    from candidates_key_eq[OF \<open>(p', K') \<in> set candidates\<close>] this
    show "\<alpha> \<notin> key p'" by simp
  qed
  ultimately show ?thesis by auto
qed

text \<open>Instantiate \<^locale>\<open>annotation_selection\<close> with \<^term>\<open>P = reverse_greedy candidates\<close>.
  This makes the abstract completeness and local minimality theorems available as
  concrete theorems about the reverse-greedy algorithm's output.\<close>

sublocale annotation_selection const_type \<Gamma> a a_star \<sigma> "reverse_greedy candidates"
proof (unfold_locales)
  show "reverse_greedy candidates \<subseteq> pos_set a_star"
    by (rule rg_result_subset)
  show "\<Union>(key ` reverse_greedy candidates) = V"
    by (rule rg_coverage)
  fix p assume "p \<in> reverse_greedy candidates"
  then show "\<exists>\<alpha> \<in> key p. \<forall>p' \<in> reverse_greedy candidates. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'"
    by (rule rg_witness)
qed

text \<open>The output of the full algorithm: \<open>t_out\<close> is the annotated raw term produced
  by running the reverse-greedy algorithm to select positions and then inserting
  annotations. This is the \<open>t_out\<close> from the paper's Theorem 1.\<close>

definition t_out :: raw_term where
  "t_out = annotate \<sigma> a_star (reverse_greedy candidates)"

text \<open>Key property: stripping the annotations from \<^term>\<open>t_out\<close> recovers the erasure of \<^term>\<open>a\<close>.\<close>

lemma strip_t_out: "strip t_out = erase a"
  unfolding t_out_def using strip_annotate same_erasure by simp

text \<open>Theorem (Completeness), stated in terms of \<open>t_out\<close>:\<close>
theorem completeness_t_out:
  assumes "well_typed const_type \<Gamma> a'"
    and "erase a' = strip t_out"
    and "\<exists>\<sigma>'. subst_aterm \<sigma>' a_star = a' \<and> (\<forall>\<alpha> \<in> tvars_ctx \<Gamma>. \<sigma>' \<alpha> = TVar \<alpha>)"
    and "consistent_with a' (reverse_greedy candidates)"
  shows "a' = a"
  using assms strip_t_out completeness by auto

text \<open>Theorem (Local Minimality), stated for the reverse-greedy selection:\<close>

thm local_minimality

end

end