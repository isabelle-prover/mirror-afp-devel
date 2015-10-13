section {* Euclidean Space: Explicit Representation *}
theory Euclidean_Space_Explicit
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

subsection {* Explicit Sum for Composition of Components *}

definition (in plus) plusE :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "+\<^sub>E" 65) where "plusE = plus"

definition (in comm_monoid_add) setsumE where "setsumE = setsum"

lemmas setsumE_insert = setsum.insert[simplified plusE_def[symmetric] setsumE_def[symmetric]]
lemma setsumE_singleton: "setsumE f {a} = f a" by (simp add: setsumE_def)

lemmas euclidean_representationE =
  euclidean_representation[simplified setsumE_def[symmetric], symmetric]

subsection {* Conversion for Explicit Representation *}

lemma scaleR_real_1: "scaleR x 1 = x" by simp

named_theorems euclidean_Basis
  "simplification rules for Basis of Euclidean Space"
named_theorems euclidean_Outer
  "simplification rules for rewriting of Euclidean Space as return value"
named_theorems euclidean_Inner
  "simplification rules for rewriting of Euclidean Space as argument"

declare simp_thms[euclidean_Basis, euclidean_Inner, euclidean_Outer]
lemmas [euclidean_Basis] =
  image_insert image_empty Un_insert_left Un_empty_left Un_insert_right Un_empty_right
  Basis_prod_def
  zero_prod_def
  Basis_real_def
  setsumE_insert setsumE_singleton
  setsum.insert setsum.empty
  finite_insert finite.emptyI
  prod.inject
  empty_iff insert_iff
  refl
  one_neq_zero

lemmas [euclidean_Outer] =
  inner_prod_def
  inner_real_def

lemmas [euclidean_Inner] = plus_prod_def scaleR_prod_def fst_conv snd_conv
  add_0_left
  add_0_right
  scaleR_zero_left
  scaleR_zero_right
  scaleR_real_1
  add_0_left
  add_0_right
  mult_zero_right
  mult_1_right

ML {*

fun Basis_simps ctxt =
  (put_simpset (HOL_basic_ss) ctxt)
    addsimps (Named_Theorems.get ctxt @{named_theorems euclidean_Basis})
fun Outer_simps ctxt =
  (put_simpset (HOL_basic_ss) ctxt)
    addsimps (Named_Theorems.get ctxt @{named_theorems euclidean_Outer})
fun Inner_simps ctxt =
  (put_simpset (HOL_basic_ss) ctxt)
    addsimps (Named_Theorems.get ctxt @{named_theorems euclidean_Inner})

fun rewrite_outer_eucl ctxt =
  Conv.top_sweep_conv
    (fn ctxt => Conv.rewr_conv (@{thm euclidean_representationE[THEN eq_reflection]})
      then_conv Simplifier.rewrite (Basis_simps ctxt)
      then_conv Simplifier.rewrite (Outer_simps ctxt)
    ) ctxt;

fun rewrite_split_beta ctxt =
  Simplifier.rewrite (clear_simpset ctxt addsimps (@{thms split_beta' split_beta}));

fun represent_euclidean ct1 ct2 =
  if ct1 aconvc ct2
  then Conv.rewr_conv @{thm euclidean_representation[symmetric, THEN eq_reflection]} ct2
  else Conv.no_conv ct2

fun rewrite_inner_eucl vs cv ctxt =
  Conv.abs_conv (fn (v, ctxt) => rewrite_inner_eucl (v::vs) cv ctxt else_conv cv (v::vs) ctxt) ctxt

fun component_conv conv ct =
  (case Thm.term_of ct of
    Const (@{const_name scaleR}, _) $ _ $ _ => Conv.arg1_conv conv ct
  | _ => raise CTERM ("scaleR_conv", [ct]));

fun euclidify ctxt = rewrite_outer_eucl ctxt
  then_conv rewrite_split_beta ctxt
  then_conv rewrite_inner_eucl []
    (fn vs => fn ctxt =>
      Conv.every_conv (map (fn v => Conv.top_sweep_conv (fn _ => represent_euclidean v) ctxt) vs))
    ctxt
  then_conv Conv.top_sweep_conv (fn ctxt => component_conv (
    Simplifier.rewrite (Basis_simps ctxt)
    then_conv Simplifier.rewrite (Inner_simps ctxt))) ctxt
  ;

*}

lemma
  "(\<lambda>(x1::real, x2::real) (y1::real, y2::real) (z1::real, z2::real, z3::real).
       (x1 + x2, x2 * x1 + 1, y1, y2 + z1 * z2 * z3)) =
  (\<lambda>x xa xb.
       (xa \<bullet> (0, 1) + xb \<bullet> (1, 0, 0) * (xb \<bullet> (0, 1, 0)) * (xb \<bullet> (0, 0, 1))) *\<^sub>R (0, 0, 0, 1) +\<^sub>E
       (xa \<bullet> (1, 0)) *\<^sub>R (0, 0, 1, 0) +\<^sub>E
       (x \<bullet> (0, 1) * (x \<bullet> (1, 0)) + 1) *\<^sub>R (0, 1, 0, 0) +\<^sub>E
       (x \<bullet> (1, 0) + x \<bullet> (0, 1)) *\<^sub>R (1, 0, 0, 0))"
  by (tactic {*
    CONVERSION (HOLogic.Trueprop_conv (HOLogic.eq_conv (euclidify @{context}) Conv.all_conv)) 1
  *}) (rule refl)

lemma "(\<lambda>(x1, x2) (y1, y2). (x1 + x2, x2 * x1 + 1, y1, y2)::real*real*real*real) =
    (\<lambda>x xa.
       (xa \<bullet> (0, 1)) *\<^sub>R (0, 0, 0, 1) +\<^sub>E
       (xa \<bullet> (1, 0)) *\<^sub>R (0, 0, 1, 0) +\<^sub>E
       (x \<bullet> (0, 1) * (x \<bullet> (1, 0)) + 1) *\<^sub>R (0, 1, 0, 0) +\<^sub>E
       (x \<bullet> (1, 0) + x \<bullet> (0, 1)) *\<^sub>R (1, 0, 0, 0))"
  by (tactic {*
    CONVERSION (HOLogic.Trueprop_conv (HOLogic.eq_conv (euclidify @{context}) Conv.all_conv)) 1
  *}) (rule refl)

lemma "(\<lambda>x y. x + y::real) = (\<lambda>x y. (x \<bullet> 1 + y \<bullet> 1) *\<^sub>R 1)"
  by (tactic {*
    CONVERSION (HOLogic.Trueprop_conv (HOLogic.eq_conv (euclidify @{context}) Conv.all_conv)) 1
  *}) (rule refl)

lemma
  "(\<lambda>x y. (x \<bullet> (1, 0, 0) + y \<bullet> (0, 0, 1)) *\<^sub>R (1, 0) + (x \<bullet> (1, 0, 0) + y \<bullet> (0, 0, 1)) *\<^sub>R (1, 0)) =
  (\<lambda>(x::real*real*real) (y::real*real*real). 0 *\<^sub>R (0, 1) +\<^sub>E
    (x \<bullet> (1, 0, 0) + y \<bullet> (0, 0, 1) + (x \<bullet> (1, 0, 0) + y \<bullet> (0, 0, 1))) *\<^sub>R (1, 0)::real*real)"
  by (tactic {*
    CONVERSION (HOLogic.Trueprop_conv (HOLogic.eq_conv (euclidify @{context}) Conv.all_conv)) 1
  *}) (rule refl)

end
