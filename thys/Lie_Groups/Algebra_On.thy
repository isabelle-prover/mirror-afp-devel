(*  Title:       Algebra_On
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Algebra_On
imports
  "HOL-Types_To_Sets.Linear_Algebra_On"
  "Jacobson_Basic_Algebra.Ring_Theory"
begin

section \<open>Abstract algebra locales over a \<^class>\<open>field\<close>\<close>
text \<open>... with carrier set and some implicit operations
  (only algebraic multiplication, scaling, and derived constants are not implicit).\<close>

text \<open>For full generality, one could define an algebra as a ring that is also a module
  (rather than a vector space, i.e. have a (non/commutative) base ring instead of a base field).\<close>

subsection \<open>Bilinearity, Jacobi identity\<close>


lemma (in module_hom_on) mem_hom:
  assumes "x \<in> S1"
  shows "f x \<in> S2"
  using scale[OF assms, of 1] m2.mem_scale[of "f x" 1] m2.scale_one_on[of "f x"] oops

locale bilinear_on =
  vector_space_pair_on V W scaleV scaleW +
  vector_space_on X scaleX
  for V:: "'b::ab_group_add set" and W::"'c::ab_group_add set" and X::"'d::ab_group_add set"
    and scaleV::"'a::field\<Rightarrow>'b\<Rightarrow>'b" (infixr \<open>\<Zspot>\<^sub>V\<close> 75)
    and scaleW::"'a\<Rightarrow>'c\<Rightarrow>'c" (infixr \<open>\<Zspot>\<^sub>W\<close> 75)
    and scaleX::"'a\<Rightarrow>'d\<Rightarrow>'d" (infixr \<open>\<Zspot>\<^sub>X\<close> 75) +
  fixes f::"'b\<Rightarrow>'c\<Rightarrow>'d"
  assumes linearL: "w\<in>W \<Longrightarrow> linear_on V X scaleV scaleX (\<lambda>v. f v w)"
    and linearR: "v\<in>V \<Longrightarrow> linear_on W X scaleW scaleX (\<lambda>w. f v w)"
begin

lemma linearL': "\<lbrakk>v\<in>V; w\<in>W\<rbrakk> \<Longrightarrow> f (a \<Zspot>\<^sub>V v) w = a \<Zspot>\<^sub>X (f v w)"
    "\<lbrakk>v\<in>V; v'\<in>V; w\<in>W\<rbrakk> \<Longrightarrow> f (v + v') w = (f v w) + (f v' w)"
  using linearL unfolding linear_on_def module_hom_on_def module_hom_on_axioms_def
  by simp+

lemma linearR': "\<lbrakk>v\<in>V; w\<in>W\<rbrakk> \<Longrightarrow> f v (a \<Zspot>\<^sub>W w) = a \<Zspot>\<^sub>X (f v w)"
    "\<lbrakk>v\<in>V; w\<in>W; w'\<in>W\<rbrakk> \<Longrightarrow> f v (w + w') = (f v w) + (f v w')"
  using linearR unfolding linear_on_def module_hom_on_def module_hom_on_axioms_def
  by simp+

lemma bilinear_zero [simp]:
  shows "w\<in>W \<Longrightarrow> f 0 w = 0" "v\<in>V \<Longrightarrow> f v 0 = 0"
  using linearL'(2) m1.mem_zero linearR'(2) m2.mem_zero by fastforce+

lemma bilinear_uminus [simp]:
  assumes v: "v\<in>V" and w: "w\<in>W"
  shows "f (-v) w = - (f v w)" "f v (-w) = - (f v w)"
  using v w linearL'(2) m1.mem_uminus bilinear_zero(1) ab_left_minus add_right_imp_eq apply metis
  using v w linearR'(2) m2.mem_uminus bilinear_zero(2) add_left_cancel add.right_inverse by metis


end


text \<open>For bilinear maps, "alternating" means the same as "skew-symmetric",
  which is the same as "anti-symmetric".\<close>
locale alternating_bilinear_on = bilinear_on S S S scale scale scale f for S scale f +
  assumes alternating: "x\<in>S \<Longrightarrow> f x x = 0"
begin

lemma antisym:
  assumes "x\<in>S" "y\<in>S"
  shows "(f x y) + (f y x) = 0"
proof -
  have "f (x+y) (x+y) = (f x x) + (f x y) + (f y x) + (f y y)"
    using linearL'(2) linearR'(2) by (simp add: assms m1.mem_add)
  thus ?thesis
    using alternating by (simp add: assms m1.mem_add)
qed

lemma antisym':
  assumes "x\<in>S" "y\<in>S"
  shows "(f x y) = - (f y x)"
  using antisym[OF assms] by (simp add: eq_neg_iff_add_eq_0)

lemma antisym_uminus:
  assumes "x\<in>S" "y\<in>S"
  shows "f (-x) y = f y x""f x (-y) = f y x"
  using bilinear_uminus by (metis antisym' assms)+


end


abbreviation (input) jacobi_identity_with::"'a \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow>  ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "jacobi_identity_with zero_add f_add f_mult x y z \<equiv>
      zero_add = f_add (f_add (f_mult x (f_mult y z)) (f_mult y (f_mult z x))) (f_mult z (f_mult x y))"

abbreviation (input) jacobi_identity::"('a::{monoid_add}\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "jacobi_identity f_mult x y z \<equiv> jacobi_identity_with 0 (+) f_mult x y z"

lemma (in module_hom_on) mapsto_zero: "f 0 = 0"
  using add m1.mem_zero by fastforce

lemma (in module_hom_on) mapsto_uminus: "a\<in>S1 \<Longrightarrow> f (-a) = - f a"
  by (metis add m1.mem_uminus neg_eq_iff_add_eq_0 mapsto_zero)

lemma (in module_hom_on) mapsto_closed: "a\<in>S1 \<Longrightarrow> f a \<in> S2"
  using mapsto_zero add mapsto_uminus
oops


subsection \<open>Unital and associative algebras\<close>

locale algebra_on = bilinear_on S S S scale scale scale amult
  for S
    and scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*\<^sub>S\<close> 75)
    and amult (infixr \<open>\<Zspot>\<close> 74) +
  assumes amult_closed [simp]: "a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> amult a b \<in> S"
begin

lemma
    shows distR: "\<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x+y) \<Zspot> z = x \<Zspot> z + y \<Zspot> z"
      and distL: "\<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> z \<Zspot> (x+y) = z \<Zspot> x + z \<Zspot> y"
      and scalar_compat (* [simp] *): "\<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> (a *\<^sub>S x) \<Zspot> (b *\<^sub>S y) = (a*b) *\<^sub>S (x \<Zspot> y)"
    using algebra_on_axioms unfolding algebra_on_def bilinear_on_def bilinear_on_axioms_def
      linear_on_def module_hom_on_def module_hom_on_axioms_def
    by (blast, blast, metis m1.mem_scale m1.scale_scale_on)

  lemma scalar_compat' [simp]:
    shows "\<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> (a *\<^sub>S x) \<Zspot> y = a *\<^sub>S (x \<Zspot> y)"
      and "\<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> x \<Zspot> (a *\<^sub>S y) = a *\<^sub>S (x \<Zspot> y)"
      by (simp_all add: linearL' linearR')

end

text\<open>
  Sometimes an associative algebra is defined as a ring that is also a module (over a comm. ring),
  with the module and scalar multiplication being compatible, and the ring and module addition being the same.
  That definition implies an associative algebra is also unital, i.e. there is a multiplicative identity;
  in contrast, our definition doesn't. This is in agreement with how a \<^typ>\<open>'a::ring\<close> needs no identity,
  and an additional type class typ>\<open>'a::ring_1\<close> is provided (instead of the terminology of rng vs. ring).\<close>
locale assoc_algebra_on = algebra_on +
  assumes amult_assoc: "\<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x\<Zspot>y)\<Zspot>z = x\<Zspot>(y\<Zspot>z)"


locale unital_algebra_on = algebra_on +
  fixes a_id
  assumes amult_id [simp]: "a_id\<in>S" "a\<in>S \<Longrightarrow> a\<Zspot>a_id=a" "a\<in>S \<Longrightarrow> a_id\<Zspot>a=a"
begin

  lemma id_neq_0_iff: "\<exists>a\<in>S. \<exists>b\<in>S. a\<noteq>b \<longleftrightarrow> 0 \<noteq> a_id"
    using amult_id(1) m1.mem_zero by blast

  lemma id_neq_0_if:
    shows "a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> a\<noteq>b \<Longrightarrow> 0 \<noteq> a_id"
      and "card S \<ge> 2 \<Longrightarrow> 0 \<noteq> a_id"
      and "infinite S \<Longrightarrow> 0 \<noteq> a_id"
  proof -

    (* Lifted from HOL-Analysis.Linear_Algebra, which I didn't want to import for one lemma. *)
    have ex_card: "\<exists>S\<subseteq>A. card S = n"
      if "n \<le> card A"
      for n and A::"'a set"
    proof (cases "finite A")
      case True
      from ex_bij_betw_nat_finite[OF this] obtain f where f: "bij_betw f {0..<card A} A" ..
      moreover from f \<open>n \<le> card A\<close> have "{..< n} \<subseteq> {..< card A}" "inj_on f {..< n}"
        by (auto simp: bij_betw_def intro: subset_inj_on)
      ultimately have "f ` {..< n} \<subseteq> A" "card (f ` {..< n}) = n"
        by (auto simp: bij_betw_def card_image)
      then show ?thesis by blast
    next
      case False
      with \<open>n \<le> card A\<close> show ?thesis by force
    qed

    show "a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> a\<noteq>b \<Longrightarrow> 0 \<noteq> a_id"
      using amult_id(2) linearR' m1.mem_zero m1.scale_zero_left by metis
    thus "card S \<ge> 2 \<Longrightarrow> 0 \<noteq> a_id"
      by (metis amult_id(2) card_2_iff' ex_card m1.mem_zero m1.scale_zero_left scalar_compat'(2) subset_iff)
    thus "infinite S \<Longrightarrow> 0 \<noteq> a_id"
      using infinite_arbitrarily_large
      by (metis amult_id(2) card_2_iff' linearR'(1) m1.mem_zero m1.scale_zero_left subset_iff)
  qed

  lemma id_neq_0_implies_elements (* [simp] *): "\<exists>a\<in>S. \<exists>b\<in>S. a\<noteq>b" if "0 \<noteq> a_id"
    using amult_id(1) m1.mem_zero that by blast

  lemma id_neq_0_implies_card:
    assumes "0 \<noteq> a_id"
    obtains "card S \<ge> 2" | "infinite S"
    using id_neq_0_implies_elements[OF assms] unfolding numeral_2_eq_2
    using card_le_Suc0_iff_eq not_less_eq_eq by blast

  lemma id_unique [simp]:
    fixes other_id
    assumes "other_id\<in>S" "\<And>a. a\<in>S \<Longrightarrow> a\<Zspot>other_id=a \<and> other_id\<Zspot>a=a"
    shows "other_id = a_id"
    using assms amult_id by fastforce

end


locale assoc_algebra_1_on = assoc_algebra_on + unital_algebra_on +
  assumes id_neq_0 [simp]: "a_id \<noteq> 0" \<comment> \<open>this is as in the class \<open>ring_1\<close>, and merely assures \<open>S\<close> has at least two elements\<close>
begin

  lemma is_ring_1_axioms:
    shows "\<And>a b c. a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> c\<in>S \<Longrightarrow> a \<Zspot> b \<Zspot> c = a \<Zspot> (b \<Zspot> c)"
      and "\<And>a. a\<in>S \<Longrightarrow> a_id \<Zspot> a = a"
      and "\<And>a. a\<in>S \<Longrightarrow> a \<Zspot> a_id = a"
      and "\<And>a b c. a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> c\<in>S \<Longrightarrow> (a + b) \<Zspot> c = a \<Zspot> c + b \<Zspot> c"
      and "\<And>a b c. a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> c\<in>S \<Longrightarrow> a \<Zspot> (b + c) = a \<Zspot> b + a \<Zspot> c"
      by (simp_all add: distR distL algebra_simps)

  lemma inverse_unique [simp]:
    assumes a: "a\<in>S" "a\<noteq>0"
      and x: "x\<in>S" "a\<Zspot>x=a_id \<and> x\<Zspot>a=a_id"
      and y: "y\<in>S" "a\<Zspot>y=a_id \<and> y\<Zspot>a=a_id"
    shows "x = y"
    using amult_assoc[of x a x] amult_assoc[of x a y]
    by (simp add: assms)

  lemma inverse_unique':
    assumes a: "a\<in>S" "a\<noteq>0"
      and inv_ex: "\<exists>x\<in>S. a\<Zspot>x=a_id \<and> x\<Zspot>a=a_id"
    shows "\<exists>!x\<in>S. a\<Zspot>x=a_id \<and> x\<Zspot>a=a_id"
    using a inv_ex inverse_unique by (metis (no_types, lifting)) 

end

lemma algebra_onI [intro]:
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*\<^sub>S\<close> 75)
    and amult (infixr \<open>\<Zspot>\<close> 74)
  assumes "vector_space_on S scale"
    and distR: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x+y) \<Zspot> z = x \<Zspot> z + y \<Zspot> z"
    and distL: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> z \<Zspot> (x+y) = z \<Zspot> x + z \<Zspot> y"
    and scalar_compat: "\<And>a x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> (a *\<^sub>S x) \<Zspot> y = a *\<^sub>S (x \<Zspot> y) \<and> x \<Zspot> (a *\<^sub>S y) = a *\<^sub>S (x \<Zspot> y)"
    and closure: "\<And>x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> x \<Zspot> y \<in> S"
  shows "algebra_on S scale amult"
  unfolding algebra_on_def bilinear_on_def vector_space_pair_on_def bilinear_on_axioms_def
  apply (intro conjI algebra_on_axioms.intro, simp_all add: assms(1))
  unfolding linear_on_def module_hom_on_def module_hom_on_axioms_def
  by (auto simp: assms vector_space_on.axioms)


lemma (in vector_space_on) scalar_compat_iff:
  fixes scale_notation (infixr \<open>*\<^sub>S\<close> 75)
    and amult (infixr \<open>\<Zspot>\<close> 74)
  defines "scale_notation \<equiv> scale"
  assumes distR: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x+y) \<Zspot> z = x \<Zspot> z + y \<Zspot> z"
    and distL: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> z \<Zspot> (x+y) = z \<Zspot> x + z \<Zspot> y"
  shows "(\<forall>a. \<forall>x\<in>S. \<forall>y\<in>S. (a *\<^sub>S x) \<Zspot> y = a *\<^sub>S (x \<Zspot> y) \<and> x \<Zspot> (a *\<^sub>S y) = a *\<^sub>S (x \<Zspot> y)) \<longleftrightarrow>
      (\<forall>a b. \<forall>x\<in>S. \<forall>y\<in>S. (a *\<^sub>S x) \<Zspot> (b *\<^sub>S y) = (a*b) *\<^sub>S (x \<Zspot> y))"
proof (intro iffI)
  { assume asm: "\<And>a b x y. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> a *\<^sub>S x \<Zspot> b *\<^sub>S y = (a * b) *\<^sub>S (x \<Zspot> y)"
    { fix a x y
      assume S: "x\<in>S" "y\<in>S"
      have "a *\<^sub>S x \<Zspot> y = a *\<^sub>S (x \<Zspot> y)" "x \<Zspot> a *\<^sub>S y = a *\<^sub>S (x \<Zspot> y)"
        using asm[of x y a 1] S apply (simp add: scale_notation_def)
        using asm[of x y 1 a] S by (simp add: scale_notation_def) }}
  thus "\<forall>a b. \<forall>x\<in>S. \<forall>y\<in>S. a *\<^sub>S x \<Zspot> b *\<^sub>S y = (a * b) *\<^sub>S (x \<Zspot> y) \<Longrightarrow>
      \<forall>a. \<forall>x\<in>S. \<forall>y\<in>S. a *\<^sub>S x \<Zspot> y = a *\<^sub>S (x \<Zspot> y) \<and> x \<Zspot> a *\<^sub>S y = a *\<^sub>S (x \<Zspot> y)"
    by blast
qed (metis mem_scale scale_notation_def scale_scale_on)


lemma (in vector_space_on) algebra_onI:
  fixes scale_notation (infixr \<open>*\<^sub>S\<close> 75)
    and amult (infixr \<open>\<Zspot>\<close> 74)
  defines "scale_notation \<equiv> scale"
  assumes distR: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x+y) \<Zspot> z = x \<Zspot> z + y \<Zspot> z"
    and distL: "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> z \<Zspot> (x+y) = z \<Zspot> x + z \<Zspot> y"
    and scalar_compat: "\<And>a x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> (a *\<^sub>S x) \<Zspot> y = a *\<^sub>S (x \<Zspot> y) \<and> x \<Zspot> (a *\<^sub>S y) = a *\<^sub>S (x \<Zspot> y)"
    and closure: "\<And>x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> x \<Zspot> y \<in> S"
  shows "algebra_on S scale amult"
  using algebra_onI[of S scale amult] assms scale_notation_def vector_space_on_axioms by simp


subsection \<open>Lie algebra (locale)\<close>

text \<open>
  List syntax interferes with the standard notation for the Lie bracket,
  so it can be disabled it here. Instead, we add a delimiter to the notation for Lie brackets,
  which also helps with unambiguous parsing.
\<close>
(*no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
unbundle no list_syntax and no list_enumeration_syntax
*)
(*end*)

locale lie_algebra = algebra_on \<gg> scale lie_bracket + alternating_bilinear_on \<gg> scale lie_bracket
  for \<gg>
    and scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*\<^sub>S\<close> 75)
    and lie_bracket :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (\<open>[_;_]\<close> 74) +
  assumes jacobi: "\<lbrakk>x\<in>\<gg>; y\<in>\<gg>; z\<in>\<gg>\<rbrakk> \<Longrightarrow> 0 = [x;[y;z]] + [y;[z;x]] + [z;[x;y]]"

lemma (in algebra_on) lie_algebraI:
  assumes alternating: "\<forall>x\<in>S. amult x x = 0"
    and jacobi: "\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. jacobi_identity amult x y z"
  shows "lie_algebra S scale amult"
  apply unfold_locales using assms by auto

lemma (in vector_space_on) lie_algebraI:
  fixes lie_bracket :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (\<open>[_;_]\<close> 74)
    and scale_notation (infixr \<open>*\<^sub>S\<close> 75)
  defines "scale_notation \<equiv> scale"
  assumes distributivity:
      "\<And>x y z. \<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> [(x+y); z] = [x; z] + [y; z] \<and> [z; (x+y)] = [z; x] + [z; y]"
    and scalar_compatibility:
      "\<And>a x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> [(a *\<^sub>S x); y] = a *\<^sub>S ([x; y]) \<and> [x; (a *\<^sub>S y)] = a *\<^sub>S ([x; y])"
    and closure: "\<And>x y. \<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> [x; y] \<in> S"
    and alternating: "\<forall>x\<in>S. lie_bracket x x = 0"
    and jacobi: "\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. jacobi_identity lie_bracket x y z"
  shows "lie_algebra S scale lie_bracket"
  using assms(1,3,6) by (auto simp: assms(2,4,5) intro!: algebra_on.lie_algebraI algebra_onI)

context lie_algebra begin

lemma jacobi_alt:
  assumes x: "x\<in>\<gg>" and y: "y\<in>\<gg>" and z: "z\<in>\<gg>"
  shows "[x;[y;z]] = [[x;y];z] + [y;[x;z]]"
proof -
  have "[x;[y;z]] = - ([y;[z;x]]) + (- ([z;[x;y]]))"
    using jacobi[OF assms] add_implies_diff[of "[x;[y;z]]" "[y;[z;x]] + [z;[x;y]]" 0]
    by (simp add: add.commute add.left_commute)
  moreover have "[[x;y];z] = - ([z;[x;y]])" "- ([y;[z;x]]) = [y;[x;z]]"
    using antisym'[OF amult_closed[OF x y] z] antisym'[OF z x] by (simp_all add: assms)
  ultimately show "[x;[y;z]] = [[x;y];z] + [y;[x;z]]" by simp
qed


lemma lie_subalgebra:
  assumes h: "\<hh>\<subseteq>\<gg>" "m1.subspace \<hh>" and closed: "\<And>x y. x \<in> \<hh> \<Longrightarrow> y \<in> \<hh> \<Longrightarrow> lie_bracket x y \<in> \<hh>"
  shows "lie_algebra \<hh> scale lie_bracket"
proof -
  interpret \<hh>: vector_space_on \<hh> scale
    apply unfold_locales
    apply (meson h(1) m1.scale_right_distrib_on subset_iff)
    apply (meson h(1) in_mono m1.scale_left_distrib_on)
    using h(1) m1.scale_scale_on m1.scale_one_on apply auto[2]
    by (simp_all add: h m1.subspace_add m1.subspace_0 m1.subspace_scale)

  show ?thesis
    apply (intro \<hh>.lie_algebraI)
    using alternating h(1) jacobi linearL' linearR' by (auto simp: closed subset_iff)
qed

end


subsection \<open>Division algebras\<close>

abbreviation (in algebra_on) "is_left_divisor x a b  \<equiv>  x \<in> S  \<and>  a = amult x b"
abbreviation (in algebra_on) "is_right_divisor x a b  \<equiv>  x \<in> S  \<and>  a = amult b x"

locale div_algebra_on = algebra_on +
  fixes divL::"'a\<Rightarrow>'a\<Rightarrow>'a" (* (infix "/\<^sub>L" 74) *)
    and divR::"'a\<Rightarrow>'a\<Rightarrow>'a" (* (infix "/\<^sub>R" 74) *)
  assumes divL: "\<lbrakk>a\<in>S; b\<in>S; b\<noteq>0\<rbrakk> \<Longrightarrow> is_left_divisor (divL a b) a b"
      "\<lbrakk>a\<in>S; b\<in>S; b\<noteq>0\<rbrakk> \<Longrightarrow> is_left_divisor y a b \<Longrightarrow> y = (divL a b)"
    and divR: "\<lbrakk>a\<in>S; b\<in>S; b\<noteq>0\<rbrakk> \<Longrightarrow> is_right_divisor (divR a b) a b"
      "\<lbrakk>a\<in>S; b\<in>S; b\<noteq>0\<rbrakk> \<Longrightarrow> is_right_divisor y a b \<Longrightarrow> y = (divR a b)"
begin
text \<open> In terms of the vocabulary of division rings,
  the expression \<^term>\<open>a = (divL a b) \<Zspot> b\<close> means that \<^term>\<open>divL a b\<close> is a left divisor of \<^term>\<open>a\<close>,
  and conversely that \<^term>\<open>a\<close> is a right multiple of \<^term>\<open>divL a b\<close>.\<close>
text \<open>
  For \<^term>\<open>b=0\<close>, the divisiors still exist as members of the correct type (necessarily),
  but they have no properties. Similarly for correctly-typed input outside the algebra.\<close>

  lemma [simp]:
    assumes "a\<in>S" "b\<in>S" "b\<noteq>0"
    shows divL': "divL a b \<in> S" "(divL a b) \<Zspot> b = a" "\<forall>y\<in>S. a = y \<Zspot> b \<longrightarrow> y = divL a b"
      and divR': "divR a b \<in> S" "b \<Zspot> (divR a b) = a" "\<forall>y\<in>S. a = b \<Zspot> y \<longrightarrow> y = divR a b"
    using assms divL divR by simp_all
end

lemma (in algebra_on) div_algebra_onI:
  assumes "\<forall>a\<in>S. \<forall>b\<in>S. b\<noteq>0 \<longrightarrow> (\<exists>!x\<in>S. a=b\<Zspot>x) \<and> (\<exists>!y\<in>S. a=y\<Zspot>b)"
  shows "div_algebra_on S scale amult (\<lambda>a b. THE y. y\<in>S \<and> a=y\<Zspot>b) (\<lambda>a b. THE x. x\<in>S \<and> a=b\<Zspot>x)"
proof (unfold div_algebra_on_def div_algebra_on_axioms_def, intro conjI allI impI)
  fix a b x
  assume "a\<in>S" "b\<in>S" "b\<noteq>0"
  have exL: "\<exists>!x\<in>S. a=x\<Zspot>b" by (simp add: \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>b \<noteq> 0\<close> assms)
  from theI'[OF this]
    show L: "(THE y. y \<in> S \<and> a = y \<Zspot> b) \<in> S" "a = (THE y. y \<in> S \<and> a = y \<Zspot> b) \<Zspot> b"
    by simp+
  have exR: "\<exists>!x\<in>S. a=b\<Zspot>x" by (simp add: \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>b \<noteq> 0\<close> assms)
  from theI'[OF this]
    show R: "(THE x. x \<in> S \<and> a = b \<Zspot> x) \<in> S" "a = b \<Zspot> (THE x. x \<in> S \<and> a = b \<Zspot> x)"
    by simp+
  { assume "x \<in> S \<and> a = x \<Zspot> b"
    thus "x = (THE y. y \<in> S \<and> a = y \<Zspot> b)" using L exL by auto
  } { assume "x \<in> S \<and> a = b \<Zspot> x"
    thus "x = (THE x. x \<in> S \<and> a = b \<Zspot> x)" using R exR by auto
  }
qed (simp add: algebra_on_axioms)

lemma (in assoc_algebra_1_on) div_algebra_onI':
  fixes ainv adivL adivR
  defines "ainv a \<equiv> (THE x. x\<in>S \<and> a_id=x\<Zspot>a \<and> a_id=a\<Zspot>x)"
    and "adivL b a \<equiv> b \<Zspot> (ainv a)"
    and "adivR b a \<equiv> (ainv a) \<Zspot> b"
  assumes "\<forall>a\<in>S. a\<noteq>0 \<longrightarrow> (\<exists>x\<in>S. a_id=x\<Zspot>a \<and> a_id=a\<Zspot>x)"
  shows "div_algebra_on S scale amult adivL adivR"
proof (unfold_locales)
  fix a b
  assume asm: "a \<in> S" "b \<in> S" "b \<noteq> 0"
  have inv_ex: "\<exists>!x\<in>S. a_id=x\<Zspot>b \<and> a_id=b\<Zspot>x"
    using assms(4) inverse_unique' asm(2,3) by metis
  let ?a = "THE x. x \<in> S \<and> a_id = x \<Zspot> b \<and> a_id = b \<Zspot> x"
  from theI'[OF inv_ex] show 1: "adivR a b \<in> S \<and> a = b \<Zspot> adivR a b"
    unfolding adivR_def ainv_def apply (intro conjI)
    using asm(1) apply simp
    using amult_assoc amult_id(2) asm(1,2) is_ring_1_axioms(2) by (metis (no_types, lifting))
  from theI'[OF inv_ex] show 2: "adivL a b \<in> S \<and> a = adivL a b \<Zspot> b"
    unfolding adivL_def ainv_def apply (intro conjI)
    apply (simp add: asm(1))
    using amult_assoc asm(1,2) is_ring_1_axioms(3) by presburger
  { fix y assume "y \<in> S \<and> a = y \<Zspot> b"
    thus "y = adivL a b"
      by (metis inv_ex 2 amult_assoc asm(2) amult_id(2))
  } { fix y assume "y \<in> S \<and> a = b \<Zspot> y"
    thus "y = adivR a b"
    by (metis 1 amult_assoc asm(2) inv_ex is_ring_1_axioms(2)) }
qed

lemma (in assoc_algebra_on) div_algebra_on_imp_inverse:
  assumes "div_algebra_on S scale amult divL divR" "card S \<ge> 2 \<or> infinite S"
  shows "\<exists>a_id\<in>S. (\<forall>a\<in>S. a\<Zspot>a_id=a \<and> a_id\<Zspot>a=a) \<and> (\<forall>a\<in>S. a\<noteq>0 \<longrightarrow> divL a_id a = divR a_id a)"
proof -
  obtain x where "x\<noteq>0" "x\<in>S"
    using assms(2) unfolding numeral_2_eq_2
    by (metis card_1_singleton_iff card_gt_0_iff card_le_Suc0_iff_eq insertI1 not_less_eq_eq
      rev_finite_subset subsetI zero_less_Suc)
  let ?id = "divL x x"
  show ?thesis
  proof (intro bexI conjI ballI impI)
    show 1: "?id \<in> S"
      using assms unfolding div_algebra_on_def div_algebra_on_axioms_def
      using \<open>x \<in> S\<close> \<open>x \<noteq> 0\<close> by blast
    fix a assume "a\<in>S"
    show 2: "a \<Zspot> ?id = a"
      by (smt (verit) 1 \<open>a\<in>S\<close> \<open>x\<in>S\<close> \<open>x\<noteq>0\<close> amult_assoc amult_closed assms(1) div_algebra_on.divL)
    show 3: "?id \<Zspot> a = a"
      by (smt (verit) \<open>a\<in>S\<close> \<open>x\<in>S\<close> \<open>x\<noteq>0\<close> amult_assoc assms(1) div_algebra_on.divL(1) div_algebra_on.divR')
    assume "a\<noteq>0"
    show 4: "divL ?id a = divR ?id a"
      by (smt (verit) 1 3 \<open>a\<in>S\<close> \<open>a\<noteq>0\<close> amult_assoc amult_closed assms(1) div_algebra_on.divL div_algebra_on.divR(2))
  qed
qed

lemma (in assoc_algebra_on) assoc_div_algebra_on_iff:
  assumes "card S \<ge> 2 \<or> infinite S"
  shows "(\<exists>divL divR. div_algebra_on S scale amult divL divR) \<longleftrightarrow>
      (\<exists>id. unital_algebra_on S scale amult id \<and> (\<forall>a\<in>S. a\<noteq>0 \<longrightarrow> (\<exists>x\<in>S. a\<Zspot>x=id \<and> x\<Zspot>a=id)))"
  proof (intro iffI)
    assume "\<exists>id. unital_algebra_on S (*\<^sub>S) (\<Zspot>) id \<and> (\<forall>a\<in>S. a \<noteq> 0 \<longrightarrow> (\<exists>x\<in>S. a \<Zspot> x = id \<and> x \<Zspot> a = id))"
    then obtain id
      where id: "id\<in>S" "\<forall>a\<in>S. a\<Zspot>id=a \<and> id\<Zspot>a=a" and inv: "\<forall>a\<in>S. a\<noteq>0 \<longrightarrow> (\<exists>x\<in>S. a\<Zspot>x=id \<and> x\<Zspot>a=id)"
      using unital_algebra_on.amult_id by blast
    then have unital: "unital_algebra_on S scale amult id"
      by (unfold_locales, simp_all)
    then have assoc_alg: "assoc_algebra_1_on S scale amult id"
      unfolding assoc_algebra_1_on_def assoc_algebra_1_on_axioms_def
      using assms unital_algebra_on.id_neq_0_if(2,3) assoc_algebra_on_axioms
      by blast
    show "\<exists>divL divR. div_algebra_on S (*\<^sub>S) (\<Zspot>) divL divR"
      using assoc_algebra_1_on.div_algebra_onI'[OF assoc_alg] inv by fastforce
  next
    assume "\<exists>divL divR. div_algebra_on S (*\<^sub>S) (\<Zspot>) divL divR"
    then obtain divL divR where div_alg: "div_algebra_on S (*\<^sub>S) (\<Zspot>) divL divR" by blast
    show "\<exists>id. unital_algebra_on S (*\<^sub>S) (\<Zspot>) id \<and> (\<forall>a\<in>S. a \<noteq> 0 \<longrightarrow> (\<exists>x\<in>S. a \<Zspot> x = id \<and> x \<Zspot> a = id))"
      using div_algebra_on_imp_inverse[OF div_alg assms] unital_algebra_on_axioms.intro assoc_algebra_on_axioms
      unfolding unital_algebra_on_def unital_algebra_on_axioms_def assoc_algebra_on_def
      by (smt (verit) div_alg div_algebra_on.divL(1) div_algebra_on.divR(1))
qed


locale assoc_div_algebra_on =
  assoc_algebra_1_on S scale amult a_id +
  div_algebra_on S scale amult "\<lambda>a b. amult a (a_inv b)" "\<lambda>a b. amult (a_inv b) a"
  for S
    and scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*\<^sub>S\<close> 75)
    and amult :: "'b\<Rightarrow>'b\<Rightarrow>'b" (infixr \<open>\<Zspot>\<close> 74)
    and a_id  :: 'b(\<open>\<one>\<close>)
    and a_inv :: "'b\<Rightarrow>'b" (* (\<open>_\<^sup>\<Zspot>\<close> 73) *)
begin
text \<open>
  The definition \<^locale>\<open>assoc_div_algebra_on\<close> is justified by @{thm assoc_div_algebra_on_iff} above:
  If we have an associative algebra already, the only way it can be a division algebra
  is to be unital as well. Since now left and right divisors can be defined through
  multiplicative inverses, we take only the inverse as a locale parameter, and construct
  the divisors.
  The only case we miss here (due to the requirement \<^term>\<open>a_id\<noteq>0\<close>) is the trivial algebra,
  which contains only the zero element (which acts as identity as well). This is for compatibility
  with the standard Isabelle/HOL type classes, which are subclasses of \<^class>\<open>zero_neq_one\<close>.
\<close>

  abbreviation (input) divL :: "'b\<Rightarrow>'b\<Rightarrow>'b"
    where "divL a b \<equiv> amult a (a_inv b)"

  abbreviation (input) divR :: "'b\<Rightarrow>'b\<Rightarrow>'b"
    where "divR a b \<equiv> amult (a_inv b) a"

  lemma div_self_eq_id:
    assumes "a\<in>S" "a\<noteq>0"
    shows "divL a a = a_id"
      and "divR a a = a_id"
    apply (metis amult_id(1,3) assms divL'(3))
    by (metis amult_id(1,2) assms divR'(3))

end


locale finite_dimensional_assoc_div_algebra_on =
  assoc_div_algebra_on S scale amult a_id a_inv +
  finite_dimensional_vector_space_on S scale basis
  for S :: \<open>'b::ab_group_add set\<close>
    and scale :: \<open>'a::field \<Rightarrow> 'b \<Rightarrow> 'b\<close>  (infixr \<open>*\<^sub>S\<close> 75)
    and amult :: \<open>'b\<Rightarrow>'b\<Rightarrow>'b\<close>             (infixr \<open>\<Zspot>\<close> 74)
    and a_id  :: \<open>'b\<close>                   (\<open>\<one>\<close>)
    and a_inv :: \<open>'b\<Rightarrow>'b\<close>                (*(\<open>_\<^sup>\<Zspot>\<close> 73)*)
    and basis :: \<open>'b set\<close>


lemma (in assoc_div_algebra_on) finite_dimensional_assoc_div_algebra_onI [intro]:
  fixes basis :: "'b set"
  assumes finite_Basis: "finite basis"
    and independent_Basis: "\<not> m1.dependent basis"
    and span_Basis: "m1.span basis = S"
    and basis_subset: "basis \<subseteq> S"
  shows "finite_dimensional_assoc_div_algebra_on S scale amult a_id a_inv basis"
  by (unfold_locales, simp_all add: assms)

end