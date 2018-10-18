(* Author: Andreas Lochbihler, ETH Zurich
   Author: Florian Haftmann, TU Muenchen
*)

section \<open>Polynomial mapping: combination of almost everywhere zero functions with an algebraic view\<close>

theory Poly_Mapping
imports
  "HOL-Library.Groups_Big_Fun"
  "HOL-Library.Fun_Lexorder"
  "HOL-Library.More_List"
begin

subsection \<open>Preliminary: auxiliary operations for \qt{almost everywhere zero}\<close>

text \<open>
  A central notion for polynomials are functions being \qt{almost everywhere zero}.
  For these we provide some auxiliary definitions and lemmas.
\<close>

lemma finite_mult_not_eq_zero_leftI:
  fixes f :: "'b \<Rightarrow> 'a :: mult_zero"
  assumes "finite {a. f a \<noteq> 0}"
  shows "finite {a. g a * f a \<noteq> 0}"
proof -
  have "{a. g a * f a \<noteq> 0} \<subseteq> {a. f a \<noteq> 0}" by auto
  then show ?thesis using assms by (rule finite_subset)
qed

lemma finite_mult_not_eq_zero_rightI:
  fixes f :: "'b \<Rightarrow> 'a :: mult_zero"
  assumes "finite {a. f a \<noteq> 0}"
  shows "finite {a. f a * g a \<noteq> 0}"
proof -
  have "{a. f a * g a \<noteq> 0} \<subseteq> {a. f a \<noteq> 0}" by auto
  then show ?thesis using assms by (rule finite_subset)
qed

lemma finite_mult_not_eq_zero_prodI:
  fixes f g :: "'a \<Rightarrow> 'b::semiring_0"
  assumes "finite {a. f a \<noteq> 0}" (is "finite ?F")
  assumes "finite {b. g b \<noteq> 0}" (is "finite ?G")
  shows "finite {(a, b). f a * g b \<noteq> 0}"
proof -
  from assms have "finite (?F \<times> ?G)"
    by blast
  then have "finite {(a, b). f a \<noteq> 0 \<and> g b \<noteq> 0}"
    by simp
  then show ?thesis
    by (rule rev_finite_subset) auto
qed

lemma finite_not_eq_zero_sumI:
  fixes f g :: "'a::monoid_add \<Rightarrow> 'b::semiring_0"
  assumes "finite {a. f a \<noteq> 0}" (is "finite ?F")
  assumes "finite {b. g b \<noteq> 0}" (is "finite ?G")
  shows "finite {a + b | a b. f a \<noteq> 0 \<and> g b \<noteq> 0}" (is "finite ?FG")
proof -
  from assms have "finite (?F \<times> ?G)"
    by (simp add: finite_cartesian_product_iff)
  then have "finite (case_prod plus ` (?F \<times> ?G))"
    by (rule finite_imageI)
  also have "case_prod plus ` (?F \<times> ?G) = ?FG"
    by auto
  finally show ?thesis
    by simp
qed

lemma finite_mult_not_eq_zero_sumI:
  fixes f g :: "'a::monoid_add \<Rightarrow> 'b::semiring_0"
  assumes "finite {a. f a \<noteq> 0}"
  assumes "finite {b. g b \<noteq> 0}"
  shows "finite {a + b | a b. f a * g b \<noteq> 0}"
proof -
  from assms
  have "finite {a + b | a b. f a \<noteq> 0 \<and> g b \<noteq> 0}"
    by (rule finite_not_eq_zero_sumI)
  then show ?thesis
    by (rule rev_finite_subset) (auto dest: mult_not_zero)
qed

lemma finite_Sum_any_not_eq_zero_weakenI:
  assumes "finite {a. \<exists>b. f a b \<noteq> 0}"
  shows "finite {a. Sum_any (f a) \<noteq> 0}"
proof -
  have "{a. Sum_any (f a) \<noteq> 0} \<subseteq> {a. \<exists>b. f a b \<noteq> 0}"
    by (auto elim: Sum_any.not_neutral_obtains_not_neutral)
  then show ?thesis using assms by (rule finite_subset)
qed

context zero
begin

definition "when" :: "'a \<Rightarrow> bool \<Rightarrow> 'a" (infixl "when" 20)
where
  "(a when P) = (if P then a else 0)"

text \<open>
  Case distinctions always complicate matters, particularly when
  nested.  The @{const "when"} operation allows to minimise these
  if @{term 0} is the false-case value and makes proof obligations
  much more readable.
\<close>

lemma "when" [simp]:
  "P \<Longrightarrow> (a when P) = a"
  "\<not> P \<Longrightarrow> (a when P) = 0"
  by (simp_all add: when_def)

lemma when_simps [simp]:
  "(a when True) = a"
  "(a when False) = 0"
  by simp_all

lemma when_cong:
  assumes "P \<longleftrightarrow> Q"
    and "Q \<Longrightarrow> a = b"
  shows "(a when P) = (b when Q)"
  using assms by (simp add: when_def)

lemma zero_when [simp]:
  "(0 when P) = 0"
  by (simp add: when_def)

lemma when_when:
  "(a when P when Q) = (a when P \<and> Q)"
  by (cases Q) simp_all

lemma when_commute:
  "(a when Q when P) = (a when P when Q)"
  by (simp add: when_when conj_commute)

lemma when_neq_zero [simp]:
  "(a when P) \<noteq> 0 \<longleftrightarrow> P \<and> a \<noteq> 0"
  by (cases P) simp_all

end

context monoid_add
begin

lemma when_add_distrib:
  "(a + b when P) = (a when P) + (b when P)"
  by (simp add: when_def)

end

context semiring_1
begin

lemma zero_power_eq:
  "0 ^ n = (1 when n = 0)"
  by (simp add: power_0_left)

end

context comm_monoid_add
begin

lemma Sum_any_when_equal [simp]:
  "(\<Sum>a. (f a when a = b)) = f b"
  by (simp add: when_def)

lemma Sum_any_when_equal' [simp]:
  "(\<Sum>a. (f a when b = a)) = f b"
  by (simp add: when_def)

lemma Sum_any_when_independent:
  "(\<Sum>a. g a when P) = ((\<Sum>a. g a) when P)"
  by (cases P) simp_all

lemma Sum_any_when_dependent_prod_right:
  "(\<Sum>(a, b). g a when b = h a) = (\<Sum>a. g a)"
proof -
  have "inj_on (\<lambda>a. (a, h a)) {a. g a \<noteq> 0}"
    by (rule inj_onI) auto
  then show ?thesis unfolding Sum_any.expand_set
    by (rule sum.reindex_cong) auto
qed

lemma Sum_any_when_dependent_prod_left:
  "(\<Sum>(a, b). g b when a = h b) = (\<Sum>b. g b)"
proof -
  have "(\<Sum>(a, b). g b when a = h b) = (\<Sum>(b, a). g b when a = h b)"
    by (rule Sum_any.reindex_cong [of prod.swap]) (simp_all add: fun_eq_iff)
  then show ?thesis by (simp add: Sum_any_when_dependent_prod_right)
qed

end

context cancel_comm_monoid_add
begin

lemma when_diff_distrib:
  "(a - b when P) = (a when P) - (b when P)"
  by (simp add: when_def)

end

context group_add
begin

lemma when_uminus_distrib:
  "(- a when P) = - (a when P)"
  by (simp add: when_def)

end

context mult_zero
begin

lemma mult_when:
  "a * (b when P) = (a * b when P)"
  by (cases P) simp_all

lemma when_mult:
  "(a when P) * b = (a * b when P)"
  by (cases P) simp_all

end


subsection \<open>Type definition\<close>

text \<open>
  The following type is of central importance:
\<close>

typedef (overloaded) ('a, 'b) poly_mapping ("(_ \<Rightarrow>\<^sub>0 /_)" [1, 0] 0) =
  "{f :: 'a \<Rightarrow> 'b::zero. finite {x. f x \<noteq> 0}}"
  morphisms lookup Abs_poly_mapping
proof -
  have "(\<lambda>_::'a. (0 :: 'b)) \<in> ?poly_mapping" by simp
  then show ?thesis by (blast intro!: exI)
qed

lemma lookup_Abs_poly_mapping:
  "finite {x. f x \<noteq> 0} \<Longrightarrow> lookup (Abs_poly_mapping f) = f"
  using Abs_poly_mapping_inverse [of f] by simp

lemma finite_lookup [simp]:
  "finite {k. lookup f k \<noteq> 0}"
  using poly_mapping.lookup [of f] by simp

lemma finite_lookup_nat [simp]:
  fixes f :: "'a \<Rightarrow>\<^sub>0 nat"
  shows "finite {k. 0 < lookup f k}"
  using poly_mapping.lookup [of f] by simp

lemma poly_mapping_eqI:
  assumes "\<And>k. lookup f k = lookup g k"
  shows "f = g"
  using assms unfolding poly_mapping.lookup_inject [symmetric] by auto

lemma poly_mapping_eq_iff: "a = b \<longleftrightarrow> lookup a = lookup b"
  unfolding fun_eq_iff using poly_mapping_eqI by blast

text \<open>
  We model the universe of functions being \qt{almost everywhere zero}
  by means of a separate type @{typ "('a, 'b) poly_mapping"}.
  For convenience we provide a suggestive infix syntax which
  is a variant of the usual function space syntax.  Conversion between both types
  happens through the morphisms
  \begin{quote}
    @{term_type lookup}
  \end{quote}
  \begin{quote}
    @{term_type Abs_poly_mapping}
  \end{quote}
  satisfying
  \begin{quote}
    @{thm lookup_inverse}
  \end{quote}
  \begin{quote}
    @{thm lookup_Abs_poly_mapping}
  \end{quote}
  Luckily, we have rarely to deal with those low-level morphisms explicitly
  but rely on Isabelle's \emph{lifting} package with its method @{text transfer}
  and its specification tool @{text lift_definition}.
\<close>

setup_lifting type_definition_poly_mapping
code_datatype Abs_poly_mapping\<comment>\<open>FIXME? workaround for preventing \<open>code_abstype\<close> setup\<close>

text \<open>
  @{typ "'a \<Rightarrow>\<^sub>0 'b"} serves distinctive purposes:
  \begin{enumerate}
    \item A clever nesting as @{typ "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"}
      later in theory @{text MPoly} gives a suitable
      representation type for polynomials \qt{almost for free}:
      Interpreting @{typ "nat \<Rightarrow>\<^sub>0 nat"} as a mapping from variable identifiers
      to exponents yields monomials, and the whole type maps monomials
      to coefficients.  Lets call this the \emph{ultimate interpretation}.
    \item A further more specialised type isomorphic to @{typ "nat \<Rightarrow>\<^sub>0 'a"}
      is apt to direct implementation using code generation
      \cite{Haftmann-Nipkow:2010:code}.
  \end{enumerate}
  Note that despite the names \qt{mapping} and \qt{lookup} suggest something
  implementation-near, it is best to keep @{typ "'a \<Rightarrow>\<^sub>0 'b"} as an abstract
  \emph{algebraic} type
  providing operations like \qt{addition}, \qt{multiplication} without any notion
  of key-order, data structures etc.  This implementations-specific notions are
  easily introduced later for particular implementations but do not provide any
  gain for specifying logical properties of polynomials.
\<close>

subsection \<open>Additive structure\<close>

text \<open>
  The additive structure covers the usual operations @{text 0}, @{text "+"} and
  (unary and binary) @{text "-"}.  Recalling the ultimate interpretation, it
  is obvious that these have just lift the corresponding operations on values
  to mappings.

  Isabelle has a rich hierarchy of algebraic type classes, and in such situations
  of pointwise lifting a typical pattern is to have instantiations for a considerable
  number of type classes.

  The operations themselves are specified using @{text lift_definition}, where
  the proofs of the \qt{almost everywhere zero} property can be significantly involved.

  The @{const lookup} operation is supposed to be usable explicitly (unless in
  other situations where the morphisms between types are somehow internal
  to the \emph{lifting} package).  Hence it is good style to provide explicit rewrite
  rules how @{const lookup} acts on operations immediately.
\<close>

instantiation poly_mapping :: (type, zero) zero
begin

lift_definition zero_poly_mapping :: "'a \<Rightarrow>\<^sub>0 'b"
  is "\<lambda>k. 0"
  by simp

instance ..

end

lemma lookup_zero [simp]:
  "lookup 0 k = 0"
  by transfer rule

instantiation poly_mapping :: (type, monoid_add) monoid_add
begin

lift_definition plus_poly_mapping ::
    "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is "\<lambda>f1 f2 k. f1 k + f2 k"
proof -
  fix f1 f2 :: "'a \<Rightarrow> 'b"
  assume "finite {k. f1 k \<noteq> 0}"
    and "finite {k. f2 k \<noteq> 0}"
  then have "finite ({k. f1 k \<noteq> 0} \<union> {k. f2 k \<noteq> 0})" by auto
  moreover have "{x. f1 x + f2 x \<noteq> 0} \<subseteq> {k. f1 k \<noteq> 0} \<union> {k. f2 k \<noteq> 0}"
    by auto
  ultimately show "finite {x. f1 x + f2 x \<noteq> 0}"
    by (blast intro: finite_subset)
qed

instance
  by intro_classes (transfer, simp add: fun_eq_iff ac_simps)+

end

lemma lookup_add:
  "lookup (f + g) k = lookup f k + lookup g k"
  by transfer rule

instance poly_mapping :: (type, comm_monoid_add) comm_monoid_add
  by intro_classes (transfer, simp add: fun_eq_iff ac_simps)+

lemma lookup_sum: "lookup (sum pp X) i = sum (\<lambda>x. lookup (pp x) i) X"
  by (induction rule: infinite_finite_induct) (auto simp: lookup_add)

(*instance poly_mapping :: (type, "{monoid_add, cancel_semigroup_add}") cancel_semigroup_add
  by intro_classes (transfer, simp add: fun_eq_iff)+*)

instantiation poly_mapping :: (type, cancel_comm_monoid_add) cancel_comm_monoid_add
begin

lift_definition minus_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is "\<lambda>f1 f2 k. f1 k - f2 k"
proof -
  fix f1 f2 :: "'a \<Rightarrow> 'b"
  assume "finite {k. f1 k \<noteq> 0}"
    and "finite {k. f2 k \<noteq> 0}"
  then have "finite ({k. f1 k \<noteq> 0} \<union> {k. f2 k \<noteq> 0})" by auto
  moreover have "{x. f1 x - f2 x \<noteq> 0} \<subseteq> {k. f1 k \<noteq> 0} \<union> {k. f2 k \<noteq> 0}"
    by auto
  ultimately show "finite {x. f1 x - f2 x \<noteq> 0}" by (blast intro: finite_subset)
qed

instance
  by intro_classes (transfer, simp add: fun_eq_iff diff_diff_add)+

end

instantiation poly_mapping :: (type, ab_group_add) ab_group_add
begin

lift_definition uminus_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is uminus
  by simp


instance
  by intro_classes (transfer, simp add: fun_eq_iff ac_simps)+

end

lemma lookup_uminus [simp]:
  "lookup (- f) k = - lookup f k"
  by transfer simp

lemma lookup_minus:
  "lookup (f - g) k = lookup f k - lookup g k"
  by transfer rule


subsection \<open>Multiplicative structure\<close>

instantiation poly_mapping :: (zero, zero_neq_one) zero_neq_one
begin

lift_definition one_poly_mapping :: "'a \<Rightarrow>\<^sub>0 'b"
  is "\<lambda>k. 1 when k = 0"
  by simp

instance
  by intro_classes (transfer, simp add: fun_eq_iff)

end

lemma lookup_one:
  "lookup 1 k = (1 when k = 0)"
  by transfer rule

lemma lookup_one_zero [simp]:
  "lookup 1 0 = 1"
  by transfer simp

definition prod_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a::monoid_add \<Rightarrow> 'b::semiring_0"
where
  "prod_fun f1 f2 k = (\<Sum>l. f1 l * (\<Sum>q. (f2 q when k = l + q)))"

lemma prod_fun_unfold_prod:
  fixes f g :: "'a :: monoid_add \<Rightarrow> 'b::semiring_0"
  assumes fin_f: "finite {a. f a \<noteq> 0}"
  assumes fin_g: "finite {b. g b \<noteq> 0}"
  shows "prod_fun f g k = (\<Sum>(a, b). f a * g b when k = a + b)"
proof -
  let ?C = "{a. f a \<noteq> 0} \<times> {b. g b \<noteq> 0}"
  from fin_f fin_g have "finite ?C" by blast
  moreover have "{a. \<exists>b. (f a * g b when k = a + b) \<noteq> 0} \<times>
    {b. \<exists>a. (f a * g b when k = a + b) \<noteq> 0} \<subseteq> {a. f a \<noteq> 0} \<times> {b. g b \<noteq> 0}"
    by auto
  ultimately show ?thesis using fin_g
    by (auto simp add: prod_fun_def
      Sum_any.cartesian_product [of "{a. f a \<noteq> 0} \<times> {b. g b \<noteq> 0}"] Sum_any_right_distrib mult_when)
qed

lemma finite_prod_fun:
  fixes f1 f2 :: "'a :: monoid_add \<Rightarrow> 'b :: semiring_0"
  assumes fin1: "finite {l. f1 l \<noteq> 0}"
  and fin2: "finite {q. f2 q \<noteq> 0}"
  shows "finite {k. prod_fun f1 f2 k \<noteq> 0}"
proof -
  have *: "finite {k. (\<exists>l. f1 l \<noteq> 0 \<and> (\<exists>q. f2 q \<noteq> 0 \<and> k = l + q))}"
    using assms by simp
  { fix k l
    have "{q. (f2 q when k = l + q) \<noteq> 0} \<subseteq> {q. f2 q \<noteq> 0 \<and> k = l + q}" by auto
    with fin2 have "sum f2 {q. f2 q \<noteq> 0 \<and> k = l + q} = (\<Sum>q. (f2 q when k = l + q))"
      by (simp add: Sum_any.expand_superset [of "{q. f2 q \<noteq> 0 \<and> k = l + q}"]) }
  note aux = this
  have "{k. (\<Sum>l. f1 l * sum f2 {q. f2 q \<noteq> 0 \<and> k = l + q}) \<noteq> 0}
    \<subseteq> {k. (\<exists>l. f1 l * sum f2 {q. f2 q \<noteq> 0 \<and> k = l + q} \<noteq> 0)}"
    by (auto elim!: Sum_any.not_neutral_obtains_not_neutral)
  also have "\<dots> \<subseteq> {k. (\<exists>l. f1 l \<noteq> 0 \<and> sum f2 {q. f2 q \<noteq> 0 \<and> k = l + q} \<noteq> 0)}"
    by (auto dest: mult_not_zero)
  also have "\<dots> \<subseteq> {k. (\<exists>l. f1 l \<noteq> 0 \<and> (\<exists>q. f2 q \<noteq> 0 \<and> k = l + q))}"
    by (auto elim!: sum.not_neutral_contains_not_neutral)
  finally have "finite {k. (\<Sum>l. f1 l * sum f2 {q. f2 q \<noteq> 0 \<and> k = l + q}) \<noteq> 0}"
    using * by (rule finite_subset)
  with aux have "finite {k. (\<Sum>l. f1 l * (\<Sum>q. (f2 q when k = l + q))) \<noteq> 0}"
    by simp
  with fin2 show ?thesis
   by (simp add: prod_fun_def)
qed

instantiation poly_mapping :: (monoid_add, semiring_0) semiring_0
begin

lift_definition times_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is prod_fun
by(rule finite_prod_fun)

instance
proof
  fix a b c :: "'a \<Rightarrow>\<^sub>0 'b"
  show "a * b * c = a * (b * c)"
  proof transfer
    fix f g h :: "'a \<Rightarrow> 'b"
    assume fin_f: "finite {a. f a \<noteq> 0}" (is "finite ?F")
    assume fin_g: "finite {b. g b \<noteq> 0}" (is "finite ?G")
    assume fin_h: "finite {c. h c \<noteq> 0}" (is "finite ?H")
    from fin_f fin_g have fin_fg: "finite {(a, b). f a * g b \<noteq> 0}" (is "finite ?FG")
      by (rule finite_mult_not_eq_zero_prodI)
    from fin_g fin_h have fin_gh: "finite {(b, c). g b * h c \<noteq> 0}" (is "finite ?GH")
      by (rule finite_mult_not_eq_zero_prodI)
    from fin_f fin_g have fin_fg': "finite {a + b | a b. f a * g b \<noteq> 0}" (is "finite ?FG'")
      by (rule finite_mult_not_eq_zero_sumI)
    then have fin_fg'': "finite {d. (\<Sum>(a, b). f a * g b when d = a + b) \<noteq> 0}"
      by (auto intro: finite_Sum_any_not_eq_zero_weakenI)
    from fin_g fin_h have fin_gh': "finite {b + c | b c. g b * h c \<noteq> 0}" (is "finite ?GH'")
      by (rule finite_mult_not_eq_zero_sumI)
    then have fin_gh'': "finite {d. (\<Sum>(b, c). g b * h c when d = b + c) \<noteq> 0}"
      by (auto intro: finite_Sum_any_not_eq_zero_weakenI)
    show "prod_fun (prod_fun f g) h = prod_fun f (prod_fun g h)" (is "?lhs = ?rhs")
    proof
      fix k
      from fin_f fin_g fin_h fin_fg''
      have "?lhs k = (\<Sum>(ab, c). (\<Sum>(a, b). f a * g b when ab = a + b) * h c when k = ab + c)"
        by (simp add: prod_fun_unfold_prod)
      also have "\<dots> = (\<Sum>(ab, c). (\<Sum>(a, b). f a * g b * h c when k = ab + c when ab = a + b))"
        apply (subst Sum_any_left_distrib)
        using fin_fg apply (simp add: split_def)
        apply (subst Sum_any_when_independent [symmetric])
        apply (simp add: when_when when_mult mult_when split_def conj_commute)
        done
      also have "\<dots> = (\<Sum>(ab, c, a, b). f a * g b * h c when k = ab + c when ab = a + b)"
        apply (subst Sum_any.cartesian_product2 [of "(?FG' \<times> ?H) \<times> ?FG"])
        apply (auto simp add: finite_cartesian_product_iff fin_fg fin_fg' fin_h dest: mult_not_zero)
        done
      also have "\<dots> = (\<Sum>(ab, c, a, b). f a * g b * h c when k = a + b + c when ab = a + b)"
        by (rule Sum_any.cong) (simp add: split_def when_def)
      also have "\<dots> = (\<Sum>(ab, cab). (case cab of (c, a, b) \<Rightarrow> f a * g b * h c when k = a + b + c)
        when ab = (case cab of (c, a, b) \<Rightarrow> a + b))"
        by (simp add: split_def)
      also have "\<dots> = (\<Sum>(c, a, b). f a * g b * h c when k = a + b + c)"
        by (simp add: Sum_any_when_dependent_prod_left)
      also have "\<dots> = (\<Sum>(bc, cab). (case cab of (c, a, b) \<Rightarrow> f a * g b * h c when k = a + b + c)
        when bc = (case cab of (c, a, b) \<Rightarrow> b + c))"
        by (simp add: Sum_any_when_dependent_prod_left)
      also have "\<dots> = (\<Sum>(bc, c, a, b). f a * g b * h c when k = a + b + c when bc = b + c)"
        by (simp add: split_def)
      also have "\<dots> = (\<Sum>(bc, c, a, b). f a * g b * h c when bc = b + c when k = a + bc)"
        by (rule Sum_any.cong) (simp add: split_def when_def ac_simps)
      also have "\<dots> = (\<Sum>(a, bc, b, c). f a * g b * h c when bc = b + c when k = a + bc)"
      proof -
        have "bij (\<lambda>(a, d, b, c). (d, c, a, b))"
          by (auto intro!: bijI injI surjI [of _ "\<lambda>(d, c, a, b). (a, d, b, c)"] simp add: split_def)
        then show ?thesis
          by (rule Sum_any.reindex_cong) auto
      qed
      also have "\<dots> = (\<Sum>(a, bc). (\<Sum>(b, c). f a * g b * h c when bc = b + c when k = a + bc))"
        apply (subst Sum_any.cartesian_product2 [of "(?F \<times> ?GH') \<times> ?GH"])
        apply (auto simp add: finite_cartesian_product_iff fin_f fin_gh fin_gh' ac_simps dest: mult_not_zero)
        done
      also have "\<dots> = (\<Sum>(a, bc). f a * (\<Sum>(b, c). g b * h c when bc = b + c) when k = a + bc)"
        apply (subst Sum_any_right_distrib)
        using fin_gh apply (simp add: split_def)
        apply (subst Sum_any_when_independent [symmetric])
        apply (simp add: when_when when_mult mult_when split_def ac_simps)
        done
      also from fin_f fin_g fin_h fin_gh''
      have "\<dots> = ?rhs k"
        by (simp add: prod_fun_unfold_prod)
      finally show "?lhs k = ?rhs k" .
    qed
  qed
  show "(a + b) * c = a * c + b * c"
  proof transfer
    fix f g h :: "'a \<Rightarrow> 'b"
    assume fin_f: "finite {k. f k \<noteq> 0}"
    assume fin_g: "finite {k. g k \<noteq> 0}"
    assume fin_h: "finite {k. h k \<noteq> 0}"
    show "prod_fun (\<lambda>k. f k + g k) h = (\<lambda>k. prod_fun f h k + prod_fun g h k)"
      apply (rule ext)
      apply (auto simp add: prod_fun_def algebra_simps)
      apply (subst Sum_any.distrib)
      using fin_f fin_g apply (auto intro: finite_mult_not_eq_zero_rightI)
      done
  qed
  show "a * (b + c) = a * b + a * c"
  proof transfer
    fix f g h :: "'a \<Rightarrow> 'b"
    assume fin_f: "finite {k. f k \<noteq> 0}"
    assume fin_g: "finite {k. g k \<noteq> 0}"
    assume fin_h: "finite {k. h k \<noteq> 0}"
    show "prod_fun f (\<lambda>k. g k + h k) = (\<lambda>k. prod_fun f g k + prod_fun f h k)"
      apply (rule ext)
      apply (auto simp add: prod_fun_def Sum_any.distrib algebra_simps when_add_distrib)
      apply (subst Sum_any.distrib)
      apply (simp_all add: algebra_simps)
      apply (auto intro: fin_g fin_h)
      apply (subst Sum_any.distrib)
      apply (simp_all add: algebra_simps)
      using fin_f apply (rule finite_mult_not_eq_zero_rightI)
      using fin_f apply (rule finite_mult_not_eq_zero_rightI)
      done
  qed
  show "0 * a = 0"
    by transfer (simp add: prod_fun_def [abs_def])
  show "a * 0 = 0"
    by transfer (simp add: prod_fun_def [abs_def])
qed

end

lemma lookup_mult:
  "lookup (f * g) k = (\<Sum>l. lookup f l * (\<Sum>q. lookup g q when k = l + q))"
  by transfer (simp add: prod_fun_def)

instance poly_mapping :: (comm_monoid_add, comm_semiring_0) comm_semiring_0
proof
  fix a b c :: "'a \<Rightarrow>\<^sub>0 'b"
  show "a * b = b * a"
  proof transfer
    fix f g :: "'a \<Rightarrow> 'b"
    assume fin_f: "finite {a. f a \<noteq> 0}"
    assume fin_g: "finite {b. g b \<noteq> 0}"
    show "prod_fun f g = prod_fun g f"
    proof
      fix k
      have fin1: "\<And>l. finite {a. (f a when k = l + a) \<noteq> 0}"
        using fin_f by auto
      have fin2: "\<And>l. finite {b. (g b when k = l + b) \<noteq> 0}"
        using fin_g by auto
      from fin_f fin_g have "finite {(a, b). f a \<noteq> 0 \<and> g b \<noteq> 0}" (is "finite ?AB")
        by simp
      show "prod_fun f g k = prod_fun g f k"
        apply (simp add: prod_fun_def)
        apply (subst Sum_any_right_distrib)
        apply (rule fin2)
        apply (subst Sum_any_right_distrib)
         apply (rule fin1)
        apply (subst Sum_any.swap [of ?AB])
        apply (fact \<open>finite ?AB\<close>)
        apply (auto simp add: mult_when ac_simps)
        done
    qed
  qed
  show "(a + b) * c = a * c + b * c"
  proof transfer
    fix f g h :: "'a \<Rightarrow> 'b"
    assume fin_f: "finite {k. f k \<noteq> 0}"
    assume fin_g: "finite {k. g k \<noteq> 0}"
    assume fin_h: "finite {k. h k \<noteq> 0}"
    show "prod_fun (\<lambda>k. f k + g k) h = (\<lambda>k. prod_fun f h k + prod_fun g h k)"
      apply (auto simp add: prod_fun_def fun_eq_iff algebra_simps)
      apply (subst Sum_any.distrib)
      using fin_f apply (rule finite_mult_not_eq_zero_rightI)
      using fin_g apply (rule finite_mult_not_eq_zero_rightI)
      apply simp_all
      done
  qed
qed

instance poly_mapping :: (monoid_add, semiring_0_cancel) semiring_0_cancel
  ..

instance poly_mapping :: (comm_monoid_add, comm_semiring_0_cancel) comm_semiring_0_cancel
  ..

instance poly_mapping :: (monoid_add, semiring_1) semiring_1
proof
  fix a :: "'a \<Rightarrow>\<^sub>0 'b"
  show "1 * a = a"
    by transfer (simp add: prod_fun_def [abs_def] when_mult)
  show "a * 1 = a"
    apply transfer
    apply (simp add: prod_fun_def [abs_def] Sum_any_right_distrib Sum_any_left_distrib mult_when)
    apply (subst when_commute)
    apply simp
    done
qed

instance poly_mapping :: (comm_monoid_add, comm_semiring_1) comm_semiring_1
proof
  fix a :: "'a \<Rightarrow>\<^sub>0 'b"
  show "1 * a = a"
    by transfer (simp add: prod_fun_def [abs_def])
qed

instance poly_mapping :: (monoid_add, semiring_1_cancel) semiring_1_cancel
  ..

instance poly_mapping :: (monoid_add, ring) ring
  ..

instance poly_mapping :: (comm_monoid_add, comm_ring) comm_ring
  ..

instance poly_mapping :: (monoid_add, ring_1) ring_1
  ..

instance poly_mapping :: (comm_monoid_add, comm_ring_1) comm_ring_1
  ..


subsection \<open>Single-point mappings\<close>

lift_definition single :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::zero"
  is "\<lambda>k v k'. (v when k = k')"
  by simp

lemma inj_single [iff]:
  "inj (single k)"
proof (rule injI, transfer)
  fix k :: 'b and a b :: "'a::zero"
  assume "(\<lambda>k'. a when k = k') = (\<lambda>k'. b when k = k')"
  then have "(\<lambda>k'. a when k = k') k = (\<lambda>k'. b when k = k') k"
    by (rule arg_cong)
  then show "a = b" by simp
qed

lemma lookup_single:
  "lookup (single k v) k' = (v when k = k')"
  by transfer rule

lemma lookup_single_eq [simp]:
  "lookup (single k v) k = v"
  by transfer simp

lemma lookup_single_not_eq:
  "k \<noteq> k' \<Longrightarrow> lookup (single k v) k' = 0"
  by transfer simp

lemma single_zero [simp]:
  "single k 0 = 0"
  by transfer simp

lemma single_one [simp]:
  "single 0 1 = 1"
  by transfer simp

lemma single_add:
  "single k (a + b) = single k a + single k b"
  by transfer (simp add: fun_eq_iff when_add_distrib)

lemma single_uminus:
  "single k (- a) = - single k a"
  by transfer (simp add: fun_eq_iff when_uminus_distrib)

lemma single_diff:
  "single k (a - b) = single k a - single k b"
  by transfer (simp add: fun_eq_iff when_diff_distrib)

lemma single_numeral [simp]:
  "single 0 (numeral n) = numeral n"
  by (induct n) (simp_all only: numeral.simps numeral_add single_zero single_one single_add)

lemma lookup_numeral:
  "lookup (numeral n) k = (numeral n when k = 0)"
proof -
  have "lookup (numeral n) k = lookup (single 0 (numeral n)) k"
    by simp
  then show ?thesis unfolding lookup_single by simp
qed

lemma single_of_nat [simp]:
  "single 0 (of_nat n) = of_nat n"
  by (induct n) (simp_all add: single_add)

lemma lookup_of_nat:
  "lookup (of_nat n) k = (of_nat n when k = 0)"
proof -
  have "lookup (of_nat n) k = lookup (single 0 (of_nat n)) k"
    by simp
  then show ?thesis unfolding lookup_single by simp
qed

lemma of_nat_single:
  "of_nat = single 0 \<circ> of_nat"
  by (simp add: fun_eq_iff)

lemma mult_single:
  "single k a * single l b = single (k + l) (a * b)"
proof transfer
  fix k l :: 'a and a b :: 'b
  show "prod_fun (\<lambda>k'. a when k = k') (\<lambda>k'. b when l = k') = (\<lambda>k'. a * b when k + l = k')"
  proof
    fix k'
    have "prod_fun (\<lambda>k'. a when k = k') (\<lambda>k'. b when l = k') k' = (\<Sum>n. a * b when l = n when k' = k + n)"
      by (simp add: prod_fun_def Sum_any_right_distrib mult_when when_mult)
    also have "\<dots> = (\<Sum>n. a * b when k' = k + n when l = n)"
      by (simp add: when_when conj_commute)
    also have "\<dots> = (a * b when k' = k + l)"
      by simp
    also have "\<dots> = (a * b when k + l = k')"
      by (simp add: when_def)
    finally show "prod_fun (\<lambda>k'. a when k = k') (\<lambda>k'. b when l = k') k' =
      (\<lambda>k'. a * b when k + l = k') k'" .
  qed
qed

instance poly_mapping :: (monoid_add, semiring_char_0) semiring_char_0
  by intro_classes (auto intro: inj_comp inj_of_nat simp add: of_nat_single)

instance poly_mapping :: (monoid_add, ring_char_0) ring_char_0
  ..

lemma single_of_int [simp]:
  "single 0 (of_int k) = of_int k"
  by (cases k) (simp_all add: single_diff single_uminus)

lemma lookup_of_int:
  "lookup (of_int l) k = (of_int l when k = 0)"
proof -
  have "lookup (of_int l) k = lookup (single 0 (of_int l)) k"
    by simp
  then show ?thesis unfolding lookup_single by simp
qed


subsection \<open>Integral domains\<close>

instance poly_mapping :: ("{ordered_cancel_comm_monoid_add, linorder}", ring_no_zero_divisors) ring_no_zero_divisors
  text \<open>The @{class "linorder"} constraint is a pragmatic device for the proof --- maybe it can be dropped\<close>
proof
  fix f g :: "'a \<Rightarrow>\<^sub>0 'b"
  assume "f \<noteq> 0" and "g \<noteq> 0"
  then show "f * g \<noteq> 0"
  proof transfer
    fix f g :: "'a \<Rightarrow> 'b"
    define F where "F = {a. f a \<noteq> 0}"
    moreover define G where "G = {a. g a \<noteq> 0}"
    ultimately have [simp]:
      "\<And>a. f a \<noteq> 0 \<longleftrightarrow> a \<in> F"
      "\<And>b. g b \<noteq> 0 \<longleftrightarrow> b \<in> G"
      by simp_all
    assume "finite {a. f a \<noteq> 0}"
    then have [simp]: "finite F"
      by simp
    assume "finite {a. g a \<noteq> 0}"
    then have [simp]: "finite G"
      by simp
    assume "f \<noteq> (\<lambda>a. 0)"
    then obtain a where "f a \<noteq> 0"
      by (auto simp add: fun_eq_iff)
    assume "g \<noteq> (\<lambda>b. 0)"
    then obtain b where "g b \<noteq> 0"
      by (auto simp add: fun_eq_iff)
    from \<open>f a \<noteq> 0\<close> and \<open>g b \<noteq> 0\<close> have "F \<noteq> {}" and "G \<noteq> {}"
      by auto
    note Max_F = \<open>finite F\<close> \<open>F \<noteq> {}\<close>
    note Max_G = \<open>finite G\<close> \<open>G \<noteq> {}\<close>
    from Max_F and Max_G have [simp]:
      "Max F \<in> F"
      "Max G \<in> G"
      by auto
    from Max_F Max_G have [dest!]:
      "\<And>a. a \<in> F \<Longrightarrow> a \<le> Max F"
      "\<And>b. b \<in> G \<Longrightarrow> b \<le> Max G"
      by auto
    define q where "q = Max F + Max G"
    have "(\<Sum>(a, b). f a * g b when q = a + b) =
      (\<Sum>(a, b). f a * g b when q = a + b when a \<in> F \<and> b \<in> G)"
      by (rule Sum_any.cong) (auto simp add: split_def when_def q_def intro: ccontr)
    also have "\<dots> =
      (\<Sum>(a, b). f a * g b when (Max F, Max G) = (a, b))"
    proof (rule Sum_any.cong)
      fix ab :: "'a \<times> 'a"
      obtain a b where [simp]: "ab = (a, b)"
        by (cases ab) simp_all
      have [dest!]:
        "a \<le> Max F \<Longrightarrow> Max F \<noteq> a \<Longrightarrow> a < Max F"
        "b \<le> Max G \<Longrightarrow> Max G \<noteq> b \<Longrightarrow> b < Max G"
        by auto
      show "(case ab of (a, b) \<Rightarrow> f a * g b when q = a + b when a \<in> F \<and> b \<in> G) =
         (case ab of (a, b) \<Rightarrow> f a * g b when (Max F, Max G) = (a, b))"
        by (auto simp add: split_def when_def q_def dest: add_strict_mono [of a "Max F" b "Max G"])
    qed
    also have "\<dots> = (\<Sum>ab. (case ab of (a, b) \<Rightarrow> f a * g b) when
      (Max F, Max G) = ab)"
      unfolding split_def when_def by auto
    also have "\<dots> \<noteq> 0"
      by simp
    finally have "prod_fun f g q \<noteq> 0"
      by (simp add: prod_fun_unfold_prod)
    then show "prod_fun f g \<noteq> (\<lambda>k. 0)"
      by (auto simp add: fun_eq_iff)
  qed
qed

instance poly_mapping :: ("{ordered_cancel_comm_monoid_add, linorder}", ring_1_no_zero_divisors) ring_1_no_zero_divisors
  ..

instance poly_mapping :: ("{ordered_cancel_comm_monoid_add, linorder}", idom) idom
  ..


subsection \<open>Mapping order\<close>

instantiation poly_mapping :: (linorder, "{zero, linorder}") linorder
begin

lift_definition less_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  is less_fun
  .

lift_definition less_eq_poly_mapping :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  is "\<lambda>f g. less_fun f g \<or> f = g"
  .

instance proof (rule class.Orderings.linorder.of_class.intro)
  show "class.linorder (less_eq :: (_ \<Rightarrow>\<^sub>0 _) \<Rightarrow> _) less"
  proof (rule linorder_strictI, rule order_strictI)
    fix f g h :: "'a \<Rightarrow>\<^sub>0 'b"
    show "f \<le> g \<longleftrightarrow> f < g \<or> f = g"
      by transfer (rule refl)
    show "\<not> f < f"
      by transfer (rule less_fun_irrefl)
    show "f < g \<or> f = g \<or> g < f"
    proof transfer
      fix f g :: "'a \<Rightarrow> 'b"
      assume "finite {k. f k \<noteq> 0}" and "finite {k. g k \<noteq> 0}"
      then have "finite ({k. f k \<noteq> 0} \<union> {k. g k \<noteq> 0})"
        by simp
      moreover have "{k. f k \<noteq> g k} \<subseteq> {k. f k \<noteq> 0} \<union> {k. g k \<noteq> 0}"
        by auto
      ultimately have "finite {k. f k \<noteq> g k}"
        by (rule rev_finite_subset)
      then show "less_fun f g \<or> f = g \<or> less_fun g f"
        by (rule less_fun_trichotomy)
    qed
    assume "f < g" then show "\<not> g < f"
      by transfer (rule less_fun_asym)
    note \<open>f < g\<close> moreover assume "g < h"
      ultimately show "f < h"
      by transfer (rule less_fun_trans)
  qed
qed

end

instance poly_mapping :: (linorder, "{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le, linorder}") ordered_ab_semigroup_add
proof (intro_classes, transfer)
  fix f g h :: "'a \<Rightarrow> 'b"
  assume *: "less_fun f g \<or> f = g"
  { assume "less_fun f g"
    then obtain k where "f k < g k" "(\<And>k'. k' < k \<Longrightarrow> f k' = g k')"
      by (blast elim!: less_funE)
    then have "h k + f k < h k + g k" "(\<And>k'. k' < k \<Longrightarrow> h k' + f k' = h k' + g k')"
      by simp_all
    then have "less_fun (\<lambda>k. h k + f k) (\<lambda>k. h k + g k)"
      by (blast intro: less_funI)
  }
  with * show "less_fun (\<lambda>k. h k + f k) (\<lambda>k. h k + g k) \<or> (\<lambda>k. h k + f k) = (\<lambda>k. h k + g k)"
    by (auto simp add: fun_eq_iff)
qed

instance poly_mapping :: (linorder, "{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le, cancel_comm_monoid_add, linorder}") linordered_cancel_ab_semigroup_add
  ..

instance poly_mapping :: (linorder, "{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le, cancel_comm_monoid_add, linorder}") ordered_comm_monoid_add
  ..

instance poly_mapping :: (linorder, "{ordered_comm_monoid_add, ordered_ab_semigroup_add_imp_le, cancel_comm_monoid_add, linorder}") ordered_cancel_comm_monoid_add
  ..

instance poly_mapping :: (linorder, linordered_ab_group_add) linordered_ab_group_add
  ..

text \<open>
  For pragmatism we leave out the final elements in the hierarchy:
  @{class linordered_ring}, @{class linordered_ring_strict}, @{class linordered_idom};
  remember that the order instance is a mere technical device, not a deeper algebraic
  property.
\<close>


subsection \<open>Fundamental mapping notions\<close>

lift_definition keys :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a set"
  is "\<lambda>f. {k. f k \<noteq> 0}" .

lift_definition range :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b set"
  is "\<lambda>f :: 'a \<Rightarrow> 'b. Set.range f - {0}" .

lemma finite_keys [simp]:
  "finite (keys f)"
  by transfer

lemma not_in_keys_iff_lookup_eq_zero [simp]:
  "k \<notin> keys f \<longleftrightarrow> lookup f k = 0"
  by transfer simp

lemma lookup_not_eq_zero_eq_in_keys [simp]:
  "lookup f k \<noteq> 0 \<longleftrightarrow> k \<in> keys f"
  by transfer simp

lemma lookup_eq_zero_in_keys_contradict [dest]:
  "lookup f k = 0 \<Longrightarrow> \<not> k \<in> keys f"
  by simp

lemma finite_range [simp]: "finite (Poly_Mapping.range p)"
proof transfer
  fix f :: "'b \<Rightarrow> 'a"
  assume *: "finite {x. f x \<noteq> 0}"
  have "Set.range f - {0} \<subseteq> f ` {x. f x \<noteq> 0}"
    by auto
  thus "finite (Set.range f - {0})"
    by(rule finite_subset)(rule finite_imageI[OF *])
qed

lemma in_keys_lookup_in_range [simp]:
  "k \<in> keys f \<Longrightarrow> lookup f k \<in> range f"
  by transfer simp

lemma in_keys_iff: "x \<in> (keys s) = (lookup s x \<noteq> 0)"
  by (transfer, simp)

lemma keys_zero [simp]:
  "keys 0 = {}"
  by transfer simp

lemma range_zero [simp]:
  "range 0 = {}"
  by transfer auto

lemma keys_add_subset:
  "keys (f + g) \<subseteq> keys f \<union> keys g"
  by transfer auto

lemma keys_one [simp]:
  "keys 1 = {0}"
  by transfer simp

lemma range_one [simp]:
  "range 1 = {1}"
  by transfer (auto simp add: when_def)

lemma keys_single [simp]:
  "keys (single k v) = (if v = 0 then {} else {k})"
  by transfer simp

lemma range_single [simp]:
  "range (single k v) = (if v = 0 then {} else {v})"
  by transfer (auto simp add: when_def)

lemma keys_mult:
  "keys (f * g) \<subseteq> {a + b | a b. a \<in> keys f \<and> b \<in> keys g}"
  apply transfer
  apply (auto simp add: prod_fun_def dest!: mult_not_zero elim!: Sum_any.not_neutral_obtains_not_neutral)
  apply blast
  done

lemma setsum_keys_plus_distrib:
  assumes hom_0: "\<And>k. f k 0 = 0"
  and hom_plus: "\<And>k. k \<in> Poly_Mapping.keys p \<union> Poly_Mapping.keys q \<Longrightarrow> f k (Poly_Mapping.lookup p k + Poly_Mapping.lookup q k) = f k (Poly_Mapping.lookup p k) + f k (Poly_Mapping.lookup q k)"
  shows
  "(\<Sum>k\<in>Poly_Mapping.keys (p + q). f k (Poly_Mapping.lookup (p + q) k)) =
   (\<Sum>k\<in>Poly_Mapping.keys p. f k (Poly_Mapping.lookup p k)) +
   (\<Sum>k\<in>Poly_Mapping.keys q. f k (Poly_Mapping.lookup q k))"
  (is "?lhs = ?p + ?q")
proof -
  let ?A = "Poly_Mapping.keys p \<union> Poly_Mapping.keys q"
  have "?lhs = (\<Sum>k\<in>?A. f k (Poly_Mapping.lookup p k + Poly_Mapping.lookup q k))"
    apply(rule sum.mono_neutral_cong_left)
       apply(simp_all add: Poly_Mapping.keys_add_subset)
     apply(transfer fixing: f)
     apply(auto simp add: hom_0)[1]
    apply(transfer fixing: f)
    apply(auto simp add: hom_0)[1]
    done
  also have "\<dots> = (\<Sum>k\<in>?A. f k (Poly_Mapping.lookup p k) + f k (Poly_Mapping.lookup q k))"
    by(rule sum.cong)(simp_all add: hom_plus)
  also have "\<dots> = (\<Sum>k\<in>?A. f k (Poly_Mapping.lookup p k)) + (\<Sum>k\<in>?A. f k (Poly_Mapping.lookup q k))"
    (is "_ = ?p' + ?q'")
    by(simp add: sum.distrib)
  also have "?p' = ?p"
    by(rule sum.mono_neutral_right)(auto simp add: hom_0)
  also have "?q' = ?q"
    by(rule sum.mono_neutral_right)(auto simp add: hom_0)
  finally show ?thesis .
qed

subsection \<open>Degree\<close>

definition degree :: "(nat \<Rightarrow>\<^sub>0 'a::zero) \<Rightarrow> nat"
where
  "degree f = Max (insert 0 (Suc ` keys f))"

lemma degree_zero [simp]:
  "degree 0 = 0"
  unfolding degree_def by transfer simp

lemma degree_one [simp]:
  "degree 1 = 1"
  unfolding degree_def by transfer simp

lemma degree_single_zero [simp]:
  "degree (single k 0) = 0"
  unfolding degree_def by transfer simp

lemma degree_single_not_zero [simp]:
  "v \<noteq> 0 \<Longrightarrow> degree (single k v) = Suc k"
  unfolding degree_def by transfer simp

lemma degree_zero_iff [simp]:
  "degree f = 0 \<longleftrightarrow> f = 0"
unfolding degree_def proof transfer
  fix f :: "nat \<Rightarrow> 'a"
  assume "finite {n. f n \<noteq> 0}"
  then have fin: "finite (insert 0 (Suc ` {n. f n \<noteq> 0}))" by auto
  show "Max (insert 0 (Suc ` {n. f n \<noteq> 0})) = 0 \<longleftrightarrow> f = (\<lambda>n. 0)" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    have "{n. f n \<noteq> 0} = {}"
    proof (rule ccontr)
      assume "{n. f n \<noteq> 0} \<noteq> {}"
      then obtain n where "n \<in> {n. f n \<noteq> 0}" by blast
      then have "{n. f n \<noteq> 0} = insert n {n. f n \<noteq> 0}" by auto
      then have "Suc ` {n. f n \<noteq> 0} = insert (Suc n) (Suc ` {n. f n \<noteq> 0})" by auto
      with \<open>?P\<close> have "Max (insert 0 (insert (Suc n) (Suc ` {n. f n \<noteq> 0}))) = 0" by simp
      then have "Max (insert (Suc n) (insert 0 (Suc ` {n. f n \<noteq> 0}))) = 0"
        by (simp add: insert_commute)
      with fin have "max (Suc n) (Max (insert 0 (Suc ` {n. f n \<noteq> 0}))) = 0"
        by simp
      then show False by simp
    qed
    then show ?Q by (simp add: fun_eq_iff)
  next
    assume ?Q then show ?P by simp
  qed
qed

lemma degree_greater_zero_in_keys:
  assumes "0 < degree f"
  shows "degree f - 1 \<in> keys f"
proof -
  from assms have "keys f \<noteq> {}"
    by (auto simp add: degree_def)
  then show ?thesis unfolding degree_def
    by (simp add: mono_Max_commute [symmetric] mono_Suc)
qed

lemma in_keys_less_degree:
  "n \<in> keys f \<Longrightarrow> n < degree f"
unfolding degree_def by transfer (auto simp add: Max_gr_iff)

lemma beyond_degree_lookup_zero:
  "degree f \<le> n \<Longrightarrow> lookup f n = 0"
  unfolding degree_def by transfer auto

lemma degree_add:
  "degree (f + g) \<le> max (degree f) (Poly_Mapping.degree g)"
unfolding degree_def proof transfer
  fix f g :: "nat \<Rightarrow> 'a"
  assume f: "finite {x. f x \<noteq> 0}"
  assume g: "finite {x. g x \<noteq> 0}"
  let ?f = "Max (insert 0 (Suc ` {k. f k \<noteq> 0}))"
  let ?g = "Max (insert 0 (Suc ` {k. g k \<noteq> 0}))"
  have "Max (insert 0 (Suc ` {k. f k + g k \<noteq> 0})) \<le> Max (insert 0 (Suc ` ({k. f k \<noteq> 0} \<union> {k. g k \<noteq> 0})))"
    by (rule Max.subset_imp) (insert f g, auto)
  also have "\<dots> = max ?f ?g"
    using f g by (simp_all add: image_Un Max_Un [symmetric])
  finally show "Max (insert 0 (Suc ` {k. f k + g k \<noteq> 0}))
    \<le> max (Max (insert 0 (Suc ` {k. f k \<noteq> 0}))) (Max (insert 0 (Suc ` {k. g k \<noteq> 0})))"
    .
qed

lemma sorted_list_of_set_keys:
  "sorted_list_of_set (keys f) = filter (\<lambda>k. k \<in> keys f) [0..<degree f]" (is "_ = ?r")
proof -
  have "keys f = set ?r"
    by (auto dest: in_keys_less_degree)
  moreover have "sorted_list_of_set (set ?r) = ?r"
    unfolding sorted_list_of_set_sort_remdups
    by (simp add: remdups_filter filter_sort [symmetric])
  ultimately show ?thesis by simp
qed


subsection \<open>Inductive structure\<close>

lift_definition update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b"
  is "\<lambda>k v f. f(k := v)"
proof -
  fix f :: "'a \<Rightarrow> 'b" and k' v
  assume "finite {k. f k \<noteq> 0}"
  then have "finite (insert k' {k. f k \<noteq> 0})"
    by simp
  then show "finite {k. (f(k' := v)) k \<noteq> 0}"
    by (rule rev_finite_subset) auto
qed

lemma update_induct [case_names const update]:
  assumes const': "P 0"
  assumes update': "\<And>f a b. a \<notin> keys f \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> P f \<Longrightarrow> P (update a b f)"
  shows "P f"
proof -
  obtain g where "f = Abs_poly_mapping g" and "finite {a. g a \<noteq> 0}"
    by (cases f) simp_all
  define Q where "Q g = P (Abs_poly_mapping g)" for g
  from \<open>finite {a. g a \<noteq> 0}\<close> have "Q g"
  proof (induct g rule: finite_update_induct)
    case const with const' Q_def show ?case
      by (simp add: zero_poly_mapping.abs_eq)
  next
    case (update a b g)
    from \<open>finite {a. g a \<noteq> 0}\<close> \<open>g a = 0\<close> have "a \<notin> keys (Abs_poly_mapping g)"
      by (simp add: Abs_poly_mapping_inverse keys.rep_eq)
    moreover note \<open>b \<noteq> 0\<close>
    moreover from \<open>Q g\<close> have "P (Abs_poly_mapping g)"
      by (simp add: Q_def)
    ultimately have "P (update a b (Abs_poly_mapping g))"
      by (rule update')
    also from \<open>finite {a. g a \<noteq> 0}\<close>
    have "update a b (Abs_poly_mapping g) = Abs_poly_mapping (g(a := b))"
      by (simp add: update.abs_eq eq_onp_same_args)
    finally show ?case
      by (simp add: Q_def fun_upd_def)
  qed
  then show ?thesis by (simp add: Q_def \<open>f = Abs_poly_mapping g\<close>)
qed

lemma lookup_update:
  "lookup (update k v f) k' = (if k = k' then v else lookup f k')"
  by transfer simp

lemma keys_update:
  "keys (update k v f) = (if v = 0 then keys f - {k} else insert k (keys f))"
  by transfer auto


subsection \<open>Quasi-functorial structure\<close>

lift_definition map :: "('b::zero \<Rightarrow> 'c::zero)
  \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'c::zero)"
  is "\<lambda>g f k. g (f k) when f k \<noteq> 0"
  by simp

context
  fixes f :: "'b \<Rightarrow> 'a"
  assumes inj_f: "inj f"
begin

lift_definition map_key :: "('a \<Rightarrow>\<^sub>0 'c::zero) \<Rightarrow> 'b \<Rightarrow>\<^sub>0 'c"
  is "\<lambda>p. p \<circ> f"
proof -
  fix g :: "'c \<Rightarrow> 'd" and p :: "'a \<Rightarrow> 'c"
  assume "finite {x. p x \<noteq> 0}"
  hence "finite (f ` {y. p (f y) \<noteq> 0})"
    by(rule finite_subset[rotated]) auto
  thus "finite {x. (p \<circ> f) x \<noteq> 0}" unfolding o_def
    by(rule finite_imageD)(rule subset_inj_on[OF inj_f], simp)
qed

end

lemma map_key_compose:
  assumes [transfer_rule]: "inj f" "inj g"
  shows "map_key f (map_key g p) = map_key (g \<circ> f) p"
proof -
  from assms have [transfer_rule]: "inj (g \<circ> f)"
    by(simp add: inj_comp)
  show ?thesis by transfer(simp add: o_assoc)
qed

lemma map_key_id:
  "map_key (\<lambda>x. x) p = p"
proof -
  have [transfer_rule]: "inj (\<lambda>x. x)" by simp
  show ?thesis by transfer(simp add: o_def)
qed

context
  fixes f :: "'a \<Rightarrow> 'b"
  assumes inj_f [transfer_rule]: "inj f"
begin

lemma map_key_map:
  "map_key f (map g p) = map g (map_key f p)"
  by transfer (simp add: fun_eq_iff)

lemma map_key_plus:
  "map_key f (p + q) = map_key f p + map_key f q"
  by transfer (simp add: fun_eq_iff)

lemma keys_map_key:
  "keys (map_key f p) = f -` keys p"
  by transfer auto

lemma map_key_zero [simp]:
  "map_key f 0 = 0"
  by transfer (simp add: fun_eq_iff)

lemma map_key_single [simp]:
  "map_key f (single (f k) v) = single k v"
  by transfer (simp add: fun_eq_iff inj_onD [OF inj_f] when_def)

end

lemma mult_map_scale_conv_mult: "map ((*) s) p = single 0 s * p"
proof(transfer fixing: s)
  fix p :: "'a \<Rightarrow> 'b"
  assume *: "finite {x. p x \<noteq> 0}"
  { fix x
    have "prod_fun (\<lambda>k'. s when 0 = k') p x =
          (\<Sum>l :: 'a. if l = 0 then s * (\<Sum>q. p q when x = q) else 0)"
      by(auto simp add: prod_fun_def when_def intro: Sum_any.cong simp del: Sum_any.delta)
    also have "\<dots> = (\<lambda>k. s * p k when p k \<noteq> 0) x" by(simp add: when_def)
    also note calculation }
  then show "(\<lambda>k. s * p k when p k \<noteq> 0) = prod_fun (\<lambda>k'. s when 0 = k') p"
    by(simp add: fun_eq_iff)
qed

lemma map_single [simp]:
  "(c = 0 \<Longrightarrow> f 0 = 0) \<Longrightarrow> map f (single x c) = single x (f c)"
by transfer(auto simp add: fun_eq_iff when_def)

lemma map_eq_zero_iff: "map f p = 0 \<longleftrightarrow> (\<forall>k \<in> keys p. f (lookup p k) = 0)"
by transfer(auto simp add: fun_eq_iff when_def)

subsection \<open>Canonical dense representation of @{typ "nat \<Rightarrow>\<^sub>0 'a"}\<close>

abbreviation no_trailing_zeros :: "'a :: zero list \<Rightarrow> bool"
where
  "no_trailing_zeros \<equiv> no_trailing ((=) 0)"

lift_definition "nth" :: "'a list \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a::zero)"
  is "nth_default 0"
  by (fact finite_nth_default_neq_default)

text \<open>
  The opposite direction is directly specified on (later)
  type @{text nat_mapping}.
\<close>

lemma nth_Nil [simp]:
  "nth [] = 0"
  by transfer (simp add: fun_eq_iff)

lemma nth_singleton [simp]:
  "nth [v] = single 0 v"
proof (transfer, rule ext)
  fix n :: nat and v :: 'a
  show "nth_default 0 [v] n = (v when 0 = n)"
    by (auto simp add: nth_default_def nth_append)
qed

lemma nth_replicate [simp]:
  "nth (replicate n 0 @ [v]) = single n v"
proof (transfer, rule ext)
  fix m n :: nat and v :: 'a
  show "nth_default 0 (replicate n 0 @ [v]) m = (v when n = m)"
    by (auto simp add: nth_default_def nth_append)
qed

lemma nth_strip_while [simp]:
  "nth (strip_while ((=) 0) xs) = nth xs"
  by transfer (fact nth_default_strip_while_dflt)

lemma nth_strip_while' [simp]:
  "nth (strip_while (\<lambda>k. k = 0) xs) = nth xs"
  by (subst eq_commute) (fact nth_strip_while)

lemma nth_eq_iff:
  "nth xs = nth ys \<longleftrightarrow> strip_while (HOL.eq 0) xs = strip_while (HOL.eq 0) ys"
  by transfer (simp add: nth_default_eq_iff)

lemma lookup_nth [simp]:
  "lookup (nth xs) = nth_default 0 xs"
  by (fact nth.rep_eq)

lemma keys_nth [simp]:
  "keys (nth xs) =  fst ` {(n, v) \<in> set (enumerate 0 xs). v \<noteq> 0}"
proof transfer
  fix xs :: "'a list"
  { fix n
    assume "nth_default 0 xs n \<noteq> 0"
    then have "n < length xs" and "xs ! n \<noteq> 0"
      by (auto simp add: nth_default_def split: if_splits)
    then have "(n, xs ! n) \<in> {(n, v). (n, v) \<in> set (enumerate 0 xs) \<and> v \<noteq> 0}" (is "?x \<in> ?A")
      by (auto simp add: in_set_conv_nth enumerate_eq_zip)
    then have "fst ?x \<in> fst ` ?A"
      by blast
    then have "n \<in> fst ` {(n, v). (n, v) \<in> set (enumerate 0 xs) \<and> v \<noteq> 0}"
      by simp
  }
  then show "{k. nth_default 0 xs k \<noteq> 0} = fst ` {(n, v). (n, v) \<in> set (enumerate 0 xs) \<and> v \<noteq> 0}"
    by (auto simp add: in_enumerate_iff_nth_default_eq)
qed

lemma range_nth [simp]:
  "range (nth xs) = set xs - {0}"
  by transfer simp

lemma degree_nth:
  "no_trailing_zeros xs \<Longrightarrow> degree (nth xs) = length xs"
unfolding degree_def proof transfer
  fix xs :: "'a list"
  assume *: "no_trailing_zeros xs"
  let ?A = "{n. nth_default 0 xs n \<noteq> 0}"
  let ?f = "nth_default 0 xs"
  let ?bound = "Max (insert 0 (Suc ` {n. ?f n \<noteq> 0}))"
  show "?bound = length xs"
  proof (cases "xs = []")
    case False
    with * obtain n where n: "n < length xs" "xs ! n \<noteq> 0"
      by (fastforce simp add: no_trailing_unfold last_conv_nth neq_Nil_conv)
    then have "?bound = Max (Suc ` {k. (k < length xs \<longrightarrow> xs ! k \<noteq> (0::'a)) \<and> k < length xs})"
      by (subst Max_insert) (auto simp add: nth_default_def)
    also let ?A = "{k. k < length xs \<and> xs ! k \<noteq> 0}"
    have "{k. (k < length xs \<longrightarrow> xs ! k \<noteq> (0::'a)) \<and> k < length xs} = ?A" by auto
    also have "Max (Suc ` ?A) = Suc (Max ?A)" using n
      by (subst mono_Max_commute [where f = Suc, symmetric]) (auto simp add: mono_Suc)
    also {
      have "Max ?A \<in> ?A" using n Max_in [of ?A] by fastforce
      hence "Suc (Max ?A) \<le> length xs" by simp
      moreover from * False have "length xs - 1 \<in> ?A"
        by(auto simp add: no_trailing_unfold last_conv_nth)
      hence "length xs - 1 \<le> Max ?A" using Max_ge[of ?A "length xs - 1"] by auto
      hence "length xs \<le> Suc (Max ?A)" by simp
      ultimately have "Suc (Max ?A) = length xs" by simp }
    finally show ?thesis .
  qed simp
qed

lemma nth_trailing_zeros [simp]:
  "nth (xs @ replicate n 0) = nth xs"
  by transfer simp

lemma nth_idem:
  "nth (List.map (lookup f) [0..<degree f]) = f"
  unfolding degree_def by transfer
    (auto simp add: nth_default_def fun_eq_iff not_less)

lemma nth_idem_bound:
  assumes "degree f \<le> n"
  shows "nth (List.map (lookup f) [0..<n]) = f"
proof -
  from assms obtain m where "n = degree f + m"
    by (blast dest: le_Suc_ex)
  then have "[0..<n] = [0..<degree f] @ [degree f..<degree f + m]"
    by (simp add: upt_add_eq_append [of 0])
  moreover have "List.map (lookup f) [degree f..<degree f + m] = replicate m 0"
    by (rule replicate_eqI) (auto simp add: beyond_degree_lookup_zero)
  ultimately show ?thesis by (simp add: nth_idem)
qed


subsection \<open>Canonical sparse representation of @{typ "'a \<Rightarrow>\<^sub>0 'b"}\<close>

lift_definition the_value :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b::zero"
  is "\<lambda>xs k. case map_of xs k of None \<Rightarrow> 0 | Some v \<Rightarrow> v"
proof -
  fix xs :: "('a \<times> 'b) list"
  have fin: "finite {k. \<exists>v. map_of xs k = Some v}"
    using finite_dom_map_of [of xs] unfolding dom_def by auto
  then show "finite {k. (case map_of xs k of None \<Rightarrow> 0 | Some v \<Rightarrow> v) \<noteq> 0}"
    using fin by (simp split: option.split)
qed

definition items :: "('a::linorder \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> ('a \<times> 'b) list"
where
  "items f = List.map (\<lambda>k. (k, lookup f k)) (sorted_list_of_set (keys f))"

text \<open>
  For the canonical sparse representation we provide both
  directions of morphisms since the specification of
  ordered association lists in theory @{text OAList}
  will support arbitrary linear orders @{class linorder}
  as keys, not just natural numbers @{typ nat}.
\<close>

lemma the_value_items [simp]:
  "the_value (items f) = f"
  unfolding items_def
  by transfer (simp add: fun_eq_iff map_of_map_restrict restrict_map_def)

lemma lookup_the_value:
  "lookup (the_value xs) k = (case map_of xs k of None \<Rightarrow> 0 | Some v \<Rightarrow> v)"
  by transfer rule

lemma items_the_value:
  assumes "sorted (List.map fst xs)" and "distinct (List.map fst xs)" and "0 \<notin> snd ` set xs"
  shows "items (the_value xs) = xs"
proof -
  from assms have "sorted_list_of_set (set (List.map fst xs)) = List.map fst xs"
    unfolding sorted_list_of_set_sort_remdups by (simp add: distinct_remdups_id sorted_sort_id)
  moreover from assms have "keys (the_value xs) = fst ` set xs"
    by transfer (auto simp add: image_def split: option.split dest: set_map_of_compr)
  ultimately show ?thesis
    unfolding items_def using assms
    by (auto simp add: lookup_the_value intro: map_idI)
qed

lemma the_value_Nil [simp]:
  "the_value [] = 0"
  by transfer (simp add: fun_eq_iff)

lemma the_value_Cons [simp]:
  "the_value (x # xs) = update (fst x) (snd x) (the_value xs)"
  by transfer (simp add: fun_eq_iff)

lemma items_zero [simp]:
  "items 0 = []"
  unfolding items_def by simp

lemma items_one [simp]:
  "items 1 = [(0, 1)]"
  unfolding items_def by transfer simp

lemma items_single [simp]:
  "items (single k v) = (if v = 0 then [] else [(k, v)])"
  unfolding items_def by simp

lemma in_set_items_iff [simp]:
  "(k, v) \<in> set (items f) \<longleftrightarrow> k \<in> keys f \<and> lookup f k = v"
  unfolding items_def by transfer auto


subsection \<open>Size estimation\<close>

context
  fixes f :: "'a \<Rightarrow> nat"
  and g :: "'b :: zero \<Rightarrow> nat"
begin

definition poly_mapping_size :: "('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> nat"
where
  "poly_mapping_size m = g 0 + (\<Sum>k \<in> keys m. Suc (f k + g (lookup m k)))"

lemma poly_mapping_size_0 [simp]:
  "poly_mapping_size 0 = g 0"
  by (simp add: poly_mapping_size_def)

lemma poly_mapping_size_single [simp]:
  "poly_mapping_size (single k v) = (if v = 0 then g 0 else g 0 + f k + g v + 1)"
  unfolding poly_mapping_size_def by transfer simp

lemma keys_less_poly_mapping_size:
  "k \<in> keys m \<Longrightarrow> f k + g (lookup m k) < poly_mapping_size m"
unfolding poly_mapping_size_def
proof transfer
  fix k :: 'a and m :: "'a \<Rightarrow> 'b" and f :: "'a \<Rightarrow> nat" and g
  let ?keys = "{k. m k \<noteq> 0}"
  assume *: "finite ?keys" "k \<in> ?keys"
  then have "f k + g (m k) = (\<Sum>k' \<in> ?keys. f k' + g (m k') when k' = k)"
    by (simp add: sum.delta when_def)
  also have "\<dots> < (\<Sum>k' \<in> ?keys. Suc (f k' + g (m k')))" using *
    by (intro sum_strict_mono) (auto simp add: when_def)
  also have "\<dots> \<le> g 0 + \<dots>" by simp
  finally have "f k + g (m k) < \<dots>" .
  then show "f k + g (m k) < g 0 + (\<Sum>k | m k \<noteq> 0. Suc (f k + g (m k)))"
    by simp
qed

lemma lookup_le_poly_mapping_size:
  "g (lookup m k) \<le> poly_mapping_size m"
proof (cases "k \<in> keys m")
  case True
  with keys_less_poly_mapping_size [of k m]
  show ?thesis by simp
qed (simp add: poly_mapping_size_def)

lemma poly_mapping_size_estimation:
  "k \<in> keys m \<Longrightarrow> y \<le> f k + g (lookup m k) \<Longrightarrow> y < poly_mapping_size m"
  using keys_less_poly_mapping_size by (auto intro: le_less_trans)

lemma poly_mapping_size_estimation2:
  assumes "v \<in> range m" and "y \<le> g v"
  shows "y < poly_mapping_size m"
proof -
  from assms obtain k where *: "lookup m k = v" "v \<noteq> 0"
    by transfer blast
  from * have "k \<in> keys m"
    by auto
  then show ?thesis
  proof (rule poly_mapping_size_estimation)
    from assms * have "y \<le> g (lookup m k)"
      by simp
    then show "y \<le> f k + g (lookup m k)"
      by simp
  qed
qed

end

lemma poly_mapping_size_one [simp]:
  "poly_mapping_size f g 1 = g 0 + f 0 + g 1 + 1"
  unfolding poly_mapping_size_def by transfer simp

lemma poly_mapping_size_cong [fundef_cong]:
  "m = m' \<Longrightarrow> g 0 = g' 0 \<Longrightarrow> (\<And>k. k \<in> keys m' \<Longrightarrow> f k = f' k)
    \<Longrightarrow> (\<And>v. v \<in> range m' \<Longrightarrow> g v = g' v)
    \<Longrightarrow> poly_mapping_size f g m = poly_mapping_size f' g' m'"
  by (auto simp add: poly_mapping_size_def intro!: sum.cong)

instantiation poly_mapping :: (type, zero) size
begin

definition "size = poly_mapping_size (\<lambda>_. 0) (\<lambda>_. 0)"

instance ..

end


subsection \<open>Further mapping operations and properties\<close>

text \<open>It is like in algebra: there are many definitions, some are also used\<close>

lift_definition mapp ::
  "('a \<Rightarrow> 'b :: zero \<Rightarrow> 'c :: zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'c)"
  is "\<lambda>f p k. (if k \<in> keys p then f k (lookup p k) else 0)"
  by simp

lemma mapp_cong [fundef_cong]:
  "\<lbrakk> m = m'; \<And>k. k \<in> keys m' \<Longrightarrow> f k (lookup m' k) = f' k (lookup m' k) \<rbrakk>
  \<Longrightarrow> mapp f m = mapp f' m'"
  by transfer (auto simp add: fun_eq_iff)

lemma lookup_mapp:
  "lookup (mapp f p) k = (f k (lookup p k) when k \<in> keys p)"
  unfolding when_def
  by transfer simp

lemma keys_mapp_subset: "keys (mapp f p) \<subseteq> keys p"
  by transfer auto

hide_const (open) lookup single update keys range map map_key degree nth the_value items foldr mapp

end