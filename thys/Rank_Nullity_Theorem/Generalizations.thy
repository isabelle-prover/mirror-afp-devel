  (*
    Title: Generalizations.thy
    Author: Jose Divasón <jose.divasonm at unirioja.es>
    Author: Jesús Aransay <jesus-maria.aransay at unirioja.es>
  *)

section{*Generalizations*}

theory Generalizations
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

subsection{*Generalization of parts of the HMA library*}

text{*In this file, some parts of the Multivariate Analysis library required for our
formalizations of both the Rank Nullity Theorem and the Gauss-Jordan algorithm are generalized.

Mainly, we have carried out four kinds of generalizations:
\begin{enumerate}
\item Lemmas involving real vector spaces (that is, lemmas that used the @{text "real_vector"} 
  class) are now generalized to vector spaces over any field.
\item Some lemmas involving euclidean spaces (the @{text "euclidean_space"} class) have been 
  generalized to finite dimensional vector spaces.
\item Lemmas involving real matrices have been generalized to matrices over any field.
\item Lemmas about determinants involving the class @{text "linordered_idom"}, such as the lemma 
  @{text "det_identical_columns"}, are now proven using the class @{text "comm_ring_1"}.
\end{enumerate}
*}

hide_const (open) span
hide_const (open) dependent
hide_const (open) independent
hide_const (open) dim

interpretation vec: vector_space "op *s :: 'a::field => 'a^'b => 'a^'b"
  by (unfold_locales, simp_all)

(*A linear map is a mapping between the elements of two vector spaces over same field*)
(*A linear form is a mapping between a vector space and the field of its scalars*)

(******************* Generalized parts of the file Real_Vector_Space.thy *******************)

locale linear = B?: vector_space scaleB + C?: vector_space scaleC
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75) +
  fixes f :: "('b=>'c)"
  assumes cmult: "f (r *b x) = r *c (f x)"
  and add: "f (a + b) = f a + f b"
begin
(***************** Here ends the generalization of Real_Vector_Space.thy *****************)

(******************* Generalized parts of the file Linear_Algebra.thy *******************)

lemma linear_0: "f 0 = 0"
  by (metis add eq_add_iff)

lemma linear_cmul: "f (c *b x) = c *c (f x)" 
  by (metis cmult)
  
lemma linear_neg: "f (- x) = - f x"
  using linear_cmul [where c="-1"]
    by (metis add add_eq_0_iff linear_0)

lemma linear_add: "f (x + y) = f x + f y"
  by (metis add)

lemma linear_sub: "f (x - y) = f x - f y"
  by (metis diff_conv_add_uminus linear_add linear_neg)  

lemma linear_setsum:
  assumes fin: "finite S"
  shows "f (setsum g S) = setsum (f \<circ> g) S"
  using fin
proof induct
  case empty
  then show ?case
    by (simp add: linear_0)
next
  case (insert x F)
  have "f (setsum g (insert x F)) = f (g x + setsum g F)"
    using insert.hyps by simp
  also have "\<dots> = f (g x) + f (setsum g F)"
    using linear_add by simp
  also have "\<dots> = setsum (f \<circ> g) (insert x F)"
    using insert.hyps by simp
  finally show ?case .
qed


lemma linear_setsum_mul:
  assumes fin: "finite S"
  shows "f (setsum (\<lambda>i. c i *b v i) S) = setsum (\<lambda>i. c i *c f (v i)) S"
  using linear_setsum[OF fin] linear_cmul
  by simp


lemma linear_injective_0:
  shows "inj f \<longleftrightarrow> (\<forall>x. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj f \<longleftrightarrow> (\<forall> x y. f x = f y \<longrightarrow> x = y)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall> x y. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear_sub)
  also have "\<dots> \<longleftrightarrow> (\<forall> x. f x = 0 \<longrightarrow> x = 0)"
    by auto
  finally show ?thesis .
qed

end

lemma linear_iff:
  "linear scaleB scaleC  f \<longleftrightarrow> (vector_space scaleB) \<and> (vector_space scaleC) 
    \<and> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (scaleB c x) = scaleC c (f x))"
  (is "linear scaleB scaleC  f \<longleftrightarrow> ?rhs")
proof
  assume lf: "linear scaleB scaleC f" then interpret f: linear  scaleB scaleC  f .
  have B: "vector_space scaleB" using lf unfolding linear_def by simp
  moreover have C: "vector_space scaleC" using lf unfolding linear_def by simp
  ultimately show "?rhs" using f.linear_add f.linear_cmul by simp
next
  assume "?rhs" then show "linear scaleB scaleC  f" 
    by (unfold_locales, auto simp add: vector_space.scale_right_distrib
    vector_space.scale_left_distrib vector_space.scale_scale vector_space.scale_one)
qed

(*This lemma doesn't appear in the file Linear_Algebra.thy, but it's useful in my case.*)
lemma linear_iff2:
  "linear (op *s) (op *s)  f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *s x) = c *s (f x))"
  (is "linear (op *s) (op *s)  f \<longleftrightarrow> ?rhs")
proof
  assume "linear  (op *s) (op *s) f" then interpret f: linear  "(op *s)" "(op *s)" f .
  show "?rhs" by (metis f.linear_add f.linear_cmul)
next
  assume "?rhs" then show "linear (op *s) (op *s) f" by (unfold_locales,auto)
qed

lemma linear_compose_sub: "linear scale scaleC f \<Longrightarrow> linear scale scaleC g \<Longrightarrow> linear scale scaleC (\<lambda>x. f x - g x)"
  unfolding linear_iff
  by (simp add: vector_space.scale_right_diff_distrib)
    
lemma linear_compose: "linear scale scaleC f \<Longrightarrow> linear scaleC scaleT  g \<Longrightarrow> linear scale scaleT  (g o f)"
  unfolding linear_iff by auto
    
context vector_space
begin

lemma linear_id: "linear scale scale id"
 by (simp add: linear_iff, unfold_locales)

(*This lemma doesn't appear in the file Linear_Algebra.thy, but it's useful for my formalization.*)
lemma scale_minus1_left[simp]:
  shows "scale (-1) x = - x"
  using scale_minus_left [of 1 x] by simp

definition subspace :: "'b set \<Rightarrow> bool"
  where "subspace S \<longleftrightarrow> 0 \<in> S \<and> (\<forall>x\<in> S. \<forall>y \<in>S. x + y \<in> S) \<and> (\<forall>c. \<forall>x \<in>S. scale c x \<in>S )"  
definition "span (S::'b set) = (subspace hull S)"
definition "dependent S \<longleftrightarrow> (\<exists>a \<in> S. a \<in> span (S - {a}))"
abbreviation"independent s \<equiv> \<not> dependent s"

text {* Closure properties of subspaces.*}

lemma subspace_UNIV[simp]: "subspace UNIV"
  by (simp add: subspace_def)

lemma subspace_0: "subspace S \<Longrightarrow> 0 \<in> S"
  by (metis subspace_def)

lemma subspace_add: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S"
  by (metis subspace_def)

lemma  subspace_mul: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> scale c x \<in> S"
  by (metis subspace_def)

lemma subspace_neg: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> - x \<in> S" 
by (metis scale_minus_left scale_one subspace_mul)

lemma subspace_sub: "subspace S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x - y \<in> S"
  by (metis diff_conv_add_uminus subspace_add subspace_neg)
  
lemma subspace_setsum:
  assumes sA: "subspace A"
    and fB: "finite B"
    and f: "\<forall>x\<in> B. f x \<in> A"
  shows "setsum f B \<in> A"
  using  fB f sA
  by (induct rule: finite_induct[OF fB])
    (simp add: subspace_def sA, auto simp add: sA subspace_add)
      
lemma subspace_linear_image:
  assumes lf: "linear scale scaleC f"
    and sS: "subspace S"
  shows "vector_space.subspace scaleC (f ` S)"
proof -
interpret lf: linear scale scaleC f using lf by simp
have C: "vector_space scaleC"  using lf unfolding linear_def by simp
show ?thesis
  proof (unfold vector_space.subspace_def[OF C], auto)
    show " 0 \<in> f ` S"
      by (metis (full_types) image_eqI lf.linear_0 sS subspace_0)
   fix x y assume x: "x \<in> S" and y: "y \<in> S"
   show "f x + f y \<in> f ` S"  unfolding image_iff
    apply (rule_tac x="x + y" in bexI) using lf.add subspace_add[OF sS x y] by auto
   fix c
   show "scaleC c (f x) \<in> f ` S" by (metis imageI subspace_mul lf.linear_cmul sS x)
  qed
qed

lemma subspace_linear_vimage: 
  assumes lf: "linear scale scaleC (f::'b::ab_group_add=>'c::ab_group_add)"
  and s: "vector_space.subspace scaleC S"
  shows "subspace (f -` S)"
  proof -
  interpret lf: linear scale scaleC f using lf by simp
  have C: "vector_space scaleC" using lf by (unfold_locales)
  show ?thesis
    unfolding subspace_def
      apply (auto)
      apply (metis lf.C.subspace_0 lf.linear_0 s)
      apply (metis (full_types) lf.C.subspace_def lf.linear_add s)
      by (metis lf.C.subspace_mul lf.linear_cmul s)
qed

lemma subspace_Times:
assumes A: "subspace A" and B: "subspace B"
shows "vector_space.subspace (\<lambda>x (a,b). (scale x a, scale x b)) (A \<times> B)"
proof -
have v: "vector_space (\<lambda>x (a,b). (scale x a, scale x b))"
  unfolding vector_space_def
  by (simp add: scale_left_distrib scale_right_distrib)
show ?thesis
  using A B unfolding subspace_def
  unfolding vector_space.subspace_def[OF v] zero_prod_def by auto
qed

(*This lemma doesn't appear in the file Linear_Algebra.thy, but it's useful for my formalization.*)
lemma vector_space_product: "vector_space (\<lambda>x (a, b). (scale x a, scale x b))"
  by (unfold_locales, auto simp: scale_right_distrib scale_left_distrib)

text {* Properties of span. *}  
  
lemma  span_mono: "A \<subseteq> B \<Longrightarrow> span A \<subseteq> span B"
  by (metis span_def hull_mono)  
  
lemma subspace_span: "subspace (span S)"
  unfolding span_def
  apply (rule hull_in)
  apply (simp only: subspace_def Inter_iff Int_iff subset_eq)
  apply auto
  done
  
  
lemma span_clauses:
  "a \<in> S ==> a \<in> span S"
  "0 \<in> span S"
  "x\<in> span S ==> y \<in> span S ==> x + y \<in> span S"
  "x \<in> span S ==> scale c x \<in> span S"
  by (metis span_def hull_subset subset_eq) (metis subspace_span subspace_def)+
  
lemma span_unique:
  "S \<subseteq> T ==> subspace T ==> (!!T'. S \<subseteq> T' ==> subspace T' ==> T \<subseteq> T') ==> span S = T"
  unfolding span_def by (rule hull_unique)
  
  
lemma span_minimal: "S \<subseteq> T ==> subspace T ==> span S \<subseteq> T"
  unfolding span_def by (rule hull_minimal)

lemma span_induct:
  assumes x: "x \<in> span S"
    and P: "subspace P"
    and SP: "!!x. x \<in> S ==> x \<in> P"
  shows "x \<in> P"
proof -
  from SP have SP': "S \<subseteq> P"
    by (simp add: subset_eq)
  from x hull_minimal[where S=subspace, OF SP' P, unfolded span_def[symmetric]]
  show "x \<in> P"
    by (metis subset_eq)
qed

lemma span_empty[simp]: "span {} = {0}"
  apply (simp add: span_def)
  apply (rule hull_unique)
  apply (auto simp add: subspace_def)
  done

  
lemma  independent_empty[intro]: "independent {}"
  by (simp add: dependent_def)

lemma dependent_single[simp]: "dependent {x} \<longleftrightarrow> x = 0"
  unfolding dependent_def by auto

lemma  independent_mono: "independent A ==> B \<subseteq> A ==> independent B"
  apply (clarsimp simp add: dependent_def span_mono)
  apply (subgoal_tac "span (B - {a}) \<le> span (A - {a})")
  apply force
  apply (rule span_mono)
  apply auto
  done

lemma span_subspace: "A \<subseteq> B ==> B \<le> span A ==>  subspace B ==> span A = B"
  by (metis order_antisym span_def hull_minimal) 
  
  
lemma span_induct':
  assumes SP: "\<forall>x \<in> S. P x"
    and P: "subspace {x. P x}"
  shows "\<forall>x \<in> span S. P x"
  using span_induct SP P by blast

inductive_set  span_induct_alt_help for S:: "'b set"
where
  span_induct_alt_help_0: "0 \<in> span_induct_alt_help S"
| span_induct_alt_help_S:
    "x \<in> S ==> z \<in> span_induct_alt_help S ==>
      (scale c x + z) \<in> span_induct_alt_help S"

lemma span_induct_alt':
  assumes h0: "h 0"
    and hS: "!!c x y. x \<in> S ==> h y ==> h (scale c x + y)"
  shows "\<forall>x \<in> span S. h x"
proof -
  {
    fix x :: 'b
    assume x: "x \<in> span_induct_alt_help S"
    have "h x"
      apply (rule span_induct_alt_help.induct[OF x])
      apply (rule h0)
      apply (rule hS)
      apply assumption
      apply assumption
      done
  }
  note th0 = this
  {
    fix x
    assume x: "x \<in> span S"
    have "x \<in> span_induct_alt_help S"
    proof (rule span_induct[where x=x and S=S])
      show "x \<in> span S" by (rule x)
    next
      fix x
      assume xS: "x \<in> S"
      from span_induct_alt_help_S[OF xS span_induct_alt_help_0, of 1]
      show "x \<in> span_induct_alt_help S"
        by simp
    next
      have "0 \<in> span_induct_alt_help S" by (rule span_induct_alt_help_0)
      moreover
      {
        fix x y
        assume h: "x \<in> span_induct_alt_help S" "y \<in> span_induct_alt_help S"
        from h have "(x + y) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply simp
          unfolding add.assoc
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done
      }
      moreover
      {
        fix c x
        assume xt: "x \<in> span_induct_alt_help S"
        then have "(scale c x) \<in> span_induct_alt_help S"
          apply (induct rule: span_induct_alt_help.induct)
          apply (simp add: span_induct_alt_help_0)
          apply (simp add: scale_right_distrib)
          apply (rule span_induct_alt_help_S)
          apply assumption
          apply simp
          done }
      ultimately show "subspace (span_induct_alt_help S)"
        unfolding subspace_def Ball_def by blast
    qed
  }
  with th0 show ?thesis by blast
qed

lemma span_induct_alt:
  assumes h0: "h 0"
    and hS: "!!c x y. x \<in> S ==> h y ==> h (scale c x + y)"
    and x: "x \<in> span S"
  shows "h x"
  using span_induct_alt'[of h S] h0 hS x by blast
  
text {* Individual closure properties. *}

lemma span_span: "span (span A) = span A"
  unfolding span_def hull_hull ..

lemma span_superset: "x \<in> S ==> x \<in> span S"
  by (metis span_clauses(1))

lemma  span_0: "0 \<in> span S"
  by (metis span_clauses(2))

lemma span_inc: "S \<subseteq> span S"
  by (metis subset_eq span_superset)

lemma dependent_0:
  assumes "0 \<in> A"
  shows "dependent A"
  unfolding dependent_def
  apply (rule_tac x=0 in bexI)
  using assms span_0
  apply auto
  done

lemma span_add: "x \<in> span S ==> y \<in> span S ==> x + y \<in> span S"
  by (metis subspace_add subspace_span)

lemma span_mul: "x \<in> span S ==> scale c x \<in> span S"
  by (metis span_clauses(4))

lemma span_neg: "x \<in> span S ==> - x \<in> span S"
  by (metis subspace_neg subspace_span)

lemma span_sub: "x \<in> span S ==> y \<in> span S ==> x - y \<in> span S"
  by (metis subspace_span subspace_sub)

lemma span_setsum: "finite A ==> \<forall>x \<in> A. f x \<in> span S ==> setsum f A \<in> span S"
  by (rule subspace_setsum, rule subspace_span)

lemma span_add_eq: "x \<in> span S ==> x + y \<in> span S \<longleftrightarrow> y \<in> span S"
  apply (auto simp only: span_add span_sub)
  apply (subgoal_tac "(x + y) - x \<in> span S")
  apply simp
  apply (simp only: span_add span_sub)
  done
  

lemma span_linear_image:
  assumes lf: "linear scale scaleC (f::'b::ab_group_add=>'c::ab_group_add)"
  shows "vector_space.span scaleC (f ` S) = f ` (span S)" 
proof -
interpret B: vector_space scale using lf by (metis linear_iff)
interpret C: vector_space scaleC using lf by (metis linear_iff)
interpret lf: linear scale scaleC f using lf by simp
show ?thesis
proof (rule C.span_unique)
  show "f ` S \<subseteq> f ` span S" 
    by (rule image_mono, rule span_inc)
  show "vector_space.subspace scaleC (f ` span S)"
    using lf subspace_span by (rule subspace_linear_image)
next
  fix T
  assume "f ` S \<subseteq> T" and "vector_space.subspace scaleC T"
  then show "f ` span S \<subseteq> T"
    unfolding image_subset_iff_subset_vimage
    by (metis subspace_linear_vimage lf span_minimal)
qed
qed

lemma span_union: "span (A \<union> B) = (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
proof (rule span_unique)
  show "A \<union> B \<subseteq> (\<lambda>(a, b). a + b) ` (span A \<times> span B)"
    by safe (force intro: span_clauses)+
next   
  have "linear (\<lambda>x (a,b). (scale x a, scale x b)) scale (\<lambda>(a, b). a + b)"
    proof (unfold linear_def linear_axioms_def, auto)
        show "vector_space (\<lambda>x (a, b). (scale x a, scale x b))" using vector_space_product .
        show "vector_space scale" by (unfold_locales)
        show "\<And>r a b. scale r a + scale r b = scale r (a + b)" by (metis scale_right_distrib)
    qed
  moreover have "vector_space.subspace (\<lambda>x (a,b). (scale x a, scale x b))  (span A \<times> span B)"
    by (intro subspace_Times subspace_span)
  ultimately show "subspace ((\<lambda>(a, b). a + b) ` (span A \<times> span B))"
    by (metis (lifting) linear_iff vector_space.subspace_linear_image)
next
  fix T
  assume "A \<union> B \<subseteq> T" and "subspace T"
  then show "(\<lambda>(a, b). a + b) ` (span A \<times> span B) \<subseteq> T"
    by (auto intro!: subspace_add elim: span_induct)
qed


lemma span_singleton: "span {x} = range (\<lambda>k. scale k x)"
proof (rule span_unique)
  show "{x} \<subseteq> range (\<lambda>k. scale k x)"
    by (fast intro: scale_one [symmetric])
  show "subspace (range (\<lambda>k. scale k x))"
    unfolding subspace_def
    by (auto intro: scale_left_distrib [symmetric])
next
  fix T
  assume "{x} \<subseteq> T" and "subspace T"
  then show "range (\<lambda>k. scale k x) \<subseteq> T"
    unfolding subspace_def by auto
qed

lemma span_insert: "span (insert a S) = {x. \<exists>k. (x - scale k a) \<in> span S}"
proof -
  have "span ({a} \<union> S) = {x. \<exists>k. (x - scale k a) \<in> span S}"
    unfolding span_union span_singleton
    apply safe
    apply (rule_tac x=k in exI, simp)
    apply (erule rev_image_eqI [OF SigmaI [OF rangeI]])
    apply auto
    done
  then show ?thesis by simp
qed


lemma span_breakdown:
  assumes bS: "b \<in> S"
    and aS: "a \<in> span S"
  shows "\<exists>k. a - scale k b \<in> span (S - {b})"
  using assms span_insert [of b "S - {b}"]
  by (simp add: insert_absorb)

lemma span_breakdown_eq: "x \<in> span (insert a S) \<longleftrightarrow> (\<exists>k. x - scale k a \<in> span S)"
  by (simp add: span_insert)
  
lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)"
    and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - scale k b \<in> span (S - {b})" by auto
  show ?thesis
  proof (cases "k = 0")
    case True
    with k have "a \<in> span S"
      apply (simp)
      apply (rule set_rev_mp)
      apply assumption
      apply (rule span_mono)
      apply blast
      done
    with na show ?thesis by blast
  next
    case False
    have eq: "b = scale (1/k) a - (scale (1/k) a - b)" by simp
    from False have eq': "scale (1/k) (a - scale k b) = scale (1/k) a - b"
      by (simp add: algebra_simps)
    from k have "scale (1/k) (a - scale k b) \<in> span (S - {b})"
      by (rule span_mul)
    then have th: "scale (1/k) a - b \<in> span (S - {b})"
      unfolding eq' .
    from k show ?thesis
      apply (subst eq)
      apply (rule span_sub)
      apply (rule span_mul)
      apply (rule span_superset)
      apply blast
      apply (rule set_rev_mp)
      apply (rule th)
      apply (rule span_mono)
      using na
      apply blast
      done
  qed
qed



lemma in_span_delete:
  assumes a: "a \<in> span S"
    and na: "a \<notin> span (S - {b})"
  shows "b \<in> span (insert a (S - {b}))"
  apply (rule in_span_insert)
  apply (rule set_rev_mp)
  apply (rule a)
  apply (rule span_mono)
  apply blast
  apply (rule na)
  done
  
  
lemma span_redundant: "x \<in> span S \<Longrightarrow> span (insert x S) = span S"
  unfolding span_def by (rule hull_redundant)

lemma span_trans:
  assumes x: "x \<in> span S"
    and y: "y \<in> span (insert x S)"
  shows "y \<in> span S"
  using assms by (simp only: span_redundant)
  
lemma span_insert_0[simp]: "span (insert 0 S) = span S"
  by (metis span_0 span_redundant)

lemma span_explicit:
  "span  P = {y. \<exists>S u. finite S \<and> S \<subseteq> P \<and> setsum (\<lambda>v. scale (u v) v) S = y}"
  (is "_ = ?E" is "_ = {y. ?h y}" is "_ = {y. \<exists>S u. ?Q S u y}")
  proof -
  {
    fix x
    assume x: "x \<in> ?E"
    then obtain S u where fS: "finite S" and SP: "S\<subseteq>P" and u: "setsum (\<lambda>v. scale (u v) v) S = x"
      by blast
    have "x \<in> span P"
      unfolding u[symmetric]
      apply (rule span_setsum[OF fS])
      using span_mono[OF SP]
      apply (auto intro: span_superset span_mul)
      done
  }
  moreover
  have "\<forall>x \<in> span P. x \<in> ?E"
  proof (rule span_induct_alt')
    show "0 \<in> Collect ?h"
      unfolding mem_Collect_eq
      apply (rule exI[where x="{}"])
      apply simp
      done
  next
    fix c x y
    assume x: "x \<in> P"
    assume hy: "y \<in> Collect ?h"
    from hy obtain S u where fS: "finite S" and SP: "S\<subseteq>P"
      and u: "setsum (\<lambda>v. scale (u v) v) S = y" by blast
    let ?S = "insert x S"
    let ?u = "\<lambda>y. if y = x then (if x \<in> S then u y + c else c) else u y"
    from fS SP x have th0: "finite (insert x S)" "insert x S \<subseteq> P"
      by blast+
    have "?Q ?S ?u (scale c x + y)"
    proof cases
      assume xS: "x \<in> S"
      have S1: "S = (S - {x}) \<union> {x}"
        and Sss:"finite (S - {x})" "finite {x}" "(S - {x}) \<inter> {x} = {}"
        using xS fS by auto
      have "setsum (\<lambda>v. scale (?u v) v) ?S =(\<Sum>v\<in>S - {x}.  scale (?u v) v) + scale (u x + c) x"
        using xS by (simp add: setsum.remove [OF fS xS] insert_absorb)
      also have "\<dots> = (\<Sum>v\<in>S. scale (u v) v) + scale c x"
        by (simp add: setsum.remove [OF fS xS] algebra_simps)
      also have "\<dots> = scale c x + y"
        by (simp add: add.commute u)
      finally have "setsum (\<lambda>v. scale (?u v) v) ?S = scale c x + y" .
      then show ?thesis using th0 by blast
    next
      assume xS: "x \<notin> S"
      have th00: "(\<Sum>v\<in>S. scale (if v = x then c else u v) v) = y"
        unfolding u[symmetric]
        apply (rule setsum.cong)
        using xS
        apply auto
        done
      show ?thesis using fS xS th0
        by (simp add: th00 setsum_clauses add.commute cong del: if_weak_cong)
    qed
    then show "(scale c x + y) \<in> Collect ?h"
      unfolding mem_Collect_eq
      apply -
      apply (rule exI[where x="?S"])
      apply (rule exI[where x="?u"])
      apply metis
      done
  qed
  ultimately show ?thesis by blast
qed


lemma dependent_explicit:
  "dependent P \<longleftrightarrow> (\<exists>S u. finite S \<and> S \<subseteq> P \<and> (\<exists>v\<in>S. u v \<noteq> 0 \<and> setsum (\<lambda>v. scale (u v) v) S = 0))"
  (is "?lhs = ?rhs")
  proof -
  {
    assume dP: "dependent P"
    then obtain a S u where aP: "a \<in> P" and fS: "finite S"
      and SP: "S \<subseteq> P - {a}" and ua: "setsum (\<lambda>v. scale (u v) v) S = a"
      unfolding dependent_def span_explicit by blast
    let ?S = "insert a S"
    let ?u = "\<lambda>y. if y = a then - 1 else u y"
    let ?v = a
    from aP SP have aS: "a \<notin> S"
      by blast
    from fS SP aP have th0: "finite ?S" "?S \<subseteq> P" "?v \<in> ?S" "?u ?v \<noteq> 0" by auto
    have s0: "setsum (\<lambda>v. scale (?u v) v) ?S = 0"
      using fS aS
      apply (simp add: setsum_clauses field_simps)
      apply (subst (2) ua[symmetric])
      apply (rule setsum.cong)
      apply auto
      done
    with th0 have ?rhs by fast
  }
  moreover
  {
    fix S u v
    assume fS: "finite S"
      and SP: "S \<subseteq> P"
      and vS: "v \<in> S"
      and uv: "u v \<noteq> 0"
      and u: "setsum (\<lambda>v. scale (u v) v) S = 0"
    let ?a = v
    let ?S = "S - {v}"
    let ?u = "\<lambda>i. (- u i) / u v"
    have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"
      using fS SP vS by auto
    have "setsum (\<lambda>v. scale (?u v) v) ?S =
      setsum (\<lambda>v. scale (- (inverse (u ?a))) (scale (u v) v)) S - scale (?u v) v" 
      using fS vS uv by (simp add: setsum_diff1 field_simps)   
    also have "\<dots> = ?a" 
      unfolding scale_setsum_right[symmetric] u using uv by simp
    finally have "setsum (\<lambda>v. scale (?u v) v) ?S = ?a" .
    with th0 have ?lhs
      unfolding dependent_def span_explicit
      apply -
      apply (rule bexI[where x= "?a"])
      apply (simp_all del: scale_minus_left)
      apply (rule exI[where x= "?S"])
      apply (auto simp del: scale_minus_left)
      done
  }
  ultimately show ?thesis by blast
qed



lemma span_finite:
  assumes fS: "finite S"
  shows "span S = {y. \<exists>u. setsum (\<lambda>v. scale (u v)  v) S = y}"
  (is "_ = ?rhs")
proof -
  {
    fix y
    assume y: "y \<in> span S"
    from y obtain S' u where fS': "finite S'"
      and SS': "S' \<subseteq> S"
      and u: "setsum (\<lambda>v. scale (u v)v) S' = y"
      unfolding span_explicit by blast
    let ?u = "\<lambda>x. if x \<in> S' then u x else 0"
    have "setsum (\<lambda>v. scale (?u v) v) S = setsum (\<lambda>v. scale (u v) v) S'"
      using SS' fS by (auto intro!: setsum.mono_neutral_cong_right)
    then have "setsum (\<lambda>v. scale (?u v) v) S = y" by (metis u)
    then have "y \<in> ?rhs" by auto
  }
  moreover
  {
    fix y u
    assume u: "setsum (\<lambda>v. scale (u v) v) S = y"
    then have "y \<in> span S" using fS unfolding span_explicit by auto
  }
  ultimately show ?thesis by blast
qed


lemma independent_insert:
  "independent (insert a S) \<longleftrightarrow>
    (if a \<in> S then independent S else independent S \<and> a \<notin> span S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "a \<in> S")
  case True
  then show ?thesis
    using insert_absorb[OF True] by simp
next
  case False
  show ?thesis
  proof
    assume i: ?lhs
    then show ?rhs
      using False
      apply simp
      apply (rule conjI)
      apply (rule independent_mono)
      apply assumption
      apply blast
      apply (simp add: dependent_def)
      done
  next
    assume i: ?rhs
    show ?lhs
      using i False
      apply simp
      apply (auto simp add: dependent_def)
      apply (case_tac "aa = a")
      apply auto
      apply (subgoal_tac "insert a S - {aa} = insert a (S - {aa})")
      apply simp
      apply (subgoal_tac "a \<in> span (insert aa (S - {aa}))")
      apply (subgoal_tac "insert aa (S - {aa}) = S")
      apply simp
      apply blast
      apply (rule in_span_insert)
      apply assumption
      apply blast
      apply blast
      done
  qed
qed


lemma spanning_subset_independent:
  assumes BA: "B \<subseteq> A"
    and iA: "independent A"
    and AsB: "A \<subseteq> span B"
  shows "A = B"
proof
  show "B \<subseteq> A" by (rule BA)

  from span_mono[OF BA] span_mono[OF AsB]
  have sAB: "span A = span B" unfolding span_span by blast

  {
    fix x
    assume x: "x \<in> A"
    from iA have th0: "x \<notin> span (A - {x})"
      unfolding dependent_def using x by blast
    from x have xsA: "x \<in> span A"
      by (blast intro: span_superset)
    have "A - {x} \<subseteq> A" by blast
    then have th1: "span (A - {x}) \<subseteq> span A"
      by (metis span_mono)
    {
      assume xB: "x \<notin> B"
      from xB BA have "B \<subseteq> A - {x}"
        by blast
      then have "span B \<subseteq> span (A - {x})"
        by (metis span_mono)
      with th1 th0 sAB have "x \<notin> span A"
        by blast
      with x have False
        by (metis span_superset)
    }
    then have "x \<in> B" by blast
  }
  then show "A \<subseteq> B" by blast
qed

lemma exchange_lemma:
  assumes f:"finite t"
  and i: "independent s"
  and sp: "s \<subseteq> span t"
  shows "\<exists>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  using f i sp
proof (induct "card (t - s)" arbitrary: s t rule: less_induct)
  case less
  note ft = `finite t` and s = `independent s` and sp = `s \<subseteq> span t`
  let ?P = "\<lambda>t'. card t' = card t \<and> finite t' \<and> s \<subseteq> t' \<and> t' \<subseteq> s \<union> t \<and> s \<subseteq> span t'"
  let ?ths = "\<exists>t'. ?P t'"
  {
    assume st: "s \<subseteq> t"
    from st ft span_mono[OF st]
    have ?ths
      apply -
      apply (rule exI[where x=t])
      apply (auto intro: span_superset)
      done
  }
  moreover
  {
    assume st: "t \<subseteq> s"
    from spanning_subset_independent[OF st s sp] st ft span_mono[OF st]
    have ?ths
      apply -
      apply (rule exI[where x=t])
      apply (auto intro: span_superset)
      done
  }
  moreover
  {
    assume st: "\<not> s \<subseteq> t" "\<not> t \<subseteq> s"
    from st(2) obtain b where b: "b \<in> t" "b \<notin> s"
      by blast
    from b have "t - {b} - s \<subset> t - s"
      by blast
    then have cardlt: "card (t - {b} - s) < card (t - s)"
      using ft by (auto intro: psubset_card_mono)
    from b ft have ct0: "card t \<noteq> 0"
      by auto
    have ?ths
    proof cases
      assume stb: "s \<subseteq> span (t - {b})"
      from ft have ftb: "finite (t - {b})"
        by auto
      from less(1)[OF cardlt ftb s stb]
      obtain u where u: "card u = card (t - {b})" "s \<subseteq> u" "u \<subseteq> s \<union> (t - {b})" "s \<subseteq> span u"
        and fu: "finite u" by blast
      let ?w = "insert b u"
      have th0: "s \<subseteq> insert b u"
        using u by blast
      from u(3) b have "u \<subseteq> s \<union> t"
        by blast
      then have th1: "insert b u \<subseteq> s \<union> t"
        using u b by blast
      have bu: "b \<notin> u"
        using b u by blast
      from u(1) ft b have "card u = (card t - 1)"
        by auto
      then have th2: "card (insert b u) = card t"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from u(4) have "s \<subseteq> span u" .
      also have "\<dots> \<subseteq> span (insert b u)"
        by (rule span_mono) blast
      finally have th3: "s \<subseteq> span (insert b u)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"
        by blast
      from th show ?thesis by blast
    next
      assume stb: "\<not> s \<subseteq> span (t - {b})"
      from stb obtain a where a: "a \<in> s" "a \<notin> span (t - {b})"
        by blast
      have ab: "a \<noteq> b"
        using a b by blast
      have at: "a \<notin> t"
        using a ab span_superset[of a "t- {b}"] by auto
      have mlt: "card ((insert a (t - {b})) - s) < card (t - s)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (t - {b}))"
        using ft by auto
      {
        fix x
        assume xs: "x \<in> s"
        have t: "t \<subseteq> insert b (insert a (t - {b}))"
          using b by auto
        from b(1) have "b \<in> span t"
          by (simp add: span_superset)
        have bs: "b \<in> span (insert a (t - {b}))"
          apply (rule in_span_delete)
          using a sp unfolding subset_eq
          apply auto
          done
        from xs sp have "x \<in> span t"
          by blast
        with span_mono[OF t] have x: "x \<in> span (insert b (insert a (t - {b})))" ..
        from span_trans[OF bs x] have "x \<in> span (insert a (t - {b}))" .
      }
      then have sp': "s \<subseteq> span (insert a (t - {b}))"
        by blast
      from less(1)[OF mlt ft' s sp'] obtain u where u:
        "card u = card (insert a (t - {b}))"
        "finite u" "s \<subseteq> u" "u \<subseteq> s \<union> insert a (t - {b})"
        "s \<subseteq> span u" by blast
      from u a b ft at ct0 have "?P u"
        by auto
      then show ?thesis by blast
    qed
  }
  ultimately show ?ths by blast
qed

lemma independent_span_bound:
  assumes f: "finite t"
    and i: "independent s"
    and sp: "s \<subseteq> span t"
  shows "finite s \<and> card s \<le> card t"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)


(*The following lemmas don't appear in the library, but they are useful in my development.*)
lemma independent_explicit:
  "independent A = 
  (\<forall>S \<subseteq> A. finite S \<longrightarrow> (\<forall>u. (\<Sum>v\<in>S. scale (u v) v) = 0 \<longrightarrow> (\<forall>v\<in>S. u v = 0)))" 
  unfolding dependent_explicit [of A] by (simp add: disj_not2)

text{*A finite set @{term "A::'a set"} for which
  every of its linear combinations equal to zero 
  requires every coefficient being zero, is independent:*}  
  
lemma independent_if_scalars_zero:
  assumes fin_A: "finite A"
  and sum: "\<forall>f. (\<Sum>x\<in>A. scale (f x) x) = 0 \<longrightarrow> (\<forall>x \<in> A. f x = 0)"
  shows "independent A"
proof (unfold independent_explicit, clarify)
  fix S v and u :: "'b \<Rightarrow> 'a"
  assume S: "S \<subseteq> A" and v: "v \<in> S" 
  let ?g = "\<lambda>x. if x \<in> S then u x else 0"
  have "(\<Sum>v\<in>A. scale (?g v) v) = (\<Sum>v\<in>S. scale (u v) v)"
    using S fin_A by (auto intro!: setsum.mono_neutral_cong_right) 
  also assume "(\<Sum>v\<in>S. scale (u v) v) = 0"
  finally have "?g v = 0" using v S sum by force
  thus "u v = 0"  unfolding if_P[OF v] .
qed
end

definition "cart_basis = {axis i 1 | i. i\<in>UNIV}"

lemma finite_cart_basis: "finite (cart_basis)" unfolding cart_basis_def
  using finite_Atleast_Atmost_nat by fastforce

lemma independent_cart_basis:
  "vec.independent (cart_basis)"
  proof (rule vec.independent_if_scalars_zero, auto)
  show "finite (cart_basis)" using finite_cart_basis .
  fix f::"('a, 'b) vec \<Rightarrow> 'a" and x::"('a, 'b) vec"
  assume eq_0: "(\<Sum>x\<in>cart_basis. f x *s x) = 0" and x_in: "x \<in> cart_basis"
  obtain i where x: "x = axis i 1" using x_in unfolding cart_basis_def by auto
  have setsum_eq_0: "(\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i)) = 0"
    proof (rule setsum.neutral, rule ballI)
      fix xa assume xa: "xa \<in> cart_basis - {x}"
      obtain a where a: "xa = axis a 1" and a_not_i: "a \<noteq> i"
        using xa x unfolding cart_basis_def by auto
      have "xa $ i = 0" unfolding a axis_def using a_not_i by auto
      thus "f xa * xa $ i = 0" by simp
   qed    
  have "0 = (\<Sum>x\<in>cart_basis. f x *s x) $ i" using eq_0 by simp
  also have "... = (\<Sum>x\<in>cart_basis. (f x *s x) $ i)" unfolding setsum_component ..
  also have "... = (\<Sum>x\<in>cart_basis. f x * (x $ i))" unfolding vector_smult_component ..
  also have "... = f x * (x $ i) + (\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i))"
    by (rule setsum.remove[OF finite_cart_basis x_in])
  also have "... =  f x * (x $ i)" unfolding setsum_eq_0 by simp
  also have "... = f x" unfolding x axis_def by auto
  finally show "f x = 0" .. 
qed

lemma span_cart_basis:
  "vec.span (cart_basis) = UNIV"
proof (auto)
fix x::"('a, 'b) vec"
let ?f="\<lambda>v. x $ (THE i. v = axis i 1)"
show "x \<in> vec.span (cart_basis)"
proof (unfold vec.span_finite[OF finite_cart_basis], auto, rule exI[of _ ?f] , subst (2) vec_eq_iff, clarify)
fix i::'b
let ?w = "axis i (1::'a)"
have the_eq_i: "(THE a. ?w = axis a 1) = i" 
  by (rule the_equality, auto simp: axis_eq_axis)
have setsum_eq_0: "(\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i) = 0"
  proof (rule setsum.neutral, rule ballI)
     fix xa::"('a, 'b) vec"
     assume xa: "xa \<in> cart_basis - {?w}"
     obtain j where j: "xa = axis j 1" and i_not_j: "i \<noteq> j" using xa unfolding cart_basis_def by auto
     have the_eq_j: "(THE i. xa = axis i 1) = j"
      proof (rule the_equality)
         show "xa = axis j 1" using j .
         show "\<And>i. xa = axis i 1 \<Longrightarrow> i = j" by (metis axis_eq_axis j zero_neq_one)
      qed
     show "x $ (THE i. xa = axis i 1) * xa $ i = 0" 
      apply (subst (2) j) 
      unfolding the_eq_j unfolding axis_def using i_not_j by simp
   qed
have "(\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i = 
  (\<Sum>v\<in>cart_basis. (x $ (THE i. v = axis i 1) *s v) $ i)" unfolding setsum_component ..
also have "... = (\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) * v $ i)" 
  unfolding vector_smult_component ..
also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i + (\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i)"
 by (rule setsum.remove[OF finite_cart_basis], auto simp add: cart_basis_def)
also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i" unfolding setsum_eq_0 by simp
also have "... = x $ i" unfolding the_eq_i unfolding axis_def by auto
finally show "(\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i = x $ i" .
qed
qed

(*Locale of a finite dimensional vector space. From here on, some theorems that were based on
the euclidean_space class will be proven over this new locale.*)
locale finite_dimensional_vector_space = vector_space +
  fixes Basis :: "'b set"
  assumes finite_Basis: "finite (Basis)"
  and independent_Basis: "independent (Basis)"
  and span_Basis: "span (Basis) = UNIV"  
begin

(*In the library, this is an abbreviation and it appears in the file Euclidean_Space.thy*)
definition dimension :: "nat" where
  "dimension \<equiv> card (Basis :: 'b set)"

lemma independent_bound:
  shows "independent S \<Longrightarrow> finite S \<and> card S \<le> dimension"
  using independent_span_bound[OF finite_Basis, of S]
  unfolding dimension_def span_Basis by auto
  
  
  lemma maximal_independent_subset_extend:
  assumes sv: "S \<subseteq> V"
    and iS: "independent S"
  shows "\<exists>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  using sv iS
proof (induct "dimension - card S" arbitrary: S rule: less_induct)
  case less
  note sv = `S \<subseteq> V` and i = `independent S`
  let ?P = "\<lambda>B. S \<subseteq> B \<and> B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  let ?ths = "\<exists>x. ?P x"
  let ?d = "dimension"
  show ?ths
  proof (cases "V \<subseteq> span S")
    case True
    then show ?thesis
      using sv i by blast
  next
    case False
    then obtain a where a: "a \<in> V" "a \<notin> span S"
      by blast
    from a have aS: "a \<notin> S"
      by (auto simp add: span_superset)
    have th0: "insert a S \<subseteq> V"
      using a sv by blast
    from independent_insert[of a S]  i a
    have th1: "independent (insert a S)"
      by auto
    have mlt: "?d - card (insert a S) < ?d - card S"
      using aS a independent_bound[OF th1] by auto

    from less(1)[OF mlt th0 th1]
    obtain B where B: "insert a S \<subseteq> B" "B \<subseteq> V" "independent B" " V \<subseteq> span B"
      by blast
    from B have "?P B" by auto
    then show ?thesis by blast
  qed
qed

lemma maximal_independent_subset:
  "\<exists>B. B\<subseteq> V \<and> independent B \<and> V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}"]
    empty_subsetI independent_empty)
end

context vector_space
begin  
definition "dim V = (SOME n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> card B = n)"
end

context finite_dimensional_vector_space
begin
lemma basis_exists:
  "\<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = dim V)"
  unfolding dim_def some_eq_ex[of "\<lambda>n. \<exists>B. B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> (card B = n)"]
  using maximal_independent_subset[of V] independent_bound
  by auto
  
  lemma independent_card_le_dim:
  assumes "B \<subseteq> V"
    and "independent B"
  shows "card B \<le> dim V"
proof -
  from basis_exists[of V] `B \<subseteq> V`
  obtain B' where "independent B'"
    and "B \<subseteq> span B'"
    and "card B' = dim V"
    by blast
  with independent_span_bound[OF _ `independent B` `B \<subseteq> span B'`] independent_bound[of B']
  show ?thesis by auto
qed

lemma span_card_ge_dim:
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (metis basis_exists[of V] independent_span_bound subset_trans)

lemma basis_card_eq_dim:
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> finite B \<and> card B = dim V"
  by (metis order_eq_iff independent_card_le_dim span_card_ge_dim independent_bound)

lemma dim_unique:
  shows "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)
  
lemma dim_UNIV:
  shows "dim UNIV = card (Basis)"
  by (metis basis_card_eq_dim independent_Basis span_Basis top_greatest)

lemma dim_subset:
  shows "S \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using basis_exists[of T] basis_exists[of S]
  by (metis independent_card_le_dim subset_trans)  

(*This lemma doesn't appear in the library, but it's useful in my development*)  
lemma dim_univ_eq_dimension:
  shows "dim UNIV = dimension"
  by (metis basis_card_eq_dim dimension_def independent_Basis span_Basis top_greatest)

lemma dim_subset_UNIV:
  shows "dim S \<le> dimension"
  by (metis dimension_def dim_subset subset_UNIV dim_UNIV)

lemma card_ge_dim_independent:
  assumes BV: "B \<subseteq> V"
    and iB: "independent B"
    and dVB: "dim V \<le> card B"
  shows "V \<subseteq> span B"
proof
  fix a
  assume aV: "a \<in> V"
  {
    assume aB: "a \<notin> span B"
    then have iaB: "independent (insert a B)"
      using iB aV BV by (simp add: independent_insert)
    from aV BV have th0: "insert a B \<subseteq> V"
      by blast
    from aB have "a \<notin>B"
      by (auto simp add: span_superset)
    with independent_card_le_dim[OF th0 iaB] dVB independent_bound[OF iB]
    have False by auto
  }
  then show "a \<in> span B" by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "B \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  {
    fix a
    assume a: "a \<in> B" "a \<in> span (B - {a})"
    from a fB have c0: "card B \<noteq> 0"
      by auto
    from a fB have cb: "card (B - {a}) = card B - 1"
      by auto
    from BV a have th0: "B - {a} \<subseteq> V"
      by blast
    {
      fix x
      assume x: "x \<in> V"
      from a have eq: "insert a (B - {a}) = B"
        by blast
      from x VB have x': "x \<in> span B"
        by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B - {a})" .
    }
    then have th1: "V \<subseteq> span (B - {a})"
      by blast
    have th2: "finite (B - {a})"
      using fB by auto
    from span_card_ge_dim[OF th0 th1 th2]
    have c: "dim V \<le> card (B - {a})" .
    from c c0 dVB cb have False by simp
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

lemma card_eq_dim:
  shows "B \<subseteq> V \<Longrightarrow> card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning card_ge_dim_independent)
  
lemma independent_bound_general:
  shows "independent S ==> finite S \<and> card S \<le> dim S"
  by (metis independent_card_le_dim independent_bound subset_refl)

lemma dim_span:
  shows "dim (span S) = dim S"
proof -
  have th0: "dim S \<le> dim (span S)"
    by (auto simp add: subset_eq intro: dim_subset span_superset)
  from basis_exists[of S]
  obtain B where B: "B \<subseteq> S" "independent B" "S \<subseteq> span B" "card B = dim S"
    by blast
  from B have fB: "finite B" "card B = dim S"
    using independent_bound by blast+
  have bSS: "B \<subseteq> span S"
    using B(1) by (metis subset_eq span_inc)
  have sssB: "span S \<subseteq> span B"
    using span_mono[OF B(3)] by (simp add: span_span)
  from span_card_ge_dim[OF bSS sssB fB(1)] th0 show ?thesis
    using fB(2) by arith
qed

lemma subset_le_dim:
  shows "S \<subseteq> span T ==> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma span_eq_dim:
  shows "span S = span T ==> dim S = dim T"
  by (metis dim_span)
end

context linear
begin

lemma independent_injective_image:
  assumes iS: "B.independent S"
    and fi: "inj f"
  shows "C.independent (f ` S)"
proof -
  have l: "linear scaleB scaleC f" by unfold_locales
  {
    fix a
    assume a: "a \<in> S" "f a \<in> C.span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})"
      using fi by (auto simp add: inj_on_def)
    from a have "f a \<in> f ` B.span (S - {a})"
      unfolding eq B.span_linear_image[OF l, of "S - {a}"] by blast
    then have "a \<in> B.span (S - {a})"
      using fi by (auto simp add: inj_on_def)
    with a(1) iS have False
      by (simp add: B.dependent_def)
  }
  then show ?thesis
    unfolding dependent_def by blast
qed
end


(*This is a new locale to make easier some proofs.*)
locale two_vector_spaces_over_same_field = B?: vector_space scaleB + C?: vector_space scaleC
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75)
  
context two_vector_spaces_over_same_field
begin

lemma linear_indep_image_lemma:
  assumes lf: "linear (op *b) (op *c) f"
    and fB: "finite B"
    and ifB: "C.independent (f ` B)"
    and fi: "inj_on f B"
    and xsB: "x \<in> B.span B"
    and fx: "f x = 0"
  shows "x = 0"
  using fB ifB fi xsB fx
proof (induct arbitrary: x rule: finite_induct[OF fB])
  case 1
  then show ?case by auto
next
  case (2 a b x)
  have fb: "finite b" using "2.prems" by simp
  have th0: "f ` b \<subseteq> f ` (insert a b)"
    apply (rule image_mono)
    apply blast
    done
  from independent_mono[ OF "2.prems"(2) th0]
  have ifb: "independent (f ` b)"  .
  have fib: "inj_on f b"
    apply (rule subset_inj_on [OF "2.prems"(3)])
    apply blast
    done
  from B.span_breakdown[of a "insert a b", simplified, OF "2.prems"(4)]
  obtain k where k: "x - k *b a \<in> B.span (b - {a})"
    by blast
  have "f (x - k *b a) \<in> C.span (f ` b)"
    unfolding B.span_linear_image[OF lf]
    apply (rule imageI)
    using k B.span_mono[of "b - {a}" b]
    apply blast
    done
  then have "f x - k *c f a \<in> C.span (f ` b)"
    by (metis (full_types) lf linear.linear_cmul linear.linear_sub)
  then have th: "-k *c f a \<in> C.span (f ` b)"
    using "2.prems"(5) by simp
  have xsb: "x \<in> B.span b"
  proof (cases "k = 0")
    case True
    with k have "x \<in> B.span (b - {a})" by simp
    then show ?thesis using B.span_mono[of "b - {a}" b]
      by blast
  next
    case False
    with span_mul[OF th, of "- 1/ k"]
    have th1: "f a \<in> span (f ` b)"
      by auto
    from inj_on_image_set_diff[OF "2.prems"(3), of "insert a b " "{a}", symmetric]
    have tha: "f ` insert a b - f ` {a} = f ` (insert a b - {a})" by blast
    from "2.prems"(2) [unfolded dependent_def bex_simps(8), rule_format, of "f a"]
    have "f a \<notin> span (f ` b)" using tha
      using "2.hyps"(2)
      "2.prems"(3) by auto
    with th1 have False by blast
    then show ?thesis by blast
  qed
  from "2.hyps"(3)[OF fb ifb fib xsb "2.prems"(5)] show "x = 0" .
qed

lemma linear_independent_extend_lemma:
  fixes f :: "'b \<Rightarrow> 'c"
  assumes fi: "finite B"
    and ib: "B.independent B"
  shows "\<exists>g.
    (\<forall>x\<in> B.span B. \<forall>y\<in> B.span B. g (x + y) = g x + g y) \<and>
    (\<forall>x\<in> B.span B. \<forall>c. g (c *b x) = c *c (g x)) \<and>
    (\<forall>x\<in> B. g x = f x)"
  using ib fi
proof (induct rule: finite_induct[OF fi])
  case 1
  then show ?case by auto
next
  case (2 a b)
  from "2.prems" "2.hyps" have ibf: "B.independent b" "finite b"
    by (simp_all add: B.independent_insert)
  from "2.hyps"(3)[OF ibf] obtain g where
    g: "\<forall>x\<in>B.span b. \<forall>y\<in>B.span b. g (x + y) = g x + g y"
    "\<forall>x\<in>B.span b. \<forall>c. g (c *b x) = c *c g x" "\<forall>x\<in>b. g x = f x" by blast
  let ?h = "\<lambda>z. SOME k. (z - k *b a) \<in> B.span b"
  {
    fix z
    assume z: "z \<in> B.span (insert a b)"
    have th0: "z - ?h z *b a \<in> B.span b"
      apply (rule someI_ex)
      unfolding B.span_breakdown_eq[symmetric]
      apply (rule z)
      done
    {
      fix k
      assume k: "z - k *b a \<in> B.span b"
      have eq: "z - ?h z *b a - (z - k *b a) = (k - ?h z) *b a"
        by (simp add: field_simps B.scale_left_distrib [symmetric])
      from B.span_sub[OF th0 k] have khz: "(k - ?h z) *b a \<in> B.span b"
        by (simp add: eq)
      {
        assume "k \<noteq> ?h z"
        then have k0: "k - ?h z \<noteq> 0" by simp
        from k0 B.span_mul[OF khz, of "1 /(k - ?h z)"]
        have "a \<in> B.span b" by simp
        with "2.prems"(1) "2.hyps"(2) have False
          by (auto simp add: B.dependent_def)
      }
      then have "k = ?h z" by blast
    }
    with th0 have "z - ?h z *b a \<in> B.span b \<and> (\<forall>k. z - k *b a \<in> B.span b \<longrightarrow> k = ?h z)"
      by blast
  }
  note h = this
  let ?g = "\<lambda>z. (?h z) *c (f a) + g (z - (?h z) *b a)"
  {
    fix x y
    assume x: "x \<in> B.span (insert a b)"
      and y: "y \<in> B.span (insert a b)"
    have tha: "\<And>(x::'b) y a k l. (x + y) - (k + l) *b a = (x - k *b a) + (y - l *b a)"
      by (simp add: algebra_simps)
    have addh: "?h (x + y) = ?h x + ?h y"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (rule B.span_add[OF x y])
      unfolding tha
      apply (metis B.span_add x y conjunct1[OF h, rule_format])
      done
    have "?g (x + y) = ?g x + ?g y"
      unfolding addh tha
      g(1)[rule_format,OF conjunct1[OF h, OF x] conjunct1[OF h, OF y]]
      by (simp add: C.scale_left_distrib)}
  moreover
  {
    fix x :: "'b"
    fix c :: 'a
    assume x: "x \<in> B.span (insert a b)"
    have tha: "\<And>(x::'b) c k a. c *b x - (c * k) *b a = c *b (x - k *b a)"
      by (simp add: algebra_simps)
    have hc: "?h (c *b x) = c * ?h x"
      apply (rule conjunct2[OF h, rule_format, symmetric])
      apply (metis B.span_mul x)
      apply (metis tha B.span_mul x conjunct1[OF h])
      done
    have "?g (c *b x) = c *c ?g x"
      unfolding hc tha g(2)[rule_format, OF conjunct1[OF h, OF x]]
      by (simp add: algebra_simps)
  }
  moreover
  {
    fix x
    assume x: "x \<in> insert a b"
    {
      assume xa: "x = a"
      have ha1: "1 = ?h a"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis B.span_superset insertI1)
        using conjunct1[OF h, OF B.span_superset, OF insertI1]
        apply (auto simp add: B.span_0)
        done
      from xa ha1[symmetric] have "?g x = f x"
        apply simp
        using g(2)[rule_format, OF B.span_0, of 0]
        apply simp
        done
    }
    moreover
    {
      assume xb: "x \<in> b"
      have h0: "0 = ?h x"
        apply (rule conjunct2[OF h, rule_format])
        apply (metis B.span_superset x)
        apply simp
        apply (metis B.span_superset xb)
        done
      have "?g x = f x"
        by (simp add: h0[symmetric] g(3)[rule_format, OF xb])
    }
    ultimately have "?g x = f x"
      using x by blast
  }
  ultimately show ?case
    apply -
    apply (rule exI[where x="?g"])
    apply blast
    done
qed
end

(*This is a new locale, similar to the previous one, to make easier some proofs.*)
locale two_finite_dimensional_vector_spaces_over_same_field = B?: finite_dimensional_vector_space scaleB BasisB + 
  C?: finite_dimensional_vector_space scaleC BasisC
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75)
  and BasisB :: "('b set)"
  and BasisC :: "('c set)"

context two_finite_dimensional_vector_spaces_over_same_field
begin

sublocale two_vector_spaces?: two_vector_spaces_over_same_field by unfold_locales

lemma linear_independent_extend:
  assumes iB: "B.independent B"
  shows "\<exists>g. linear (op *b) (op *c) g \<and> (\<forall>x\<in>B. g x = f x)"
proof -
  have 1: "vector_space (op *b)" and 2: "vector_space (op *c)" by unfold_locales
  from B.maximal_independent_subset_extend[of B UNIV] iB
  obtain C where C: "B \<subseteq> C" "B.independent C" "\<And>x. x \<in> B.span C"
    by auto
  from C(2) B.independent_bound[of C] two_vector_spaces.linear_independent_extend_lemma[of C]
  obtain g where g:
    "(\<forall>x\<in> B.span C. \<forall>y\<in> B.span C. g (x + y) = g x + g y) \<and>
     (\<forall>x\<in> B.span C. \<forall>c. g (c *b x) = c *c g x) \<and>
     (\<forall>x\<in> C. g x = f x)" by blast
  from g show ?thesis
    unfolding linear_iff
    using C 1 2
    apply clarsimp
    apply blast
    done
qed
end

context vector_space
begin
  
lemma spans_image:
  assumes lf: "linear scale scaleC (f::'b=>'c::ab_group_add)"
  and VB: "V \<subseteq> span B"
  shows "f ` V \<subseteq> vector_space.span scaleC (f ` B)"
  unfolding span_linear_image[OF lf] by (metis VB image_mono) 

lemma subspace_kernel:
  assumes lf: "linear scale scaleC f"
  shows "subspace {x. f x = 0}"
  proof (unfold subspace_def, auto)
  interpret lf: linear scale scaleC f using lf by simp
  show "f 0 = 0" using lf.linear_0 .
  fix x y assume fx: "f x = 0" and fy: "f y = 0"
  show "f (x + y) = 0" unfolding lf.linear_add fx fy by simp
  fix c::'a show "f (scale c x) = 0" unfolding fx lf.linear_cmul lf.scale_zero_right ..
qed

lemma linear_eq_0_span:
  assumes lf: "linear scale scaleC f" and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> span B. f x = 0"
  using f0 subspace_kernel[OF lf]
  by (rule span_induct')

lemma linear_eq_0:
  assumes lf: "linear scale scaleB f"
    and SB: "S \<subseteq> span B"
    and f0: "\<forall>x\<in>B. f x = 0"
  shows "\<forall>x \<in> S. f x = 0"
  by (metis linear_eq_0_span[OF lf] subset_eq SB f0)

lemma linear_eq:
  assumes lf: "linear scale scaleC f"
    and lg: "linear scale scaleC g"
    and S: "S \<subseteq> span  B"
    and fg: "\<forall> x\<in> B. f x = g x"
  shows "\<forall>x\<in> S. f x = g x"
proof -
  let ?h = "\<lambda>x. f x - g x"
  from fg have fg': "\<forall>x\<in> B. ?h x = 0" by simp
  from linear_eq_0[OF linear_compose_sub[OF lf lg] S fg']
  show ?thesis by simp
qed
end

(*A new locale to make easier some proofs.*)

locale linear_between_finite_dimensional_vector_spaces =
  l?: linear scaleB scaleC f +
  B?: finite_dimensional_vector_space scaleB BasisB + 
  C?: finite_dimensional_vector_space scaleC BasisC
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75) 
  and BasisB :: "('b set)"
  and BasisC :: "('c set)"
  and f :: "('b=>'c)"
  
context linear_between_finite_dimensional_vector_spaces
begin

lemma linear_eq_stdbasis:
  assumes lg: "linear (op *b) (op *c) g"
  and fg: "\<forall>b\<in>BasisB. f b = g b"
  shows "f = g" 
proof -
  have l: "linear (op *b) (op *c) f" by unfold_locales
  show ?thesis 
  using B.linear_eq[OF l lg, of UNIV BasisB] fg using B.span_Basis by auto
qed
  
lemma linear_injective_left_inverse:
  assumes fi: "inj f"
  shows "\<exists>g. linear (op *c) (op *b) g \<and> g o f = id"
proof -
  interpret fd: two_finite_dimensional_vector_spaces_over_same_field "(op *c)" "(op *b)" BasisC BasisB
    by unfold_locales  
 have lf: "linear op *b op *c f" by unfold_locales
  from fd.linear_independent_extend[OF independent_injective_image, OF B.independent_Basis, OF fi]
  obtain h:: "'c \<Rightarrow> 'b" where h: "linear (op *c) (op *b) h" "\<forall>x \<in> f ` BasisB. h x = inv f x"
    by blast
  from h(2) have th: "\<forall>i\<in>BasisB. (h \<circ> f) i = id i"
    using inv_o_cancel[OF fi, unfolded fun_eq_iff id_def o_def]
    by auto
  interpret l_hg: linear_between_finite_dimensional_vector_spaces "op *b" "op *b" BasisB BasisB "(h \<circ> f)" 
  apply (unfold_locales) using linear_compose[OF lf h(1)] unfolding linear_iff by fast+
  show ?thesis
    using h(1)  l_hg.linear_eq_stdbasis[OF B.linear_id th] by blast
qed

sublocale two_finite_dimensional_vector_spaces?: two_finite_dimensional_vector_spaces_over_same_field 
by unfold_locales

lemma linear_surjective_right_inverse:
  assumes sf: "surj f"
  shows "\<exists>g. linear (op *c) (op *b) g \<and> f o g = id"
proof -
  interpret lh: two_finite_dimensional_vector_spaces_over_same_field "op *c" "op *b" BasisC BasisB 
    by unfold_locales
  have lf: "linear (op *b) (op *c) f" by unfold_locales
  from lh.linear_independent_extend[OF independent_Basis]
  obtain h:: "'c \<Rightarrow> 'b" where h: "linear (op *c) (op *b) h" "\<forall>x\<in>BasisC. h x = inv f x"
    by blast
  interpret l_fg: linear_between_finite_dimensional_vector_spaces  "op *c" "op *c" BasisC BasisC "(f \<circ> h)"
     using linear_compose[OF h(1) lf] by (unfold_locales, auto simp add: linear_def linear_axioms_def)
  from h(2) have th: "\<forall>i\<in>BasisC. (f o h) i = id i"
    using sf by (metis comp_apply surj_iff)
  from l_fg.linear_eq_stdbasis[OF linear_id th]
  have "f o h = id" .
  then show ?thesis
    using h(1) by blast
qed

end


context finite_dimensional_vector_space
begin

lemma linear_injective_imp_surjective:
  assumes lf: "linear scale scale f"
    and fi: "inj f"
  shows "surj f"
proof -
  interpret lf: linear scale scale f using lf by auto
  let ?U = "UNIV :: 'b set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" "card B = dim ?U"
    by blast
  from B(4) have d: "dim ?U = card B"
    by simp
  have th: "?U \<subseteq> span (f ` B)"
    apply (rule card_ge_dim_independent)
    apply blast
    apply (rule lf.independent_injective_image[OF B(2) fi])
    apply (rule order_eq_refl)
    apply (rule sym)
    unfolding d
    apply (rule card_image)
    apply (rule subset_inj_on[OF fi])
    apply blast
    done
  from th show ?thesis
    unfolding span_linear_image[OF lf] surj_def
    using B(3) by auto 
qed


lemma linear_surjective_imp_injective:
  assumes lf: "linear scale scale f"
    and sf: "surj f"
  shows "inj f"
proof -
  interpret t: two_vector_spaces_over_same_field scale scale by unfold_locales
  let ?U = "UNIV :: 'b set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" and d: "card B = dim ?U"
    by blast
  {
    fix x
    assume x: "x \<in> span B"
    assume fx: "f x = 0"
    from B(2) have fB: "finite B"
      using independent_bound by auto
    have fBi: "independent (f ` B)"
      apply (rule card_le_dim_spanning[of "f ` B" ?U])
      apply blast
      using sf B(3)
      unfolding span_linear_image[OF lf] surj_def subset_eq image_iff
      apply blast
      using fB apply blast
      unfolding d[symmetric]
      apply (rule card_image_le)
      apply (rule fB)
      done
    have th0: "dim ?U \<le> card (f ` B)"
      apply (rule span_card_ge_dim)
      apply blast
      unfolding span_linear_image[OF lf]
      apply (rule subset_trans[where B = "f ` UNIV"])
      using sf unfolding surj_def
      apply blast
      apply (rule image_mono)
      apply (rule B(3))
      apply (metis finite_imageI fB)
      done
    moreover have "card (f ` B) \<le> card B"
      by (rule card_image_le, rule fB)
    ultimately have th1: "card B = card (f ` B)"
      unfolding d by arith
    have fiB: "inj_on f B"
      unfolding surjective_iff_injective_gen[OF fB finite_imageI[OF fB] th1 subset_refl, symmetric]
      by blast
    from t.linear_indep_image_lemma[OF lf fB fBi fiB x] fx
    have "x = 0" by blast
  }
  then show ?thesis
    unfolding linear.linear_injective_0[OF lf]
    using B(3)
    by blast
qed


lemma linear_injective_isomorphism:
  assumes lf: "linear scale scale f"
    and fi: "inj f"
  shows "\<exists>f'. linear scale scale f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
proof -
  interpret lbfdvs: linear_between_finite_dimensional_vector_spaces scale scale Basis Basis f
    by (unfold_locales, simp add: lf linear.linear_cmul linear.linear_add, metis lf linear.linear_add)
  show ?thesis
  unfolding isomorphism_expand[symmetric]
  using lbfdvs.linear_surjective_right_inverse
  using linear_injective_imp_surjective 
  by (metis comp_assoc comp_id fi lbfdvs.linear_injective_left_inverse lf)
qed


lemma linear_surjective_isomorphism:
  assumes lf: "linear scale scale f"
    and sf: "surj f"
  shows "\<exists>f'. linear scale scale f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  proof -
  interpret lbfdvs: linear_between_finite_dimensional_vector_spaces scale scale Basis Basis f
    apply (unfold_locales) apply (simp add:  lf linear.linear_cmul linear.linear_add)
    by (metis lf linear.linear_add)
  show ?thesis  
  unfolding isomorphism_expand[symmetric]
    using lbfdvs.linear_surjective_right_inverse[OF sf]
   using lbfdvs.linear_injective_left_inverse[OF linear_surjective_imp_injective[OF lf sf]]
  by (metis left_right_inverse_eq)
qed


lemma left_inverse_linear:
  assumes lf: "linear scale scale f"
    and gf: "g \<circ> f = id"
  shows "linear scale scale g"
proof -
  from gf have fi: "inj f"
    by (metis inj_on_id inj_on_imageI2)
  from linear_injective_isomorphism[OF lf fi]
  obtain h :: "'b \<Rightarrow> 'b" where h: "linear scale scale h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x"
    by blast
  have "h = g"
    apply (rule ext) using gf h(2,3)
    by (metis comp_apply id_apply)
  with h(1) show ?thesis by blast
qed
end

(********************** Here ends the generalization of Linear_Algebra.thy **********************)

(*Some interpretations:*)
interpretation vec: finite_dimensional_vector_space "op *s" "(cart_basis)"
  by (unfold_locales, auto simp add: finite_cart_basis independent_cart_basis span_cart_basis) 
  
lemma matrix_vector_mul_linear_between_finite_dimensional_vector_spaces: 
  "linear_between_finite_dimensional_vector_spaces (op *s) (op *s) 
    (cart_basis) (cart_basis) (\<lambda>x. A *v (x::'a::{field} ^ _))"
  by (unfold_locales) 
    (auto simp add: linear_iff2 matrix_vector_mult_def vec_eq_iff
      field_simps setsum_right_distrib setsum.distrib)

interpretation euclidean_space: 
  finite_dimensional_vector_space "scaleR :: real => 'a => 'a::{euclidean_space}" "Basis"
proof
  have v: "vector_space (scaleR :: real => 'a => 'a::{euclidean_space})" by (unfold_locales)
  show "finite (Basis::'a set)" by (metis finite_Basis)
  show "vector_space.independent op *\<^sub>R (Basis::'a set)"
    unfolding vector_space.dependent_def[OF v]
    apply (subst vector_space.span_finite[OF v])
    apply simp
    apply clarify
    apply (drule_tac f="inner a" in arg_cong)
    apply (simp add: inner_Basis inner_setsum_right eq_commute)
    done
  show "vector_space.span op *\<^sub>R (Basis::'a set) = UNIV"
    unfolding vector_space.span_finite [OF v finite_Basis]
    by (fast intro: euclidean_representation)
qed

(****************** Generalized parts of the file Cartesian_Euclidean_Space.thy ******************)

lemma vector_mul_lcancel[simp]: "a *s x = a *s y \<longleftrightarrow> a = (0::'a::{field}) \<or> x = y"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_ssub_ldistrib)
  
lemma vector_mul_lcancel_imp: "a \<noteq> (0::'a::{field}) ==>  a *s x = a *s y ==> (x = y)"
  by (metis vector_mul_lcancel)
  
lemma linear_componentwise:
  fixes f:: "'a::field ^'m \<Rightarrow> 'a ^ 'n"
  assumes lf: "linear (op *s) (op *s) f"
  shows "(f x)$j = setsum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  interpret lf: linear "(op *s)" "(op *s)" f
    using lf .   
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (setsum (\<lambda>i. (x$i) *s (f (axis i 1))) ?M)$j"
    unfolding setsum_component by simp
  then show ?thesis
    unfolding lf.linear_setsum_mul[OF fM, symmetric]
    unfolding basis_expansion by auto
qed


lemma matrix_vector_mul_linear: "linear (op *s) (op *s) (\<lambda>x. A *v (x::'a::{field} ^ _))"
  by (simp add: linear_iff2 matrix_vector_mult_def vec_eq_iff
      field_simps setsum_right_distrib setsum.distrib)
  
(*Two new interpretations*)
interpretation vec: linear "op *s" "op *s" "(\<lambda>x. A *v (x::'a::{field} ^ _))" 
  using matrix_vector_mul_linear .
  
interpretation vec: linear_between_finite_dimensional_vector_spaces "op *s" "op *s" 
  "(cart_basis)" "(cart_basis)" "(op *v A)"
  by unfold_locales
  
lemma matrix_works:
  assumes lf: "linear (op *s) (op *s) f"
  shows "matrix f *v x = f (x::'a::field ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  apply clarify
  apply (rule linear_componentwise[OF lf, symmetric])
  done
      
lemma matrix_vector_mul: "linear (op *s) (op *s) f ==> f = (\<lambda>x. matrix f *v (x::'a::{field}^ 'n))"
  by (simp add: ext matrix_works)
  
lemma matrix_of_matrix_vector_mul: "matrix(\<lambda>x. A *v (x :: 'a::{field} ^ 'n)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)
  
lemma matrix_compose:
  assumes lf: "linear (op *s) (op *s) (f::'a::{field}^'n \<Rightarrow> 'a^'m)"
    and lg: "linear (op *s) (op *s) (g::'a^'m \<Rightarrow> 'a^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)
  
lemma matrix_left_invertible_injective:
  "(\<exists>B. (B::'a::{field}^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1) 
    \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
proof -
  { fix B:: "'a^'m^'n" and x y assume B: "B ** A = mat 1" and xy: "A *v x = A*v y"
    from xy have "B*v (A *v x) = B *v (A*v y)" by simp
    hence "x = y"
      unfolding matrix_vector_mul_assoc B matrix_vector_mul_lid . }
  moreover
  { assume A: "\<forall>x y. A *v x = A *v y \<longrightarrow> x = y"
    hence i: "inj (op *v A)" unfolding inj_on_def by auto
    from vec.linear_injective_left_inverse[OF i]
    obtain g where g: "linear (op *s)  (op *s) g" "g o op *v A = id" by blast
    have "matrix g ** A = mat 1"
      unfolding matrix_eq matrix_vector_mul_lid matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) by (metis comp_apply id_apply)
    then have "\<exists>B. (B::'a::{field}^'m^'n) ** A = mat 1" by blast }
  ultimately show ?thesis by blast
qed


lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::'a::{field} ^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using vec.linear_injective_0[of A]
  by (simp add: inj_on_def)
  
  lemma matrix_left_invertible_independent_columns:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a ^'m^'n). B ** A = mat 1) \<longleftrightarrow>
      (\<forall>c. setsum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  { assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    { fix c i
      assume c: "setsum (\<lambda>i. c i *s column i A) ?U = 0" and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        unfolding matrix_mult_vsum vec_eq_iff
        by auto
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
    hence ?rhs by blast }
  moreover
  { assume H: ?rhs
    { fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: 'a)"
      from H[rule_format, of ?c, unfolded matrix_mult_vsum[symmetric], OF x]
      have "x = 0" by vector }
  }
  ultimately show ?thesis unfolding matrix_left_invertible_ker by blast
qed

  
lemma matrix_right_invertible_independent_rows:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. setsum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add: column_transpose)


lemma matrix_left_right_inverse:
  fixes A A' :: "'a::{field}^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "'a ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj (op *v A)"
      unfolding surj_def
      apply clarify
      apply (rule_tac x="(A' *v y)" in exI)
      apply (simp add: matrix_vector_mul_assoc AA' matrix_vector_mul_lid)
      done
    from vec.linear_surjective_isomorphism[OF matrix_vector_mul_linear sA]
    obtain f' :: "'a ^'n \<Rightarrow> 'a ^'n"
      where f': "linear (op *s) (op *s) f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)]
          matrix_vector_mul_assoc[symmetric] matrix_vector_mul_lid f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'"
      by (simp add: matrix_mul_assoc[symmetric] AA' matrix_mul_rid matrix_mul_lid)
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)
  }
  then show ?thesis by blast
qed

(***************** Here ends the generalization of Cartesian_Euclidean_Space.thy *****************)

(****************** Generalized parts of the file Convex_Euclidean_Space.thy ******************)

context vector_space
begin

lemma linear_injective_on_subspace_0:
  assumes lf: "linear scale scale f"
    and "subspace S"
  shows "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
proof -
  have "inj_on f S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x = f y \<longrightarrow> x = y)"
    by (simp add: inj_on_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f x - f y = 0 \<longrightarrow> x - y = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. f (x - y) = 0 \<longrightarrow> x - y = 0)"
    by (simp add: linear.linear_sub[OF lf])
  also have "\<dots> \<longleftrightarrow> (\<forall>x \<in> S. f x = 0 \<longrightarrow> x = 0)"
    using `subspace S` subspace_def[of S] subspace_sub[of S] by auto
  finally show ?thesis .
qed

end

(*Maybe change de name*)
lemma setsum_constant_scaleR:
  shows "(\<Sum>x\<in>A. y) = of_nat (card A) *s y"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (simp_all add: algebra_simps)
  done

context finite_dimensional_vector_space
begin
  
lemma indep_card_eq_dim_span:
  assumes "independent B"
  shows "finite B \<and> card B = dim (span B)"
  using assms basis_card_eq_dim[of B "span B"] span_inc by auto
end

context linear
begin

lemma independent_injective_on_span_image:
  assumes iS: "B.independent S"
    and fi: "inj_on f (B.span S)"
  shows "C.independent (f ` S)"
proof -
  have l: "linear (op *b) (op *c) f"
    by unfold_locales
  {
    fix a
    assume a: "a \<in> S" "f a \<in> C.span (f ` S - {f a})"
    have eq: "f ` S - {f a} = f ` (S - {a})"
      using fi a B.span_inc by (auto simp add: inj_on_def)
    from a have "f a \<in> f ` B.span (S -{a})"
      unfolding eq using B.span_linear_image[OF l] by auto
    moreover have "B.span (S - {a}) \<subseteq> B.span S"
      using B.span_mono[of "S - {a}" S] by auto
    ultimately have "a \<in> B.span (S - {a})"
      using fi a B.span_inc by (auto simp add: inj_on_def)
    with a(1) iS have False
      by (simp add: B.dependent_def)
  }
  then show ?thesis
    unfolding dependent_def by blast
qed
end

context vector_space
begin
lemma subspace_Inter: "\<forall>s \<in> f. subspace s \<Longrightarrow> subspace (Inter f)"
  unfolding subspace_def by auto
  
lemma span_eq[simp]: "span s = s \<longleftrightarrow> subspace s"
  unfolding span_def by (rule hull_eq) (rule subspace_Inter)
end

context finite_dimensional_vector_space
begin  
lemma subspace_dim_equal:
  assumes "subspace S"
    and "subspace T"
    and "S \<subseteq> T"
    and "dim S \<ge> dim T"
  shows "S = T"
proof -
  obtain B where B: "B \<le> S" "independent B \<and> S \<subseteq> span B" "card B = dim S"
    using basis_exists[of S] by auto
  then have "span B \<subseteq> S"
    using span_mono[of B S] span_eq[of S] assms by metis
  then have "span B = S"
    using B by auto
  have "dim S = dim T"
    using assms dim_subset[of S T] by auto
  then have "T \<subseteq> span B"
    using card_eq_dim[of B T] B  assms 
    by (metis independent_bound_general subset_trans)
  then show ?thesis
    using assms `span B = S` by auto
qed
end
(***************** Here ends the generalization of Convex_Euclidean_Space.thy *****************)

(*********************** Generalized parts of the file Determinants.thy ***********************)

(*Here I generalize some lemmas, from the class linordered_idom to a comm_ring_1.
  Next proof follows the one presented in: http://hobbes.la.asu.edu/courses/site/442-f09/dets.pdf*)
lemma det_identical_columns:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes jk: "j \<noteq> k"
  and r: "column j A = column k A"
  shows "det A = 0"
proof -
let ?U="UNIV::'n set"
let ?t_jk="Fun.swap j k id"
let ?PU="{p. p permutes ?U}"
let ?S1="{p. p\<in>?PU \<and> evenperm p}"
let ?S2="{(?t_jk \<circ> p) |p. p \<in>?S1}"
let ?f="\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"
let ?g="\<lambda>p. ?t_jk \<circ> p"
have g_S1: "?S2 = ?g` ?S1" by auto
have inj_g: "inj_on ?g ?S1" 
  proof (unfold inj_on_def, auto)
      fix x y assume x: "x permutes ?U" and even_x: "evenperm x"
        and y: "y permutes ?U" and even_y: "evenperm y" and eq: "?t_jk \<circ> x = ?t_jk \<circ> y"
      show "x = y" by (metis (hide_lams, no_types) comp_assoc eq id_comp swap_id_idempotent)
  qed
have tjk_permutes: "?t_jk permutes ?U" unfolding permutes_def swap_id_eq by (auto,metis)
have tjk_eq: "\<forall>i l. A $ i $ ?t_jk l  =  A $ i $ l" 
  using r jk 
  unfolding column_def vec_eq_iff swap_id_eq by fastforce
have sign_tjk: "sign ?t_jk = -1" using sign_swap_id[of j k] jk by auto
  {fix x
   assume x: "x\<in> ?S1"
   have "sign (?t_jk \<circ> x) = sign (?t_jk) * sign x"
    by (metis (lifting) finite_class.finite_UNIV mem_Collect_eq 
        permutation_permutes permutation_swap_id sign_compose x)
   also have "... = - sign x" using sign_tjk by simp
   also have "... \<noteq> sign x" unfolding sign_def by simp
   finally have "sign (?t_jk \<circ> x) \<noteq> sign x" and "(?t_jk \<circ> x) \<in> ?S2"
   by (auto, metis (lifting, full_types) mem_Collect_eq x)
  }
hence disjoint: "?S1 \<inter> ?S2 = {}" by (auto, metis sign_def)
have PU_decomposition: "?PU = ?S1 \<union> ?S2" 
  proof (auto)
    fix x
    assume x: "x permutes ?U" and "\<forall>p. p permutes ?U \<longrightarrow> x = Fun.swap j k id \<circ> p \<longrightarrow> \<not> evenperm p"    
    from this obtain p where p: "p permutes UNIV" and x_eq: "x = Fun.swap j k id \<circ> p" 
      and odd_p: "\<not> evenperm p"
      by (metis (no_types) comp_assoc id_comp inv_swap_id permutes_compose 
          permutes_inv_o(1) tjk_permutes)
    thus "evenperm x"
      by (metis evenperm_comp evenperm_swap finite_class.finite_UNIV 
        jk permutation_permutes permutation_swap_id)
   next
   fix p assume p: "p permutes ?U"
   show "Fun.swap j k id \<circ> p permutes UNIV" by (metis p permutes_compose tjk_permutes)
qed
have "setsum ?f ?S2 = setsum ((\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)) 
  \<circ> op \<circ> (Fun.swap j k id)) {p \<in> {p. p permutes UNIV}. evenperm p}"
    unfolding g_S1 by (rule setsum.reindex[OF inj_g])
also have "... = setsum (\<lambda>p. of_int (sign (?t_jk \<circ> p)) * (\<Prod>i\<in>UNIV. A $ i $ p i)) ?S1"
  unfolding o_def by (rule setsum.cong, auto simp add: tjk_eq)
also have "... = setsum (\<lambda>p. - ?f p) ?S1"
  proof (rule setsum.cong, auto)
     fix x assume x: "x permutes ?U"
     and even_x: "evenperm x"
     hence perm_x: "permutation x" and perm_tjk: "permutation ?t_jk" 
      using permutation_permutes[of x] permutation_permutes[of ?t_jk] permutation_swap_id
      by (metis finite_code)+
     have "(sign (?t_jk \<circ> x)) = - (sign x)" 
      unfolding sign_compose[OF perm_tjk perm_x] sign_tjk by auto
     thus "of_int (sign (?t_jk \<circ> x)) * (\<Prod>i\<in>UNIV. A $ i $ x i) 
      = - (of_int (sign x) * (\<Prod>i\<in>UNIV. A $ i $ x i))"
      by auto
  qed
also have "...= - setsum ?f ?S1" unfolding setsum_negf ..
finally have *: "setsum ?f ?S2 = - setsum ?f ?S1" .
have "det A = (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))" 
  unfolding det_def ..
also have "...= setsum ?f ?S1 + setsum ?f ?S2"
  by (subst PU_decomposition, rule setsum.union_disjoint[OF _ _ disjoint], auto)
also have "...= setsum ?f ?S1 - setsum ?f ?S1 " unfolding * by auto
also have "...= 0" by simp
finally show "det A = 0" by simp
qed


lemma det_identical_rows:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes ij: "i \<noteq> j"
  and r: "row i A = row j A"
  shows "det A = 0"
  apply (subst det_transpose[symmetric])
  apply (rule det_identical_columns[OF ij])
  apply (metis column_transpose r)
  done
  
(*The following two lemmas appear in the library with the restriction:

  lemma det_zero_row:
  fixes A :: "'a::{idom, ring_char_0}^'n^'n"
  assumes r: "row i A = 0"
  shows "det A = 0"

Now I will do the proof over a field in general. But that is not a generalization, since integers
are not a field, although they satisfy {idom, ring_char_0}. Nevertheless, in my case I'll work with
Z/Z2 (the field of integers modulo 2), which are a field but not a {idom, ring_char_0}.*)  
  
lemma det_zero_row:
  fixes A :: "'a::{field}^'n^'n"
  assumes r: "row i A = 0"
  shows "det A = 0"
  using r
  apply (simp add: row_def det_def vec_eq_iff)
  apply (rule setsum.neutral)
  apply (auto)
  done
  
  
lemma det_zero_column:
  fixes A :: "'a::{field}^'n^'n"
  assumes r: "column i A = 0"
  shows "det A = 0"
  apply (subst det_transpose[symmetric])
  apply (rule det_zero_row [of i])
  apply (metis row_transpose r)
  done
  
lemma det_row_operation:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes ij: "i \<noteq> j"
  shows "det (\<chi> k. if k = i then row i A + c *s row j A else row k A) = det A"
proof -
  let ?Z = "(\<chi> k. if k = i then row j A else row k A) :: 'a ^'n^'n"
  have th: "row i ?Z = row j ?Z" by (vector row_def)
  have th2: "((\<chi> k. if k = i then row i A else row k A) :: 'a^'n^'n) = A"
    by (vector row_def)
  show ?thesis
    unfolding det_row_add [of i] det_row_mul[of i] det_identical_rows[OF ij th] th2
    by simp
qed  

lemma det_row_span:
  fixes A :: "'a::{field}^'n^'n"
  assumes x: "x \<in> vec.span {row j A |j. j \<noteq> i}"
  shows "det (\<chi> k. if k = i then row i A + x else row k A) = det A"
proof -
  let ?U = "UNIV :: 'n set"
  let ?S = "{row j A |j. j \<noteq> i}"
  let ?d = "\<lambda>x. det (\<chi> k. if k = i then x else row k A)"
  let ?P = "\<lambda>x. ?d (row i A + x) = det A"
  {
    fix k
    have "(if k = i then row i A + 0 else row k A) = row k A"
      by simp
  }
  then have P0: "?P 0"
    apply -
    apply (rule cong[of det, OF refl])
    apply (vector row_def)
    done
  moreover
  {
    fix c z y
    assume zS: "z \<in> ?S" and Py: "?P y"
    from zS obtain j where j: "z = row j A" "i \<noteq> j"
      by blast
    let ?w = "row i A + y"
    have th0: "row i A + (c*s z + y) = ?w + c*s z"
      by vector
    have thz: "?d z = 0"
      apply (rule det_identical_rows[OF j(2)])
      using j
      apply (vector row_def)
      done
    have "?d (row i A + (c*s z + y)) = ?d (?w + c*s z)"
      unfolding th0 ..
    then have "?P (c*s z + y)"
      unfolding thz Py det_row_mul[of i] det_row_add[of i]
      by simp
  }
  ultimately show ?thesis
    apply -
    apply (rule vec.span_induct_alt[of ?P ?S, OF P0, folded scalar_mult_eq_scaleR])
    apply blast
    apply (rule x)
    done
qed

lemma det_dependent_rows:
  fixes A:: "'a::{field}^'n^'n"
  assumes d: "vec.dependent (rows A)"
  shows "det A = 0"
proof -
  let ?U = "UNIV :: 'n set"
  from d obtain i where i: "row i A \<in> vec.span (rows A - {row i A})"
    unfolding vec.dependent_def rows_def by blast
  {
    fix j k
    assume jk: "j \<noteq> k" and c: "row j A = row k A"
    from det_identical_rows[OF jk c] have ?thesis .
  }
  moreover
  {
    assume H: "\<And> i j. i \<noteq> j \<Longrightarrow> row i A \<noteq> row j A"
    have th0: "- row i A \<in> vec.span {row j A|j. j \<noteq> i}"
      apply (rule vec.span_neg)
      apply (rule set_rev_mp)
      apply (rule i)
      apply (rule vec.span_mono)
      using H i
      apply (auto simp add: rows_def)
      done
    from det_row_span[OF th0]
    have "det A = det (\<chi> k. if k = i then 0 *s 1 else row k A)"
      unfolding right_minus vector_smult_lzero ..
    with det_row_mul[of i "0::'a" "\<lambda>i. 1"]
    have "det A = 0" by simp
  }
  ultimately show ?thesis by blast
qed

lemma det_mul:
  fixes A B :: "'a::{comm_ring_1}^'n^'n"
  shows "det (A ** B) = det A * det B"
proof -
  let ?U = "UNIV :: 'n set"
  let ?F = "{f. (\<forall>i\<in> ?U. f i \<in> ?U) \<and> (\<forall>i. i \<notin> ?U \<longrightarrow> f i = i)}"
  let ?PU = "{p. p permutes ?U}"
  have fU: "finite ?U"
    by simp
  have fF: "finite ?F"
    by (rule finite)
  {
    fix p
    assume p: "p permutes ?U"
    have "p \<in> ?F" unfolding mem_Collect_eq permutes_in_image[OF p]
      using p[unfolded permutes_def] by simp
  }
  then have PUF: "?PU \<subseteq> ?F" by blast
  {
    fix f
    assume fPU: "f \<in> ?F - ?PU"
    have fUU: "f ` ?U \<subseteq> ?U"
      using fPU by auto
    from fPU have f: "\<forall>i \<in> ?U. f i \<in> ?U" "\<forall>i. i \<notin> ?U \<longrightarrow> f i = i" "\<not>(\<forall>y. \<exists>!x. f x = y)"
      unfolding permutes_def by auto

    let ?A = "(\<chi> i. A$i$f i *s B$f i) :: 'a^'n^'n"
    let ?B = "(\<chi> i. B$f i) :: 'a^'n^'n"
    {
      assume fni: "\<not> inj_on f ?U"
      then obtain i j where ij: "f i = f j" "i \<noteq> j"
        unfolding inj_on_def by blast
      from ij
      have rth: "row i ?B = row j ?B"
        by (vector row_def)
      from det_identical_rows[OF ij(2) rth]
      have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        unfolding det_rows_mul by simp
    }
    moreover
    {
      assume fi: "inj_on f ?U"
      from f fi have fith: "\<And>i j. f i = f j \<Longrightarrow> i = j"
        unfolding inj_on_def by metis
      note fs = fi[unfolded surjective_iff_injective_gen[OF fU fU refl fUU, symmetric]]
      {
        fix y
        from fs f have "\<exists>x. f x = y"
          by blast
        then obtain x where x: "f x = y"
          by blast
        {
          fix z
          assume z: "f z = y"
          from fith x z have "z = x"
            by metis
        }
        with x have "\<exists>!x. f x = y"
          by blast
      }
      with f(3) have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        by blast
    }
    ultimately have "det (\<chi> i. A$i$f i *s B$f i) = 0"
      by blast
  }
  then have zth: "\<forall> f\<in> ?F - ?PU. det (\<chi> i. A$i$f i *s B$f i) = 0"
    by simp
  {
    fix p
    assume pU: "p \<in> ?PU"
    from pU have p: "p permutes ?U"
      by blast
    let ?s = "\<lambda>p. of_int (sign p)"
    let ?f = "\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))"
    have "(setsum (\<lambda>q. ?s q *
        (\<Prod>i\<in> ?U. (\<chi> i. A $ i $ p i *s B $ p i :: 'a^'n^'n) $ i $ q i)) ?PU) =
      (setsum (\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))) ?PU)"
      unfolding sum_permutations_compose_right[OF permutes_inv[OF p], of ?f]
    proof (rule setsum.cong)
      fix q
      assume qU: "q \<in> ?PU"
      then have q: "q permutes ?U"
        by blast
      from p q have pp: "permutation p" and pq: "permutation q"
        unfolding permutation_permutes by auto
      have th00: "of_int (sign p) * of_int (sign p) = (1::'a)"
        "\<And>a. of_int (sign p) * (of_int (sign p) * a) = a"
        unfolding mult.assoc[symmetric]
        unfolding of_int_mult[symmetric]
        by (simp_all add: sign_idempotent)
      have ths: "?s q = ?s p * ?s (q \<circ> inv p)"
        using pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add:  th00 ac_simps sign_idempotent sign_compose)
      have th001: "setprod (\<lambda>i. B$i$ q (inv p i)) ?U = setprod ((\<lambda>i. B$i$ q (inv p i)) \<circ> p) ?U"
        by (rule setprod_permute[OF p])
      have thp: "setprod (\<lambda>i. (\<chi> i. A$i$p i *s B$p i :: 'a^'n^'n) $i $ q i) ?U =
        setprod (\<lambda>i. A$i$p i) ?U * setprod (\<lambda>i. B$i$ q (inv p i)) ?U"
          unfolding th001 setprod.distrib[symmetric] o_def permutes_inverses[OF p]
          apply (rule setprod.cong[OF refl])
          using permutes_in_image[OF q]
          apply vector
          done
      show "?s q * setprod (\<lambda>i. (((\<chi> i. A$i$p i *s B$p i) :: 'a^'n^'n)$i$q i)) ?U =
        ?s p * (setprod (\<lambda>i. A$i$p i) ?U) * (?s (q \<circ> inv p) * setprod (\<lambda>i. B$i$(q \<circ> inv p) i) ?U)"
        using ths thp pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add: sign_nz th00 field_simps sign_idempotent sign_compose)
    qed rule
  }
  then have th2: "setsum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU = det A * det B"
    unfolding det_def setsum_product
    by (rule setsum.cong[OF refl])
  have "det (A**B) = setsum (\<lambda>f.  det (\<chi> i. A $ i $ f i *s B $ f i)) ?F"
    unfolding matrix_mul_setsum_alt det_linear_rows_setsum[OF fU]
    by simp
  also have "\<dots> = setsum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU"
    using setsum.mono_neutral_cong_left[OF fF PUF zth, symmetric]
    unfolding det_rows_mul by auto
  finally show ?thesis unfolding th2 .
qed

lemma invertible_left_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). B ** A = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

  lemma invertible_righ_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). A** B = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)
  
  lemma invertible_det_nz:
  fixes A::"'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> det A \<noteq> 0"
proof -
  {
    assume "invertible A"
    then obtain B :: "'a^'n^'n" where B: "A ** B = mat 1"
      unfolding invertible_righ_inverse by blast
    then have "det (A ** B) = det (mat 1 :: 'a^'n^'n)"
      by simp
    then have "det A \<noteq> 0"
      by (simp add: det_mul det_I) algebra
  }
  moreover
  {
    assume H: "\<not> invertible A"
    let ?U = "UNIV :: 'n set"
    have fU: "finite ?U"
      by simp
    from H obtain c i where c: "setsum (\<lambda>i. c i *s row i A) ?U = 0"
      and iU: "i \<in> ?U"
      and ci: "c i \<noteq> 0"
      unfolding invertible_righ_inverse
      unfolding matrix_right_invertible_independent_rows
      by blast
    have *: "\<And>(a::'a^'n) b. a + b = 0 \<Longrightarrow> -a = b"
      apply (drule_tac f="op + (- a)" in cong[OF refl])
      apply (simp only: ab_left_minus add.assoc[symmetric])
      apply simp
      done
    from c ci
    have thr0: "- row i A = setsum (\<lambda>j. (1/ c i) *s (c j *s row j A)) (?U - {i})"
      unfolding setsum.remove[OF fU iU] setsum_cmul
      apply -
      apply (rule vector_mul_lcancel_imp[OF ci])
      apply (auto simp add: field_simps)
      unfolding *
      apply rule
      done
    have thr: "- row i A \<in> vec.span {row j A| j. j \<noteq> i}"
      unfolding thr0
      apply (rule vec.span_setsum)
      apply simp
      apply (rule ballI)
      apply (rule vec.span_mul [folded scalar_mult_eq_scaleR])+
      apply (rule vec.span_superset)
      apply auto
      done
    let ?B = "(\<chi> k. if k = i then 0 else row k A) :: 'a^'n^'n"
    have thrb: "row i ?B = 0" using iU by (vector row_def)
    have "det A = 0"
      unfolding det_row_span[OF thr, symmetric] right_minus
      unfolding det_zero_row[OF thrb] ..
  }
  ultimately show ?thesis
    by blast
qed
(********************** Here ends the generalization of Determinants.thy **********************)

(*Finally, some interesting theorems and interpretations that don't appear in any file of the 
  library.*)

locale linear_first_finite_dimensional_vector_space =
  l?: linear scaleB scaleC f +
  B?: finite_dimensional_vector_space scaleB BasisB + 
  C?: vector_space scaleC 
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75) 
  and BasisB :: "('b set)"
  and f :: "('b=>'c)"  

context linear_between_finite_dimensional_vector_spaces
begin
  sublocale lblf?: linear_first_finite_dimensional_vector_space by unfold_locales
end
  
lemma vec_dim_card: "vec.dim (UNIV::('a::{field}^'n) set) = CARD ('n)"
proof -
  let ?f="\<lambda>i::'n. axis i (1::'a)"
  have "vec.dim (UNIV::('a::{field}^'n) set) = card (cart_basis::('a^'n) set)" 
    unfolding vec.dim_UNIV ..
  also have "... = card ({i. i\<in> UNIV}::('n) set)"
    proof (rule bij_betw_same_card[of ?f, symmetric], unfold bij_betw_def, auto)
      show "inj (\<lambda>i::'n. axis i (1::'a))"  by (simp add: inj_on_def axis_eq_axis)
      fix i::'n
      show "axis i 1 \<in> cart_basis" unfolding cart_basis_def by auto
      fix x::"'a^'n"
      assume "x \<in> cart_basis"
      thus "x \<in> range (\<lambda>i. axis i 1)" unfolding cart_basis_def by auto
    qed
  also have "... = CARD('n)" by auto
  finally show ?thesis .
qed                   

interpretation vector_space_over_itself: vector_space "op * :: 'a::field => 'a => 'a" 
  by unfold_locales (simp_all add: algebra_simps)

interpretation vector_space_over_itself: finite_dimensional_vector_space 
  "op * :: 'a::field => 'a => 'a" "{1}"  
proof (unfold_locales, auto)
 (* interpret v: vector_space "op * :: 'a::field => 'a => 'a" by unfold_locales*) 
  have v: "vector_space (op * :: 'a::field => 'a => 'a)" by unfold_locales 
  fix x::'a
  show "x \<in> vector_space.span (op *) {1::'a}" unfolding vector_space.span_singleton[OF v] by auto  
qed

lemma dimension_eq_1[code_unfold]: "vector_space_over_itself.dimension TYPE('a::field)= 1"
  unfolding vector_space_over_itself.dimension_def by simp

interpretation complex_over_reals: finite_dimensional_vector_space "(op *\<^sub>R)::real=>complex=>complex" 
  "{1, \<i>}"
proof unfold_locales
show "finite {1, \<i>}" by auto
show "vector_space.independent (op *\<^sub>R) {1, \<i>}"
  by (metis Basis_complex_def euclidean_space.independent_Basis)
show "vector_space.span (op *\<^sub>R) {1, \<i>} = UNIV" 
  by (metis Basis_complex_def euclidean_space.span_Basis)
qed

lemma complex_over_reals_dimension[code_unfold]:
  "complex_over_reals.dimension = 2" unfolding complex_over_reals.dimension_def by auto

term "op *s"
term "op *\<^sub>R"

(* The following definition will be very useful in our formalization. The problem was that 
  (op *\<^sub>R) has type real=>'a=>'a but (op *s) has type 'a \<Rightarrow> ('a, 'b) vec \<Rightarrow> ('a, 'b) vec, 
  so we can't use (op *s) to multiply a matrix by a scalar.*) 
(*
  definition matrix_scalar_mult :: "'a => ('a::semiring_1) ^'n^'m => ('a::semiring_1) ^'n^'m"
    (infixl "*k" 70)
  where "k *k A \<equiv> (\<chi> i j. k * A $ i $ j)"
*)

(*One example of the use of *\<^sub>R, *s and *k appears in the following theorem (obtained from AFP entry 
  about Tarski's Geometry, 
  see http://afp.sourceforge.net/browser_info/devel/AFP/Tarskis_Geometry/Linear_Algebra2.html)*)
(*
  lemma scalar_matrix_vector_assoc:
  fixes A :: "real^('m::finite)^('n::finite)"
  shows "k *\<^sub>R (A *v v) = k *\<^sub>R A *v v"*)
  
(*Now, the generalization of the statement would be: *)

(*
  lemma scalar_matrix_vector_assoc:
  fixes A :: "'a::{field}^'m^'n"
  shows "k *s (A *v v) = k *k A *v v"
*)
end
