(*  
    Title:      Dim_Formula.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

header "Rank Nullity Theorem of Linear Algebra"

theory Dim_Formula
  imports "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

subsection{*Previous results*}

text{*Linear dependency is a monotone property, based on the 
  monotonocity of linear independence:*}

lemma dependent_mono:
  assumes d:"dependent A"
  and A_in_B: "A \<subseteq> B"
  shows  "dependent B"
  using independent_mono [OF _ A_in_B] d by auto

text{*The negation of @{thm [display] dependent_explicit [no_vars]} 
  produces the following result:*}

lemma independent_explicit:
  "independent A = 
  (\<forall>S \<subseteq> A. finite S \<longrightarrow> (\<forall>u. (\<Sum>v\<in>S. u v *\<^sub>R v) = 0 \<longrightarrow> (\<forall>v\<in>S. u v = 0)))" 
  unfolding dependent_explicit [of A] by (simp add: disj_not2)

text{*A finite set @{term "A::'a set"} for which
  every of its linear combinations equal to zero 
  requires every coefficient being zero, is independent:*}

lemma independent_if_scalars_zero:
  assumes fin_A: "finite A"
  and sum: "\<forall>f. (\<Sum>x\<in>A. f x *\<^sub>R x) = 0 \<longrightarrow> (\<forall>x \<in> A. f x = 0)"
  shows "independent A"
proof (unfold independent_explicit, clarify)
  fix S v and u :: "'a \<Rightarrow> real"
  assume S: "S \<subseteq> A" and v: "v \<in> S" 
  let ?g = "\<lambda>x. if x \<in> S then u x else 0"
  have "(\<Sum>v\<in>A. ?g v *\<^sub>R v) = (\<Sum>v\<in>S. u v *\<^sub>R  v)"
    using S fin_A by (auto intro!: setsum.mono_neutral_cong_right)  
  also assume "(\<Sum>v\<in>S. u v *\<^sub>R v) = 0"
  finally have "?g v = 0" using v S sum by force
  thus "u v = 0"  unfolding if_P[OF v] .
qed

text{*Given a finite independent set, a linear combination of its 
  elements equal to zero is possible only if every coefficient is zero:*}

lemma scalars_zero_if_independent:
  assumes fin_A: "finite A"
  and ind: "independent A"
  and sum: "(\<Sum>x\<in>A. f x *\<^sub>R x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  using assms unfolding independent_explicit by auto

text{*In an euclidean space, every set is finite, and 
  thus @{thm [display ]scalars_zero_if_independent [no_vars]} holds:*}

corollary scalars_zero_if_independent_euclidean:
  fixes A::"'a::euclidean_space set"
  assumes ind: "independent A"
  and sum: "(\<Sum>x\<in>A. f x *\<^sub>R x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  by (rule scalars_zero_if_independent, 
      rule conjunct1 [OF independent_bound [OF ind]]) 
     (rule ind, rule sum)

text{*The following lemma states that every linear form is injective over the 
  elements which define the basis of the range of the linear form. 
  This property is applied later over the elements of an arbitrary 
  basis which are not in the basis of the nullifier or kernel set 
  (\emph{i.e.}, the candidates to be the basis of the range space 
  of the linear form).*}

text{*Thanks to this result, it can be concluded that the cardinal 
  of the elements of a basis which do not belong to the kernel 
  of a linear form @{term "f::'a => 'b"} is equal to the cardinal 
  of the set obtained when applying @{term "f::'a => 'b"} to such elements.*}

text{*The application of this lemma is not usually found in the pencil and paper 
  proofs of the ``Rank nullity theorem'', but will be crucial to know that,
  being @{term "f::'a => 'b"} a linear form from a finite dimensional
  vector space @{term "V"} to a vector space @{term "V'"}, 
  and given a basis @{term "B::'a::real_vector set"} of @{term "ker f"}, 
  when @{term "B"} is completed up to a basis of @{term "V::'a::real_vector set"}
  with a set @{term "W::'a::real_vector set"}, the cardinal of this set is
  equal to the cardinal of its range set:*}

lemma inj_on_extended:
  assumes lf: "linear f"
  and f: "finite C"
  and ind_C: "independent C"
  and C_eq: "C = B \<union> W"
  and disj_set: "B \<inter> W = {}"
  and span_B: "{x. f x = 0} \<subseteq> span B"
  shows "inj_on f W"
  -- "The proof is carried out by reductio ad absurdum"
proof (unfold inj_on_def, rule+, rule ccontr)
  -- "Some previous consequences of the premises that are used later:"
  have fin_B: "finite B" using finite_subset [OF _ f] C_eq by simp  
  have ind_B: "independent B" and ind_W: "independent W" 
    using independent_mono[OF ind_C] C_eq by simp_all
  -- "The proof starts here; we assume that there exist two different elements "
  -- "with the same image:"
  fix x::'a and y::'a
  assume x: "x \<in> W" and y: "y \<in> W" and f_eq: "f x = f y" and x_not_y: "x \<noteq> y"
  have fin_yB: "finite (insert y B)" using fin_B by simp
  have "f (x - y) = 0" by (metis diff_self f_eq lf linear_0 linear_sub)
  hence "x - y \<in> {x. f x = 0}" by simp
  hence "\<exists>g. (\<Sum>v\<in>B. g v *\<^sub>R v) = (x - y)" using span_B 
    unfolding span_finite [OF fin_B] by auto
  then obtain g where sum: "(\<Sum>v\<in>B. g v *\<^sub>R v) = (x - y)" by blast
  -- "We define one of the elements as a linear combination of the second 
      element and the ones in $B$"
  def h \<equiv> "(\<lambda>a. if a = y then (1::real) else g a)"
  have "x = y + (\<Sum>v\<in>B. g v *\<^sub>R v)" using sum by auto
  also have "... = h y *\<^sub>R y  + (\<Sum>v\<in>B. g v *\<^sub>R v)" unfolding h_def by simp
  also have "... = h y *\<^sub>R y + (\<Sum>v\<in>B. h v *\<^sub>R v)"
    by (unfold add_left_cancel, rule setsum.cong, rule refl)
       (metis (mono_tags) IntI disj_set empty_iff y h_def)
  also have "... = (\<Sum>v\<in>(insert y B). h v *\<^sub>R v)"
    by (rule setsum.insert[symmetric], rule fin_B)
       (metis (lifting) IntI disj_set empty_iff y)
  finally have x_in_span_yB: "x \<in> span (insert y B)"
    unfolding span_finite[OF fin_yB] by auto
  -- "We have that a subset of elements of $C$ is linearly dependent"
  have dep: "dependent (insert x (insert y B))" 
    by (unfold dependent_def, rule bexI [of _ x])
       (metis Diff_insert_absorb Int_iff disj_set empty_iff insert_iff 
         x x_in_span_yB x_not_y, simp)
  -- "Therefore, the set $C$ is also dependent:"
  hence "dependent C" using C_eq x y
    by (metis Un_commute Un_upper2 dependent_mono insert_absorb insert_subset)
  -- "This yields the contradiction, since $C$ is independent:"
  thus False using ind_C by contradiction
qed

subsection{*The proof*}

text{*Now the rank nullity theorem can be proved; given any linear form 
  @{term "f::'a => 'b"}, the sum of the dimensions of its kernel and 
  range subspaces is equal to the dimension of the source vector space.*}

text{*It is relevant to note that the source vector space must be 
  finite-dimensional (this restriction is introduced by means of the 
  euclidean space type class), whereas the destination vector space may be 
  finite or infinite dimensional (and thus a real vector space is used); 
  this is the usual way the theorem is stated in the literature.*}

text{*The statement of the ``rank nullity theorem for linear algebra'', as 
  well as its proof, follow the ones on~\cite{AX97}. The proof is the 
  traditional one found in the literature. The theorem is also named 
  ``fundamental theorem of linear algebra'' in some texts (for instance,
  in~\cite{GO10}).*}

theorem rank_nullity_theorem:
  assumes l: "linear (f::('a::{euclidean_space}) => ('b::{real_vector}))"
  shows "DIM ('a::{euclidean_space}) = dim {x. f x = 0} + dim (range f)"
proof -
  -- "For convenience we define abbreviations for the universe set, $V$, 
    and the kernel of $f$"
  def V == "UNIV::'a set"
  def ker_f == "{x. f x = 0}"
  -- "The kernel is a proper subspace:"
  have sub_ker: "subspace {x. f x = 0}" using subspace_kernel [OF l] .
  -- "The kernel has its proper basis, $B$:"
  obtain B where B_in_ker: "B \<subseteq> {x. f x = 0}" 
    and independent_B: "independent B"
    and ker_in_span:"{x. f x = 0} \<subseteq> span B"
    and card_B: "card B = dim {x. f x = 0}" using basis_exists by blast
  -- "The space $V$ has a (finite dimensional) basis, $C$:"
  obtain C where B_in_C: "B \<subseteq> C" and C_in_V: "C \<subseteq> V" 
    and independent_C: "independent C"
    and span_C: "V = span C"
    using maximal_independent_subset_extend [OF _ independent_B, of V]
    unfolding V_def by auto
  -- "The basis of $V$, $C$, can be decomposed in the disjoint union of the 
      basis of the kernel, $B$, and its complementary set, $C - B$"
  have C_eq: "C = B \<union> (C - B)" by (rule Diff_partition [OF B_in_C, symmetric])
  have eq_fC: "f ` C = f ` B \<union> f ` (C - B)" 
    by (subst C_eq, unfold image_Un, simp) 
  -- "The basis $C$, and its image, are finite, since $V$ is finite-dimensional"
  have finite_C: "finite C" 
    using independent_bound_general [OF independent_C] by fast
  have finite_fC: "finite (f ` C)" by (rule finite_imageI [OF finite_C])
  -- "The basis $B$ of the kernel of $f$, and its image, are also finite"
  have finite_B: "finite B" by (rule rev_finite_subset [OF finite_C B_in_C])
  have finite_fB: "finite (f ` B)" by (rule finite_imageI[OF finite_B])
  -- "The set $C - B$ is also finite"
  have finite_CB: "finite (C - B)" by (rule finite_Diff [OF finite_C, of B])
  have dim_ker_le_dim_V:"dim (ker_f) \<le> dim V" 
    using dim_subset [of ker_f V] unfolding V_def by simp
  -- "Here it starts the proof of the theorem: the sets $B$ and 
      $C - B$ must be proven to be bases, respectively, of the kernel 
      of $f$ and its range"
  show ?thesis
  proof -
    have "DIM ('a::{euclidean_space}) = dim V" unfolding V_def dim_UNIV .. 
    also have "dim V = dim C" unfolding span_C dim_span ..
    also have "... = card C"
      using basis_card_eq_dim [of C C, OF _ span_inc independent_C] by simp 
    also have "... = card (B \<union> (C - B))" using C_eq by simp
    also have "... = card B + card (C-B)" 
      by (rule card_Un_disjoint[OF finite_B finite_CB], fast)
    also have "... = dim ker_f + card (C-B)" unfolding ker_f_def card_B ..
    -- "Now it has to be proved that the elements of $C - B$ are a basis of 
      the range of $f$"
    also have "... = dim ker_f + dim (range f)"
    proof (unfold add_left_cancel)
      def W == "C - B"
      have finite_W: "finite W" unfolding W_def using finite_CB .
      have finite_fW: "finite (f ` W)" using finite_imageI[OF finite_W] .    
      have "card W = card (f ` W)"
        by (rule card_image [symmetric], rule inj_on_extended [of _ C B], 
          rule l, rule finite_C)
           (rule independent_C, unfold W_def, subst C_eq, rule refl, simp, 
             rule ker_in_span)
      also have "... = dim (range f)"
      proof (unfold dim_def, rule someI2)
        -- "1. The image set of $W$ generates the range of $f$:"
        have range_in_span_fW: "range f \<subseteq> span (f ` W)"
        proof (unfold span_finite [OF finite_fW], auto)
          -- "Given any element $v$ in $V$, its image can be expressed as a 
            linear combination of elements of the image by $f$ of $C$:"
          fix v :: 'a
          have fV_span: "f ` V \<subseteq> span (f ` C)" 
            using spans_image [OF l] span_C by simp
          have "\<exists>g. (\<Sum>x\<in>f`C. g x *\<^sub>R x) = f v"
            using fV_span unfolding V_def 
            using span_finite [OF finite_fC] by blast
          then obtain g where fv: "f v = (\<Sum>x\<in>f ` C. g x *\<^sub>R x)" by metis
            -- "We recall that $C$ is equal to $B$ union $(C - B)$, and $B$ 
            is the basis of the kernel; thus, the image of the elements of 
            $B$ will be equal to zero:"
          have zero_fB: "(\<Sum>x\<in>f ` B. g x *\<^sub>R x) = 0"
            using B_in_ker by (auto intro!: setsum.neutral)
          have zero_inter: "(\<Sum>x\<in>(f ` B \<inter> f ` W). g x *\<^sub>R x) = 0"
            using B_in_ker by (auto intro!: setsum.neutral)
          have "f v = (\<Sum>x\<in>f ` C. g x *\<^sub>R x)" using fv .
          also have "... = (\<Sum>x\<in>(f ` B \<union> f ` W). g x *\<^sub>R x)" 
            using eq_fC W_def by simp
          also have "... = 
                    (\<Sum>x\<in>f ` B. g x *\<^sub>R x) + (\<Sum>x\<in>f ` W. g x *\<^sub>R x) - (\<Sum>x\<in>(f ` B \<inter> f ` W). g x *\<^sub>R x)" 
            using setsum_Un [OF finite_fB finite_fW] by simp
          also have "... = (\<Sum>x\<in>f ` W. g x *\<^sub>R x)" 
            unfolding zero_fB zero_inter by simp
            -- "We have proved that the image set of $W$ is a generating set 
              of the range of $f$"
          finally show "\<exists>s. (\<Sum>x\<in>f ` W. s x *\<^sub>R x) = f v" by auto
       qed
       -- "2. The image set of $W$ is linearly independent:"
       have independent_fW: "independent (f ` W)"
       proof (rule independent_if_scalars_zero [OF finite_fW], rule+)
        -- "Every linear combination (given by $g x$) of the elements of 
           the image set of $W$ equal to zero, requires every coefficient to 
           be zero:"
        fix g :: "'b => real" and w :: 'b
        assume sum: "(\<Sum>x\<in>f ` W. g x *\<^sub>R x) = 0" and w: "w \<in> f ` W"
        have "0 = (\<Sum>x\<in>f ` W. g x *\<^sub>R x)" using sum by simp
        also have "... = setsum ((\<lambda>x. g x *\<^sub>R x) \<circ> f) W"
          by (rule setsum.reindex, rule inj_on_extended [of f C B], rule l)
             (unfold W_def, rule finite_C, rule independent_C, rule C_eq, simp, 
              rule ker_in_span)
        also have "... = (\<Sum>x\<in>W. ((g \<circ> f) x) *\<^sub>R f x)" unfolding o_def ..
        also have "... = f (\<Sum>x\<in>W. ((g \<circ> f) x) *\<^sub>R x)" 
          using linear_setsum_mul [symmetric, OF l] .
        finally have f_sum_zero:"f (\<Sum>x\<in>W. (g \<circ> f) x *\<^sub>R x) = 0" by (rule sym)
        hence "(\<Sum>x\<in>W. (g \<circ> f) x *\<^sub>R x) \<in> ker_f" unfolding ker_f_def by simp
        hence "\<exists>h. (\<Sum>v\<in>B. h v *\<^sub>R v) = (\<Sum>x\<in>W. (g \<circ> f) x *\<^sub>R x)"
          using span_finite[OF finite_B] using ker_in_span 
          unfolding ker_f_def by auto
        then obtain h where 
          sum_h: "(\<Sum>v\<in>B. h v *\<^sub>R v) = (\<Sum>x\<in>W. (g \<circ> f) x *\<^sub>R x)" by blast
        def t \<equiv> "(\<lambda>a. if a \<in> B then h a else - ((g \<circ> f) a))"
        have "0 = (\<Sum>v\<in>B. h v *\<^sub>R v) + - (\<Sum>x\<in>W. (g \<circ> f) x *\<^sub>R x)" 
          using sum_h by simp
        also have "... =  (\<Sum>v\<in>B. h v *\<^sub>R v) + (\<Sum>x\<in>W. -((g \<circ> f) x *\<^sub>R x))" 
          unfolding setsum_negf ..
        also have "... = (\<Sum>v\<in>B. t v *\<^sub>R v) + (\<Sum>x\<in>W. -((g \<circ> f) x *\<^sub>R x))" 
          unfolding add_right_cancel unfolding t_def by simp
        also have "... =  (\<Sum>v\<in>B. t v *\<^sub>R v) + (\<Sum>x\<in>W. t x *\<^sub>R x)"
          by (unfold add_left_cancel t_def W_def, rule setsum.cong) simp_all
        also have "... = (\<Sum>v\<in>B \<union> W. t v  *\<^sub>R v)" 
          by (rule setsum.union_inter_neutral [symmetric], rule finite_B, rule finite_W) 
             (simp add: W_def)       
        finally have "(\<Sum>v\<in>B \<union> W. t v  *\<^sub>R v) = 0" by simp
        hence coef_zero: "\<forall>x\<in>B \<union> W. t x = 0"
          using C_eq scalars_zero_if_independent [OF finite_C independent_C]
          unfolding W_def by simp
        obtain y where w_fy: "w = f y " and y_in_W: "y \<in> W" using w by fast
        have "- g w = t y" 
          unfolding t_def w_fy using y_in_W unfolding W_def by simp
        also have "... = 0" using coef_zero y_in_W unfolding W_def by simp
        finally show "g w = 0" by simp
       qed
      -- "The image set of $W$ is independent and its span contains the range 
           of $f$, so it is a basis of the range:"
      show "\<exists>B\<subseteq>range f. independent B \<and> range f \<subseteq> span B 
        \<and> card B = card (f ` W)"
        by (rule exI [of _"(f ` W)"], 
             simp add: range_in_span_fW independent_fW image_mono)
     -- "Now, it has to be proved that any other basis of the subspace 
          range of $f$ has equal cardinality:"
     show "\<And>n\<Colon>nat. \<exists>S\<subseteq>range f. independent S \<and> range f \<subseteq> span S 
       \<and> card S = n \<Longrightarrow> card (f ` W) = n"
     proof (clarify)
        fix S :: "'b set"
        assume S_in_range: "S \<subseteq> range f" and independent_S: "independent S" 
          and range_in_spanS: "range f \<subseteq> span S"
        have S_le: "finite S \<and> card S \<le> card (f ` W)"
        by (rule independent_span_bound, rule finite_fW, rule independent_S)
           (rule subset_trans [OF S_in_range range_in_span_fW])
        show "card (f ` W) = card S"
          by (rule le_antisym) (rule conjunct2, rule independent_span_bound, 
            rule conjunct1 [OF S_le], rule independent_fW, 
            rule subset_trans [OF _ range_in_spanS], auto simp add: S_le)
     qed
    qed
    finally show "card (C - B) = dim (range f)" unfolding W_def .
  qed
  finally show ?thesis unfolding V_def ker_f_def unfolding dim_UNIV .
  qed
qed

subsection{*The rank nullity theorem for matrices*}

text{*The previous lemma can be moved to the matrices' representation 
  of linear forms; we introduce first the notions of null space (or kernel) 
  and range (or column space) for matrices. The result 
  @{thm [display] "rank_nullity_theorem" [no_vars]} is more general than 
  its corresponding version for matrices representing linear forms, since 
  in the first one the destination vector space could be finite 
  or infinite dimensional, whereas in its version for matrices,
  both the source and destination vector spaces have to be 
  finite-dimensional.*}

text{*The null space correponds to the kernel of the linear form,
  and is a subset of the ``row space'':*}

definition null_space :: "real^'n^'m => (real^'n) set"
  where "null_space A = {x. A *v x = 0}"

text{*The column space is a subset of the destination vector space of the 
  linear form:*}

definition col_space :: "real^'n^'m=>(real^'m) set"
  where "col_space A = range (\<lambda>x. A *v x)"

lemma col_space_eq: "col_space A = {y. \<exists>x. A *v x = y}"
  unfolding col_space_def by blast

lemma null_space_eq_ker:
  assumes lf: "linear f"
  shows "null_space (matrix f) = {x. f x = 0}" 
  unfolding null_space_def using matrix_works [OF lf] by auto

lemma col_space_eq_range:
  assumes lf: "linear f"
  shows "col_space (matrix f) = range f"
  unfolding col_space_def using matrix_works[OF lf] by auto

text{*After the previous equivalences between the null space and 
  the column space and the range, the proof of the theorem for matrices 
  is direct, as a consequence of the ``rank nullity theorem''.*}

lemma rank_nullity_theorem_matrices:
  fixes A::"real^'a^'b"
  shows "DIM (real^'a) = dim (null_space A) + dim (col_space A)"
  apply (subst (1 2) matrix_of_matrix_vector_mul [of A, symmetric])
  unfolding null_space_eq_ker[OF matrix_vector_mul_linear] 
  unfolding col_space_eq_range [OF matrix_vector_mul_linear]
  using rank_nullity_theorem [OF matrix_vector_mul_linear] .

end
