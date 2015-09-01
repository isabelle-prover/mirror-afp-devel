(*  
    Title:      Dim_Formula.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section "Rank Nullity Theorem of Linear Algebra"

theory Dim_Formula
  imports Fundamental_Subspaces
begin

context vector_space
begin
  
subsection{*Previous results*}

text{*Linear dependency is a monotone property, based on the 
  monotonocity of linear independence:*}

lemma dependent_mono:
  assumes d:"dependent A"
  and A_in_B: "A \<subseteq> B"
  shows  "dependent B"
  using independent_mono [OF _ A_in_B] d by auto

text{*Given a finite independent set, a linear combination of its 
  elements equal to zero is possible only if every coefficient is zero:*}

lemma scalars_zero_if_independent:
  assumes fin_A: "finite A"
  and ind: "independent A"
  and sum: "(\<Sum>x\<in>A. scale (f x) x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  using assms unfolding independent_explicit by auto
  
end

context finite_dimensional_vector_space
begin
  
text{*In an finite dimensional vector space, every independent set is finite, and 
  thus @{thm [display ]scalars_zero_if_independent [no_vars]} holds:*}

corollary scalars_zero_if_independent_euclidean:
  assumes ind: "independent A"
  and sum: "(\<Sum>x\<in>A. scale (f x) x) = 0"
  shows "\<forall>x \<in> A. f x = 0"
  by (rule scalars_zero_if_independent, 
      rule conjunct1 [OF independent_bound [OF ind]]) 
     (rule ind, rule sum)
end

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
  proofs of the ``rank nullity theorem'', but will be crucial to know that,
  being @{term "f::'a => 'b"} a linear form from a finite dimensional
  vector space @{term "V"} to a vector space @{term "V'"}, 
  and given a basis @{term "B::'a set"} of @{term "ker f"}, 
  when @{term "B"} is completed up to a basis of @{term "V::'a set"}
  with a set @{term "W::'a set"}, the cardinal of this set is
  equal to the cardinal of its range set:*}
  
context vector_space
begin

lemma inj_on_extended:
  assumes lf: "linear scaleB scaleC f"
  and f: "finite C"
  and ind_C: "independent C"
  and C_eq: "C = B \<union> W"
  and disj_set: "B \<inter> W = {}"
  and span_B: "{x. f x = 0} \<subseteq> span B"
  shows "inj_on f W"
  -- "The proof is carried out by reductio ad absurdum"
proof (unfold inj_on_def, rule+, rule ccontr)
  interpret lf: linear scaleB scaleC f using lf by simp
  -- "Some previous consequences of the premises that are used later:"
  have fin_B: "finite B" using finite_subset [OF _ f] C_eq by simp  
  have ind_B: "independent B" and ind_W: "independent W" 
    using independent_mono[OF ind_C] C_eq by simp_all
  -- "The proof starts here; we assume that there exist two different elements "
  -- "with the same image:"
  fix x::'b and y::'b
  assume x: "x \<in> W" and y: "y \<in> W" and f_eq: "f x = f y" and x_not_y: "x \<noteq> y"
  have fin_yB: "finite (insert y B)" using fin_B by simp
  have "f (x - y) = 0" by (metis diff_self f_eq lf.linear_sub)
  hence "x - y \<in> {x. f x = 0}" by simp
  hence "\<exists>g. (\<Sum>v\<in>B. scale (g v) v) = (x - y)" using span_B 
    unfolding span_finite [OF fin_B] by auto
  then obtain g where sum: "(\<Sum>v\<in>B. scale (g v) v) = (x - y)" by blast
  -- "We define one of the elements as a linear combination of the second 
      element and the ones in $B$"
  def h \<equiv> "(\<lambda>a. if a = y then (1::'a) else g a)"
  have "x = y + (\<Sum>v\<in>B. scale (g v) v)" using sum by auto
  also have "... = scale (h y) y  + (\<Sum>v\<in>B. scale (g v) v)" unfolding h_def by simp
  also have "... = scale (h y) y + (\<Sum>v\<in>B. scale (h v) v)"
    apply (unfold add_left_cancel, rule setsum.cong) 
    using y h_def empty_iff disj_set by auto   
  also have "... = (\<Sum>v\<in>(insert y B). scale (h v) v)"
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
end

subsection{*The proof*}

text{*Now the rank nullity theorem can be proved; given any linear form 
  @{term "f::'a => 'b"}, the sum of the dimensions of its kernel and 
  range subspaces is equal to the dimension of the source vector space.*}

text{*The statement of the ``rank nullity theorem for linear algebra'', as 
  well as its proof, follow the ones on~\cite{AX97}. The proof is the 
  traditional one found in the literature. The theorem is also named 
  ``fundamental theorem of linear algebra'' in some texts (for instance,
  in~\cite{GO10}).*}

context linear_first_finite_dimensional_vector_space
begin

theorem rank_nullity_theorem:
  shows "B.dimension = B.dim {x. f x = 0} + C.dim (range f)"
proof -
  have l: "linear scaleB scaleC f" by unfold_locales
  -- "For convenience we define abbreviations for the universe set, $V$, 
    and the kernel of $f$"
  def V == "UNIV::'b set"
  def ker_f == "{x. f x = 0}"
  -- "The kernel is a proper subspace:"
  have sub_ker: "B.subspace {x. f x = 0}" using B.subspace_kernel[OF l] .
  -- "The kernel has its proper basis, $B$:"
  obtain B where B_in_ker: "B \<subseteq> {x. f x = 0}" 
    and independent_B: "B.independent B"
    and ker_in_span:"{x. f x = 0} \<subseteq> B.span B"
    and card_B: "card B = B.dim {x. f x = 0}" using B.basis_exists by blast
  -- "The space $V$ has a (finite dimensional) basis, $C$:"
  obtain C where B_in_C: "B \<subseteq> C" and C_in_V: "C \<subseteq> V" 
    and independent_C: "B.independent C"
    and span_C: "V = B.span C"
    using B.maximal_independent_subset_extend [OF _ independent_B, of V]
    unfolding V_def by auto
  -- "The basis of $V$, $C$, can be decomposed in the disjoint union of the 
      basis of the kernel, $B$, and its complementary set, $C - B$"
  have C_eq: "C = B \<union> (C - B)" by (rule Diff_partition [OF B_in_C, symmetric])
  have eq_fC: "f ` C = f ` B \<union> f ` (C - B)" 
    by (subst C_eq, unfold image_Un, simp) 
  -- "The basis $C$, and its image, are finite, since $V$ is finite-dimensional"
  have finite_C: "finite C"
    using B.independent_bound_general [OF independent_C] by fast
  have finite_fC: "finite (f ` C)" by (rule finite_imageI [OF finite_C])
  -- "The basis $B$ of the kernel of $f$, and its image, are also finite"
  have finite_B: "finite B" by (rule rev_finite_subset [OF finite_C B_in_C])
  have finite_fB: "finite (f ` B)" by (rule finite_imageI[OF finite_B])
  -- "The set $C - B$ is also finite"
  have finite_CB: "finite (C - B)" by (rule finite_Diff [OF finite_C, of B])
  have dim_ker_le_dim_V:"B.dim (ker_f) \<le> B.dim V" 
    using B.dim_subset [of ker_f V] unfolding V_def by simp
  -- "Here it starts the proof of the theorem: the sets $B$ and 
      $C - B$ must be proven to be bases, respectively, of the kernel 
      of $f$ and its range"
  show ?thesis
  proof -
    have "B.dimension = B.dim V" unfolding V_def dim_UNIV dimension_def
      by (metis B.basis_card_eq_dim B.dimension_def B.independent_Basis B.span_Basis top_greatest)
    also have "B.dim V = B.dim C" unfolding span_C B.dim_span ..
    also have "... = card C"
      using B.basis_card_eq_dim [of C C, OF _ B.span_inc independent_C] by simp 
    also have "... = card (B \<union> (C - B))" using C_eq by simp
    also have "... = card B + card (C-B)" 
      by (rule card_Un_disjoint[OF finite_B finite_CB], fast)
    also have "... = B.dim ker_f + card (C-B)" unfolding ker_f_def card_B ..
    -- "Now it has to be proved that the elements of $C - B$ are a basis of 
      the range of $f$"
    also have "... = B.dim ker_f + C.dim (range f)"
    proof (unfold add_left_cancel)
      def W == "C - B"
      have finite_W: "finite W" unfolding W_def using finite_CB .
      have finite_fW: "finite (f ` W)" using finite_imageI[OF finite_W] .    
      have "card W = card (f ` W)" 
        by (rule card_image [symmetric], rule B.inj_on_extended[OF l, of C B], rule finite_C)
         (rule independent_C,unfold W_def, subst C_eq, rule refl, simp, rule ker_in_span)       
      also have "... = C.dim (range f)"
      unfolding C.dim_def
      proof (rule someI2)    
        -- "1. The image set of $W$ generates the range of $f$:"
        have range_in_span_fW: "range f \<subseteq> C.span (f ` W)"
        proof (unfold l.C.span_finite [OF finite_fW], auto)
          -- "Given any element $v$ in $V$, its image can be expressed as a 
            linear combination of elements of the image by $f$ of $C$:"
          fix v :: 'b
          have fV_span: "f ` V \<subseteq> C.span  (f ` C)" 
            using B.spans_image [OF l] span_C by simp
          have "\<exists>g. (\<Sum>x\<in>f`C. scaleC (g x) x) = f v"
            using fV_span unfolding V_def
            using l.C.span_finite[OF finite_fC] by auto
          then obtain g where fv: "f v = (\<Sum>x\<in>f ` C. scaleC (g x) x)" by metis
            -- "We recall that $C$ is equal to $B$ union $(C - B)$, and $B$ 
            is the basis of the kernel; thus, the image of the elements of 
            $B$ will be equal to zero:"
          have zero_fB: "(\<Sum>x\<in>f ` B. scaleC (g x) x) = 0"
            using B_in_ker by (auto intro!: setsum.neutral)
          have zero_inter: "(\<Sum>x\<in>(f ` B \<inter> f ` W). scaleC (g x) x) = 0"
            using B_in_ker by (auto intro!: setsum.neutral)
          have "f v = (\<Sum>x\<in>f ` C. scaleC (g x) x)" using fv .
          also have "... = (\<Sum>x\<in>(f ` B \<union> f ` W).  scaleC (g x) x)" 
            using eq_fC W_def by simp
          also have "... = 
              (\<Sum>x\<in>f ` B. scaleC (g x) x) + (\<Sum>x\<in>f ` W. scaleC (g x) x) 
                - (\<Sum>x\<in>(f ` B \<inter> f ` W). scaleC (g x) x)" 
            using setsum_Un [OF finite_fB finite_fW] by simp
          also have "... = (\<Sum>x\<in>f ` W. scaleC (g x) x)" 
            unfolding zero_fB zero_inter by simp
            -- "We have proved that the image set of $W$ is a generating set 
              of the range of $f$"
          finally show "\<exists>s. (\<Sum>x\<in>f ` W. scaleC (s x) x) = f v" by auto
       qed
       -- "2. The image set of $W$ is linearly independent:"
       have independent_fW: "l.C.independent (f ` W)"
       proof (rule l.C.independent_if_scalars_zero [OF finite_fW], rule+)
        -- "Every linear combination (given by $g x$) of the elements of 
           the image set of $W$ equal to zero, requires every coefficient to 
           be zero:"
        fix g :: "'c => 'a" and w :: 'c
        assume sum: "(\<Sum>x\<in>f ` W. scaleC (g x) x) = 0" and w: "w \<in> f ` W"
        have "0 = (\<Sum>x\<in>f ` W. scaleC (g x) x)" using sum by simp
        also have "... = setsum ((\<lambda>x. scaleC (g x) x) \<circ> f) W"
          by (rule setsum.reindex, rule B.inj_on_extended[OF l, of C B])
           (unfold W_def, rule finite_C, rule independent_C, rule C_eq, simp, 
              rule ker_in_span)
        also have "... = (\<Sum>x\<in>W. scaleC ((g \<circ> f) x) (f x))" unfolding o_def ..
        also have "... = f (\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x)"
           using l.linear_setsum_mul [symmetric, OF finite_W] .
        finally have f_sum_zero:"f (\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x) = 0" by (rule sym)
        hence "(\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x) \<in> ker_f" unfolding ker_f_def by simp
        hence "\<exists>h. (\<Sum>v\<in>B. scaleB (h v) v) = (\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x)"
          using B.span_finite[OF finite_B] using ker_in_span 
          unfolding ker_f_def by auto
        then obtain h where 
          sum_h: "(\<Sum>v\<in>B. scaleB (h v) v) = (\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x)" by blast
        def t \<equiv> "(\<lambda>a. if a \<in> B then h a else - ((g \<circ> f) a))"
        have "0 = (\<Sum>v\<in>B. scaleB (h v) v) + - (\<Sum>x\<in>W. scaleB ((g \<circ> f) x) x)" 
          using sum_h by simp
          also have "... =  (\<Sum>v\<in>B. scaleB (h v) v) + (\<Sum>x\<in>W. - (scaleB ((g \<circ> f) x) x))" 
          unfolding setsum_negf ..
        also have "... = (\<Sum>v\<in>B. scaleB (t v) v) + (\<Sum>x\<in>W. -(scaleB((g \<circ> f) x) x))" 
          unfolding add_right_cancel unfolding t_def by simp
        also have "... =  (\<Sum>v\<in>B. scaleB (t v) v) + (\<Sum>x\<in>W. scaleB (t x) x)"
          by (unfold add_left_cancel t_def W_def, rule setsum.cong) simp+
        also have "... = (\<Sum>v\<in>B \<union> W. scaleB (t v) v)"
          by (rule setsum.union_inter_neutral [symmetric], rule finite_B, rule finite_W) 
             (simp add: W_def)
        finally have "(\<Sum>v\<in>B \<union> W. scaleB (t v) v) = 0" by simp
        hence coef_zero: "\<forall>x\<in>B \<union> W. t x = 0"
          using C_eq B.scalars_zero_if_independent [OF finite_C independent_C]
          unfolding W_def by simp
        obtain y where w_fy: "w = f y " and y_in_W: "y \<in> W" using w by fast
        have "- g w = t y" 
          unfolding t_def w_fy using y_in_W unfolding W_def by simp
        also have "... = 0" using coef_zero y_in_W unfolding W_def by simp
        finally show "g w = 0" by simp
       qed
      -- "The image set of $W$ is independent and its span contains the range 
           of $f$, so it is a basis of the range:" 
      show " \<exists>B\<subseteq>range f. \<not> vector_space.dependent scaleC B 
        \<and> range f \<subseteq> vector_space.span scaleC B \<and> card B = card (f ` W)"
        by (rule exI [of _"(f ` W)"], 
             simp add: range_in_span_fW independent_fW image_mono)
     -- "Now, it has to be proved that any other basis of the subspace 
          range of $f$ has equal cardinality:"
     show "\<And>n::nat. \<exists>B\<subseteq>range f. l.C.independent B \<and> range f \<subseteq> l.C.span B \<and> card B = n 
      \<Longrightarrow> card (f ` W) = n"
     proof (clarify)
        fix S :: "'c set"
        assume S_in_range: "S \<subseteq> range f" and independent_S: "vector_space.independent scaleC S" 
          and range_in_spanS: "range f \<subseteq> vector_space.span scaleC S"
        have S_le: "finite S \<and> card S \<le> card (f ` W)" 
        by (rule l.C.independent_span_bound[OF finite_fW independent_S]) 
          (rule subset_trans [OF S_in_range range_in_span_fW])
        show "card (f ` W) = card S"
          by (rule le_antisym, rule conjunct2, rule l.C.independent_span_bound)
             (rule conjunct1 [OF S_le], rule independent_fW, 
                rule subset_trans [OF _ range_in_spanS], auto simp add: S_le)
     qed
    qed
    finally show "card (C - B) = C.dim (range f)" unfolding W_def .
  qed
  finally show ?thesis unfolding V_def ker_f_def unfolding dim_UNIV .
  qed
qed

end

subsection{*The rank nullity theorem for matrices*}

text{*The proof of the theorem for matrices 
  is direct, as a consequence of the ``rank nullity theorem''.*}

lemma rank_nullity_theorem_matrices:
  fixes A::"'a::{field}^'cols::{finite, wellorder}^'rows"
  shows "ncols A = vec.dim (null_space A) + vec.dim (col_space A)"
proof -
show ?thesis
  apply (subst (1 2) matrix_of_matrix_vector_mul [of A, symmetric])
  unfolding null_space_eq_ker[OF matrix_vector_mul_linear]
  unfolding col_space_eq_range [OF matrix_vector_mul_linear]
  using vec.rank_nullity_theorem
  by (metis col_space_eq' ncols_def vec.dim_UNIV vec.dimension_def vec_dim_card) 
qed

end
