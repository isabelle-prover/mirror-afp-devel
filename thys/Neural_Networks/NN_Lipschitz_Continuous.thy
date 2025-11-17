(***********************************************************************************
 * Copyright (c) University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 ***********************************************************************************)

subsection\<open>Neural Network Lipschitz Continuity\<close>

theory
  NN_Lipschitz_Continuous
imports 
  NN_Layers
  "HOL-Library.Numeral_Type"
  Activation_Functions
  Matrix_Utils
  "HOL-Analysis.Analysis"
begin

subsubsection "Lipschitz Continuity of Functions (real)"

paragraph \<open>Splitting Function\<close>

paragraph \<open>Neural Network: Activations\<close>

lemma relu_lipschitz: "1-lipschitz_on (X::real set) (relu)"
  unfolding lipschitz_on_def relu_def dist_real_def 
  by auto

lemma identity_lipschitz: "1-lipschitz_on (X::real set) (identity)"
  unfolding lipschitz_on_def identity_def dist_real_def 
  by auto

paragraph \<open>Neural Network: Layers\<close> 

lemma input_output_lipschitz_continuous:
  \<open>1-lipschitz_on (U::real set) (\<lambda> i. i)\<close>
  using lipschitz_intros by simp

lemma activation_lipschitz_continuous:
  assumes \<open>C-lipschitz_on U f\<close>
  shows \<open>C-lipschitz_on U (\<lambda> i . f i)\<close>
  using assms by simp

lemma lipschitz_on_add_const:
  shows "(1::real)-lipschitz_on (U::real set) (\<lambda>x. x + c)"
  unfolding lipschitz_on_def by simp

lemma lipschitz_on_fold_add:
  shows "1-lipschitz_on (U::real set) (fold (+) xs)"
  unfolding lipschitz_on_def 
  by (simp add: fold_plus_sum_list_rev)

lemma lipschitz_on_fold_add_zero:
  shows "1-lipschitz_on (U::real set) (\<lambda> x . fold (+) [x] (0::real))"
  unfolding lipschitz_on_def  
  by (simp add: fold_plus_sum_list_rev foldr_conv_fold)

lemma lipschitz_on_foldr_add:
  shows "1-lipschitz_on (U::real set) (\<lambda> s. foldr (+) xs s)"
  unfolding lipschitz_on_def  
  by (simp add: fold_plus_sum_list_rev foldr_conv_fold)

lemma lipschitz_on_sumlist_rev:
  shows "1-lipschitz_on (U::real set) ((+) (sum_list (rev xs)))" 
  using fold_plus_sum_list_rev lipschitz_on_fold_add by metis

lemma lipschitz_on_sumlist:
  shows "1-lipschitz_on (U::real set) ((+) (sum_list xs))" 
  using fold_plus_sum_list_rev lipschitz_on_fold_add 
  by (metis sum_list_rev)

lemma lipschitz_on_mult_const:
  shows "\<bar>c\<bar>-lipschitz_on (U::real set) (\<lambda> x . x * c)"
  unfolding lipschitz_on_def dist_real_def using abs_mult
  by (metis (no_types, opaque_lifting) Orderings.order_eq_iff abs_ge_zero mult.commute 
      real_scaleR_def scaleR_right_diff_distrib)

lemma lipschitz_on_weighted_sum_single:
  "\<bar>w\<bar>-lipschitz_on (U::real set) (\<lambda> x . x * w + b)"
  unfolding lipschitz_on_def dist_real_def using abs_mult 
  by (metis Groups.mult_ac(2) abs_ge_zero add_diff_cancel_right left_diff_distrib order.refl)

lemma lipschitz_on_fold_add_zero':
  shows "2-lipschitz_on (U::real set) (\<lambda> x . (fold (+) [x,x] (0::real)) + w)"
  unfolding lipschitz_on_def 
  by (metis (no_types, lifting) ext List.fold_simps(1,2) add.commute dist_add_cancel dist_triangle_add mult.commute mult_2_right zero_le_numeral)

lemma lipschitz_on_mult_const':
  shows \<open>\<forall> x \<in> set xs . \<bar>c\<bar>-lipschitz_on (set xs) (\<lambda> y . c * y)\<close>
  using lipschitz_on_mult_const 
  by (metis mult_commute_abs)

typedef ('a, 'nr::finite, 'nc::finite) fixed_mat = 
  "carrier_mat (CARD('nr)) (CARD('nc)) :: 'a mat set"
  morphisms Rep_fixed_mat Abs_fixed_mat by blast

setup_lifting type_definition_fixed_mat

typedef ('a, 'n::finite) fixed_vec = 
  "carrier_vec (CARD('n)) :: 'a vec set"
  morphisms Rep_fixed_vec Abs_fixed_vec 
  using vec_carrier by blast
 
setup_lifting type_definition_fixed_vec

definition dim_vecf :: "('a, 'n::finite) fixed_vec \<Rightarrow> nat" where
  "dim_vecf v = CARD('n)"

definition dim_colf :: "('a, 'nc::finite, 'nr::finite) fixed_mat \<Rightarrow> nat" where
  "dim_colf m = CARD('nc)"

definition dim_rowf :: "('a, 'nc::finite, 'nr::finite) fixed_mat \<Rightarrow> nat" where
  "dim_rowf m = CARD('nr)"

definition fixed_mat_zero :: "('a::zero, 'nr::finite, 'nc::finite) fixed_mat" where
  "fixed_mat_zero = Abs_fixed_mat (0\<^sub>m (CARD('nr)) (CARD('nc)))"

definition fixed_mat_add :: "('a::plus, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "fixed_mat_add A B = Abs_fixed_mat (Rep_fixed_mat A + Rep_fixed_mat B)"

definition fixed_vec_zero :: "('a::zero, 'nr::finite ) fixed_vec" where
  "fixed_vec_zero = Abs_fixed_vec (0\<^sub>v (CARD('nr)))"

definition fixed_vec_add :: "('a::plus, 'nr::finite) fixed_vec \<Rightarrow> ('a, 'nr) fixed_vec \<Rightarrow> ('a, 'nr) fixed_vec" where
  "fixed_vec_add A B = Abs_fixed_vec (Rep_fixed_vec A + Rep_fixed_vec B)"

lift_definition fixed_mat_smult :: "'a::times \<Rightarrow> ('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat"
  is "\<lambda>c A. c \<cdot>\<^sub>m A" 
  using smult_carrier_mat .

lift_definition fixed_mat_index :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"
  is "\<lambda>A i j. A $$ (i, j)" .

lift_definition fixed_vec_index :: "('a, 'nr::finite) fixed_vec \<Rightarrow> nat \<Rightarrow> 'a"
  is "vec_index" .

lift_definition fixed_vec_smult :: "'a::times \<Rightarrow> ('a, 'nr::finite) fixed_vec \<Rightarrow> ('a, 'nr) fixed_vec"
  is "\<lambda>c A. c \<cdot>\<^sub>v A" 
  using smult_carrier_mat by simp

lift_definition mult_vec_fixed_mat :: 
  "('a::semiring_0, 'nr::finite) fixed_vec \<Rightarrow> ('a, 'nr, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nc) fixed_vec" 
  (infixl "\<^sub>f\<^sub>v*" 70)
  is "\<lambda>v A. vec (dim_col A) (\<lambda>i. col A i \<bullet> v)" 
  by simp 

lift_definition map_fixed_vec :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'n::finite) fixed_vec \<Rightarrow> ('b, 'n::finite) fixed_vec" 
  is "map_vec :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a vec \<Rightarrow> 'b vec"
  by simp

lemma zero_in_carrier:
  "0\<^sub>m (CARD('nr)) (CARD('nc)) \<in> carrier_mat (CARD('nr)) (CARD('nc))"
  using zero_carrier_mat by simp

lemma Rep_fixed_mat_zero [simp]:
  "Rep_fixed_mat (fixed_mat_zero :: ('a::zero, 'nr::finite, 'nc::finite) fixed_mat) = 0\<^sub>m (CARD('nr)) (CARD('nc))"
  unfolding fixed_mat_zero_def
  using zero_in_carrier 
  by (simp add: Abs_fixed_mat_inverse)

lemma Rep_fixed_mat_add [simp]:
  "Rep_fixed_mat (fixed_mat_add A B) = Rep_fixed_mat A + Rep_fixed_mat B"
  unfolding fixed_mat_add_def
  apply (subst Abs_fixed_mat_inverse)
  using Rep_fixed_mat 
   apply fastforce by auto

lemma Rep_fixed_vec_zero [simp]:
  "Rep_fixed_vec (fixed_vec_zero :: ('a::zero, 'n::finite) fixed_vec) = 0\<^sub>v (CARD('n))"
  unfolding fixed_vec_zero_def
  using zero_in_carrier 
  by (simp add: Abs_fixed_vec_inverse)

lemma Rep_fixed_vec_add [simp]:
  "Rep_fixed_vec (fixed_vec_add A B) = Rep_fixed_vec A + Rep_fixed_vec B"
  unfolding fixed_vec_add_def
  apply (subst Abs_fixed_vec_inverse)
  subgoal using Rep_fixed_vec 
    using add_carrier_vec by blast
  subgoal by blast
  done

lemma Rep_fixed_mat_inject: "Rep_fixed_mat A = Rep_fixed_mat B \<Longrightarrow> A = B"
  by (simp add: Rep_fixed_mat_inject)

lemma Rep_fixed_vec_inject: "Rep_fixed_vec A = Rep_fixed_vec B \<Longrightarrow> A = B"
  by (simp add: Rep_fixed_vec_inject)

lift_definition row_fixed :: "('a, 'n::finite, 'm::finite) fixed_mat \<Rightarrow> nat \<Rightarrow> ('a, 'm) fixed_vec" is
  "\<lambda>A i.  vec (CARD('m)) (\<lambda>j. A $$ (i, j))"
  by simp

lift_definition col_fixed :: "('a, 'n::finite, 'm::finite) fixed_mat \<Rightarrow> nat \<Rightarrow> ('a, 'n) fixed_vec" is
  "\<lambda>A j.  vec (CARD('n)) (\<lambda>i. A $$ (i, j))"
  by simp

lemma "CARD(285) = 285" by auto (*using the numeral type*)

instantiation fixed_mat :: (semiring_1, finite, finite) times
begin

lift_definition mat_mult :: "('a::semiring_1, 'n::finite, 'm::finite) fixed_mat \<Rightarrow> 
                             ('a, 'm, 'k::finite) fixed_mat \<Rightarrow> 
                             ('a, 'n, 'k) fixed_mat" is
  "\<lambda>A B. mat (CARD('n)) (CARD('k)) (\<lambda>(i,j). 
    sum_list (map (\<lambda>l. A $$ (i,l) * B $$ (l,j)) [0..<CARD('m)]))"
  using mat_carrier by blast

instance ..

end

instantiation fixed_mat :: ("{real_normed_vector, times, one, real_algebra_1}", finite, finite) real_normed_vector
begin

definition zero_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat" where
  "zero_fixed_mat = fixed_mat_zero"

definition plus_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "plus_fixed_mat = fixed_mat_add"

definition minus_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "minus_fixed_mat A B = fixed_mat_add A (fixed_mat_smult (-1) B)"

definition uminus_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "uminus_fixed_mat A = fixed_mat_smult (-1) A"

definition scaleR_fixed_mat :: "real \<Rightarrow> ('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "scaleR_fixed_mat r A = fixed_mat_smult (of_real r) A"

definition norm_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> real" where
  "norm_fixed_mat A = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index A i j))^2)"

definition dist_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat \<Rightarrow> real" where
  "dist_fixed_mat A B = norm (A - B)"

definition uniformity_fixed_mat :: "(('a::{real_algebra_1,real_normed_vector}, 'nr::finite, 'nc::finite) fixed_mat \<times> ('a, 'nr, 'nc) fixed_mat) filter" where
  "uniformity_fixed_mat = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})"

definition open_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat set \<Rightarrow> bool" where
  "open_fixed_mat S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

(* Define the sign function for fixed matrices *)
definition sgn_fixed_mat :: "('a, 'nr::finite, 'nc::finite) fixed_mat \<Rightarrow> ('a, 'nr, 'nc) fixed_mat" where
  "sgn_fixed_mat A = (if A = 0 then 0 
                      else scaleR (1 / norm A) A)"

lemma uminus_add: "- (A :: ('a, 'nr::finite, 'nc::finite) fixed_mat) + A = 0"
proof - 
  have a0: "Rep_fixed_mat A \<in> carrier_mat CARD('nr) CARD('nc)" 
    using Rep_fixed_mat by blast
  have a1: "- (Rep_fixed_mat A) + (Rep_fixed_mat A) = 0\<^sub>m CARD('nr) CARD('nc)"
    using uminus_l_inv_mat[of "Rep_fixed_mat A" "CARD('nr)" "CARD('nc)"] a0 by simp
  have a2: "- A + A = Abs_fixed_mat (Rep_fixed_mat (- A + A))"
    by (simp add: Rep_fixed_mat_inverse)
  have a3: "Rep_fixed_mat (- A + A) = Rep_fixed_mat (- A) + Rep_fixed_mat A"
    using Rep_fixed_mat_add[of "-A" A] unfolding fixed_mat_add_def 
    by (simp add: plus_fixed_mat_def)
  have a4: "Rep_fixed_mat (- A) = - Rep_fixed_mat A"
    using  fixed_mat_smult.rep_eq[of "-1" A]
    unfolding uminus_fixed_mat_def fixed_mat_smult_def by auto
  have a5: "Abs_fixed_mat (0\<^sub>m CARD('nr) CARD('nc)) = Abs_fixed_mat (Rep_fixed_mat (fixed_mat_zero:: ('a, 'nr::finite, 'nc::finite) fixed_mat))"
    using Rep_fixed_mat_zero  unfolding fixed_mat_zero_def
    by metis
  have a6: "Abs_fixed_mat (Rep_fixed_mat (fixed_mat_zero:: ('a, 'nr::finite, 'nc::finite) fixed_mat)) = 
            ( fixed_mat_zero::('a, 'nr::finite, 'nc::finite) fixed_mat)"
    using Rep_fixed_mat_inverse[of "( fixed_mat_zero::('a, 'nr::finite, 'nc::finite) fixed_mat)"] by simp 
  have a7: "( fixed_mat_zero::('a, 'nr::finite, 'nc::finite) fixed_mat) = 0"
    unfolding zero_fixed_mat_def
    by simp
  show ?thesis  using a0 a1 a2 a3 a4 a5 a6 a7 
    by (smt (verit, best)) 
qed

lemma smult:  "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R (x:: ('a, 'nr::finite, 'nc::finite) fixed_mat)"
proof -
  have b8: "a *\<^sub>R b *\<^sub>R x = scaleR a (scaleR b x)" 
    by (simp add: scaleR_fixed_mat_def)
  also have b7: "... = fixed_mat_smult (of_real a) (fixed_mat_smult (of_real b) x)"
    by (simp add: scaleR_fixed_mat_def) 
  also have b6: "... = Abs_fixed_mat (of_real a \<cdot>\<^sub>m Rep_fixed_mat (fixed_mat_smult (of_real b) x))"
    by (simp add: fixed_mat_smult.rep_eq fixed_mat_smult_def)
  also have b5: "... = Abs_fixed_mat (of_real a \<cdot>\<^sub>m (of_real b \<cdot>\<^sub>m Rep_fixed_mat x))"
    by (simp add: fixed_mat_smult.rep_eq)
  also have b4: "... = Abs_fixed_mat ((of_real a * of_real b) \<cdot>\<^sub>m Rep_fixed_mat x)"
    using  mult_smult_assoc_mat Rep_fixed_mat 
   proof -
  have "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow>
              (of_real a \<cdot>\<^sub>m (of_real b \<cdot>\<^sub>m Rep_fixed_mat x)) $$ (i, j) = 
              ((of_real a * of_real b) \<cdot>\<^sub>m Rep_fixed_mat x) $$ (i, j)"
  proof -
    have a0: "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> 
          (of_real a \<cdot>\<^sub>m (of_real b \<cdot>\<^sub>m Rep_fixed_mat x)) $$ (i, j) = 
          of_real a * ((of_real b \<cdot>\<^sub>m Rep_fixed_mat x) $$ (i, j))"
      unfolding smult_mat_def 
      by (metis Rep_fixed_mat carrier_matD(1) carrier_matD(2) fixed_mat_smult.rep_eq index_smult_mat(1) smult_mat_def)
      
    have a1: "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow>  
              of_real a * ((of_real b \<cdot>\<^sub>m Rep_fixed_mat x) $$ (i, j)) = 
              of_real a * (of_real b * (Rep_fixed_mat x $$ (i, j)))"
      unfolding smult_mat_def index_mat_def using index_smult_mat(1)
      by (metis Rep_fixed_mat carrier_matD(1) carrier_matD(2) index_mat_def smult_mat_def)
    have a2: "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow>  
          of_real a * (of_real b * (Rep_fixed_mat x $$ (i, j)))
           = (of_real a * of_real b) * (Rep_fixed_mat x $$ (i, j))"
      by (simp add: mult.assoc)     
    have a3: " \<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow>  
        (of_real a * of_real b) * (Rep_fixed_mat x $$ (i, j))
      = ((of_real a * of_real b) \<cdot>\<^sub>m Rep_fixed_mat x) $$ (i, j)"
      unfolding smult_mat_def index_mat_def using index_smult_mat(1)
      by (metis Rep_fixed_mat carrier_matD(1) carrier_matD(2) index_mat_def smult_mat_def)     
    show ?thesis using a0 a1 a2 a3 by presburger
  qed
  hence "of_real a \<cdot>\<^sub>m (of_real b \<cdot>\<^sub>m Rep_fixed_mat x) = 
         (of_real a * of_real b) \<cdot>\<^sub>m Rep_fixed_mat x"
    using mat_eq_iff Rep_fixed_mat unfolding carrier_mat_def 
    by (smt (verit, best) Rep_fixed_mat carrier_matD(1) carrier_matD(2) index_smult_mat(2) index_smult_mat(3))
  thus ?thesis by simp
qed
  also have b1: "... = Abs_fixed_mat (of_real (a * b) \<cdot>\<^sub>m Rep_fixed_mat x)"
    by simp
  also have b0: "... = fixed_mat_smult (of_real (a * b)) x"
    by (simp add: fixed_mat_smult.rep_eq fixed_mat_smult_def)
  also have b3: "... = scaleR(a * b) x"
    by (simp add: scaleR_fixed_mat_def)
  also have b2: "... = (a * b) *\<^sub>R x"
    by (simp add: scaleR_fixed_mat_def)
   show ?thesis 
     using b0 b1 b2 b3 b4 b5 b6 b7 b8
     by argo
 qed

lemma scaleR: " 1 *\<^sub>R x =( x:: ('a, 'nr::finite, 'nc::finite) fixed_mat)"
proof -
  have a0: "1 *\<^sub>R x = scaleR 1 x"
    by (simp add: scaleR_fixed_mat_def)
  have a1: "... = fixed_mat_smult (of_real 1) x"
    by (simp add: scaleR_fixed_mat_def)
  have a2: "... = fixed_mat_smult 1 x"
    by simp
  have a3: "... = x"
proof -
  have "fixed_mat_smult 1 x = Abs_fixed_mat (smult_mat 1 (Rep_fixed_mat x))"
    by (simp add: fixed_mat_smult_def)
  also have "smult_mat 1 (Rep_fixed_mat x) = Rep_fixed_mat x"
  proof -
    have "\<forall>i j. i < dim_row (Rep_fixed_mat x) \<and> j < dim_col (Rep_fixed_mat x) \<longrightarrow>
           (smult_mat 1 (Rep_fixed_mat x)) $$ (i, j) = Rep_fixed_mat x $$ (i, j)"
      by (auto simp add: smult_mat_def)
    thus ?thesis by auto
  qed
  hence "Abs_fixed_mat (smult_mat 1 (Rep_fixed_mat x)) = Abs_fixed_mat (Rep_fixed_mat x)" by simp
  also have "... = x" by (rule Rep_fixed_mat_inverse)
  finally show "fixed_mat_smult 1 x = x" .
qed
  show "1 *\<^sub>R x = x"
    using a0 a1 a2 a3 by simp
qed


lemma scaleR_0: " 0 *\<^sub>R x =( 0:: ('a, 'nr::finite, 'nc::finite) fixed_mat)"
proof -
  have a0: "0 *\<^sub>R x = scaleR 0 x"
    by (simp add: scaleR_fixed_mat_def)
  have a1: "... = fixed_mat_smult (of_real 0) x"
    by (simp add: scaleR_fixed_mat_def)
  have a2: "... = fixed_mat_smult 0 x"
    by simp
  have a3: "... = 0"
proof -
  have "fixed_mat_smult 0 x = Abs_fixed_mat (smult_mat 0 (Rep_fixed_mat x))"
    by (simp add: fixed_mat_smult_def)
  also have "smult_mat 0 (Rep_fixed_mat x) = (Rep_fixed_mat ( 0:: ('a, 'nr::finite, 'nc::finite) fixed_mat))"
   proof -
      have "0 \<cdot>\<^sub>m Rep_fixed_mat x = 0\<^sub>m (CARD('nr)) (CARD('nc))"
        proof -
          have "\<forall>i j. i < dim_row (Rep_fixed_mat x) \<and> j < dim_col (Rep_fixed_mat x) \<longrightarrow>
                (0 \<cdot>\<^sub>m Rep_fixed_mat x) $$ (i,j) = 0"
            unfolding smult_mat_def by auto
          then have "0 \<cdot>\<^sub>m Rep_fixed_mat x = Matrix.mat CARD('nr) CARD('nc) (\<lambda>ij. 0)"
           using Rep_fixed_mat[of x] by auto
          moreover have "Matrix.mat CARD('nr) CARD('nc) (\<lambda>ij. 0) = 0\<^sub>m (CARD('nr)) (CARD('nc))"
            by (simp add: zero_mat_def)
          ultimately show ?thesis by simp
        qed
      also have "... = Rep_fixed_mat (fixed_mat_zero:: ('a, 'nr::finite, 'nc::finite) fixed_mat)"
        apply(subst fixed_mat_zero_def) 
        by (metis Rep_fixed_mat_inverse Rep_fixed_mat_zero)
      finally show ?thesis unfolding zero_fixed_mat_def by blast
    qed 
  hence "Abs_fixed_mat (smult_mat 0 (Rep_fixed_mat x)) = Abs_fixed_mat (Rep_fixed_mat ( 0:: ('a, 'nr::finite, 'nc::finite) fixed_mat))" by simp
  also have "... = ( 0:: ('a, 'nr::finite, 'nc::finite) fixed_mat)" 
    using Rep_fixed_mat_inverse by auto
  finally show "fixed_mat_smult 0 x = ( 0:: ('a, 'nr::finite, 'nc::finite) fixed_mat)" .
qed
  show "0 *\<^sub>R x = 0"
    using a0 a1 a2 a3 by simp
qed


lemma norm_0:  "norm (0::('a, 'nr::finite, 'nc::finite) fixed_mat) = 0"
proof -
  have a0: "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}.
              fixed_mat_index (0::('a, 'nr, 'nc) fixed_mat) i j = 0"
    unfolding zero_fixed_mat_def fixed_mat_zero_def zero_mat_def fixed_mat_index_def 
    by (simp add: Abs_fixed_mat_inverse)
  have "norm (0::('a, 'nr, 'nc) fixed_mat) =
        sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}.
              (norm (fixed_mat_index (0::('a, 'nr, 'nc) fixed_mat) i j))^2)"
    by (simp add: norm_fixed_mat_def)
  also have "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. 0^2)"
    using a0 by simp
  also have "... = sqrt 0" by simp
  finally show ?thesis by simp
qed

lemma sgn: "sgn x = inverse (norm x) *\<^sub>R (x::('a, 'nr::finite, 'nc::finite) fixed_mat)"
proof -
  have "sgn x = (if x = 0 then 0 else scaleR (1 / norm x) x)"
    by (simp add: sgn_fixed_mat_def)
  show "sgn x = inverse (norm x) *\<^sub>R x"
  proof (cases "x = 0")
    case True
    have "inverse (norm x) *\<^sub>R x = inverse (norm (0::('a, 'nr::finite, 'nc::finite) fixed_mat)) *\<^sub>R 0" 
      using True by simp 
    also have "... = inverse 0 *\<^sub>R 0"
      using norm_0 using arg_cong by fast
    also have "... = 0" 
      using scaleR_0 by simp
    finally have "inverse (norm x) *\<^sub>R x = 0" .
    with True show ?thesis 
      by (simp add: sgn_fixed_mat_def)
  next
    case False
    have b0: "sgn x = scaleR (1 / norm x) x"
      using False by (simp add: sgn_fixed_mat_def)
    have b1: "... = scaleR (inverse (norm x)) x"
      by (simp add: divide_inverse)
    have b2: "... = inverse (norm x) *\<^sub>R x"
      by (simp add: scaleR_fixed_mat_def)
    show ?thesis using b0 b1 b2 by simp
  qed
qed

lemma norm_eq_zero_iff: "(norm x = (0::real)) = (x = (0::('a, 'nr::finite, 'nc::finite) fixed_mat))"
proof
  assume "norm x = 0"
  have norm_def: "norm x = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2)"
    by (simp add: norm_fixed_mat_def)
  with \<open>norm x = 0\<close> have b0: "sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) = 0"
    by simp
  then have b1: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) = 0"
    by simp
  then have b2: "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 = 0"
  proof -
    have non_neg: "\<And>i j. (norm (fixed_mat_index x i j))\<^sup>2 \<ge> 0"
      by (simp add: power2_eq_square)
    {
      fix i j
      assume i_range: "i \<in> {0..<CARD('nr)}"
      assume j_range: "j \<in> {0..<CARD('nc)}"
      have "(norm (fixed_mat_index x i j))\<^sup>2 \<le> (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index x i j))\<^sup>2)"
      proof -
        have a0: "(norm (fixed_mat_index x i j))\<^sup>2 = (\<Sum>j' = 0..<CARD('nc). if j' = j then (norm (fixed_mat_index x i j))\<^sup>2 else 0)"
          using j_range by (simp add: sum.delta)
        also have "... \<le> (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2)"
        proof (rule sum_mono)
          fix j'
          assume "j' \<in> {0..<CARD('nc)}"
          show "(if j' = j then (norm (fixed_mat_index x i j))\<^sup>2 else 0) \<le> (norm (fixed_mat_index x i j'))\<^sup>2"
          proof (cases "j' = j")
            case True
            then show ?thesis by simp
          next
            case False
            have "0 \<le> (norm (fixed_mat_index x i j'))\<^sup>2" by (simp add: non_neg)
            show ?thesis by simp
          qed
        qed
         have a1: "... = (\<Sum>i' = 0..<CARD('nr). \<Sum>j' = 0..<CARD('nc). 
                      if i' = i then (norm (fixed_mat_index x i j'))\<^sup>2 else 0)"
           using i_range sum.delta[of "{0..<CARD('nr)}" i "\<lambda> j' . (norm (fixed_mat_index x i j'))\<^sup>2" ]
           proof -
            have "(\<Sum>i' = 0..<CARD('nr). \<Sum>j' = 0..<CARD('nc). if i' = i then (norm (fixed_mat_index x i j'))\<^sup>2 else 0) = 
                  (\<Sum>i' = 0..<CARD('nr). if i' = i then (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2) else 0)"
              by (simp add: sum.swap)
            also have "... = (if i \<in> {0..<CARD('nr)} then (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2) else 0)"
              by simp
            also have "... = (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2)"
              using i_range by simp
            finally show "(\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2) = 
                          (\<Sum>i' = 0..<CARD('nr). \<Sum>j' = 0..<CARD('nc). if i' = i then (norm (fixed_mat_index x i j'))\<^sup>2 else 0)"
              by simp
          qed
        have a2: "... \<le> (\<Sum>i' = 0..<CARD('nr). \<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i' j'))\<^sup>2)"
        proof (rule sum_mono)
          fix i'
          assume "i' \<in> {0..<CARD('nr)}"
          show "(\<Sum>j' = 0..<CARD('nc). if i' = i then (norm (fixed_mat_index x i j'))\<^sup>2 else 0) \<le>
                (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i' j'))\<^sup>2)"
          proof (cases "i' = i")
            case True
            then show ?thesis by simp
          next
            case False
            have c0: "(\<Sum>j' = 0..<CARD('nc). if i' = i then (norm (fixed_mat_index x i j'))\<^sup>2 else 0) = 0"
              using False by simp
            have c1: "... \<le> (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i' j'))\<^sup>2)"
              by (simp add: sum_nonneg non_neg)
            show ?thesis using c0 c1 by simp
          qed
        qed
       show ?thesis using a0 a1 a2 
         using \<open>(\<Sum>j' = 0..<CARD('nc). if j' = j then (norm (fixed_mat_index x i j))\<^sup>2 else 0) \<le> (\<Sum>j' = 0..<CARD('nc). (norm (fixed_mat_index x i j'))\<^sup>2)\<close> by linarith 
     qed
      with non_neg[of i j] have "(norm (fixed_mat_index x i j))\<^sup>2 = 0" 
        using \<open>(\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index x i j))\<^sup>2) = 0\<close> by linarith 
    }
    thus b3: "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))\<^sup>2 = 0"
      by blast
  qed
  then have b4: "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. norm (fixed_mat_index x i j) = 0"
    by (simp add: power2_eq_iff)
  then have b5: "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. fixed_mat_index x i j = 0"
    by simp
  then have "x = 0"
  proof -
    have "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> fixed_mat_index x i j = 0"
      using \<open>\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. fixed_mat_index x i j = 0\<close> 
      by auto
    have "x = Abs_fixed_mat (Rep_fixed_mat x)" 
      by (simp add: Rep_fixed_mat_inverse)
    also have "Rep_fixed_mat x = Matrix.mat CARD('nr) CARD('nc) (\<lambda>(i,j). fixed_mat_index x i j)"
     using Rep_fixed_mat unfolding fixed_mat_index_def carrier_mat_def 
     by force 
    also have "... = Matrix.mat CARD('nr) CARD('nc) (\<lambda>(i,j). 0)"
      using \<open>\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> fixed_mat_index x i j = 0\<close>
      by (simp add: mat_eq_iff)
    also have "... = 0\<^sub>m CARD('nr) CARD('nc)"
      unfolding zero_mat_def by auto
    also have "Abs_fixed_mat (0\<^sub>m CARD('nr) CARD('nc)) = (fixed_mat_zero::('a, 'nr::finite, 'nc::finite) fixed_mat)"
      unfolding fixed_mat_zero_def by simp
    also have "fixed_mat_zero = 0"
      using zero_fixed_mat_def by metis
     show "x = 0" 
       by (simp add: calculation zero_fixed_mat_def)
   qed
  thus "x = 0" by simp
next
  assume "x = 0"
  have norm_def: "norm x = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2)"
    by (simp add: norm_fixed_mat_def)
  from \<open>x = 0\<close> have "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. fixed_mat_index x i j = 0"
     proof -
    have "\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> fixed_mat_index x i j = 0" 
      by (simp add: NN_Lipschitz_Continuous.zero_fixed_mat_def \<open>(x::('a, 'nr, 'nc) fixed_mat) = (0::('a, 'nr, 'nc) fixed_mat)\<close> fixed_mat_index.rep_eq)
    have "x = Abs_fixed_mat (Rep_fixed_mat x)" 
      by (simp add: Rep_fixed_mat_inverse)
    also have "Rep_fixed_mat x = Matrix.mat CARD('nr) CARD('nc) (\<lambda>(i,j). fixed_mat_index x i j)"
     using Rep_fixed_mat unfolding fixed_mat_index_def carrier_mat_def 
     by force 
    also have "... = Matrix.mat CARD('nr) CARD('nc) (\<lambda>(i,j). 0)"
      using \<open>\<forall>i j. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> fixed_mat_index x i j = 0\<close>
      by (simp add: mat_eq_iff)
    also have "... = 0\<^sub>m CARD('nr) CARD('nc)"
      unfolding zero_mat_def by auto
    also have "Abs_fixed_mat (0\<^sub>m CARD('nr) CARD('nc)) = (fixed_mat_zero::('a, 'nr::finite, 'nc::finite) fixed_mat)"
      unfolding fixed_mat_zero_def by simp
    also have "fixed_mat_zero = 0"
      using zero_fixed_mat_def by metis
    show "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. fixed_mat_index x i j = 0"
       using \<open>\<forall>(i::nat) j::nat. i < CARD('nr) \<and> j < CARD('nc) \<longrightarrow> fixed_mat_index (x::('a, 'nr, 'nc) fixed_mat) i j = (0::'a)\<close> atLeast0LessThan by blast
   qed
  then have "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. norm (fixed_mat_index x i j) = 0"
    by simp
  then have "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 = 0"
    by simp
  then have "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) = 0"
    by simp
  then have "sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) = 0"
    by simp
  with norm_def show "norm x = 0"
    by simp
qed



lemma sum_tuple: \<open>(\<Sum> i < n. \<Sum> j < m . P i j) = (\<Sum>p\<in> {(i,j). i < n \<and> j < m}.  P (fst p) (snd p))\<close>
  apply(subst prod.split_sel, simp)
  apply(subst sum.cartesian_product')
  by(simp, metis lessThan_def)
 

lemma triangle_inequality: "norm ((x::('a, 'nr::finite, 'nc::finite) fixed_mat) + y::('a, 'nr::finite, 'nc::finite) fixed_mat) \<le> norm x + norm y"
proof -
  have norm_def: "norm z = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index z i j))^2)" 
    for z :: "('a, 'nr::finite, 'nc::finite) fixed_mat"
    by (simp add: norm_fixed_mat_def)
  have component_add: "fixed_mat_index (x + y) i j = fixed_mat_index x i j + fixed_mat_index y i j"
    if "i \<in> {0..<CARD('nr)}" "j \<in> {0..<CARD('nc)}" for i j
    proof -
      have "fixed_mat_index (x + y) i j = Rep_fixed_mat (x + y) $$ (i, j)"
        by (simp add: fixed_mat_index_def)
      also have "Rep_fixed_mat (x + y) $$ (i, j) = Rep_fixed_mat ((Abs_fixed_mat (Rep_fixed_mat x + Rep_fixed_mat y)::('a, 'nr::finite, 'nc::finite) fixed_mat)) $$ (i::nat, j)"
        unfolding plus_fixed_mat_def fixed_mat_add_def plus_mat_def by blast
      have "Rep_fixed_mat x \<in> carrier_mat CARD('nr) CARD('nc)"
        by (simp add: Rep_fixed_mat) 
      moreover have "Rep_fixed_mat y \<in> carrier_mat CARD('nr) CARD('nc)"
        by (simp add: Rep_fixed_mat)
      ultimately have a0: "Rep_fixed_mat x + Rep_fixed_mat y \<in> carrier_mat CARD('nr) CARD('nc)"
        by auto   
      hence "Rep_fixed_mat (Abs_fixed_mat (Rep_fixed_mat x + Rep_fixed_mat y)::('a, 'nr::finite, 'nc::finite) fixed_mat) = Rep_fixed_mat x + Rep_fixed_mat y"
         using Abs_fixed_mat_inverse[of "Rep_fixed_mat x + Rep_fixed_mat y"] by blast  
      hence "Rep_fixed_mat ((Abs_fixed_mat (Rep_fixed_mat x + Rep_fixed_mat y)::('a, 'nr::finite, 'nc::finite) fixed_mat)) $$ (i, j) = 
             (Rep_fixed_mat x + Rep_fixed_mat y) $$ (i, j)"
        by metis
      also have "... = Rep_fixed_mat x $$ (i, j) + Rep_fixed_mat y $$ (i, j)"
        proof -
          have add_def: 
            "Rep_fixed_mat (fixed_mat_add x y) = Rep_fixed_mat x + Rep_fixed_mat y"
            using  fixed_mat_add_def Abs_fixed_mat_inverse by auto
          have index_def: 
            "(Rep_fixed_mat x + Rep_fixed_mat y) $$ (i, j) = (Rep_fixed_mat x) $$ (i, j) + (Rep_fixed_mat y) $$ (i, j)"
          proof - 
             have carrier_x: "Rep_fixed_mat x \<in> carrier_mat CARD('nr) CARD('nc)"
               by (simp add: Rep_fixed_mat)
             have carrier_y: "Rep_fixed_mat y \<in> carrier_mat CARD('nr) CARD('nc)"
               by (simp add: Rep_fixed_mat)
             have add_def: "Rep_fixed_mat x + Rep_fixed_mat y = 
                 mat CARD('nr) CARD('nc) (\<lambda>(i', j'). Rep_fixed_mat x $$ (i', j') + Rep_fixed_mat y $$ (i', j'))"
               using carrier_x carrier_y unfolding plus_mat_def mat_def carrier_mat_def 
               by (simp add: cond_case_prod_eta)
            have "(Rep_fixed_mat x + Rep_fixed_mat y) $$ (i, j) = 
                  mat CARD('nr) CARD('nc) (\<lambda>(i', j'). Rep_fixed_mat x $$ (i', j') + Rep_fixed_mat y $$ (i', j')) $$ (i, j)"
               by (simp add: add_def)
            moreover have "mat CARD('nr) CARD('nc) (\<lambda>(i', j'). Rep_fixed_mat x $$ (i', j') + Rep_fixed_mat y $$ (i', j')) $$ (i, j) =
                 (\<lambda>(i', j'). Rep_fixed_mat x $$ (i', j') + Rep_fixed_mat y $$ (i', j')) (i, j)"
              using Rep_fixed_mat[of x] Rep_fixed_mat[of y] unfolding index_mat_def carrier_mat_def               
                 by (metis (no_types, lifting) atLeastLessThan_iff index_mat(1) index_mat_def that(1) that(2))
             moreover have "(\<lambda>(i', j'). Rep_fixed_mat x $$ (i', j') + Rep_fixed_mat y $$ (i', j')) (i, j) =
                 Rep_fixed_mat x $$ (i, j) + Rep_fixed_mat y $$ (i, j)"
               by simp
            show ?thesis 
              by (simp add: calculation(2) local.add_def)
          qed
          show ?thesis
            using add_def index_def
            by simp
        qed
      also have "... = fixed_mat_index x i j + fixed_mat_index y i j"
        by (simp add: fixed_mat_index_def)
      finally show "fixed_mat_index (x + y) i j = fixed_mat_index x i j + fixed_mat_index y i j" 
        by (simp add: fixed_mat_add_def fixed_mat_index.rep_eq plus_fixed_mat_def)
    qed
  have "norm (fixed_mat_index (x + y) i j) \<le> norm (fixed_mat_index x i j) + norm (fixed_mat_index y i j)"
     if "i \<in> {0..<CARD('nr)}" "j \<in> {0..<CARD('nc)}" for i j
    using component_add  norm_triangle_ineq that by auto
  then have component_ineq: "(norm (fixed_mat_index (x + y) i j))^2 \<le> 
        (norm (fixed_mat_index x i j) + norm (fixed_mat_index y i j))^2"
     if "i \<in> {0..<CARD('nr)}" "j \<in> {0..<CARD('nc)}" for i j
    using that by simp
  have expand_square: "(a + b)^2 = a^2 + 2*a*b + b^2" for a b :: real
    by (simp add: power2_eq_square algebra_simps)
  have component_ineq2: "(norm (fixed_mat_index (x + y) i j))^2 \<le> 
        (norm (fixed_mat_index x i j))^2 + 2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j)) + 
        (norm (fixed_mat_index y i j))^2"
     if "i \<in> {0..<CARD('nr)}" "j \<in> {0..<CARD('nc)}" for i j
    using component_ineq expand_square that by simp
 have sum_ineq: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. ((norm (fixed_mat_index x i j))^2) + 
        2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j)) + 
        (norm (fixed_mat_index y i j))^2)"
  proof -
    have "\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}.
          (norm (fixed_mat_index (x + y) i j))^2 \<le>
          (norm (fixed_mat_index x i j))^2 + 2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j)) + 
          (norm (fixed_mat_index y i j))^2"
      using component_ineq2 by blast
    have inner_sum_mono: "\<forall>i\<in>{0..<CARD('nr)}. 
            (\<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
            (\<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 + 
             2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j) + 
             (norm (fixed_mat_index y i j))^2)"
    proof
      fix i
      assume "i \<in> {0..<CARD('nr)}"
      have "\<forall>j\<in>{0..<CARD('nc)}.
            (norm (fixed_mat_index (x + y) i j))^2 \<le>
            (norm (fixed_mat_index x i j))^2 + 
            2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j) + 
            (norm (fixed_mat_index y i j))^2"
        using `i \<in> {0..<CARD('nr)}` component_ineq  
        using component_ineq2 by blast 
      thus "(\<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
            (\<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 + 
             2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j) + 
             (norm (fixed_mat_index y i j))^2)"
        using sum_mono by fast
    qed
    have "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
          (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 + 
           2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j) + 
           (norm (fixed_mat_index y i j))^2)"
      using inner_sum_mono  sum_mono by fast   
    thus ?thesis .
  qed
  have sum_distribute: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2 + 
        2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j)) + 
        (norm (fixed_mat_index y i j))^2) =
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) +
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. 2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j))) +
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2)"
    by (simp add: sum.distrib)
  have cs: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. 2*(norm (fixed_mat_index x i j))*(norm (fixed_mat_index y i j))) \<le>
        2 * sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) * 
        sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2)"
    proof -
      let ?x_norm_ij = "\<lambda>i j. norm (fixed_mat_index x i j)"
      let ?y_norm_ij = "\<lambda>i j. norm (fixed_mat_index y i j)"
      let ?sum_xy = "\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). ?x_norm_ij i j * ?y_norm_ij i j"
      let ?sum_x2 = "\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (?x_norm_ij i j)^2"
      let ?sum_y2 = "\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (?y_norm_ij i j)^2"
      have step1: "(\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). 2 * ?x_norm_ij i j * ?y_norm_ij i j) = 
                   2 * (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). ?x_norm_ij i j * ?y_norm_ij i j)"
        using sum_distrib_left[of 2 _ "{0..<CARD('nr)}" ] 
        proof -
          let ?g = "\<lambda>i. \<Sum>j = 0..<CARD('nc). norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j)"
          have "2 * (\<Sum>i = 0..<CARD('nr). ?g i) = (\<Sum>i = 0..<CARD('nr). 2 * ?g i)"
            using sum_distrib_left[of 2 ?g "{0..<CARD('nr)}"] by blast
          have "(\<Sum>i = 0..<CARD('nr). 2 * (\<Sum>j = 0..<CARD('nc). norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j))) = 
                (\<Sum>i = 0..<CARD('nr). (\<Sum>j = 0..<CARD('nc). 2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j)))"
          proof -
            have "\<And>i. 2 * (\<Sum>j = 0..<CARD('nc). norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j)) = 
                      (\<Sum>j = 0..<CARD('nc). 2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j))"
              using sum_distrib_left[of 2 _ "{0..<CARD('nc)}"] 
              by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux more_arith_simps(11)) 
            thus ?thesis by simp
          qed
          show ?thesis using \<open>2 * (\<Sum>i = 0..<CARD('nr). ?g i) = (\<Sum>i = 0..<CARD('nr). 2 * ?g i)\<close> 
                         and \<open>(\<Sum>i = 0..<CARD('nr). 2 * (\<Sum>j = 0..<CARD('nc). norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j))) = 
                              (\<Sum>i = 0..<CARD('nr). (\<Sum>j = 0..<CARD('nc). 2 * norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j)))\<close>
            by simp
        qed
        have cs_ineq: "?sum_xy^2 \<le> ?sum_x2 * ?sum_y2"
        proof -
          let ?all_indices = "{(i, j). i < CARD('nr) \<and> j < CARD('nc)}"
          let ?x_vec = "\<lambda>(i, j). ?x_norm_ij i j"
          let ?y_vec = "\<lambda>(i, j). ?y_norm_ij i j"
          have rewrite_sum_xy: "?sum_xy = (\<Sum>p \<in> ?all_indices. ?x_vec p * ?y_vec p)"
            apply (subst case_prod_beta)+
            apply(subst sum_tuple[of "\<lambda> i j . norm (fixed_mat_index x i j) * norm (fixed_mat_index y i j)" "CARD('nc)" "CARD('nr)", symmetric]) 
            using atLeast0LessThan by presburger 
          have rewrite_sum_x2: "?sum_x2 = (\<Sum>p \<in> ?all_indices. (?x_vec p)^2)"
            apply (subst case_prod_beta)
            apply(subst sum_tuple[of "\<lambda> i j . (norm (fixed_mat_index x i j))\<^sup>2" "CARD('nc)" "CARD('nr)", symmetric])
            using atLeast0LessThan by presburger 
          have rewrite_sum_y2: "?sum_y2 = (\<Sum>p \<in> ?all_indices. (?y_vec p)^2)"
            apply (subst case_prod_beta)
            using sum_tuple[of "\<lambda> i j . (norm (fixed_mat_index y i j))\<^sup>2" "CARD('nc)" "CARD('nr)", symmetric]
            using atLeast0LessThan by presburger 
          have "(\<Sum>p \<in> ?all_indices. ?x_vec p * ?y_vec p)^2 \<le> 
                (\<Sum>p \<in> ?all_indices. (?x_vec p)^2) * (\<Sum>p \<in> ?all_indices. (?y_vec p)^2)"
            using Cauchy_Schwarz_ineq_sum by blast
          with rewrite_sum_xy rewrite_sum_x2 rewrite_sum_y2 show ?thesis by simp
        qed
      have "?sum_xy \<le> sqrt (?sum_x2 * ?sum_y2)"
        using  real_le_rsqrt  cs_ineq by blast
      also have "sqrt (?sum_x2 * ?sum_y2) = sqrt ?sum_x2 * sqrt ?sum_y2"
        by (rule real_sqrt_mult)
      finally have "2 * ?sum_xy \<le> 2 * sqrt ?sum_x2 * sqrt ?sum_y2"
        using  mult_right_mono by argo 
      with step1 show ?thesis by simp
    qed 
   have norm_square_ineq: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) +
        2 * sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) * 
        sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2) +
        (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2)"
    using sum_ineq sum_distribute cs by argo 
  have norm_square_ineq2: "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
        (norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2"
  proof -
    have d0: "(sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index x i j))\<^sup>2))\<^sup>2 = 
          (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index x i j))\<^sup>2) " 
      by (meson real_sqrt_pow2 sum_nonneg zero_le_power2) 
    have d1: "(sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index y i j))\<^sup>2))\<^sup>2 = 
          (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index y i j))\<^sup>2) " 
      by (meson real_sqrt_pow2 sum_nonneg zero_le_power2)
    have "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le>
            (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) +
            2 * sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2) * 
            sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2) +
            (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index y i j))^2)"
      by (rule norm_square_ineq)
     also have "... = (norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2"
        apply(subst norm_def[of x])+ 
        apply(subst d0)
        apply(subst norm_def[of y])+ 
        apply(subst d1)
        using power2_eq_square d0 
        by blast  
      finally show ?thesis .
    qed
  have "(norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2 = (norm x + norm y)^2"
    by (simp add: algebra_simps power2_sum)
  have "(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le> (norm x + norm y)^2"
    using norm_square_ineq2 `(norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2 = (norm x + norm y)^2` by simp
  have "sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le> sqrt((norm x + norm y)^2)"
    using `(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le> (norm x + norm y)^2`
    using real_sqrt_le_mono by blast
  have "sqrt((norm x + norm y)^2) = abs (norm x + norm y)"
    by (simp add: power2_eq_square)
  have "sqrt((norm x + norm y)^2) = norm x + norm y"
  proof -
    have "norm x \<ge> 0" 
      unfolding norm_def 
      by (meson norm_ge_zero real_sqrt_ge_zero sum_nonneg zero_le_power) 
    moreover have "norm y \<ge> 0" 
      unfolding norm_def 
      by (meson norm_ge_zero real_sqrt_ge_zero sum_nonneg zero_le_power) 
    ultimately have "norm x + norm y \<ge> 0" by simp
    hence "abs (norm x + norm y) = norm x + norm y" by simp
    thus ?thesis using `sqrt((norm x + norm y)^2) = abs (norm x + norm y)` by simp
  qed
  have "sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le> norm x + norm y"
    using `sqrt(\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (x + y) i j))^2) \<le> sqrt((norm x + norm y)^2)`
    `sqrt((norm x + norm y)^2) = norm x + norm y` by simp
  thus "norm (x + y) \<le> norm x + norm y"
    using norm_def by simp
qed

lemma norm_scaleR: "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm (x::('a, 'nr::finite, 'nc::finite) fixed_mat)"
proof -
  have a0: "norm (a *\<^sub>R x) = norm (scaleR a x)"
    by (simp add: scaleR_fixed_mat_def)
  have a1: "... = norm (fixed_mat_smult (of_real a) x)"
    by (simp add: scaleR_fixed_mat_def)
  have a2: "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index (fixed_mat_smult (of_real a) x) i j))^2)"
    by (simp add: norm_fixed_mat_def)
  have a3: "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm ((of_real a) * (fixed_mat_index x i j)))^2)"
  proof -
    have element_equality: "\<And>i j. i \<in> {0..<CARD('nr)} \<Longrightarrow> j \<in> {0..<CARD('nc)} \<Longrightarrow>
      map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) (fixed_mat_smult (of_real a) x) i j =
      of_real a * map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) x i j"
    proof -
      fix i j
      assume i_range: "i \<in> {0..<CARD('nr)}"
      assume j_range: "j \<in> {0..<CARD('nc)}"
      have b0: "map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) (fixed_mat_smult (of_real a) x) i j =
            (\<lambda>A i j. A $$ (i, j)) (Rep_fixed_mat (fixed_mat_smult (of_real a) x)) i j"
        by (simp add: map_fun_def)
      have b1: "... = Rep_fixed_mat (fixed_mat_smult (of_real a) x) $$ (i, j)"
        by simp
      have b2: "... = fixed_mat_index (fixed_mat_smult (of_real a) x) i j"
        using i_range j_range by (simp add: fixed_mat_index_def)
      have b3: "... = of_real a * fixed_mat_index x i j"
        using i_range j_range Rep_fixed_mat 
        unfolding fixed_mat_smult_def  smult_mat_def fixed_mat_index_def map_mat_def 
      proof -
        have f1: "\<forall>a f. Rep_fixed_mat (fixed_mat_smult a (f::('a, 'nr, 'nc) fixed_mat)) = a \<cdot>\<^sub>m Rep_fixed_mat f"
          using fixed_mat_smult.rep_eq by blast
        have f2: "j < card (UNIV::'nc set)"
          using atLeastLessThan_iff j_range by blast
        have f3: "i < card (UNIV::'nr set)"
          using atLeastLessThan_iff i_range by blast
        have f4: "\<forall>f a. Abs_fixed_mat (a \<cdot>\<^sub>m Rep_fixed_mat (f::('a, 'nr, 'nc) fixed_mat)) = fixed_mat_smult a f"
          using f1 by (metis (no_types) Rep_fixed_mat_inverse)
        have f5: "\<forall>f. dim_col (Rep_fixed_mat (0::('a, 'nr, 'nc) fixed_mat)) = dim_col (Rep_fixed_mat (f::('a, 'nr, 'nc) fixed_mat))"
          using f1 by (smt (z3) NN_Lipschitz_Continuous.scaleR_fixed_mat_def index_smult_mat(3) scaleR_0)
        then have f6: "dim_col (Rep_fixed_mat (0::('a, 'nr, 'nc) fixed_mat)) = card (UNIV::'nc set)"
          by (smt (z3) Rep_fixed_mat_zero dim_col_mat(1) zero_mat_def)
        have "\<forall>f. card (UNIV::'nr set) = dim_row (Rep_fixed_mat (f::('a, 'nr, 'nc) fixed_mat))"
          using f1 by (smt (z3) NN_Lipschitz_Continuous.scaleR_fixed_mat_def Rep_fixed_mat_zero dim_row_mat(1) index_smult_mat(2) scaleR_0 zero_mat_def)
        then show "map_fun Rep_fixed_mat id (\<lambda>m n na. m $$ (n, na)) (map_fun id (map_fun Rep_fixed_mat Abs_fixed_mat) (\<lambda>a m. Matrix.mat (dim_row m) (dim_col m) (\<lambda>p. a * m $$ p)) (of_real a) x::('a, 'nr, 'nc) fixed_mat) i j = of_real a * map_fun Rep_fixed_mat id (\<lambda>m n na. m $$ (n, na)) x i j"
          using f6 f5 f4 f3 f2 f1 by (simp add: map_mat_def smult_mat_def)
      qed 
      have b4: "... = of_real a * Rep_fixed_mat x $$ (i, j)"
        using i_range j_range by (simp add: fixed_mat_index_def)
      have b5: "... = of_real a * (\<lambda>A i j. A $$ (i, j)) (Rep_fixed_mat x) i j"
        by simp
      have b6:"... = of_real a * map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) x i j"
        by (simp add: map_fun_def)
      show "map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) (fixed_mat_smult (of_real a) x) i j =
                    of_real a * map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) x i j"
        using b0 b1 b2 b3 b4 b5 b6 by argo
    qed
    have c0: "(\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) (fixed_mat_smult (of_real a) x) i j))\<^sup>2) =
          (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (of_real a * map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) x i j))\<^sup>2)"
    proof -
      have "(\<forall>i\<in>{0..<CARD('nr)}. \<forall>j\<in>{0..<CARD('nc)}.
            (norm (map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) (fixed_mat_smult (of_real a) x) i j))\<^sup>2 = 
            (norm (of_real a * map_fun Rep_fixed_mat id (\<lambda>A i j. A $$ (i, j)) x i j))\<^sup>2)"
        using element_equality by auto
      then show ?thesis by simp
    qed
    show ?thesis using c0 
      by (simp add: fixed_mat_index_def)
  qed
  have a4: "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (\<bar>of_real a\<bar> * norm (fixed_mat_index x i j))^2)"     
    by (simp add: of_real_def)
  have a5: "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (\<bar>a\<bar> * norm (fixed_mat_index x i j))^2)"
    by simp
  have a6: "... = sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (\<bar>a\<bar>)^2 * (norm (fixed_mat_index x i j))^2)"
    by (simp add: power_mult_distrib)
  have a7: "... = sqrt ((\<bar>a\<bar>)^2 * (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2))"
    by (simp add: sum_distrib_left)
  have a8: "... = \<bar>a\<bar> * sqrt (\<Sum>i\<in>{0..<CARD('nr)}. \<Sum>j\<in>{0..<CARD('nc)}. (norm (fixed_mat_index x i j))^2)"
    by (simp add: real_sqrt_mult)
  have a9: "... = \<bar>a\<bar> * norm x"
    by (simp add: norm_fixed_mat_def)
  have a10: "... = \<bar>a\<bar> * norm x"
    by simp
  show ?thesis using a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 
    by linarith
qed

instance 
  apply standard
  subgoal 
    using dist_fixed_mat_def by blast
  subgoal 
    unfolding plus_fixed_mat_def fixed_mat_add_def
    using Rep_fixed_mat Rep_fixed_mat_inject  
    by (smt (verit, del_insts) Abs_fixed_mat_inverse add_carrier_mat assoc_add_mat) 
  subgoal 
    unfolding plus_fixed_mat_def fixed_mat_add_def  
    by (metis Rep_fixed_mat comm_add_mat) 
  subgoal 
    unfolding zero_fixed_mat_def fixed_mat_zero_def plus_fixed_mat_def fixed_mat_add_def 
    using  Rep_fixed_mat  
    by (metis Abs_fixed_mat_inverse Rep_fixed_mat_inverse left_add_zero_mat zero_carrier_mat)  
  subgoal using uminus_add by blast
  subgoal unfolding minus_fixed_mat_def uminus_fixed_mat_def plus_fixed_mat_def
    by simp 
  subgoal unfolding scaleR_fixed_mat_def fixed_mat_smult_def smult_mat_def using Rep_fixed_mat 
    by (smt (z3) Rep_fixed_mat_add Rep_fixed_mat_inverse add_smult_distrib_left_mat 
        fixed_mat_smult.rep_eq map_fun_apply plus_fixed_mat_def smult_mat_def) 
  subgoal  unfolding scaleR_fixed_mat_def fixed_mat_smult_def smult_mat_def using Rep_fixed_mat 
    by (smt (z3) Rep_fixed_mat_add Rep_fixed_mat_inverse add_smult_distrib_right_mat eq_id_iff 
        fixed_mat_smult.rep_eq map_fun_apply of_real_hom.hom_add plus_fixed_mat_def smult_mat_def)
  subgoal using smult by blast
  subgoal using scaleR by blast 
  subgoal using sgn by blast  
  subgoal unfolding uniformity_fixed_mat_def by simp 
  subgoal unfolding open_fixed_mat_def by simp
  subgoal using norm_eq_zero_iff by blast
  subgoal using triangle_inequality by blast
  subgoal using norm_scaleR by blast
  done
end

instantiation fixed_vec :: ("{real_normed_vector, times, one, real_algebra_1}", finite) real_normed_vector
begin

lift_definition zero_fixed_vec :: "('a, 'b) fixed_vec" is 
  "zero_vec (CARD('b))" 
  by (simp add: carrier_vecI)

lift_definition plus_fixed_vec :: "('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec" is
  "fixed_vec_add" .

definition scaleR_fixed_vec :: "real \<Rightarrow> ('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec" where
  "scaleR_fixed_vec r A = fixed_vec_smult (of_real r) A"

lift_definition uminus_fixed_vec :: "('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec" is
  "\<lambda> v. smult_vec (-1) v" 
  unfolding smult_vec_def by auto

lift_definition minus_fixed_vec :: "('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec" is
  "\<lambda> v w.  v + (smult_vec (-1) w)" 
  by auto

definition norm_fixed_vec :: "('a, 'b::finite) fixed_vec \<Rightarrow> real" where
  "norm_fixed_vec A = sqrt (\<Sum>i\<in>{0..<CARD('b)} . (norm (fixed_vec_index A i))^2)" 

definition sgn_fixed_vec :: "('a, 'b::finite) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec" where
  "sgn_fixed_vec v = (if v = 0 then 0 else scaleR (1 / norm v) v)"

definition dist_fixed_vec :: "('a, 'b) fixed_vec \<Rightarrow> ('a, 'b) fixed_vec \<Rightarrow> real" where
  "dist_fixed_vec v w = norm (v - w)"

definition uniformity_fixed_vec  :: "( ('a, 'b) fixed_vec \<times>  ('a, 'b) fixed_vec) filter"
  where "uniformity_fixed_vec = (INF e\<in>{0<..}. principal {(x, y). dist x y < e})"

definition open_fixed_vec :: "('a, 'b) fixed_vec set \<Rightarrow> bool" where 
"open_fixed_vec U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"


lemma uminus_add_vec: "- (A :: ('a, 'n::finite) fixed_vec) + A = 0"
proof - 
  have a0: "Rep_fixed_vec A \<in> carrier_vec CARD('n)" 
    using Rep_fixed_vec by blast
  have a1: "- (Rep_fixed_vec A) + (Rep_fixed_vec A) = 0\<^sub>v CARD('n) "
    using uminus_l_inv_vec[of "Rep_fixed_vec A" "CARD('n)" ] a0 by simp
  have a2: "- A + A = Abs_fixed_vec (Rep_fixed_vec (- A + A))"
    by (simp add: Rep_fixed_vec_inverse)
  have a3: "Rep_fixed_vec (- A + A) = Rep_fixed_vec (- A) + Rep_fixed_vec A"
    using Rep_fixed_vec_add[of "-A" A] unfolding fixed_vec_add_def 
    by (simp add: NN_Lipschitz_Continuous.plus_fixed_vec.rep_eq) 
  have a4: "Rep_fixed_vec (- A) = - Rep_fixed_vec A"
    using  fixed_vec_smult.rep_eq[of "-1" A]
    unfolding uminus_fixed_vec_def fixed_vec_smult_def smult_vec_def 
    by (simp add: Matrix.uminus_vec_def NN_Lipschitz_Continuous.uminus_fixed_vec.rep_eq smult_vec_def) 
  have a5: "Abs_fixed_vec (0\<^sub>v CARD('n)) = Abs_fixed_vec (Rep_fixed_vec (fixed_vec_zero:: ('a, 'n) fixed_vec))"
    using Rep_fixed_vec_zero  unfolding fixed_vec_zero_def
    by metis
  have a6: "Abs_fixed_vec (Rep_fixed_vec (fixed_vec_zero:: ('a, 'n::finite) fixed_vec)) = 
            ( fixed_vec_zero::('a, 'n::finite) fixed_vec)"
    using Rep_fixed_vec_inverse[of "( fixed_vec_zero::('a, 'n::finite) fixed_vec)"] by simp 
  have a7: "( fixed_vec_zero::('a, 'n::finite) fixed_vec) = 0"
    unfolding zero_fixed_vec_def fixed_vec_zero_def zero_vec_def
    by (simp add: Matrix.zero_vec_def NN_Lipschitz_Continuous.zero_fixed_vec_def) 
  show ?thesis  using a0 a1 a2 a3 a4 a5 a6 a7 
    by (smt (verit, best)) 
qed


lemma smult_vec:  "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R (x:: ('a, 'n::finite) fixed_vec)"
proof -
  have b8: "a *\<^sub>R b *\<^sub>R x = scaleR a (scaleR b x)" 
    by (simp add: scaleR_fixed_vec_def)
  also have b7: "... = fixed_vec_smult (of_real a) (fixed_vec_smult (of_real b) x)" 
    by (simp add: NN_Lipschitz_Continuous.scaleR_fixed_vec_def)
  also have b6: "... = Abs_fixed_vec (of_real a \<cdot>\<^sub>v Rep_fixed_vec (fixed_vec_smult (of_real b) x))"
    by (simp add: fixed_vec_smult.rep_eq fixed_vec_smult_def)
  also have b5: "... = Abs_fixed_vec (of_real a \<cdot>\<^sub>v (of_real b \<cdot>\<^sub>v Rep_fixed_vec x))"
    by (simp add: fixed_vec_smult.rep_eq)
  also have b4: "... = Abs_fixed_vec((of_real a * of_real b) \<cdot>\<^sub>v Rep_fixed_vec x)"
    using   Rep_fixed_vec 
    by (simp add: smult_smult_assoc)
  also have b1: "... = Abs_fixed_vec (of_real (a * b) \<cdot>\<^sub>v Rep_fixed_vec x)"
    by simp
  also have b0: "... = fixed_vec_smult (of_real (a * b)) x"
    by (simp add: fixed_vec_smult.rep_eq fixed_vec_smult_def)
  also have b3: "... = scaleR(a * b) x"
    by (simp add: NN_Lipschitz_Continuous.scaleR_fixed_vec_def) 
  also have b2: "... = (a * b) *\<^sub>R x"
    by (simp add: scaleR_fixed_vec_def)
   show ?thesis 
     using b0 b1 b2 b3 b4 b5 b6 b7 b8
     by argo
 qed

lemma scaleR_vec: " 1 *\<^sub>R x =( x:: ('a, 'n::finite) fixed_vec)"
proof -
  have a0: "1 *\<^sub>R x = scaleR 1 x"
    by (simp add: scaleR_fixed_vec_def)
  have a1: "... = fixed_vec_smult (of_real 1) x"
    by (metis NN_Lipschitz_Continuous.scaleR_fixed_vec_def)
  have a2: "... = fixed_vec_smult 1 x"
    by simp
  have a3: "... = x"
proof -
  have "fixed_vec_smult 1 x = Abs_fixed_vec (smult_vec 1 (Rep_fixed_vec x))"
    by (simp add: fixed_vec_smult_def)
  also have "smult_vec 1 (Rep_fixed_vec x) = Rep_fixed_vec x"
    by auto

  hence "Abs_fixed_vec (smult_vec 1 (Rep_fixed_vec x)) = Abs_fixed_vec (Rep_fixed_vec x)" by simp
  also have "... = x" by (rule Rep_fixed_vec_inverse)
  finally show "fixed_vec_smult 1 x = x" .
qed
  show "1 *\<^sub>R x = x"
    using a0 a1 a2 a3 by simp
qed


lemma norm_0_vec:  "norm (0::('a, 'n::finite) fixed_vec) = 0"
proof -
  have a0: "\<forall>i\<in>{0..<CARD('n)}.
              fixed_vec_index (0::('a, 'n) fixed_vec) i  = 0"
    unfolding  fixed_vec_index_def 
    by (simp add: NN_Lipschitz_Continuous.zero_fixed_vec.rep_eq)
  have "norm (0::('a, 'n) fixed_vec) =
        sqrt (\<Sum>i\<in>{0..<CARD('n)}. 
              (norm (fixed_vec_index (0::('a, 'n) fixed_vec) i ))^2)"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def a0) 
  also have "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}. 0^2)"
    using a0 by simp
  also have "... = sqrt 0" by simp
  finally show ?thesis by simp
qed


lemma scaleR_0_vec: " 0 *\<^sub>R x =( 0:: ('a, 'n::finite) fixed_vec)"
proof -
  have a0: "0 *\<^sub>R x = scaleR 0 x"
    by (simp add: scaleR_fixed_vec_def)
  have a1: "... = fixed_vec_smult (of_real 0) x"
    by (simp add: NN_Lipschitz_Continuous.scaleR_fixed_vec_def)
  have a2: "... = fixed_vec_smult 0 x"
    by simp
  have a3: "... = 0"
proof -
  have "fixed_vec_smult 0 x = Abs_fixed_vec (smult_vec 0 (Rep_fixed_vec x))"
    by (simp add: fixed_vec_smult_def)
  also have "smult_vec 0 (Rep_fixed_vec x) = (Rep_fixed_vec ( 0:: ('a, 'n::finite) fixed_vec))"
   proof -
      have "0 \<cdot>\<^sub>v Rep_fixed_vec x = 0\<^sub>v (CARD('n))" 
        proof -
          have "\<forall>i . ((i < (dim_vec (Rep_fixed_vec x))) \<longrightarrow>
                (((0 \<cdot>\<^sub>v Rep_fixed_vec x) $ i) = 0))"
            unfolding smult_mat_def by auto
          then have "0 \<cdot>\<^sub>v Rep_fixed_vec x = Matrix.vec CARD('n) (\<lambda>ij. 0)"
           using Rep_fixed_vec[of x] by auto
          moreover have "Matrix.vec CARD('n) (\<lambda>ij. 0) = 0\<^sub>v (CARD('n))"
            by (simp add: zero_vec_def)
          ultimately show ?thesis by simp
        qed
      also have "... = Rep_fixed_vec (fixed_vec_zero:: ('a, 'n::finite) fixed_vec)"
        apply(subst fixed_vec_zero_def) 
        by (metis Rep_fixed_vec_inverse Rep_fixed_vec_zero)
      finally show ?thesis unfolding zero_fixed_vec_def 
        by (simp add: NN_Lipschitz_Continuous.zero_fixed_vec.rep_eq) 
    qed 
  hence "Abs_fixed_vec (smult_vec 0 (Rep_fixed_vec x)) = Abs_fixed_vec (Rep_fixed_vec ( 0:: ('a, 'n::finite) fixed_vec))" by simp
  also have "... = ( 0:: ('a, 'n::finite) fixed_vec)" 
    using Rep_fixed_vec_inverse by auto
  finally show "fixed_vec_smult 0 x = ( 0:: ('a, 'n::finite) fixed_vec)" .
qed
  show "0 *\<^sub>R x = 0"
    using a0 a1 a2 a3 by simp
qed



lemma sgn_vec: "sgn x = inverse (norm x) *\<^sub>R (x::('a, 'n::finite) fixed_vec)"
proof -
  have "sgn x = (if x = 0 then 0 else scaleR (1 / norm x) x)" 
    by (simp add: NN_Lipschitz_Continuous.sgn_fixed_vec_def)
  show "sgn x = inverse (norm x) *\<^sub>R x"
  proof (cases "x = 0")
    case True
    have "inverse (norm x) *\<^sub>R x = inverse (norm (0::('a, 'n::finite) fixed_vec)) *\<^sub>R 0" 
      using True by simp 
    also have "... = inverse 0 *\<^sub>R 0"
      using norm_0_vec
      by (metis (mono_tags, lifting)) 
    also have "... = 0" 
      using scaleR_0_vec by simp
    finally have "inverse (norm x) *\<^sub>R x = 0" .
    with True show ?thesis 
      by (simp add: NN_Lipschitz_Continuous.sgn_fixed_vec_def)
  next
    case False
    have b0: "sgn x = scaleR (1 / norm x) x"
      using False by (simp add: NN_Lipschitz_Continuous.sgn_fixed_vec_def)
    have b1: "... = scaleR (inverse (norm x)) x"
      by (simp add: divide_inverse)
    have b2: "... = inverse (norm x) *\<^sub>R x"
      by (simp add: scaleR_fixed_mat_def)
    show ?thesis using b0 b1 b2 by simp
  qed
qed


lemma norm_eq_zero_iff_vec: "(norm x = (0::real)) = (x = (0::('a, 'n::finite) fixed_vec))"
proof
  assume "norm x = 0"
  have norm_def: "norm x = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i))^2)"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def)
  with \<open>norm x = 0\<close> have b0: "sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))^2) = 0"
    by simp
  then have b1: "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i))^2) = 0"
    by simp
  then have b2: "\<forall>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i))^2 = 0"  
  proof -
    have non_neg: "\<And>i . (norm (fixed_vec_index x i ))\<^sup>2 \<ge> 0"
      by (simp add: power2_eq_square)

    thus b3: "\<forall>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))\<^sup>2 = 0" 
      by (smt (verit, best) b1 finite_atLeastLessThan sum_nonneg_eq_0_iff) 
  qed
  then have b4: "\<forall>i\<in>{0..<CARD('n)}. norm (fixed_vec_index x i ) = 0"
    by (simp add: power2_eq_iff)
  then have b5: "\<forall>i\<in>{0..<CARD('n)}. fixed_vec_index x i = 0"
    by simp
  then have "x = 0"
  proof -
    have "\<forall>i . i < CARD('n) \<longrightarrow> fixed_vec_index x i  = 0"
      using \<open>\<forall>i\<in>{0..<CARD('n)}. fixed_vec_index x i  = 0\<close> 
      by auto
    have "x = Abs_fixed_vec (Rep_fixed_vec x)" 
      by (simp add: Rep_fixed_vec_inverse)
    also have "Rep_fixed_vec x = Matrix.vec CARD('n) (\<lambda> i. fixed_vec_index x i )"
     using Rep_fixed_vec unfolding fixed_vec_index_def carrier_vec_def 
     by force 
    also have "... = Matrix.vec CARD('n) (\<lambda> i. 0)"
      using \<open>\<forall>i . i < CARD('n)  \<longrightarrow> fixed_vec_index x i  = 0\<close>
      by (simp add: vec_eq_iff)
    also have "... = 0\<^sub>v CARD('n)"
      unfolding zero_vec_def by auto
    also have "Abs_fixed_vec (0\<^sub>v CARD('n)) = (fixed_vec_zero::('a, 'n::finite) fixed_vec)"
      unfolding fixed_vec_zero_def by simp
    also have "fixed_vec_zero = 0"
      using zero_fixed_vec_def 
      by (simp add: fixed_vec_zero_def) 
     show "x = 0" 
       by (simp add: calculation NN_Lipschitz_Continuous.zero_fixed_vec_def fixed_vec_zero_def) 
   qed
  thus "x = 0" by simp
next
  assume "x = 0"
  have norm_def: "norm x = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))^2)"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def)
  from \<open>x = 0\<close> have "\<forall>i\<in>{0..<CARD('n)}. fixed_vec_index x i  = 0"
     proof -
    have "\<forall>i . i < CARD('n)  \<longrightarrow> fixed_vec_index x i  = 0" 
      using  \<open>(x::('a, 'n) fixed_vec) = (0::('a, 'n) fixed_vec)\<close> 
        fixed_vec_index.rep_eq
      by (smt (verit) NN_Lipschitz_Continuous.zero_fixed_vec.rep_eq index_zero_vec(1)) 
    have "x = Abs_fixed_vec (Rep_fixed_vec x)" 
      by (simp add: Rep_fixed_vec_inverse)
    also have "Rep_fixed_vec x = Matrix.vec CARD('n) (\<lambda>i. fixed_vec_index x i )"
     using Rep_fixed_vec unfolding fixed_vec_index_def carrier_vec_def 
     by force 
    also have "... = Matrix.vec CARD('n)  (\<lambda> i. 0)"
      using \<open>\<forall>i . i < CARD('n) \<longrightarrow> fixed_vec_index x i  = 0\<close>
      by (simp add: vec_eq_iff)
    also have "... = 0\<^sub>v CARD('n) "
      by auto
    also have "Abs_fixed_vec (0\<^sub>v CARD('n) ) = (fixed_vec_zero::('a, 'n::finite) fixed_vec)"
      unfolding fixed_vec_zero_def by simp
    also have "fixed_vec_zero = 0"
      using zero_fixed_vec_def 
      by (simp add: fixed_vec_zero_def) 
    show "\<forall>i\<in>{0..<CARD('n)}. fixed_vec_index x i  = 0"
       using \<open>\<forall>(i::nat). i < CARD('n)  \<longrightarrow> fixed_vec_index (x::('a, 'n) fixed_vec) i  = (0::'a)\<close> atLeast0LessThan by blast
   qed
  then have "\<forall>i\<in>{0..<CARD('n)} . norm (fixed_vec_index x i ) = 0"
    by simp
  then have "\<forall>i\<in>{0..<CARD('n)} . (norm (fixed_vec_index x i ))^2 = 0"
    by simp
  then have "(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2) = 0"
    by simp
  then have "sqrt (\<Sum>i\<in>{0..<CARD('n)} . (norm (fixed_vec_index x i ))^2) = 0"
    by simp
  with norm_def show "norm x = 0"
    by simp
qed


lemma triangle_inequality_vec: "norm ((x::('a, 'n::finite) fixed_vec) + y::('a, 'n::finite) fixed_vec) \<le> norm x + norm y"
proof -
  have norm_def: "norm z = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index z i ))^2)" 
    for z :: "('a, 'n::finite) fixed_vec"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def)
  have component_add: "fixed_vec_index (x + y) i  = fixed_vec_index x i  + fixed_vec_index y i "
    if "i \<in> {0..<CARD('n)}"  for i  
    proof -
      have "fixed_vec_index (x + y) i  = Rep_fixed_vec (x + y) $ i"
        by (simp add: fixed_vec_index_def)
      also have "Rep_fixed_vec (x + y) $ i = Rep_fixed_vec ((Abs_fixed_vec (Rep_fixed_vec x + Rep_fixed_vec y)::('a, 'n::finite) fixed_vec)) $ (i::nat)"
        by (simp add: Matrix.plus_vec_def NN_Lipschitz_Continuous.plus_fixed_vec.rep_eq fixed_vec_add_def) 
      have "Rep_fixed_vec x \<in> carrier_vec CARD('n)"
        by (simp add: Rep_fixed_vec) 
      moreover have "Rep_fixed_vec y \<in> carrier_vec CARD('n)"
        by (simp add: Rep_fixed_vec)
      ultimately have a0: "Rep_fixed_vec x + Rep_fixed_vec y \<in> carrier_vec CARD('n) "
        by auto   
      hence "Rep_fixed_vec (Abs_fixed_vec (Rep_fixed_vec x + Rep_fixed_vec y)::('a, 'n::finite) fixed_vec) = Rep_fixed_vec x + Rep_fixed_vec y"
         using Abs_fixed_vec_inverse[of "Rep_fixed_vec x + Rep_fixed_vec y"] by blast  
      hence "Rep_fixed_vec ((Abs_fixed_vec (Rep_fixed_vec x + Rep_fixed_vec y)::('a, 'n::finite) fixed_vec)) $ i = 
            (Rep_fixed_vec x + Rep_fixed_vec y) $ i"
        by metis
      also have "... = Rep_fixed_vec x $ i + Rep_fixed_vec y $ i"
        proof -
          have add_def: 
            "Rep_fixed_vec (fixed_vec_add x y) = Rep_fixed_vec x + Rep_fixed_vec y"
            by auto
          have index_def: 
            "(Rep_fixed_vec x + Rep_fixed_vec y) $ i = (Rep_fixed_vec x) $ i + (Rep_fixed_vec y) $ i"
          proof - 
             have carrier_x: "Rep_fixed_vec x \<in> carrier_vec CARD('n)"
               by (simp add: Rep_fixed_vec)
             have carrier_y: "Rep_fixed_vec y \<in> carrier_vec CARD('n)"
               by (simp add: Rep_fixed_vec)
             have add_def: "Rep_fixed_vec x + Rep_fixed_vec y = 
                 vec CARD('n) (\<lambda> i'. Rep_fixed_vec x $ i' + Rep_fixed_vec y $ i')"
               using carrier_x carrier_y unfolding plus_vec_def vec_def carrier_vec_def 
               by (simp add: cond_case_prod_eta)
            have "(Rep_fixed_vec x + Rep_fixed_vec y) $ i = 
                  vec CARD('n) (\<lambda> i' . Rep_fixed_vec x $ i' + Rep_fixed_vec y $ i') $ i"
               by (simp add: add_def)
            moreover have "vec CARD('n) (\<lambda> i'. Rep_fixed_vec x $ i' + Rep_fixed_vec y $ i') $ i =
                 (\<lambda> i'. Rep_fixed_vec x $ i' + Rep_fixed_vec y $ i') i"
              using Rep_fixed_vec[of x] Rep_fixed_vec[of y] unfolding vec_index_def carrier_vec_def               
                 by (metis (no_types, lifting) atLeastLessThan_iff index_vec(1) vec_index_def that(1))
             moreover have "(\<lambda> i' . Rep_fixed_vec x $ i' + Rep_fixed_vec y $ i') i =
                 Rep_fixed_vec x $ i + Rep_fixed_vec y $ i"
               by simp
            show ?thesis 
              by (simp add: calculation(2) local.add_def)
          qed
          show ?thesis
            using add_def index_def
            by simp
        qed
      also have "... = fixed_vec_index x i  + fixed_vec_index y i "
        by (simp add: fixed_vec_index_def)
      finally show "fixed_vec_index (x + y) i  = fixed_vec_index x i  + fixed_vec_index y i " 
        apply (simp add: fixed_vec_add_def fixed_vec_index.rep_eq plus_fixed_vec_def) 
        using \<open>Rep_fixed_vec (x + y) $ i = Rep_fixed_vec (Abs_fixed_vec (Rep_fixed_vec x + Rep_fixed_vec y)) $ i\<close> by argo 
    qed
  have "norm (fixed_vec_index (x + y) i) \<le> norm (fixed_vec_index x i ) + norm (fixed_vec_index y i )"
     if "i \<in> {0..<CARD('n)}" for i 
    using component_add  norm_triangle_ineq that by auto
  then have component_ineq: "(norm (fixed_vec_index (x + y) i ))^2 \<le> 
        (norm (fixed_vec_index x i ) + norm (fixed_vec_index y i ))^2"
     if "i \<in> {0..<CARD('n)}"for i 
    using that by simp
  have expand_square: "(a + b)^2 = a^2 + 2*a*b + b^2" for a b :: real
    by (simp add: power2_eq_square algebra_simps)
  have component_ineq2: "(norm (fixed_vec_index (x + y) i ))^2 \<le> 
        (norm (fixed_vec_index x i ))^2 + 2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i )) + 
        (norm (fixed_vec_index y i ))^2"
     if "i \<in> {0..<CARD('n)}" for i 
    using component_ineq expand_square that by simp
 have sum_ineq: "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le>
        (\<Sum>i\<in>{0..<CARD('n)}. ((norm (fixed_vec_index x i ))^2) + 
        2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i )) + 
        (norm (fixed_vec_index y i ))^2)"
  proof -
    have "\<forall>i\<in>{0..<CARD('n)}.
          (norm (fixed_vec_index (x + y) i ))^2 \<le>
          (norm (fixed_vec_index x i ))^2 + 2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i )) + 
          (norm (fixed_vec_index y i ))^2"
      using component_ineq2 by blast
    have inner_sum_mono: "\<forall>i\<in>{0..<CARD('n)}. 
            ( (norm (fixed_vec_index (x + y) i ))^2) \<le>
            ((norm (fixed_vec_index x i ))^2 + 
             2 * norm (fixed_vec_index x i ) * norm (fixed_vec_index y i ) + 
             (norm (fixed_vec_index y i ))^2)" 
      using component_ineq2 by blast
  
    have "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le>
          (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))^2 + 
           2 * norm (fixed_vec_index x i ) * norm (fixed_vec_index y i ) + 
           (norm (fixed_vec_index y i ))^2)"
      using inner_sum_mono  sum_mono by fast   
    thus ?thesis .
  qed
  have sum_distribute: "(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2 + 
        2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i )) + 
        (norm (fixed_vec_index y i ))^2) =
        (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))^2) +
        (\<Sum>i\<in>{0..<CARD('n)}.  2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i ))) +
        (\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index y i ))^2)"
    by (simp add: sum.distrib)
  have cs: "(\<Sum>i\<in>{0..<CARD('n)}.  2*(norm (fixed_vec_index x i ))*(norm (fixed_vec_index y i ))) \<le>
        2 * sqrt(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2) * 
        sqrt(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index y i))^2)" 
    proof -
      let ?x_norm_i = "\<lambda>i . norm (fixed_vec_index x i )"
      let ?y_norm_i = "\<lambda>i . norm (fixed_vec_index y i )"
      let ?sum_xy = "\<Sum>i = 0..<CARD('n).  ?x_norm_i i  * ?y_norm_i i "
      let ?sum_x2 = "\<Sum>i = 0..<CARD('n). (?x_norm_i i )^2"
      let ?sum_y2 = "\<Sum>i = 0..<CARD('n). (?y_norm_i i )^2"
      have step1: "(\<Sum>i = 0..<CARD('n). 2 * ?x_norm_i i  * ?y_norm_i i ) = 
                   2 * (\<Sum>i = 0..<CARD('n). ?x_norm_i i  * ?y_norm_i i )" 
        using sum_distrib_left[of 2 _ "{0..<CARD('nr)}" ] 
        proof -
          let ?g = "\<lambda>i.  norm (fixed_vec_index x i ) * norm (fixed_vec_index y i )"
          have "2 * (\<Sum>i = 0..<CARD('n). ?g i) = (\<Sum>i = 0..<CARD('n). 2 * ?g i)"
            using sum_distrib_left[of 2 ?g "{0..<CARD('nr)}"] by blast
          have "(\<Sum>i = 0..<CARD('n). 2 * ( norm (fixed_vec_index x i ) * norm (fixed_vec_index y i ))) = 
                (\<Sum>i = 0..<CARD('n). ( 2 * norm (fixed_vec_index x i ) * norm (fixed_vec_index y i )))" 
            by (meson vector_space_over_itself.vector_space_assms(3)) 
         
          show ?thesis using \<open>2 * (\<Sum>i = 0..<CARD('n). ?g i) = (\<Sum>i = 0..<CARD('n). 2 * ?g i)\<close> 
                         and \<open>(\<Sum>i = 0..<CARD('n). 2 * ( norm (fixed_vec_index x i ) * norm (fixed_vec_index y i ))) = 
                              (\<Sum>i = 0..<CARD('n). ( 2 * norm (fixed_vec_index x i ) * norm (fixed_vec_index y i )))\<close>
            by simp
        qed
        have cs_ineq: "?sum_xy^2 \<le> ?sum_x2 * ?sum_y2" 
          by (simp add: Cauchy_Schwarz_ineq_sum) 
      have "?sum_xy \<le> sqrt (?sum_x2 * ?sum_y2)"
        using  real_le_rsqrt  cs_ineq by blast
      also have "sqrt (?sum_x2 * ?sum_y2) = sqrt ?sum_x2 * sqrt ?sum_y2"
        by (rule real_sqrt_mult)
      finally have "2 * ?sum_xy \<le> 2 * sqrt ?sum_x2 * sqrt ?sum_y2"
        using  mult_right_mono by argo 
      with step1 show ?thesis by simp
    qed 
   have norm_square_ineq: "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le>
        (\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2) +
        2 * sqrt(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index x i ))^2) * 
        sqrt(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index y i ))^2) +
        (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index y i ))^2)"
    using sum_ineq sum_distribute cs by argo 
  have norm_square_ineq2: "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le>
        (norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2" 
  proof -
    have d0: "(sqrt (\<Sum>i = 0..<CARD('n). (norm (fixed_vec_index x i ))\<^sup>2))\<^sup>2 = 
          (\<Sum>i = 0..<CARD('n).  (norm (fixed_vec_index x i ))\<^sup>2) " 
      by (meson real_sqrt_pow2 sum_nonneg zero_le_power2) 
    have d1: "(sqrt (\<Sum>i = 0..<CARD('n).  (norm (fixed_vec_index y i ))\<^sup>2))\<^sup>2 = 
          (\<Sum>i = 0..<CARD('n).  (norm (fixed_vec_index y i ))\<^sup>2) " 
      by (meson real_sqrt_pow2 sum_nonneg zero_le_power2)
    have "(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le>
            (\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2) +
            2 * sqrt(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2) * 
            sqrt(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index y i ))^2) +
            (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index y i ))^2)"
      by (rule norm_square_ineq)
     also have "... = (norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2"
        apply(subst norm_def[of x])+ 
        apply(subst d0)
        apply(subst norm_def[of y])+ 
        apply(subst d1)
        using power2_eq_square d0 
        by blast  
      finally show ?thesis .
    qed
  have "(norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2 = (norm x + norm y)^2"
    by (simp add: algebra_simps power2_sum)
  have "(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index (x + y) i))^2) \<le> (norm x + norm y)^2"
    using norm_square_ineq2 `(norm x)^2 + 2 * (norm x) * (norm y) + (norm y)^2 = (norm x + norm y)^2` by simp
  have "sqrt(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le> sqrt((norm x + norm y)^2)"
    using `(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index (x + y) i ))^2) \<le> (norm x + norm y)^2`
    using real_sqrt_le_mono by blast
  have "sqrt((norm x + norm y)^2) = abs (norm x + norm y)"
    by (simp add: power2_eq_square)
  have "sqrt((norm x + norm y)^2) = norm x + norm y"
  proof -
    have "norm x \<ge> 0" 
      unfolding norm_def 
      by (meson norm_ge_zero real_sqrt_ge_zero sum_nonneg zero_le_power) 
    moreover have "norm y \<ge> 0" 
      unfolding norm_def 
      by (meson norm_ge_zero real_sqrt_ge_zero sum_nonneg zero_le_power) 
    ultimately have "norm x + norm y \<ge> 0" by simp
    hence "abs (norm x + norm y) = norm x + norm y" by simp
    thus ?thesis using `sqrt((norm x + norm y)^2) = abs (norm x + norm y)` by simp
  qed
  have "sqrt(\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index (x + y) i ))^2) \<le> norm x + norm y"
    using `sqrt(\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (x + y) i ))^2) \<le> sqrt((norm x + norm y)^2)`
    `sqrt((norm x + norm y)^2) = norm x + norm y` by simp
  thus "norm (x + y) \<le> norm x + norm y"
    using norm_def by simp
qed


lemma norm_scaleR_vec: "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm (x::('a, 'n::finite) fixed_vec)"
proof -
  have a0: "norm (a *\<^sub>R x) = norm (scaleR a x)"
    by simp
  have a1: "... = norm (fixed_vec_smult (of_real a) x)"
    by (simp add: NN_Lipschitz_Continuous.scaleR_fixed_vec_def)
  have a2: "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm (fixed_vec_index (fixed_vec_smult (of_real a) x) i ))^2)"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def)
  have a3: "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (norm ((of_real a) * (fixed_vec_index x i )))^2)"
  proof -
    have element_equality: "\<And>i . i \<in> {0..<CARD('n)}  \<Longrightarrow>
      map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) (fixed_vec_smult (of_real a) x) i  =
      of_real a * map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) x i "
    proof -
      fix i 
      assume i_range: "i \<in> {0..<CARD('n)}"

      have b0: "map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) (fixed_vec_smult (of_real a) x) i  =
            (\<lambda>A i . A $ i ) (Rep_fixed_vec (fixed_vec_smult (of_real a) x)) i "
        by (simp add: map_fun_def)
      have b1: "... = Rep_fixed_vec (fixed_vec_smult (of_real a) x) $ i"
        by simp
      have b2: "... = fixed_vec_index (fixed_vec_smult (of_real a) x) i "
        using i_range  by (simp add: fixed_vec_index_def)
      have b3: "... = of_real a * fixed_vec_index x i "
        using i_range  Rep_fixed_vec 
        unfolding fixed_vec_smult_def  smult_vec_def fixed_vec_index_def map_vec_def 
      proof -
        have f1: "\<forall>a f. Rep_fixed_vec (fixed_vec_smult a (f::('a, 'n) fixed_vec)) = a \<cdot>\<^sub>v Rep_fixed_vec f"
          using fixed_vec_smult.rep_eq by blast
        have f3: "i < card (UNIV::'n set)"
          using atLeastLessThan_iff i_range by blast
        have f4: "\<forall>f a. Abs_fixed_vec (a \<cdot>\<^sub>v Rep_fixed_vec (f::('a, 'n) fixed_vec)) = fixed_vec_smult a f"
          using f1 by (metis (no_types) Rep_fixed_vec_inverse)
        have f5: "\<forall>f. dim_vec (Rep_fixed_vec (0::('a, 'n) fixed_vec)) = dim_vec (Rep_fixed_vec (f::('a, 'n) fixed_vec))"
          using f1 by (smt (z3) NN_Lipschitz_Continuous.scaleR_fixed_vec_def index_smult_vec scaleR_0_vec)
        then have f6: "dim_vec (Rep_fixed_vec (0::('a, 'n) fixed_vec)) = card (UNIV::'n set)"
          by (smt (z3) Rep_fixed_vec_zero dim_vec zero_vec_def)
        have "\<forall>f. card (UNIV::'n set) = dim_vec (Rep_fixed_vec (f::('a, 'n) fixed_vec))"
          using f5 f6 by force 
        then show "map_fun Rep_fixed_vec id (\<lambda>m n. m $ n ) (map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>a m. Matrix.vec (dim_vec m)  (\<lambda>p. a * m $ p)) (of_real a) x::('a, 'n) fixed_vec) i 
                 = of_real a * map_fun Rep_fixed_vec id (\<lambda>m n. m $ n ) x i "
          using f6 f5 f4 f3  f1 by (simp add: map_vec_def smult_vec_def)
      qed 
      have b4: "... = of_real a * Rep_fixed_vec x $ i"
        using i_range  by (simp add: fixed_vec_index_def)
      have b5: "... = of_real a * (\<lambda>A i. A $ i) (Rep_fixed_vec x) i "
        by simp
      have b6:"... = of_real a * map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) x i "
        by (simp add: map_fun_def)
      show "map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) (fixed_vec_smult (of_real a) x) i  =
                    of_real a * map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) x i "
        using b0 b1 b2 b3 b4 b5 b6 by argo
    qed
    have c0: "(\<Sum>i = 0..<CARD('n). (norm (map_fun Rep_fixed_vec id (\<lambda>A i. A $ i) (fixed_vec_smult (of_real a) x) i ))\<^sup>2) =
              (\<Sum>i = 0..<CARD('n). (norm (of_real a * map_fun Rep_fixed_vec id (\<lambda>A i . A $ i) x i ))\<^sup>2)" 
      using element_equality by force 
    show ?thesis using c0 
      by (simp add: fixed_vec_index_def)
  qed
  have a4: "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (\<bar>of_real a\<bar> * norm (fixed_vec_index x i ))^2)"     
    by (simp add: of_real_def)
  have a5: "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}.  (\<bar>a\<bar> * norm (fixed_vec_index x i ))^2)"
    by simp
  have a6: "... = sqrt (\<Sum>i\<in>{0..<CARD('n)}. (\<bar>a\<bar>)^2 * (norm (fixed_vec_index x i ))^2)"
    by (simp add: power_mult_distrib)
  have a7: "... = sqrt ((\<bar>a\<bar>)^2 * (\<Sum>i\<in>{0..<CARD('n)}.  (norm (fixed_vec_index x i ))^2))"
    by (simp add: sum_distrib_left)
  have a8: "... = \<bar>a\<bar> * sqrt (\<Sum>i\<in>{0..<CARD('n)}.(norm (fixed_vec_index x i ))^2)"
    by (simp add: real_sqrt_mult)
  have a9: "... = \<bar>a\<bar> * norm x"
    by (simp add: NN_Lipschitz_Continuous.norm_fixed_vec_def)
  have a10: "... = \<bar>a\<bar> * norm x"
    by simp
  show ?thesis using a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 
    by linarith
qed

instance
  apply standard 
  subgoal using dist_fixed_vec_def by simp
  subgoal unfolding plus_fixed_vec_def fixed_vec_add_def 
    using  add_carrier_vec assoc_add_vec  
    by (smt (verit, del_insts) Abs_fixed_vec_inverse Rep_fixed_vec carrier_vec_def id_apply)
  subgoal unfolding plus_fixed_vec_def fixed_vec_add_def  
    using Rep_fixed_vec comm_add_vec 
    by (metis id_def)  
  subgoal unfolding zero_fixed_vec_def  plus_fixed_vec_def fixed_vec_add_def id_def
    using Rep_fixed_vec Abs_fixed_vec_inverse Rep_fixed_vec_inverse  zero_carrier_vec  
    by (metis left_zero_vec)  
  subgoal using uminus_add_vec by blast
  subgoal 
    by (metis (mono_tags, lifting) NN_Lipschitz_Continuous.minus_fixed_vec.rep_eq 
        NN_Lipschitz_Continuous.plus_fixed_vec.transfer Rep_fixed_vec_inverse 
        fixed_vec_add_def  uminus_fixed_vec.rep_eq)  
  subgoal 
    by (smt (verit) NN_Lipschitz_Continuous.scaleR_fixed_vec_def Rep_fixed_vec 
        Rep_fixed_vec_add fixed_vec.Rep_fixed_vec_inject fixed_vec_smult.rep_eq 
        plus_fixed_vec.abs_eq smult_add_distrib_vec)
  subgoal 
    by (metis (mono_tags, opaque_lifting) NN_Lipschitz_Continuous.plus_fixed_vec.rep_eq 
        Rep_fixed_vec_add add_smult_distrib_vec fixed_vec.Rep_fixed_vec_inject 
        fixed_vec_smult.rep_eq of_real_hom.hom_add scaleR_fixed_vec_def) 
  subgoal using smult_vec by blast  
  subgoal using scaleR_vec by blast 
  subgoal using sgn_vec by blast
  subgoal unfolding uniformity_fixed_vec_def by blast 
  subgoal unfolding open_fixed_vec_def by blast 
  subgoal using norm_eq_zero_iff_vec by blast
  subgoal using triangle_inequality_vec by blast
  subgoal using norm_scaleR_vec by blast
  done

end

lemma uminus_fixed_vec:
  assumes "(v::'a::{real_algebra_1,real_normed_vector} Matrix.vec) \<in> carrier_vec (CARD('n::finite))"
  shows "- Abs_fixed_vec v = (Abs_fixed_vec (- v):: ('a::{real_algebra_1,real_normed_vector}, 'n::finite) fixed_vec)"
proof -
  have "Rep_fixed_vec ((Abs_fixed_vec v):: ('a::{real_algebra_1,real_normed_vector}, 'n::finite) fixed_vec) = v"
    using assms Abs_fixed_vec_inverse[of v] 
    by blast 
  hence "Rep_fixed_vec (- (Abs_fixed_vec v):: ('a::{real_algebra_1,real_normed_vector}, 'n::finite) fixed_vec) = - v"
    using uminus_fixed_vec.rep_eq 
  proof -
    have f1: "Rep_fixed_vec (Abs_fixed_vec v::('a, 'n) fixed_vec) = v"
      using \<open>Rep_fixed_vec (Abs_fixed_vec (v::'a Matrix.vec)) = v\<close> by blast
    have "\<forall>f. Rep_fixed_vec (- (f::('a, 'n) fixed_vec)) = - 1 \<cdot>\<^sub>v Rep_fixed_vec f"
      using uminus_fixed_vec.rep_eq by blast
    then show ?thesis 
      using f1 by auto
  qed 
  thus ?thesis
    by (metis Rep_fixed_vec_inverse) 
qed

lemma lipschitz_on_mat_add:
  shows \<open>(1::real)-lipschitz_on U (\<lambda> (A:: ('a::{real_algebra_1,real_normed_vector}, 'nr::finite, 'nc::finite) fixed_mat) . A + M)\<close> 
  by (simp add: lipschitz_onI)

lemma vec_minus_element:
  fixes v w :: "'a::{minus, zero} vec"
  assumes "dim_vec v = dim_vec w" and "i < dim_vec v"
  shows "vec_index (v - w) i = vec_index v i - vec_index w i"
proof -
  from assms have dim_eq: "dim_vec (v - w) = dim_vec v"
    by simp
  have "vec_index (v - w) i = vec_index (vec (dim_vec v) (\<lambda>j. vec_index v j - vec_index w j)) i"
    using assms by simp
  also have "... = (\<lambda>j. vec_index v j - vec_index w j) i"
    using assms dim_eq by simp
  also have "... = vec_index v i - vec_index w i"
    by simp
  finally show ?thesis 
    by (metis assms(1) assms(2) index_minus_vec(1))
qed

lemma vec_minus:
  fixes v w :: "'a::{minus, zero} vec"
  assumes "dim_vec v = dim_vec w"  and "i < dim_vec v"
  shows "(v - w) = vec (dim_vec v) (\<lambda>i. vec_index v i - vec_index w i)"
proof -
  have "v - w = vec (dim_vec (v - w)) (\<lambda>i. vec_index (v - w) i)"
    by (simp add: vec_eq_iff)
  also have "dim_vec (v - w) = dim_vec v"
    using assms vec_minus_element 
    by (metis index_minus_vec(2))
  also have  "Matrix.vec (dim_vec v) (\<lambda>i. (v - w) $ i) = Matrix.vec (dim_vec v) (\<lambda>i. v $ i - w $ i)"
    using assms(1) by fastforce 
  finally show ?thesis by simp
qed

lemma Rep_fixed_vec_plus:
  "Rep_fixed_vec ((u:: ('a::{real_algebra_1,real_normed_vector}, 'n::finite) fixed_vec) + 
                  (v:: ('a::{real_algebra_1,real_normed_vector}, 'n::finite) fixed_vec)) = 
   Rep_fixed_vec u + Rep_fixed_vec v"
proof -
  have "u + v \<in> {v. Rep_fixed_vec v \<in> carrier_vec (CARD('n))}"
    using Rep_fixed_vec unfolding carrier_vec_def 
    by blast
  thus "Rep_fixed_vec (u + v) = Rep_fixed_vec u + Rep_fixed_vec v"
    using Rep_fixed_vec unfolding plus_fixed_vec_def 
    by force 
qed

lemma fixed_vec_add:
  assumes "v1 \<in> carrier_vec (CARD('n::finite))"
      and "v2 \<in> carrier_vec (CARD('n::finite))"
    shows "Abs_fixed_vec v1 + Abs_fixed_vec v2 = (Abs_fixed_vec (v1 + v2)::('a::{real_algebra_1,real_normed_vector}, 'n) fixed_vec)"
proof -
  have carrier_sum: "v1 + v2 \<in> carrier_vec (CARD('n))"
    using assms add_carrier_vec by blast
  have "Rep_fixed_vec ((Abs_fixed_vec v1 + Abs_fixed_vec v2)::('a, 'n) fixed_vec) = 
        Rep_fixed_vec ((Abs_fixed_vec v1)::('a, 'n) fixed_vec) + 
        Rep_fixed_vec ((Abs_fixed_vec v2)::('a, 'n) fixed_vec)"
    using Rep_fixed_vec_plus[of "Abs_fixed_vec v1" "Abs_fixed_vec v2"]
    by blast
   also have "Rep_fixed_vec ((Abs_fixed_vec v1)::('a, 'n) fixed_vec) + 
              Rep_fixed_vec ((Abs_fixed_vec v2)::('a, 'n) fixed_vec) = 
              v1 + v2"
      using assms Abs_fixed_vec_inverse[of v1]  
                  Abs_fixed_vec_inverse[of v2] 
      by (metis calculation) 
   also have "... = Rep_fixed_vec ((Abs_fixed_vec (v1 + v2))::('a, 'n) fixed_vec)"
      using carrier_sum assms 
    by (metis Rep_fixed_vec_inverse calculation)
  finally have "Rep_fixed_vec ((Abs_fixed_vec v1 + Abs_fixed_vec v2)::('a, 'n) fixed_vec) = 
                Rep_fixed_vec ((Abs_fixed_vec (v1 + v2))::('a, 'n) fixed_vec)" .
  thus "Abs_fixed_vec v1 + Abs_fixed_vec v2 = (Abs_fixed_vec (v1 + v2)::('a, 'n) fixed_vec)"
    using Rep_fixed_vec_inject by blast
qed


lemma col_minus_mat:
  fixes A B :: "'a::{minus, zero} mat"
  assumes "dim_row A = dim_row B" and "dim_col A = dim_col B" and "i < dim_col A"
  shows "col (A - B) i = col A i - col B i"
proof -
  from assms have dim_col_eq: "dim_col (A - B) = dim_col A"
    by (metis index_minus_mat(3))  
  from assms have dim_row_eq: "dim_row (A - B) = dim_row A" 
    by (metis index_minus_mat(2))  
  have "col (A - B) i = col A i - col B i"
  proof -
    have "col (A - B) i = vec (dim_row (A - B)) (\<lambda>j. (A - B) $$ (j, i))"
      by (simp add: col_def)
    also have "... = vec (dim_row A) (\<lambda>j. (A - B) $$ (j, i))"
      using dim_row_eq assms(1) by presburger
    also have "... = vec (dim_row A) (\<lambda>j. A $$ (j, i) - B $$ (j, i))"
      using assms  \<open>(i::nat) < dim_col (A::'a mat)\<close> by fastforce
    also have "... = vec (dim_row A) (\<lambda>j. A $$ (j, i)) - vec (dim_row A) (\<lambda>j. B $$ (j, i))"
      by (simp add: Matrix.vec_eq_iff)
    also have "... = col A i - col B i" 
      using assms(1) col_def by metis 
    finally show "col (A - B) i = col A i - col B i" .
  qed
  show "col (A - B) i = col A i - 

col B i"
    using assms by auto
qed

lemma index_vec_mat_mult:
  assumes "v \<in> carrier_vec (dim_row A)"
      and "A \<in> carrier_mat (dim_row A) (dim_col A)"
      and "i < dim_col (A::'a::{semiring_0, ab_semigroup_mult} Matrix.mat)"
    shows "(v \<^sub>v* A) $ i = (\<Sum>j = 0..<dim_row A. v $ j * A $$ (j, i))"
proof -
  have a0: "(v \<^sub>v* A) $ i = (Matrix.vec (dim_col A) (\<lambda>k. col A k \<bullet> v)) $ i"
    using assms unfolding mult_vec_mat_def by blast
  have a1: "(Matrix.vec (dim_col A) (\<lambda>k. col A k \<bullet> v)) $ i = (\<lambda>k. col A k \<bullet> v) i"
    using assms index_vec by blast 
  have a2: "... = col A i \<bullet> v"
    using assms by blast  
  have a3: "... = (\<Sum>j = 0..<dim_row A. col A i $ j * v $ j)"
    using assms scalar_prod_def 
    by (metis carrier_vecD)   
  have a4: "(\<Sum>j = 0..<dim_row A. col A i $ j * v $ j) = (\<Sum>j = 0..<dim_row A. A $$ (j, i) * v $ j)"
    using assms index_col 
    by (metis (no_types, lifting) sum.ivl_cong) 
  have a5: "... = (\<Sum>j = 0..<dim_row A. v $ j * A $$ (j, i))"
    using mult.commute by metis
  show "(v \<^sub>v* A) $ i = (\<Sum>j = 0..<dim_row A. v $ j * A $$ (j, i))"
    using a0 a1 a2 a3 a4 a5 by argo 
qed

lemma Rep_fixed_mat_minus:
  "Rep_fixed_mat ((x - y)::('a, 'b, 'c) fixed_mat) = Rep_fixed_mat x - Rep_fixed_mat (y:: ('a:: {real_algebra_1,real_normed_vector}, 'b::finite, 'c::finite) fixed_mat)"
  proof -
  have "Rep_fixed_mat (x - y) = Rep_fixed_mat (Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y)::('a, 'b, 'c) fixed_mat)"
   proof -
  have "x - y = Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y)"
  proof -
    have "x - y = fixed_mat_add x (fixed_mat_smult (- 1) y::('a, 'b, 'c) fixed_mat)"
      using minus_fixed_mat_def by blast     
    also have "... = Abs_fixed_mat (Rep_fixed_mat x + Rep_fixed_mat (fixed_mat_smult (- 1) y::('a, 'b, 'c) fixed_mat))"
      by (simp add: fixed_mat_add_def)    
    also have "... = Abs_fixed_mat (Rep_fixed_mat x + (- 1) \<cdot>\<^sub>m Rep_fixed_mat (y::('a, 'b, 'c) fixed_mat))"
      by (simp add: fixed_mat_smult.rep_eq)     
    also have "... = Abs_fixed_mat (Rep_fixed_mat x + (- Rep_fixed_mat (y::('a, 'b, 'c) fixed_mat)))"
      by (smt (verit, ccfv_SIG) Rep_fixed_mat Rep_fixed_mat_add 
          \<open>Abs_fixed_mat (Rep_fixed_mat (x::('a, 'b, 'c) fixed_mat) + Rep_fixed_mat (fixed_mat_smult (- (1::'a)) (y::('a, 'b, 'c) fixed_mat))) = Abs_fixed_mat (Rep_fixed_mat x + - (1::'a) \<cdot>\<^sub>m Rep_fixed_mat y)\<close> 
          \<open>fixed_mat_add (x::('a, 'b, 'c) fixed_mat) (fixed_mat_smult (- (1::'a)) (y::('a, 'b, 'c) fixed_mat)) = Abs_fixed_mat (Rep_fixed_mat x + Rep_fixed_mat (fixed_mat_smult (- (1::'a)) y))\<close> 
          assoc_add_mat calculation comm_add_mat diff_add_cancel plus_fixed_mat_def 
          right_add_zero_mat uminus_carrier_iff_mat uminus_l_inv_mat)     
    also have "... = Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y)"
      by (metis Rep_fixed_mat add_uminus_minus_mat)  
    finally show "x - y = Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y)" .
  qed  
  thus "Rep_fixed_mat ((x - y)::('a, 'b, 'c) fixed_mat) = Rep_fixed_mat ((Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y))::('a, 'b, 'c) fixed_mat)"
     by argo 
qed
  also have " Rep_fixed_mat (Abs_fixed_mat (Rep_fixed_mat x - Rep_fixed_mat y)::('a, 'b, 'c) fixed_mat) = Rep_fixed_mat x - Rep_fixed_mat y"
  proof -
    have "Rep_fixed_mat x \<in> carrier_mat (CARD('b)) (CARD('c))"
      using Rep_fixed_mat[of x] by blast  
    have "Rep_fixed_mat y \<in> carrier_mat (CARD('b)) (CARD('c))"
      by (rule Rep_fixed_mat)  
    hence "Rep_fixed_mat x - Rep_fixed_mat y \<in> carrier_mat (CARD('b)) (CARD('c))"
      using \<open>Rep_fixed_mat x \<in> carrier_mat (CARD('b)) (CARD('c))\<close>
      using minus_carrier_mat by blast     
    thus ?thesis 
      by (metis Abs_fixed_mat_inverse calculation) 
    qed
  finally show "Rep_fixed_mat (x - y) = Rep_fixed_mat x - Rep_fixed_mat y" .
qed

lemma vector_matrix_inequality:
  fixes c :: "('a::{real_normed_field,real_inner}, 'nr::finite) fixed_vec"
    and U :: "('a, 'nr, 'nc::finite) fixed_mat set"
    and C :: real
  assumes C_bound: "C \<ge> norm c"
      and C_nonneg: "C \<ge> 0"
  shows "\<And>x y. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> 
    sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2) \<le>
    C * sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
proof -
  fix x y :: "('a, 'nr, 'nc) fixed_mat"
  assume x_in_U: "x \<in> U" and y_in_U: "y \<in> U"
  let ?x_rep = "Rep_fixed_mat x"
  let ?y_rep = "Rep_fixed_mat y"
  let ?c_rep = "Rep_fixed_vec c"
  have c_mult_diff: "c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y = Abs_fixed_vec (?c_rep \<^sub>v* (?x_rep - ?y_rep))"
  proof -
    have dim_col_eq_x_y: "dim_col (Rep_fixed_mat x) = dim_col (Rep_fixed_mat y)"
      by (metis Rep_fixed_mat carrier_matD(2))
    have vec_mult_x: "c \<^sub>f\<^sub>v* x = Abs_fixed_vec (?c_rep \<^sub>v* ?x_rep)"
      by (simp add: mult_vec_fixed_mat_def mult_vec_mat_def)
    have vec_mult_y: "c \<^sub>f\<^sub>v* y = Abs_fixed_vec (?c_rep \<^sub>v* ?y_rep)"
      by (simp add: mult_vec_fixed_mat_def mult_vec_mat_def)
    have "c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y = Abs_fixed_vec (?c_rep \<^sub>v* ?x_rep) - Abs_fixed_vec (?c_rep \<^sub>v* ?y_rep)"
      using vec_mult_x vec_mult_y by simp
    also have "... = Abs_fixed_vec ((?c_rep \<^sub>v* ?x_rep) - (?c_rep \<^sub>v* ?y_rep))"
    proof -
      have carrier_vx: "(?c_rep \<^sub>v* ?x_rep) \<in> carrier_vec (CARD('nc))"
        using Rep_fixed_vec  
        by (metis mult_vec_fixed_mat.rep_eq mult_vec_mat_def)       
      have carrier_vy: "(?c_rep \<^sub>v* ?y_rep) \<in> carrier_vec (CARD('nc))"
        using Rep_fixed_vec         
        by (metis mult_vec_fixed_mat.rep_eq mult_vec_mat_def)
      show ?thesis
        using carrier_vx carrier_vy 
        by (simp add: fixed_vec_add minus_add_uminus_vec pth_2 uminus_fixed_vec) 
    qed   
    also have "... = Abs_fixed_vec (?c_rep \<^sub>v* (?x_rep - ?y_rep))"
    proof -
      have "(?c_rep \<^sub>v* ?x_rep) - (?c_rep \<^sub>v* ?y_rep) = ?c_rep \<^sub>v* (?x_rep - ?y_rep)"
        using Rep_fixed_vec Rep_fixed_mat 
        by (smt (verit, del_insts) Matrix.vec_eq_iff carrier_matD(1) col_dim col_minus_mat 
            dim_col_eq_x_y dim_mult_vec_mat index_minus_mat(3) index_minus_vec(1) 
            index_minus_vec(2) index_mult_vec_mat minus_scalar_prod_distrib)
      thus ?thesis by simp
    qed   
    finally show ?thesis .
  qed  
  have vec_index_eq: "\<forall>i < CARD('nc). 
    fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i = (?c_rep \<^sub>v* (?x_rep - ?y_rep)) $ i"
  proof (intro allI impI)
    fix i
    assume "i < CARD('nc)"
    show "fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i = (?c_rep \<^sub>v* (?x_rep - ?y_rep)) $ i"
      using c_mult_diff
      by (metis (mono_tags, lifting) Abs_fixed_vec_inverse Rep_fixed_mat carrier_matD(2) 
          fixed_vec_index.rep_eq index_minus_mat(3) mult_vec_mat_def vec_carrier) 
  qed
  have vec_mult_expand: "\<forall>i < CARD('nc). 
    (?c_rep \<^sub>v* (?x_rep - ?y_rep)) $ i = (\<Sum>j = 0..<CARD('nr). ?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i))"
  proof (intro allI impI)
    fix i
    assume "i < CARD('nc)"
    show "(?c_rep \<^sub>v* (?x_rep - ?y_rep)) $ i = (\<Sum>j = 0..<CARD('nr). ?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i))"
    proof -
      have carrier_c: "?c_rep \<in> carrier_vec (CARD('nr))"
        by (rule Rep_fixed_vec)     
      have carrier_diff: "(?x_rep - ?y_rep) \<in> carrier_mat (CARD('nr)) (CARD('nc))"
        using Rep_fixed_mat minus_carrier_mat by blast      
      show ?thesis
        using carrier_c carrier_diff \<open>i < CARD('nc)\<close>
        by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux carrier_matD(1) 
            carrier_matD(2) index_vec_mat_mult)
    qed
  qed
  have triangle_step: "(\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2) \<le>
    (\<Sum>i = 0..<CARD('nc). (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j) * norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)"
  proof -
    have "\<forall>i < CARD('nc). 
      norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) \<le> 
      (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i)))"
    proof (intro allI impI)
      fix i
      assume "i < CARD('nc)"
      have "norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) = 
            norm ((?c_rep \<^sub>v* (?x_rep - ?y_rep)) $ i)"
        using vec_index_eq \<open>i < CARD('nc)\<close> by simp      
      also have "... = norm (\<Sum>j = 0..<CARD('nr). ?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i))"
        using vec_mult_expand \<open>i < CARD('nc)\<close> by simp      
      also have "... \<le> (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i)))"
        by (rule norm_sum)      
      finally show "norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) \<le> 
                    (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i)))" .
    qed    
    moreover have "\<forall>i < CARD('nc). \<forall>j < CARD('nr).
      norm (?c_rep $ j * (?x_rep - ?y_rep) $$ (j, i)) = 
      norm (?c_rep $ j) * norm ((?x_rep - ?y_rep) $$ (j, i))"
      using norm_mult by blast   
    ultimately show ?thesis
      proof -
      have "\<forall>i < CARD('nc). 
        (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2 \<le> 
        (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j) * norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))\<^sup>2"
      proof (intro allI impI)
        fix i
        assume "i < CARD('nc)"       
        have "norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) \<le> 
              (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j * (Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))"
          using \<open>\<forall>i<CARD('nc). norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) \<le> (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j * (Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))\<close>
          using \<open>i < CARD('nc)\<close> by blast       
        also have "... = (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j) * norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))"
          using \<open>\<forall>i<CARD('nc). \<forall>j<CARD('nr). norm (Rep_fixed_vec c $ j * (Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)) = norm (Rep_fixed_vec c $ j) * norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i))\<close>
          using \<open>i < CARD('nc)\<close> by simp       
        finally have "norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i) \<le> 
                      (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j) * norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))" .        
        thus "(norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2 \<le> 
              (\<Sum>j = 0..<CARD('nr). norm (Rep_fixed_vec c $ j) * norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))\<^sup>2"
          using norm_ge_zero power_mono by blast 
      qed      
      thus ?thesis
        by (meson atLeastLessThan_iff sum_mono) 
    qed
  qed  
  have cauchy_schwarz_step: 
    "(\<Sum>i = 0..<CARD('nc). (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j) * norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2) \<le>
    (\<Sum>i = 0..<CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2))"
  proof -
    have "\<forall>i < CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j) * norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2 \<le>
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)"
    proof (intro allI impI)
      fix i
      assume "i < CARD('nc)"      
      let ?a = "\<lambda>j. norm (?c_rep $ j)"
      let ?b = "\<lambda>j. norm ((?x_rep - ?y_rep) $$ (j, i))"      
      have nonneg_a: "\<forall>j. ?a j \<ge> 0" by simp
      have nonneg_b: "\<forall>j. ?b j \<ge> 0" by simp
      have "(\<Sum>j = 0..<CARD('nr). ?a j * ?b j)\<^sup>2 \<le> (\<Sum>j = 0..<CARD('nr). (?a j)\<^sup>2) * (\<Sum>j = 0..<CARD('nr). (?b j)\<^sup>2)"
        by (simp add: Cauchy_Schwarz_ineq_sum)  
      thus "(\<Sum>j = 0..<CARD('nr). norm (?c_rep $ j) * norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2 \<le>
            (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) * (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)"
        by simp
    qed
    thus ?thesis 
      by (meson atLeastLessThan_iff sum_mono)
  qed
  have factor_step:
    "(\<Sum>i = 0..<CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)) =
    (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) * 
    (\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)"
    by (simp add: sum_distrib_left)
  have norm_c_eq: "(\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2) = (norm c)\<^sup>2"
  proof -
    have "norm c = sqrt (\<Sum>j = 0..<CARD('nr). (norm (fixed_vec_index c j))\<^sup>2)"
      unfolding norm_fixed_vec_def by blast
    also have "... = sqrt (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2)"
      by (simp add: fixed_vec_index_def)   
    finally have "norm c = sqrt (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $ j))\<^sup>2)" .    
    thus ?thesis 
      by (metis norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
  qed
  have reorder_step:
    "(\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2) =
    (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
  proof -
    have "(\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2) =
          (\<Sum>j = 0..<CARD('nr). \<Sum>i = 0..<CARD('nc). (norm ((?x_rep - ?y_rep) $$ (j, i)))\<^sup>2)"
      by (rule sum.swap)   
    also have "... = (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm ((?x_rep - ?y_rep) $$ (i, j)))\<^sup>2)"
      by simp    
    also have "... = (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
       proof -
      have "\<forall>i < CARD('nr). \<forall>j < CARD('nc). 
        norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (i, j)) = norm (fixed_mat_index (x - y) i j)"
      proof (intro allI impI)
        fix i j
        assume "i < CARD('nr)" and "j < CARD('nc)"      
        have "fixed_mat_index (x - y) i j = Rep_fixed_mat (x - y) $$ (i, j)"
          by (simp add: fixed_mat_index_def)        
        also have "... = (Rep_fixed_mat x - Rep_fixed_mat y) $$ (i, j)"
           using Rep_fixed_mat_minus by metis
        finally have "fixed_mat_index (x - y) i j = (Rep_fixed_mat x - Rep_fixed_mat y) $$ (i, j)" .        
        thus "norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (i, j)) = norm (fixed_mat_index (x - y) i j)"
          by simp
      qed      
      thus ?thesis
        by simp
    qed 
    then show ?thesis 
      using \<open>(\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). 
       (norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))\<^sup>2) = 
             (\<Sum>j = 0..<CARD('nr). \<Sum>i = 0..<CARD('nc). 
        (norm ((Rep_fixed_mat x - Rep_fixed_mat y) $$ (j, i)))\<^sup>2)\<close> by presburger
  qed
  have matrix_ineq: "(\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2) \<le>
    (norm c)\<^sup>2 * (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
    using triangle_step cauchy_schwarz_step factor_step norm_c_eq reorder_step by simp
  have "sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2) \<le>
        sqrt ((norm c)\<^sup>2 * (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2))"
    using matrix_ineq real_sqrt_le_iff by blast   
  also have "... = norm c * sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
  proof -
    have "sqrt ((norm c)\<^sup>2 * (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)) =
          sqrt ((norm c)\<^sup>2) * sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
      using real_sqrt_mult by blast     
    also have "sqrt ((norm c)\<^sup>2) = norm c"
      by simp    
    finally show ?thesis by simp
  qed
  also have "... \<le> C * sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)"
    using C_bound C_nonneg 
    by (metis mult_right_mono norm_fixed_mat_def norm_ge_zero) 
  finally show "sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (c \<^sub>f\<^sub>v* x - c \<^sub>f\<^sub>v* y) i))\<^sup>2) \<le>
                C * sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index (x - y) i j))\<^sup>2)" .
qed

lemma lipschitz_on_mat_mult:
  assumes \<open>0 \<le> C \<close> and "norm c \<le> C"
  shows \<open>C-lipschitz_on U (\<lambda> (y::('a:: {real_inner,real_normed_field}, 'nr::finite, 'nc::finite) fixed_mat) . 
                             ( c::('a, 'nr) fixed_vec)  \<^sub>f\<^sub>v* y)\<close>
  unfolding mult_vec_mat_def lipschitz_on_def 
  apply (intro conjI impI allI)
  unfolding dist_fixed_vec_def dist_fixed_mat_def
  unfolding norm_fixed_vec_def norm_fixed_mat_def
  subgoal using assms by blast
  subgoal using vector_matrix_inequality[of c C _ U ] assms by blast
  done

lemma lipschitz_on_weighted_sum_bias:
  assumes \<open>0 \<le> C \<close> and "norm c \<le> C"
  shows \<open>C-lipschitz_on U (\<lambda> (y::('a:: {real_inner,real_normed_field}, 'nr::finite, 'nc::finite) fixed_mat) . (c \<^sub>f\<^sub>v* y) + b)\<close>
  using lipschitz_on_mat_mult 
proof -
  have "\<forall>F. C-lipschitz_on (F::('a, 'nr, 'nc) fixed_mat set) ((\<^sub>f\<^sub>v*) c)"
    by (meson assms(2) lipschitz_on_le lipschitz_on_mat_mult norm_imp_pos_and_ge)
  then have "\<forall>F f. (0 + C)-lipschitz_on F (\<lambda>fa. (f::('a, 'nc) fixed_vec) + c \<^sub>f\<^sub>v* fa)"
    using Lipschitz.lipschitz_on_constant lipschitz_on_add by blast
  then have "C-lipschitz_on U (\<lambda>f. b + c \<^sub>f\<^sub>v* f)"
    by simp
  then show ?thesis
    by (meson Groups.add_ac(2) lipschitz_on_cong)
qed

lemma mult_vec_mat_distrib_left:
  assumes "v1 \<in> carrier_vec n" and "v2 \<in> carrier_vec n" and "A \<in> carrier_mat n m"
  shows "(v1 - v2) \<^sub>v* A = v1 \<^sub>v* A - v2 \<^sub>v* (A:: 'a::{real_normed_field,real_inner} mat)"
proof -
  have carrier_diff: "v1 - v2 \<in> carrier_vec n"
    using assms by simp 
  have carrier_mult1: "v1 \<^sub>v* A \<in> carrier_vec m"
    using assms 
    by (simp add: mult_vec_mat_def) 
  have carrier_mult2: "v2 \<^sub>v* A \<in> carrier_vec m"
    using assms 
    by (simp add: mult_vec_mat_def) 
  have carrier_mult_diff: "(v1 - v2) \<^sub>v* A \<in> carrier_vec m"
    using carrier_diff assms 
    using carrier_dim_vec dim_mult_vec_mat by blast
  have "dim_vec ((v1 - v2) \<^sub>v* A) = dim_vec (v1 \<^sub>v* A - v2 \<^sub>v* A)"
      using carrier_mult_diff carrier_mult1 carrier_mult2 by simp
    show ?thesis  
    proof 
      show "dim_vec ((v1 - v2) \<^sub>v* A) = dim_vec (v1 \<^sub>v* A - v2 \<^sub>v* A)"
        by (simp add: mult_vec_mat_def)
    next
      fix i
      assume i_bound: "i < dim_vec (v1 \<^sub>v* A - v2 \<^sub>v* A)"
      have i_less_m: "i < m"
        using i_bound carrier_mult1 carrier_mult2 by simp
      have lhs_expand: "((v1 - v2) \<^sub>v* A) $ i = (\<Sum>j = 0..<n. (v1 - v2) $ j * A $$ (j, i))"
        using carrier_diff assms i_less_m mult_vec_mat_def 
        by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) index_vec_mat_mult sum.cong) 
      have vec_sub_expand: "(\<Sum>j = 0..<n. (v1 - v2) $ j * A $$ (j, i)) = (\<Sum>j = 0..<n. (v1 $ j - v2 $ j) * A $$ (j, i))"
        using assms by simp
      have mult_distrib: "(\<Sum>j = 0..<n. (v1 $ j - v2 $ j) * A $$ (j, i)) = (\<Sum>j = 0..<n. v1 $ j * A $$ (j, i) - v2 $ j * A $$ (j, i))"       
        by (meson vector_space_over_itself.scale_left_diff_distrib) 
      have sum_distrib: "(\<Sum>j = 0..<n. v1 $ j * A $$ (j, i) - v2 $ j * A $$ (j, i)) = (\<Sum>j = 0..<n. v1 $ j * A $$ (j, i)) - (\<Sum>j = 0..<n. v2 $ j * A $$ (j, i))"
        by (simp add: sum_subtractf) 
      have back_to_mult: "(\<Sum>j = 0..<n. v1 $ j * A $$ (j, i)) - (\<Sum>j = 0..<n. v2 $ j * A $$ (j, i)) = (v1 \<^sub>v* A) $ i - (v2 \<^sub>v* A) $ i"
        by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) carrier_matD(1) carrier_matD(2) i_less_m index_vec_mat_mult)
      have to_vec_sub: "(v1 \<^sub>v* A) $ i - (v2 \<^sub>v* A) $ i = (v1 \<^sub>v* A - v2 \<^sub>v* A) $ i"
        using carrier_mult1 carrier_mult2 i_less_m by simp
      show "((v1 - v2) \<^sub>v* A) $ i = (v1 \<^sub>v* A - v2 \<^sub>v* A) $ i"
        using lhs_expand vec_sub_expand mult_distrib sum_distrib back_to_mult to_vec_sub by simp
    qed
  qed

lemma matrix_vector_inequality:
  fixes c :: "('a::{real_normed_field,real_inner}, 'nr::finite, 'nc::finite) fixed_mat"
    and U :: "('a, 'nr) fixed_vec set"
    and C :: real
  assumes C_bound: "C \<ge> norm c"
      and C_nonneg: "C \<ge> 0"
  shows "\<And>x y. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> 
    sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2) \<le>
    C * sqrt (\<Sum>i = 0..<CARD('nr). (norm (fixed_vec_index (x - y) i))\<^sup>2)"
proof -
  fix x y :: "('a, 'nr) fixed_vec"
  assume x_in_U: "x \<in> U" and y_in_U: "y \<in> U"
  let ?x_rep = "Rep_fixed_vec x"
  let ?y_rep = "Rep_fixed_vec y"
  let ?c_rep = "Rep_fixed_mat c"
  have vec_mat_mult_diff: "x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c = Abs_fixed_vec (?x_rep \<^sub>v* ?c_rep - ?y_rep \<^sub>v* ?c_rep)"
  proof -
    have vec_mat_mult_x: "x \<^sub>f\<^sub>v* c = Abs_fixed_vec (?x_rep \<^sub>v* ?c_rep)"
      by (simp add: mult_vec_fixed_mat_def mult_vec_mat_def)  
    have vec_mat_mult_y: "y \<^sub>f\<^sub>v* c = Abs_fixed_vec (?y_rep \<^sub>v* ?c_rep)"
      by (simp add: mult_vec_fixed_mat_def mult_vec_mat_def)
    have "x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c = Abs_fixed_vec (?x_rep \<^sub>v* ?c_rep) - Abs_fixed_vec (?y_rep \<^sub>v* ?c_rep)"
      using vec_mat_mult_x vec_mat_mult_y by simp 
    also have "... = Abs_fixed_vec ((?x_rep \<^sub>v* ?c_rep) - (?y_rep \<^sub>v* ?c_rep))"
    proof -
      have carrier_vx: "(?x_rep \<^sub>v* ?c_rep) \<in> carrier_vec (CARD('nc))"
        using Rep_fixed_vec  
        by (metis mult_vec_fixed_mat.rep_eq mult_vec_mat_def)      
      have carrier_vy: "(?y_rep \<^sub>v* ?c_rep) \<in> carrier_vec (CARD('nc))"
        using Rep_fixed_vec  
        by (metis mult_vec_fixed_mat.rep_eq mult_vec_mat_def)       
      show ?thesis
        using carrier_vx carrier_vy 
        by (simp add: fixed_vec_add minus_add_uminus_vec pth_2 uminus_fixed_vec)
    qed   
    finally show ?thesis by simp
  qed
  have vec_mat_mult_linear: "?x_rep \<^sub>v* ?c_rep - ?y_rep \<^sub>v* ?c_rep = (?x_rep - ?y_rep) \<^sub>v* ?c_rep"
  proof -
    have "?x_rep \<^sub>v* ?c_rep - ?y_rep \<^sub>v* ?c_rep = (?x_rep - ?y_rep) \<^sub>v* ?c_rep"
      using Rep_fixed_vec Rep_fixed_mat 
      using mult_vec_mat_distrib_left 
      by metis
    thus ?thesis by simp
  qed
  have c_mult_diff: "x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c = Abs_fixed_vec ((?x_rep - ?y_rep) \<^sub>v* ?c_rep)"
    using vec_mat_mult_diff vec_mat_mult_linear by simp
  have vec_index_eq: "\<forall>i < CARD('nc). 
    fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i = ((?x_rep - ?y_rep) \<^sub>v* ?c_rep) $ i"
  proof (intro allI impI)
    fix i
    assume "i < CARD('nc)"
    show "fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i = ((?x_rep - ?y_rep) \<^sub>v* ?c_rep) $ i"
        using c_mult_diff
      by (metis (mono_tags, lifting) Abs_fixed_vec_inverse Rep_fixed_mat carrier_matD(2) 
          fixed_vec_index.rep_eq mult_vec_mat_def vec_carrier) 
  qed
  have vec_mat_expand: "\<forall>i < CARD('nc). 
    ((?x_rep - ?y_rep) \<^sub>v* ?c_rep) $ i = (\<Sum>j = 0..<CARD('nr). (?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i))"
  proof (intro allI impI)
    fix i
    assume "i < CARD('nc)"
    show "((?x_rep - ?y_rep) \<^sub>v* ?c_rep) $ i = (\<Sum>j = 0..<CARD('nr). (?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i))"
    proof -
      have carrier_diff: "(?x_rep - ?y_rep) \<in> carrier_vec (CARD('nr))"
        using Rep_fixed_vec 
        using minus_carrier_vec by blast     
      have carrier_c: "?c_rep \<in> carrier_mat (CARD('nr)) (CARD('nc))"
        by (rule Rep_fixed_mat)      
      show ?thesis
        using carrier_diff carrier_c \<open>i < CARD('nc)\<close>
        mult_vec_mat_def scalar_prod_def 
        by (simp add: index_vec_mat_mult)
    qed
  qed  
  have triangle_step: "(\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2) \<le>
    (\<Sum>i = 0..<CARD('nc). (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j) * norm (?c_rep $$ (j, i)))\<^sup>2)"
  proof -
    have "\<forall>i < CARD('nc). 
      norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) \<le> 
      (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i)))"
    proof (intro allI impI)
      fix i
      assume "i < CARD('nc)"     
      have "norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) = 
            norm (((?x_rep - ?y_rep) \<^sub>v* ?c_rep) $ i)"
        using vec_index_eq \<open>i < CARD('nc)\<close> by simp     
      also have "... = norm (\<Sum>j = 0..<CARD('nr). (?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i))"
        using vec_mat_expand \<open>i < CARD('nc)\<close> by simp     
      also have "... \<le> (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i)))"
        by (rule norm_sum)      
      finally show "norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) \<le> 
                    (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i)))" .
    qed    
    moreover have "\<forall>i < CARD('nc). \<forall>j < CARD('nr).
      norm ((?x_rep - ?y_rep) $ j * ?c_rep $$ (j, i)) = 
      norm ((?x_rep - ?y_rep) $ j) * norm (?c_rep $$ (j, i))"
      using norm_mult by blast
    ultimately show ?thesis   
    proof -
      have "\<forall>i < CARD('nc). 
        (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2 \<le> 
        (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j) * norm (Rep_fixed_mat c $$ (j, i)))\<^sup>2"
      proof (intro allI impI)
        fix i
        assume "i < CARD('nc)"    
        have "norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) \<le> 
              (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j * Rep_fixed_mat c $$ (j, i)))"
          using \<open>\<forall>i<CARD('nc). norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) \<le> (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j * Rep_fixed_mat c $$ (j, i)))\<close>
          using \<open>i < CARD('nc)\<close> by blast    
        also have "... = (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j) * norm (Rep_fixed_mat c $$ (j, i)))"
          using \<open>\<forall>i<CARD('nc). \<forall>j<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j * Rep_fixed_mat c $$ (j, i)) = norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j) * norm (Rep_fixed_mat c $$ (j, i))\<close>
          using \<open>i < CARD('nc)\<close> by simp    
        finally have "norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i) \<le> 
                      (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j) * norm (Rep_fixed_mat c $$ (j, i)))" .
        thus "(norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2 \<le> 
              (\<Sum>j = 0..<CARD('nr). norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ j) * norm (Rep_fixed_mat c $$ (j, i)))\<^sup>2"  
          using norm_ge_zero power_mono by blast 
      qed
      thus ?thesis
        by (meson atLeastLessThan_iff sum_mono)
    qed
  qed
  have cauchy_schwarz_step: 
    "(\<Sum>i = 0..<CARD('nc). (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j) * norm (?c_rep $$ (j, i)))\<^sup>2) \<le>
    (\<Sum>i = 0..<CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2))"
  proof -
    have "\<forall>i < CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j) * norm (?c_rep $$ (j, i)))\<^sup>2 \<le>
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2)"
    proof (intro allI impI)
      fix i
      assume "i < CARD('nc)"    
      let ?a = "\<lambda>j. norm ((?x_rep - ?y_rep) $ j)"
      let ?b = "\<lambda>j. norm (?c_rep $$ (j, i))"      
      have nonneg_a: "\<forall>j. ?a j \<ge> 0" by simp
      have nonneg_b: "\<forall>j. ?b j \<ge> 0" by simp      
      have "(\<Sum>j = 0..<CARD('nr). ?a j * ?b j)\<^sup>2 \<le> (\<Sum>j = 0..<CARD('nr). (?a j)\<^sup>2) * (\<Sum>j = 0..<CARD('nr). (?b j)\<^sup>2)"
        by (simp add: Cauchy_Schwarz_ineq_sum)      
      thus "(\<Sum>j = 0..<CARD('nr). norm ((?x_rep - ?y_rep) $ j) * norm (?c_rep $$ (j, i)))\<^sup>2 \<le>
            (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) * (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2)"
        by simp
    qed    
    thus ?thesis by (meson atLeastLessThan_iff sum_mono)
  qed
  have factor_step:
    "(\<Sum>i = 0..<CARD('nc). 
      (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) * 
      (\<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2)) =
    (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) * 
    (\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2)"
    by (simp add: sum_distrib_left)
  have norm_vec_diff_eq: "(\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2) = (norm (x - y))\<^sup>2"
  proof -
    have "norm (x - y) = sqrt (\<Sum>j = 0..<CARD('nr). (norm (fixed_vec_index (x - y) j))\<^sup>2)"
      unfolding norm_fixed_vec_def by blast
    also have "... = sqrt (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2)"
    proof -
      have "\<forall>j < CARD('nr). fixed_vec_index (x - y) j = (?x_rep - ?y_rep) $ j"
      proof (intro allI impI)
        fix j
        assume "j < CARD('nr)"
        show "fixed_vec_index (x - y) j = (?x_rep - ?y_rep) $ j"
        proof -
          have "fixed_vec_index (x - y) j = Rep_fixed_vec (x - y) $ j"
            by (simp add: fixed_vec_index_def)        
          also have "... = (?x_rep - ?y_rep) $ j"
            by (smt (verit, ccfv_threshold) Abs_fixed_vec_inverse Matrix.minus_vec_def 
                Rep_fixed_vec carrier_vecD fixed_vec_add minus_add_uminus_vec minus_fixed_vec.rep_eq 
                pth_2 uminus_fixed_vec vec_carrier zero_minus_vec)         
          finally show ?thesis .
        qed
      qed     
      thus ?thesis by simp
    qed   
    finally have "norm (x - y) = sqrt (\<Sum>j = 0..<CARD('nr). (norm ((?x_rep - ?y_rep) $ j))\<^sup>2)" .    
    thus ?thesis by (metis norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
  qed
  have norm_mat_eq: "(\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2) = (norm c)\<^sup>2"
  proof -
    have "(\<Sum>i = 0..<CARD('nc). \<Sum>j = 0..<CARD('nr). (norm (?c_rep $$ (j, i)))\<^sup>2) =
          (\<Sum>j = 0..<CARD('nr). \<Sum>i = 0..<CARD('nc). (norm (?c_rep $$ (j, i)))\<^sup>2)"
      by (rule sum.swap)   
    also have "... = (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index c i j))\<^sup>2)"
    proof -
      have "\<forall>i < CARD('nr). \<forall>j < CARD('nc). 
        norm (?c_rep $$ (i, j)) = norm (fixed_mat_index c i j)"
      proof (intro allI impI)
        fix i j
        assume "i < CARD('nr)" and "j < CARD('nc)"       
        have "fixed_mat_index c i j = ?c_rep $$ (i, j)"
          by (simp add: fixed_mat_index_def)        
        thus "norm (?c_rep $$ (i, j)) = norm (fixed_mat_index c i j)"
          by simp
      qed      
      thus ?thesis by simp
    qed    
    also have "... = (norm c)\<^sup>2"
    proof -
      have "norm c = sqrt (\<Sum>i = 0..<CARD('nr). \<Sum>j = 0..<CARD('nc). (norm (fixed_mat_index c i j))\<^sup>2)"
        unfolding norm_fixed_mat_def by blast     
      thus ?thesis by (metis norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2)
    qed    
    finally show ?thesis .
  qed
  have matrix_ineq: "(\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2) \<le>
    (norm (x - y))\<^sup>2 * (norm c)\<^sup>2"
    using triangle_step cauchy_schwarz_step factor_step norm_vec_diff_eq norm_mat_eq by simp
  have "sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2) \<le>
        sqrt ((norm (x - y))\<^sup>2 * (norm c)\<^sup>2)"
    using matrix_ineq 
    using real_sqrt_le_iff by blast
  also have "... = norm (x - y) * norm c"
  proof -
    have "sqrt ((norm (x - y))\<^sup>2 * (norm c)\<^sup>2) = sqrt ((norm (x - y))\<^sup>2) * sqrt ((norm c)\<^sup>2)"
      by (rule real_sqrt_mult)   
    also have "... = norm (x - y) * norm c"
      by simp    
    finally show ?thesis by simp
  qed
  also have "... = norm c * norm (x - y)"
    by (simp add: mult.commute)
  also have "... \<le> C * norm (x - y)"
    using C_bound C_nonneg by (simp add: mult_right_mono norm_ge_zero)
  also have "... = C * sqrt ((norm (x - y))\<^sup>2)"
    by simp 
  also have "... = C * sqrt (\<Sum>i = 0..<CARD('nr). (norm (fixed_vec_index (x - y) i))\<^sup>2)"
  proof -
    have "norm (x - y) = sqrt (\<Sum>i = 0..<CARD('nr). (norm (fixed_vec_index (x - y) i))\<^sup>2)"
      unfolding norm_fixed_vec_def by blast    
    thus ?thesis 
      using \<open>(C::real) * norm ((x::('a, 'nr) fixed_vec) - (y::('a, 'nr) fixed_vec)) = C * sqrt ((norm (x - y))\<^sup>2)\<close> by presburger
  qed 
  finally show "sqrt (\<Sum>i = 0..<CARD('nc). (norm (fixed_vec_index (x \<^sub>f\<^sub>v* c - y \<^sub>f\<^sub>v* c) i))\<^sup>2) \<le>
                C * sqrt (\<Sum>i = 0..<CARD('nr). (norm (fixed_vec_index (x - y) i))\<^sup>2)" .
qed

lemma lipschitz_on_vec_mult:
  assumes \<open>0 \<le> C \<close> and "norm c \<le> C"
  shows \<open>C-lipschitz_on U (\<lambda> y . y \<^sub>f\<^sub>v* (c::('a:: {real_inner,real_normed_field}, 'nr::finite, 'nc::finite) fixed_mat))\<close>
  unfolding mult_vec_mat_def lipschitz_on_def 
  apply (intro conjI impI allI) 
  unfolding dist_fixed_vec_def dist_fixed_mat_def
  unfolding norm_fixed_vec_def norm_fixed_mat_def
  subgoal using assms by blast
  subgoal using matrix_vector_inequality[of c C _ U _] 
    using assms(1) assms(2) by blast
  done

lemma C_ge_norm: 
  "norm (c::('a:: {real_algebra_1,real_normed_vector}, 'nr::finite, 'nc::finite) fixed_mat) \<le> C \<Longrightarrow> 0 \<le> C"
  by (smt (verit, ccfv_SIG) norm_ge_zero)

lemma lipschitz_on_weighted_sum_bias':
  assumes "norm c \<le> C"
  shows \<open>C-lipschitz_on U (\<lambda> y . (y \<^sub>f\<^sub>v* (c::('a:: {real_inner,real_normed_field}, 'nr::finite, 'nc::finite) fixed_mat)) + b)\<close>
  using lipschitz_on_vec_mult assms C_ge_norm[of c C, simplified assms, simplified]
  using Lipschitz.lipschitz_on_constant lipschitz_on_add 
  by fastforce

lemma lipschitz_on_dense:
  assumes "norm c \<le> C"
  assumes "D-lipschitz_on ((\<lambda>y. (c::('a:: {real_inner,real_normed_field}, 'n::finite) fixed_vec) \<^sub>f\<^sub>v* y + b) ` U) f"
  shows "(D * C)-lipschitz_on U (\<lambda> y . f ((c \<^sub>f\<^sub>v* y) + b))"
  using lipschitz_on_weighted_sum_bias[of D c ]
  using lipschitz_on_compose2[of D "U" "\<lambda> y . (c \<^sub>f\<^sub>v* y) + b" C f, simplified assms]
  using assms(1) assms(2) lipschitz_on_compose2 lipschitz_on_weighted_sum_bias 
proof -
  have "0 \<le> C"
    by (meson assms(1) landau_o.R_trans norm_ge_zero)
  then show ?thesis
    using assms(1) assms(2) lipschitz_on_compose2 lipschitz_on_weighted_sum_bias by blast
qed


lemma lipschitz_on_dense':
  assumes "norm c \<le> C"
  assumes "D-lipschitz_on ((\<lambda>y. y  \<^sub>f\<^sub>v* (c::('a:: {real_inner,real_normed_field}, 'nr::finite, 'nc::finite) fixed_mat) + b) ` U) f"
  shows "(D * C)-lipschitz_on U (\<lambda> y . f ((y  \<^sub>f\<^sub>v* c) + b))"
  using lipschitz_on_weighted_sum_bias[of D _ _ b ]
  using lipschitz_on_compose2[of D "U" "\<lambda> y . (y \<^sub>f\<^sub>v* c) + b" C f, simplified assms]
  using assms(1) assms(2) lipschitz_on_compose2 lipschitz_on_weighted_sum_bias
  using lipschitz_on_weighted_sum_bias' by blast


lemma lipschitz_on_input_ouput:
  shows "1-lipschitz_on U (\<lambda> i  . i)"
  unfolding lipschitz_on_def by simp

lemma lipschhitz_on_activation:
  assumes "C-lipschitz_on U f"
  shows "C-lipschitz_on U (\<lambda> i . f i)"
  using assms by simp

paragraph \<open>Neural Network: Layers\<close> 

fun  predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f ::  "(('a::{real_algebra_1,real_normed_vector}, 'b::finite) fixed_vec, 'c, 'd) neural_network_seq_layers
     \<Rightarrow> ('a, 'b::finite) fixed_vec  \<Rightarrow> (('a, 'b) fixed_vec, 'c, ('a, 'b, 'b) fixed_mat) layer \<Rightarrow> ('a, 'b) fixed_vec " 
  where
    \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N (vs) (In l)  =  vs \<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N (vs) (Out l) =  vs\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N (vs) (Dense pl) = ((the (activation_tab N (\<phi> pl))) ((vs \<^sub>f\<^sub>v*  \<omega> pl) + \<beta> pl)) \<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N (vs) (Activation pl) = ((the (activation_tab N (\<phi> pl))) vs) \<close>

definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>f N inputs = foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) inputs (layers N)\<close>


definition \<open>lipschitz_continuous_activation_tab\<^sub>f tab U = (\<forall> f \<in> ran (tab). \<exists> C. C-lipschitz_on U f)\<close>

lemma input_layer_lipschitz_on:
  "1-lipschitz_on U ((\<lambda> vs . (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs (In x1))))" 
  by (simp add: lipschitz_on_def) 

lemma output_layer_lipschitz_on:
  "1-lipschitz_on U ((\<lambda> vs . (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs (Out x1))))"
  by (simp add: lipschitz_on_def) 

lemma dense_layer_lipschitz_on:
  assumes "norm (\<omega> x1) \<le> C"
  assumes "D-lipschitz_on ((\<lambda>y. y \<^sub>f\<^sub>v* \<omega> x1 + \<beta> x1) ` U) (the (activation_tab N (\<phi> x1)))"
  shows "(C * D)-lipschitz_on U (\<lambda> vs::('a:: {real_inner,real_normed_field}, 'c::finite) fixed_vec . (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs (Dense x1)))"
  using predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f.simps(3)[of N _ x1]
  using lipschitz_on_dense'[of "\<omega> x1" C D "\<beta> x1" U, simplified assms] 
  by (metis (no_types, lifting) assms(2) lipschitz_on_transform mult_commute_abs)

lemma activation_layer_lipschitz_on:
  assumes "C-lipschitz_on U (the (activation_tab N (\<phi> x1)))"
  shows "C-lipschitz_on U (\<lambda> vs . (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs (Activation x1)))"
  using assms by simp

lemma foldl_layer_lipschitz_on:
  fixes N :: "(('a::{real_algebra_1,real_normed_vector}, 'b::finite) fixed_vec, 'c, 'd) neural_network_seq_layers"
  assumes layer_lipschitz: "\<forall>l \<in> set ls. \<exists>C. C-lipschitz_on U (\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)"
  assumes domain_invariant: "\<forall>l \<in> set ls. \<forall>vs \<in> U. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l \<in> U"
  shows "\<exists>C. C-lipschitz_on U (\<lambda>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs ls)"
  using assms
proof (induction ls )
  case Nil
  then show ?case 
    by (auto simp: lipschitz_on_def intro: exI[where x=1])
next
  case (Cons l ls)
  have l: "l \<in> set (l#ls)" using Cons by simp 
  obtain C1 where h1: "C1-lipschitz_on U (\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)" 
    using Cons(2) by auto
  obtain C2 where h2: "C2-lipschitz_on U (\<lambda>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs ls)"
    using Cons by auto
  have fold_step: "\<forall>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs (l # ls) = 
                        foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l) ls"
    by simp
  have composition: "\<forall>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs (l # ls) = 
                          (\<lambda>x. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) x ls) (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)"
    using fold_step by simp
  have image_in_domain: "(\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l) ` U \<subseteq> U"
    using Cons(1) h1 h2 
    using l local.Cons(3) by fastforce  
  have "(C1 * C2)-lipschitz_on U (\<lambda>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs (l # ls))"
    using lipschitz_on_compose[of C1 U "(\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)" C2 "(\<lambda>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs ls)", simplified h1, simplified]
      image_in_domain composition  
  proof -
    have "(C2 * C1)-lipschitz_on U (\<lambda>f. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) f (l # ls))"
      using \<open>C2-lipschitz_on ((\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l) ` U) (\<lambda>vs. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) vs ls) \<Longrightarrow> (C2 * C1)-lipschitz_on U (\<lambda>x. foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N) (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N x l) ls)\<close> h2 image_in_domain lipschitz_on_subset by force
    then show ?thesis
      by argo
  qed
  thus ?case by auto
qed

lemma layers_lipschitz_from_components:
  fixes N :: "(('a::{real_algebra_1,real_normed_vector,real_inner,real_normed_field}, 'b::finite) fixed_vec, 'c, 'd) neural_network_seq_layers"
  assumes weight_bounded: "\<forall>l \<in> set ls. (case l of Dense pl \<Rightarrow> norm (\<omega> pl) \<le> W )"
  assumes activation_lipschitz: "\<forall>l \<in> set ls. (case l of 
    Dense pl \<Rightarrow> \<exists>D. D-lipschitz_on ((\<lambda>y. y \<^sub>f\<^sub>v* \<omega> pl + \<beta> pl) ` U) (the (activation_tab N (\<phi> pl))) |
    Activation pl \<Rightarrow> \<exists>C. C-lipschitz_on U (the (activation_tab N (\<phi> pl))))"
  shows "\<forall>l \<in> set ls. \<exists>C. C-lipschitz_on U (\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)"
proof
  fix l assume "l \<in> set ls"
  show "\<exists>C. C-lipschitz_on U (\<lambda>vs. predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>f N vs l)"
  proof (cases l)
    case (In x)
    then show ?thesis using input_layer_lipschitz_on by blast
  next
    case (Out x)
    then show ?thesis using output_layer_lipschitz_on by blast
  next
    case (Dense x)
    obtain D where "D-lipschitz_on ((\<lambda>y. y \<^sub>f\<^sub>v* \<omega> x + \<beta> x) ` U) (the (activation_tab N (\<phi> x)))"
      using activation_lipschitz Dense \<open>l \<in> set ls\<close> 
      by fastforce
    moreover have "norm (\<omega> x) \<le> W"
      using weight_bounded Dense \<open>l \<in> set ls\<close> by auto
    ultimately show ?thesis 
      using dense_layer_lipschitz_on[of x W D U N] Dense
      by auto
  next
    case (Activation x)
    obtain C where "C-lipschitz_on U (the (activation_tab N (\<phi> x)))"
      using activation_lipschitz Activation \<open>l \<in> set ls\<close> by fastforce
    then show ?thesis 
      using activation_layer_lipschitz_on Activation
      by auto
  qed
qed

lemma Rep_fixed_vec_minus: "Rep_fixed_vec (x - y) = Rep_fixed_vec x - Rep_fixed_vec y"
proof -
  have "x - y = Abs_fixed_vec (Rep_fixed_vec x + smult_vec (-1) (Rep_fixed_vec y))"
    unfolding minus_fixed_vec_def minus_fixed_vec.rep_eq uminus_fixed_vec.rep_eq
    by (simp add: Rep_fixed_vec_inverse)
  then have "Rep_fixed_vec (x - y) = Rep_fixed_vec x + smult_vec (-1) (Rep_fixed_vec y)"
    using minus_fixed_vec.rep_eq by blast
  also have "... = Rep_fixed_vec x + (- Rep_fixed_vec y)"
    by (simp add: smult_vec_def uminus_vec_def)
  also have "... = Rep_fixed_vec x - Rep_fixed_vec y"
    using Rep_fixed_vec by fastforce
  finally show ?thesis .
qed

subsubsection \<open>Lipschitz Continuity of Functions (Interval)\<close>
 
paragraph \<open>Neural Network: Activations\<close>

lemma relu_lipschitz': "\<And>x y. (x::(real, 'b::finite) fixed_vec) \<in> X \<Longrightarrow>
           (y::(real, 'b::finite) fixed_vec) \<in> X \<Longrightarrow>
           dist
            ((Abs_fixed_vec
              (Matrix.vec (dim_vec (Rep_fixed_vec x))
                (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)))::(real, 'b::finite) fixed_vec)
            ((Abs_fixed_vec
              (Matrix.vec (dim_vec (Rep_fixed_vec y))
                (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b::finite) fixed_vec)
           \<le> dist x y" 
proof -
  fix x y::"(real, 'b::finite) fixed_vec"  assume "x \<in> X" "y \<in> X"
  have dist_eq: "dist ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (x::(real, 'b) fixed_vec))) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)))::(real, 'b) fixed_vec)
                      ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (y::(real, 'b) fixed_vec))) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec)
                = norm ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (x::(real, 'b) fixed_vec))) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0))::(real, 'b) fixed_vec)
                      - (Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (y::(real, 'b) fixed_vec))) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec)"
    by (simp add: dist_norm) 
  have relu_bound: "\<forall>a b::real. abs (max 0 a - max 0 b) \<le> abs (a - b)"
  proof (intro allI)
    fix a b :: real
    have "1-lipschitz_on {a, b} relu"
      using relu_lipschitz[of "UNIV"]
      by (rule lipschitz_on_subset) auto
    show "abs (max 0 a - max 0 b) \<le> abs (a - b)"
      unfolding lipschitz_on_def relu_def dist_real_def
      by auto
  qed
  have norm_bound: "norm ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0))
                        - Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b::finite) fixed_vec)
                   \<le> norm (x - y)"
  proof -
    have "norm ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0))
              - Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec)
          = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0))
                                                            - Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec) i))^2)"
      unfolding norm_fixed_vec_def by simp    
    also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (abs ((if 0 \<le> vec_index (Rep_fixed_vec (x::(real, 'b) fixed_vec)) i then vec_index (Rep_fixed_vec (x::(real, 'b) fixed_vec)) i else 0) 
                                                   - (if 0 \<le> vec_index (Rep_fixed_vec (y::(real, 'b) fixed_vec)) i then vec_index (Rep_fixed_vec (y::(real, 'b) fixed_vec)) i else 0)))^2)"
    proof -
      show ?thesis 
        proof -
          have valid_x: "Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) \<in> carrier_vec CARD('b)"
          proof -
            have "dim_vec (Rep_fixed_vec x) = CARD('b)"
              using Rep_fixed_vec[of x] by simp 
            then show ?thesis 
              using vec_carrier_vec by blast
          qed
          have valid_y: "Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0) \<in> carrier_vec CARD('b)"
          proof -
            have "dim_vec (Rep_fixed_vec y) = CARD('b)"
              using Rep_fixed_vec[of y] by simp
            then show ?thesis using vec_carrier_vec by blast
          qed
          have index_eq: "\<forall>i < CARD('b). 
            fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)) -
                             Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b::finite) fixed_vec) i
            = (if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) - 
              (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)"
          proof (clarify)
            fix i assume "i < CARD('b)"
            have "fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. if 0 \<le> Rep_fixed_vec x $ j then Rep_fixed_vec x $ j else 0)) -
                                  Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. if 0 \<le> Rep_fixed_vec y $ j then Rep_fixed_vec y $ j else 0)))::(real, 'b) fixed_vec) i
                  = Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. if 0 \<le> Rep_fixed_vec x $ j then Rep_fixed_vec x $ j else 0)) -
                                  Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. if 0 \<le> Rep_fixed_vec y $ j then Rep_fixed_vec y $ j else 0)))::(real, 'b) fixed_vec) $ i"
              by (simp add: fixed_vec_index_def)
            also have "... = (Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. if 0 \<le> Rep_fixed_vec x $ j then Rep_fixed_vec x $ j else 0)))::(real, 'b) fixed_vec) -
                              Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. if 0 \<le> Rep_fixed_vec y $ j then Rep_fixed_vec y $ j else 0)))::(real, 'b) fixed_vec)) $ i"
              using Rep_fixed_vec_minus 
              by (smt (verit, del_insts))
            also have "... = (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. if 0 \<le> Rep_fixed_vec x $ j then Rep_fixed_vec x $ j else 0) -
                             Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. if 0 \<le> Rep_fixed_vec y $ j then Rep_fixed_vec y $ j else 0)) $ i"
              using Abs_fixed_vec_inverse[OF valid_x] Abs_fixed_vec_inverse[OF valid_y] by simp
            also have "... = Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. if 0 \<le> Rep_fixed_vec x $ j then Rep_fixed_vec x $ j else 0) $ i -
                             Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. if 0 \<le> Rep_fixed_vec y $ j then Rep_fixed_vec y $ j else 0) $ i"
              apply (simp add: minus_vec_def) using \<open>(i::nat) < CARD('b::finite)\<close> valid_y by fastforce 
            also have "... = (if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) - 
                             (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)"
            proof -
              have "dim_vec (Rep_fixed_vec x) = CARD('b)" using Rep_fixed_vec[of x] by simp 
              have "dim_vec (Rep_fixed_vec y) = CARD('b)" using Rep_fixed_vec[of y] by simp 
              then show ?thesis using `i < CARD('b)` 
                by (simp add: \<open>dim_vec (Rep_fixed_vec (x::(real, 'b::finite) fixed_vec)) = CARD('b::finite)\<close>)
            qed
            finally show " fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)) -
                             Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b::finite) fixed_vec) i
            = (if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) - 
              (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)" .
          qed
          have "sqrt (\<Sum>i = 0..<CARD('b). (norm (fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)) -
                                                                   Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b::finite) fixed_vec) i))^2)
                = sqrt (\<Sum>i = 0..<CARD('b). (norm ((if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) - 
                                                  (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))^2)"
            using index_eq by simp
          also have "... = sqrt (\<Sum>i = 0..<CARD('b). abs ((if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) - 
                                                          (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0))^2)"
            by (simp add: real_norm_def)
          finally show ?thesis .
        qed
    qed
    also have "... \<le> sqrt (\<Sum>i\<in>{0..<CARD('b)}. (abs (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i))^2)"
    proof -
      have "\<forall>i. abs ((if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0) 
                    - (if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0))
               \<le> abs (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i)"
        using relu_bound by (auto simp: max_def)
      then show ?thesis
        using sum_mono power_mono 
        by (smt (verit, best) real_sqrt_le_mono) 
    qed
    also have "... = norm (x - y)"
   proof -
      have "norm (x - y) = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (fixed_vec_index (x - y) i))^2)"
        by (simp add: norm_fixed_vec_def)
      also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (Rep_fixed_vec (x - y) $ i))^2)"
        by (simp add: fixed_vec_index_def)
      also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ i))^2)"
        using Rep_fixed_vec_minus by metis
      also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i))^2)"
        apply (simp add: minus_vec_def)
        by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux Rep_fixed_vec atLeastLessThan_iff carrier_vecD index_vec)
      also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. \<bar>Rep_fixed_vec x $ i - Rep_fixed_vec y $ i\<bar>^2)"
        by simp
      finally show ?thesis by simp
    qed
    finally show " norm
     ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (x::(real, 'b::finite) fixed_vec))) (\<lambda>i::nat. if (0::real) \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else (0::real))) -
      Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (y::(real, 'b::finite) fixed_vec))) (\<lambda>i::nat. if (0::real) \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else (0::real))))::(real, 'b::finite) fixed_vec)
    \<le> norm (x - y)" by simp
  qed
  have a0: " map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) x = 
            Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. relu (Rep_fixed_vec x $ i)))" 
    unfolding relu_def max_def
        by (simp add: map_fun_def)   
  moreover have a1: "map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) y = 
                     Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. relu (Rep_fixed_vec y $ i)))" 
    unfolding relu_def max_def
    by (simp add: map_fun_def)
  also have a2: "dist ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) x)::(real, 'b) fixed_vec)
            ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) y)::(real, 'b) fixed_vec)
           \<le> 1 * dist x y = 
           ( dist ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)))::(real, 'b) fixed_vec)
            ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec)
           \<le>1 *  dist x y )"   
    apply (subst a0 a1)+
    unfolding relu_def max_def 
    by blast 
  have b0: "dist ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) x)::(real, 'b) fixed_vec)
            ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) (\<lambda>b. if 0 \<le> b then b else 0) y)::(real, 'b) fixed_vec)
           \<le> 1 * dist x y"
    using dist_eq norm_bound a0 a1 a2  dist_norm     
    by (smt (verit, del_insts))
  show " dist
        ((Abs_fixed_vec
          (Matrix.vec (dim_vec (Rep_fixed_vec x))
            (\<lambda>i::nat. if 0 \<le> Rep_fixed_vec x $ i then Rep_fixed_vec x $ i else 0)))::(real, 'b) fixed_vec)
        ((Abs_fixed_vec
          (Matrix.vec (dim_vec (Rep_fixed_vec y))
            (\<lambda>i::nat. if 0 \<le> Rep_fixed_vec y $ i then Rep_fixed_vec y $ i else 0)))::(real, 'b) fixed_vec)
       \<le> dist x y"
    using a0 a1 a2 b0 
    by argo 
qed
  
lemma relu_lipschitz_fv: "1-lipschitz_on (X::(real, 'b::finite) fixed_vec set) (map_fixed_vec relu)"
  unfolding lipschitz_on_def relu_def map_fixed_vec_def max_def map_vec_def
  apply (intro conjI impI allI)
  subgoal using rel_simps(44) by blast 
  subgoal using relu_lipschitz'[of _ X] by simp
  done 


lemma identity_lipschitz_fv: "1-lipschitz_on (X) (map_fixed_vec identity)"
  unfolding lipschitz_on_def relu_def map_fixed_vec_def  map_vec_def 
  by (auto, smt (verit) Rep_fixed_vec_inverse dim_vec eq_vecI identity_def 
      index_vec verit_comp_simplify1(2)) 

lemma softplus_lipschitz': " \<And>x y. (x::(real, 'b::finite) fixed_vec) \<in> X \<Longrightarrow>
           (y::(real, 'b::finite) fixed_vec) \<in> X \<Longrightarrow>
           dist ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus x)::(real, 'b) fixed_vec)
            (map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus y)
           \<le> 1 * dist x y"
proof -
  fix x y::"(real, 'b::finite) fixed_vec" assume "x \<in> X" "y \<in> X"
  have softplus_bound: "\<forall>a b::real. abs (softplus a - softplus b) \<le> abs (a - b)"
  proof (intro allI)
    fix a b :: real
    have deriv_bound: "\<forall> (z::real) . softplus' z \<le> 1"
    proof -
      fix z :: real
      have "softplus' z = 1 / (1 + exp(-z))"
        by (simp add: softplus'_def)
      also have "... \<le> 1"
        by (simp add: add_sign_intros(2))
      finally show ?thesis 
        by (simp add: add_sign_intros(2) softplus'_def)
    qed
    have cont: "continuous_on {min a b..max a b} softplus"
      by (meson DERIV_isCont softplus' continuous_at_imp_continuous_on) 
    have diff: "\<And>x. min a b < x \<Longrightarrow> x < max a b \<Longrightarrow> softplus differentiable at x"
      using real_differentiable_def softplus' by blast 
    have mvt: "\<exists>c. softplus b - softplus a = (b - a) * softplus' c"
    proof (cases "a = b")
      case True
      then have "softplus b - softplus a = 0" by simp
      also have "... = (b - a) * softplus' a" using True by simp
      finally show ?thesis by blast
    next
      case False
      obtain l c where c_bounds: "min a b < c \<and> c < max a b" and
        has_deriv: "(softplus has_real_derivative l) (at c)" and
        mvt_eq: "softplus (max a b) - softplus (min a b) = (max a b - min a b) * l"
        using MVT[of "min a b" "max a b" softplus] cont diff False 
        by fastforce
      
      have "l = softplus' c"
        using has_deriv softplus'[of c] 
        by (simp add: DERIV_unique) 
        
      have result: "softplus b - softplus a = (b - a) * softplus' c"
      proof (cases "a \<le> b")
        case True
        then have "min a b = a" "max a b = b" by auto
        with mvt_eq `l = softplus' c` show ?thesis 
          by simp  
      next
        case False
        then have "min a b = b" "max a b = a" by auto
        with mvt_eq `l = softplus' c` have "softplus a - softplus b = (a - b) * softplus' c" by simp
        then show ?thesis by (simp add: algebra_simps)
      qed
      
      show ?thesis using result by blast
    qed
    
    obtain c where mvt_eq: "softplus b - softplus a = (b - a) * softplus' c"
      using mvt by blast

    have "abs (softplus a - softplus b) = abs (softplus b - softplus a)"
      by simp
    also have "... = abs ((b - a) * softplus' c)"
      using mvt_eq by simp
    also have "... = abs (b - a) * abs (softplus' c)"
      by (simp add: abs_mult)
    also have "... \<le> abs (b - a) * 1"
      using deriv_bound 
      apply (simp add: mult_left_mono) 
      by (smt (verit, ccfv_threshold) divide_pos_pos exp_ge_zero mult_left_le softplus'_def)  
    also have "... = abs (a - b)"
      by simp
    finally show "abs (softplus a - softplus b) \<le> abs (a - b)" .
  qed
     
  have "dist
        ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i)))
          softplus x)::(real, 'b::finite) fixed_vec)
        ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i)))
          softplus y)::(real, 'b::finite) fixed_vec)
       \<le> 1 * dist x y"

proof -
    have dist_eq: "dist ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (x::(real, 'b) fixed_vec))) (\<lambda>i. softplus (Rep_fixed_vec x $ i))))::(real, 'b) fixed_vec)
             ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (y::(real, 'b) fixed_vec))) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b) fixed_vec)
        = norm ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (x::(real, 'b) fixed_vec))) (\<lambda>i. softplus (Rep_fixed_vec x $ i)))::(real, 'b) fixed_vec) -
                (Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec (y::(real, 'b) fixed_vec))) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b) fixed_vec)"
       by (simp add: dist_norm softplus_def)
    
    also have "... \<le> norm (x - y)"
    proof -
      have "norm ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i)))
                - Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b) fixed_vec)
            = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i)))
                                                              - Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b) fixed_vec) i))^2)"
        unfolding norm_fixed_vec_def by simp    
      also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (abs (softplus (vec_index (Rep_fixed_vec (x::(real, 'b) fixed_vec)) i) 
                                                     - softplus (vec_index (Rep_fixed_vec (y::(real, 'b) fixed_vec)) i)))^2)"
      proof -
        show ?thesis 
          proof -
            have valid_x: "Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i)) \<in> carrier_vec CARD('b)"
            proof -
              have "dim_vec (Rep_fixed_vec x) = CARD('b)"
                using Rep_fixed_vec[of x] by simp 
              then show ?thesis 
                using vec_carrier_vec by blast
            qed
            have valid_y: "Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i)) \<in> carrier_vec CARD('b)"
            proof -
              have "dim_vec (Rep_fixed_vec y) = CARD('b)"
                using Rep_fixed_vec[of y] by simp
              then show ?thesis using vec_carrier_vec by blast
            qed
            have index_eq: "\<forall>i < CARD('b). 
              fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i))) -
                               Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b::finite) fixed_vec) i
              = softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i)"
            proof (clarify)
              fix i assume "i < CARD('b)"
              have "fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. softplus (Rep_fixed_vec x $ j))) -
                                    Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. softplus (Rep_fixed_vec y $ j))))::(real, 'b) fixed_vec) i
                    = Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. softplus (Rep_fixed_vec x $ j))) -
                                    Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. softplus (Rep_fixed_vec y $ j))))::(real, 'b) fixed_vec) $ i"
                by (simp add: fixed_vec_index_def)
              also have "... = (Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. softplus (Rep_fixed_vec x $ j))))::(real, 'b) fixed_vec) -
                                Rep_fixed_vec ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. softplus (Rep_fixed_vec y $ j))))::(real, 'b) fixed_vec)) $ i"
                using Rep_fixed_vec_minus 
                by (smt (verit, del_insts))
              also have "... = (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. softplus (Rep_fixed_vec x $ j)) -
                               Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. softplus (Rep_fixed_vec y $ j))) $ i"
                using Abs_fixed_vec_inverse[OF valid_x] Abs_fixed_vec_inverse[OF valid_y] by simp
              also have "... = Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>j. softplus (Rep_fixed_vec x $ j)) $ i -
                               Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>j. softplus (Rep_fixed_vec y $ j)) $ i"
                apply (simp add: minus_vec_def) using \<open>(i::nat) < CARD('b::finite)\<close> valid_y by fastforce 
              also have "... = softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i)"
              proof -
                have "dim_vec (Rep_fixed_vec x) = CARD('b)" using Rep_fixed_vec[of x] by simp 
                have "dim_vec (Rep_fixed_vec y) = CARD('b)" using Rep_fixed_vec[of y] by simp 
                then show ?thesis using `i < CARD('b)` 
                  by (simp add: \<open>dim_vec (Rep_fixed_vec (x::(real, 'b::finite) fixed_vec)) = CARD('b::finite)\<close>)
              qed
              finally show "fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i))) -
                               Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b::finite) fixed_vec) i
              = softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i)" .
            qed
            have "sqrt (\<Sum>i = 0..<CARD('b). (norm (fixed_vec_index ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i))) -
                                                                     Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i))))::(real, 'b::finite) fixed_vec) i))^2)
                  = sqrt (\<Sum>i = 0..<CARD('b). (norm (softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i)))^2)"
              using index_eq by simp
            also have "... = sqrt (\<Sum>i = 0..<CARD('b). abs (softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i))^2)"
              by (simp add: real_norm_def)
            finally show ?thesis .
          qed
      qed
      also have "... \<le> sqrt (\<Sum>i\<in>{0..<CARD('b)}. (abs (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i))^2)"
      proof -
        have "\<forall>i. abs (softplus (Rep_fixed_vec x $ i) - softplus (Rep_fixed_vec y $ i))
                 \<le> abs (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i)"
          using softplus_bound by auto
        then show ?thesis
          using sum_mono power_mono 
          by (smt (verit, best) real_sqrt_le_mono) 
      qed
      also have "... = norm (x - y)"
     proof -
        have "norm (x - y) = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (fixed_vec_index (x - y) i))^2)"
          by (simp add: norm_fixed_vec_def)
        also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (Rep_fixed_vec (x - y) $ i))^2)"
          by (simp add: fixed_vec_index_def)
        also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm ((Rep_fixed_vec x - Rep_fixed_vec y) $ i))^2)"
          using Rep_fixed_vec_minus by metis
        also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. (norm (Rep_fixed_vec x $ i - Rep_fixed_vec y $ i))^2)"
          apply (simp add: minus_vec_def)
          by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux Rep_fixed_vec atLeastLessThan_iff carrier_vecD index_vec)
        also have "... = sqrt (\<Sum>i\<in>{0..<CARD('b)}. \<bar>Rep_fixed_vec x $ i - Rep_fixed_vec y $ i\<bar>^2)"
          by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis by simp
    qed
    
    also have "... = dist x y"
      by (simp add: dist_norm)
      
    have a0: "dist ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i))))::(real, 'b::finite) fixed_vec) ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i::nat. softplus (Rep_fixed_vec y $ i))))::(real, 'b::finite) fixed_vec)
    \<le> dist x y" 
      by (metis calculation dist_norm)
          have map_fun_eq_x: "map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus x = 
                          Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i)))"
        by (simp add: map_fun_def)
        
      have map_fun_eq_y: "map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus y = 
                          Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i. softplus (Rep_fixed_vec y $ i)))"
        by (simp add: map_fun_def)

      have a1: " dist
     ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i)))
       softplus x)::(real, 'b) fixed_vec)
     ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i)))
       softplus y)::(real, 'b) fixed_vec)
    \<le> 1 * dist x y = 
     (dist ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec x)) (\<lambda>i. softplus (Rep_fixed_vec x $ i))))::(real, 'b::finite) fixed_vec) ((Abs_fixed_vec (Matrix.vec (dim_vec (Rep_fixed_vec y)) (\<lambda>i::nat. softplus (Rep_fixed_vec y $ i))))::(real, 'b::finite) fixed_vec)
    \<le> dist x y )"
        apply(subst map_fun_eq_x map_fun_eq_y )+
        by simp

     show "dist ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i))) softplus x)::(real, 'b::finite) fixed_vec)
     ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i))) softplus y)::(real, 'b::finite) fixed_vec)
    \<le> 1 * dist x y" using a0 a1  by meson 
   qed
   show "
           dist ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus x)::(real, 'b) fixed_vec)
            ((map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>f v. Matrix.vec (dim_vec v) (\<lambda>i. f (v $ i))) softplus y)::(real, 'b) fixed_vec)
           \<le> 1 * dist x y " 
     using
       \<open>dist (map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i))) softplus (x::(real, 'b::finite) fixed_vec)) (map_fun id (map_fun Rep_fixed_vec Abs_fixed_vec) (\<lambda>(f::real \<Rightarrow> real) v::real Matrix.vec. Matrix.vec (dim_vec v) (\<lambda>i::nat. f (v $ i))) softplus (y::(real, 'b::finite) fixed_vec)) \<le> 1 * dist x y\<close>
     by fastforce
 qed

lemma softplus_lipschitz: "1-lipschitz_on (X::(real, 'b::finite) fixed_vec set) (map_fixed_vec softplus)"
  unfolding lipschitz_on_def map_fixed_vec_def map_vec_def
  apply(clarsimp)[1] 
  using softplus_lipschitz'[of _ X]
  by simp

end
