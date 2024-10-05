(*  Title:       Transfer_Cayley_Hamilton
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Transfer_Cayley_Hamilton
imports
  Cayley_Hamilton.Square_Matrix
  Cayley_Hamilton.Cayley_Hamilton
  "HOL-Types_To_Sets.Group_On_With"
begin

text \<open>Hide the definitions of \<^session>\<open>Cayley_Hamilton\<close> that override those of HOL-Analysis.
  They can still be accessed using fully qualified syntax.\<close>
hide_const (open) det transpose row trace adjugate
hide_fact (open) det_def transpose_def row_def row_transpose trace_def adjugate_def

hide_const (open) "XX" "CC" charpoly poly_mat
no_notation Cayley_Hamilton.XX (\<open>\<^bold>X\<close>)
no_notation Cayley_Hamilton.CC (\<open>\<^bold>C\<close>)
hide_fact (open) charpoly_def poly_mat_def

type_synonym ('a, 'n) square_matrix = "(('a, 'n) vec, 'n) vec"

definition to_fun_vec_vec::"(('a,'m::finite)vec,'n::finite)vec \<Rightarrow> ('n\<Rightarrow>'m\<Rightarrow>'a)" where
  "to_fun_vec_vec M \<equiv> \<lambda>i j. M$i$j"


section \<open>Missing definitions for \<^typ>\<open>('a,'n)square_matrix\<close>\<close>

definition minor_mat :: "('a,'b)square_matrix \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a::semiring_1,'b::finite)square_matrix" where
  "minor_mat A i j \<equiv> \<chi> k l. if k = i \<and> l = j then 1 else if k = i \<or> l = j then 0 else A$k$l"

lemma minor_from_vec: "from_vec (minor_mat A i j) = minor (from_vec A) i j"
  apply transfer
  unfolding minor_mat_def using vec_eq_iff fun_eq_iff by fastforce

lemma to_vec_minor: "minor_mat (to_vec A) i j = to_vec (minor A i j)"
  using minor_from_vec by (metis from_vec_to_vec to_vec_from_vec)

definition cofac :: "('a,'b)square_matrix \<Rightarrow> 'a::comm_ring_1^'b^'b" where
  "cofac A \<equiv> \<chi> i j. det (minor_mat A i j)"

definition "adjugate A \<equiv> transpose (cofac A)"

text \<open>Just for convenience, I'll define scalar multiplication as well, much like in \<open>Cayley_Hamilton\<close>.\<close>
definition smult_mat :: "'a::times \<Rightarrow> 'a^'n^'m \<Rightarrow> 'a^'n^'m" (infixr \<open>*\<^sub>s\<close> 75) where
  "s *\<^sub>s M \<equiv> \<chi> i j. s*M$i$j"

lemma smult_map: "smult_mat s = map_matrix (\<lambda>x. s*x)"
  unfolding smult_mat_def map_matrix_def by auto

abbreviation XX (\<open>\<^bold>X\<close>) where "\<^bold>X \<equiv> mat X"
abbreviation CC (\<open>\<^bold>C\<close>) where "\<^bold>C \<equiv> map_matrix C"

definition "charpoly A = det (\<^bold>X - \<^bold>C A)"

text \<open>Since multiplication \<^term>\<open>times\<close> is already defined element-wise, so is exponentiation.
  Not useful for our purposes - define exponentiation based on \<^term>\<open>matrix_matrix_mult\<close> instead.\<close>

primrec power_mat :: "'a::{semiring_1}^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n"  (infixr \<open>*^\<close> 80)
  where
    power_0: "a *^ 0 = mat 1"
  | power_Suc: "a *^ Suc n = a ** a *^ n"

definition poly_mat :: "'a::ring_1 poly \<Rightarrow> 'a^'n^'n \<Rightarrow> 'a^'n^'n" where
  "poly_mat p A = (\<Sum>i\<le>degree p. coeff p i *\<^sub>s A*^i)"



section \<open>Transfer Relation and Rules between \<^typ>\<open>'a^^'n\<close> and \<^typ>\<open>'a^'n^'n\<close>\<close>

subsection \<open>Transfer Relation\<close>
context includes lifting_syntax begin
lemma to_fun_from_vec: "to_fun_vec_vec = (to_fun \<circ> from_vec)"
  unfolding to_fun_vec_vec_def from_vec_def 
  apply transfer by (simp add: fun.map_ident map_fun_def)

definition rel_sm_vv::"('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('n\<Rightarrow>'m\<Rightarrow>bool) \<Rightarrow> 'a^^'n \<Rightarrow> 'b^'m^'m \<Rightarrow> bool" where
  "rel_sm_vv A N SM VV \<equiv> (N===>N===>A) (to_fun SM) (to_fun_vec_vec VV)"

definition Rel_vec::"('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('n\<Rightarrow>'m\<Rightarrow>bool) \<Rightarrow> 'a^'n \<Rightarrow> 'b^'m \<Rightarrow> bool" where
  "Rel_vec A N v u \<equiv> (N===>A) (vec_nth v) (vec_nth u)"

definition Rel_vec_vec::"('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('n\<Rightarrow>'i\<Rightarrow>bool) \<Rightarrow> ('m\<Rightarrow>'j\<Rightarrow>bool) \<Rightarrow> 'a^'m^'n \<Rightarrow> 'b^'j^'i \<Rightarrow> bool" where
  "Rel_vec_vec A N M v u \<equiv> (N===>M===>A) (to_fun_vec_vec v) (to_fun_vec_vec u)"

definition Rel_sq_mat::"('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('n\<Rightarrow>'i\<Rightarrow>bool) \<Rightarrow> 'a^^'n \<Rightarrow> 'b^^'i \<Rightarrow> bool" where
  "Rel_sq_mat A N v u \<equiv> (N===>N===>A) (to_fun v) (to_fun u)"

abbreviation "EQ \<equiv> rel_sm_vv (=) (=)"

lemma EQ_iff: "EQ SM VV \<longleftrightarrow> (to_fun SM) = (to_fun_vec_vec VV)"
  by (simp add: rel_fun_eq rel_sm_vv_def)

lemma EQ_cong: "EQ SM VV"
  if "EQ sm vv" "sm = SM" "vv = VV"
  using that by simp

text \<open>A kind-of halfway transfer, between raw representations.\<close>
lemma EQ_intro: "EQ (of_fun f) (\<chi> i j. g i j)"
  if "f = g"
  using that EQ_iff from_vec_to_vec to_fun_from_vec
  by (metis comp_apply to_vec.abs_eq)

end

bundle transfer_CH_matrix_syntax
begin
notation EQ (infix \<open>\<cong>\<close> 80)
end

subsection \<open>Transfer rules\<close>

context includes lifting_syntax and transfer_CH_matrix_syntax begin

lemma right_total_rel_sm_vv' [transfer_rule]: "right_total EQ"
  unfolding right_total_def EQ_iff to_fun_vec_vec_def
  using from_vec.rep_eq by blast

lemma bi_unique_rel_sm_vv' [transfer_rule]: "bi_unique EQ"
  unfolding bi_unique_def EQ_iff to_fun_vec_vec_def
  by (metis from_vec.abs_eq from_vec_eq_iff to_fun_inject)

lemma transfer_sm_vv_1 [transfer_rule]:
  shows "(diag 1) \<cong> (mat 1)"
  unfolding mat_def rel_sm_vv_def rel_fun_def
  by (simp add: diag.rep_eq to_fun_from_vec from_vec.rep_eq)

lemma transfer_sm_vv_0 [transfer_rule]:
  shows "0 \<cong> 0"
  unfolding to_fun_from_vec EQ_iff by (simp add: from_vec.rep_eq zero_sq_matrix.rep_eq)

lemma transfer_sm_vv_eq [transfer_rule]:
  shows "(EQ ===> EQ ===> (\<longleftrightarrow>)) (=) (=)"
  by transfer_prover

lemma transfer_sm_vv_forall [transfer_rule]:
  shows "((EQ ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>)) All transfer_forall"
  unfolding rel_sm_vv_def rel_fun_def to_fun_from_vec transfer_forall_def
  by (metis comp_def from_vec_to_vec)

lemma transfer_sm_vv_mult[transfer_rule]:
  shows "(EQ ===> EQ ===> EQ) (*) (**)"
  unfolding times_sq_matrix_def matrix_matrix_mult_def rel_sm_vv_def rel_fun_def to_fun_from_vec
  by (clarify, smt (z3) Finite_Cartesian_Product.sum_cong_aux comp_apply from_vec_mult
    times_sq_matrix.rep_eq times_sq_matrix_def matrix_matrix_mult_def)

lemma transfer_sm_vv_diag[transfer_rule]:
  shows "((=) ===> EQ) diag mat"
  unfolding mat_def rel_sm_vv_def rel_fun_def to_fun_from_vec
  by (simp add: diag.abs_eq from_vec.abs_eq)

lemma transfer_sm_vv_transpose[transfer_rule]:
  shows "(EQ ===> EQ) Square_Matrix.transpose transpose"
  unfolding transpose_def rel_sm_vv_def rel_fun_def
  by (metis (mono_tags, lifting) to_fun_vec_vec_def transpose.rep_eq vec_lambda_beta)

lemma transfer_sm_vv_det[transfer_rule]:
  shows "(EQ ===> (=)) Square_Matrix.det det"
  unfolding Square_Matrix.det_def det_def rel_sm_vv_def rel_fun_def to_fun_from_vec
  by (simp add: from_vec.abs_eq of_fun_inverse)

lemma transfer_sm_vv_minor[transfer_rule]:
  shows "(EQ ===> (=) ===> (=) ===> EQ) minor minor_mat"
  unfolding minor_mat_def minor_def rel_sm_vv_def rel_fun_def to_fun_from_vec
  by (simp add: from_vec.abs_eq of_fun_inverse)

lemma transfer_sm_vv_cofactor[transfer_rule]:
  shows "(EQ ===> EQ) cofactor cofac"
  unfolding cofac_def cofactor_def
    minor_mat_def minor_def det_def Square_Matrix.det_def
    rel_sm_vv_def rel_fun_def to_fun_from_vec
  apply (simp add: from_vec.abs_eq of_fun_inverse)
  by (metis (no_types, lifting) id_apply prod.cong sum.cong)

lemma transfer_sm_vv_adjugate[transfer_rule]:
  shows "(EQ ===> EQ) Square_Matrix.adjugate adjugate"
  unfolding Square_Matrix.adjugate_def adjugate_def
  using transfer_sm_vv_cofactor transfer_sm_vv_transpose
  by (smt (verit, del_insts) rel_funD rel_funI)

lemma transfer_sm_vv_smult[transfer_rule]:
  shows "((=) ===> EQ ===> EQ) (*\<^sub>S) (*\<^sub>s)"
  unfolding smult_mat_def rel_fun_def EQ_iff to_fun_from_vec
  by (simp add: from_vec.abs_eq smult_sq_matrix.abs_eq to_fun_inject)

lemma power_mat_transfer [transfer_rule]:
  \<open>(R ===> (=) ===> R) (^) (*^)\<close>
    if [transfer_rule]: \<open>R 1 (mat 1)\<close> \<open>(R ===> R ===> R) (*) (**)\<close>
    for R :: \<open>'a::power \<Rightarrow> 'b::semiring_1^'n^'n \<Rightarrow> bool\<close>
  by (simp only: power_def power_mat_def) transfer_prover

lemma transfer_sm_vv_power[transfer_rule]: "(EQ ===> (=) ===> EQ) power (*^)"
  apply (intro power_mat_transfer)
  using transfer_sm_vv_1 apply (metis diag_1)
  using transfer_sm_vv_mult by simp

lemma transfer_sum_if_plus0 [transfer_rule]: "((B ===> A) ===> rel_set B ===> A) sum sum"
  if zero_plus [transfer_rule]: "A 0 0" "(A===>A===>A) (+) (+)"
  and rt_bu [transfer_rule]: "right_total A" "bi_unique A" "bi_unique B"
proof (unfold sum_with)
  show "((B ===> A) ===> rel_set B ===> A) (sum_with (+) 0) (sum_with (+) 0)"
    using sum_with_transfer[OF rt_bu] rel_fun_def_butlast zero_plus by metis
qed

lemma transfer_sm_vv_plus[transfer_rule]: "(EQ===>EQ===>EQ) (+) (+)"
proof (intro rel_funI, unfold plus_vec_def EQ_iff to_fun_from_vec)
  fix x y :: "('a, 'b) sq_matrix"
    and a b :: "(('a, 'b) vec, 'b) vec"
  assume "to_fun x = (to_fun \<circ> from_vec) a"
    and "to_fun y = (to_fun \<circ> from_vec) b"
  then show "to_fun (x + y) = (to_fun \<circ> from_vec) (\<chi> i j. a$i$j + b$i$j)"
    by (simp add: from_vec.abs_eq plus_sq_matrix.abs_eq to_fun_inject)
qed

lemma transfer_sm_vv_sum[transfer_rule]: "(((=) ===> EQ) ===> (rel_set (=)) ===> EQ) sum sum"
  by transfer_prover

lemma transfer_sm_vv_poly_mat[transfer_rule]:
  shows "((=) ===> EQ ===> EQ) Cayley_Hamilton.poly_mat poly_mat"
  unfolding poly_mat_def Cayley_Hamilton.poly_mat_def by transfer_prover

lemma transfer_sm_vv_CC[transfer_rule]:
  shows "(EQ ===> EQ) Cayley_Hamilton.CC CC"
  unfolding map_matrix_def rel_fun_def EQ_iff to_fun_from_vec
  by (transfer, force)

lemma transfer_sm_vv_XX[transfer_rule]:
  shows "Cayley_Hamilton.XX \<cong> XX"
  unfolding rel_fun_def EQ_iff to_fun_from_vec mat_def
  by (metis (no_types) comp_apply diag.abs_eq from_vec_to_vec to_vec.abs_eq)

lemma transfer_sm_vv_minus[transfer_rule]:
  shows "(EQ ===> EQ ===> EQ) (-) (-)"
  unfolding rel_fun_def EQ_iff to_fun_from_vec
  by (transfer, simp add: minus_vec_def vec_lambda_inverse)

lemma transfer_sm_vv_charpoly[transfer_rule]:
  shows "(EQ ===> (=)) Cayley_Hamilton.charpoly charpoly"
  unfolding charpoly_def Cayley_Hamilton.charpoly_def
  by transfer_prover



section \<open>Transferred results for adjugate and inverse, Cayley-Hamilton Theorem\<close>

lemma mult_adjugate_det_2: "A ** adjugate A = mat (det A)"
  by (transfer, simp add: mult_adjugate_det)

theorem Cayley_Hamilton_2:
  fixes A :: "'a::comm_ring_1^'n^'n"
  shows "poly_mat (charpoly A) A = 0"
  by (transfer, simp add: Cayley_Hamilton)


end (*transfer_CH_matrix_syntax*)
end
