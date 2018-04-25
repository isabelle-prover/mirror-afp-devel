(*
    Authors:    Jose Divasón
                Maximilian Haslbeck
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>The LLL algorithm\<close>

text \<open>This theory provides an implementation and a soundness proof of the LLL algorithm 
      to compute a "short" vector in a lattice. 
\<close> 

theory LLL
  imports 
    Gram_Schmidt_2 
    Missing_Lemmas 
    Jordan_Normal_Form.Determinant 
    "Abstract-Rewriting.SN_Order_Carrier"
    List_Representation
begin

subsection \<open>Implementation of the LLL algorithm\<close>
definition floor_ceil where "floor_ceil x = floor (x + 1/2)" 

(* there will be code equations which compute this function more efficiently *)
definition scalar_prod_int_rat :: "int vec \<Rightarrow> rat vec \<Rightarrow> rat" (infix "\<bullet>i" 70) where 
  "x \<bullet>i y = (y \<bullet> map_vec rat_of_int x)" 

(* Throughout the algorithm we are mainly interested in base-element i, or in row i of the GSO *)
    
(* To represent the F-basis, we take the the first i elements of F in reverse order and 
   the other elements of F in original order, so 
   that we can easily access the i-th and i-1-th element and increase i and decrease i. *)
type_synonym f_repr = "int vec list_repr"     

(* For the the GSO \<mu> G, such that F = M \<times> G and G is the GSO of F,
   we do not store \<mu>, and for G we store all vectors
   together with their square-norm, again splitted at index i *)
type_synonym g_repr = "(rat vec \<times> rat) list_repr" 

(* The name "im1" stands for "i - 1" *)
definition g_i :: "g_repr \<Rightarrow> rat vec" where "g_i Gr = (fst (get_nth_i Gr))" 
definition sqnorm_g_i :: "g_repr \<Rightarrow> rat" where "sqnorm_g_i Gr = (snd (get_nth_i Gr))" 
definition g_im1 :: "g_repr \<Rightarrow> rat vec" where "g_im1 Gr = (fst (get_nth_im1 Gr))" 
definition sqnorm_g_im1 :: "g_repr \<Rightarrow> rat" where "sqnorm_g_im1 Gr = (snd (get_nth_im1 Gr))" 
definition \<mu>_i_im1 :: "f_repr \<Rightarrow> g_repr \<Rightarrow> rat" where
  "\<mu>_i_im1 Fr Gr = (get_nth_i Fr \<bullet>i g_im1 Gr) / sqnorm_g_im1 Gr"

definition \<mu>_ij :: "int vec \<Rightarrow> rat vec \<times> rat \<Rightarrow> rat" where
  "\<mu>_ij fi gj_norm = (case gj_norm of (gj,norm_gj) \<Rightarrow> (fi \<bullet>i gj) / norm_gj)" 

type_synonym state = "nat \<times> f_repr \<times> g_repr"

text \<open>The boolean in an extended state encodes 
  whether the counter $i$ was going up (True) or down (False) in the previous iteration.\<close>

type_synonym estate = "bool \<times> state"
    
fun basis_reduction_add_row_main :: "state \<Rightarrow> int vec \<Rightarrow> rat \<Rightarrow> state" where 
  "basis_reduction_add_row_main (i,F,G) fj mu = (let     
     c = floor_ceil mu
     in if c = 0 then
       (i,F,G)
     else 
     let 
     fi = get_nth_i F - (c \<cdot>\<^sub>v fj);
     F' = update_i F fi
     in (i,F',G))"

fun basis_reduction_add_row_i_all_main :: "state \<Rightarrow> int vec list \<Rightarrow> (rat vec \<times> rat) list \<Rightarrow> state" where
  "basis_reduction_add_row_i_all_main state (Cons fj fjs) (Cons gj gjs) = (case state of (i,F,G) \<Rightarrow> 
    let fi = get_nth_i F in
    basis_reduction_add_row_i_all_main (basis_reduction_add_row_main state fj (\<mu>_ij fi gj)) fjs gjs)"
| "basis_reduction_add_row_i_all_main state _ _ = state" 

definition basis_reduction_add_rows :: "state \<Rightarrow> state" where 
  "basis_reduction_add_rows state = (case state of (i,F,G) \<Rightarrow>
    let fjs = fst F;
        gjs = fst G
      in basis_reduction_add_row_i_all_main state fjs gjs)" 

definition increase_i :: "state \<Rightarrow> state" where
  "increase_i state = (case state of (i, F, G) \<Rightarrow> (Suc i, inc_i F, inc_i G))" 

fun basis_reduction_swap :: "state \<Rightarrow> state" where
  "basis_reduction_swap (i,F,G) = (let 
    mu = \<mu>_i_im1 F G;
    gi = g_i G; 
    gim1 = g_im1 G;
    fi = get_nth_i F;
    fim1 = get_nth_im1 F;
    ni = sqnorm_g_i G;
    nim1 = sqnorm_g_im1 G;
    new_gim1 = gi + mu \<cdot>\<^sub>v gim1;
    new_nim1 = ni + square_rat mu * nim1;
    new_gi = gim1 - (fim1 \<bullet>i new_gim1 / new_nim1) \<cdot>\<^sub>v new_gim1;
    new_ni = ni * nim1 / new_nim1;
    G' = dec_i (update_im1 (update_i G (new_gi,new_ni)) (new_gim1,new_nim1));
    F' = dec_i (update_im1 (update_i F fim1) fi)
  in (i - 1, F', G'))"

context 
  fixes \<alpha> :: rat
  and m :: nat
begin
definition basis_reduction_step :: "estate \<Rightarrow> estate" where
  "basis_reduction_step estate = (case estate of (upw, state) \<Rightarrow> if fst state = 0 then (True, increase_i state)
     else let state' = (if upw then basis_reduction_add_rows state else state) in
     case state' of (i, F, G) \<Rightarrow>
      if sqnorm_g_im1 G > \<alpha> * sqnorm_g_i G 
      then (False, basis_reduction_swap state')
      else (True, increase_i state')
     )" 

partial_function (tailrec) basis_reduction_main :: "estate \<Rightarrow> estate" where
  [code]: "basis_reduction_main state = (case state of (upw,i,_) \<Rightarrow>
     if i < m 
     then basis_reduction_main (basis_reduction_step state) 
     else state)"
end

definition initial_state :: "nat \<Rightarrow> int vec list \<Rightarrow> estate" where
  "initial_state n F = (let G = gram_schmidt_triv n (map (map_vec of_int) F);
     Fr = ([], F);
     Gr = ([], G)
     in (False, (0, Fr, Gr)))" 

definition basis_reduction_state :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> estate" where 
  "basis_reduction_state n \<alpha> F = (basis_reduction_main \<alpha> (length F) (initial_state n F))" 

definition reduce_basis :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> int vec list \<times> rat vec list" where
  "reduce_basis n \<alpha> F = (\<lambda> state. ((of_list_repr o fst o snd o snd) state, 
     (map fst o of_list_repr o snd o snd o snd) state))
     (basis_reduction_state n \<alpha> F)" 

definition short_vector :: "rat \<Rightarrow> int vec list \<Rightarrow> int vec" where 
  "short_vector \<alpha> F = (hd o fst) (reduce_basis (dim_vec (hd F)) \<alpha> F)"  

subsection \<open>LLL algorithm is sound\<close>

lemma floor_ceil: "\<bar>x - rat_of_int (floor_ceil x)\<bar> \<le> inverse 2" 
  unfolding floor_ceil_def by (metis (no_types, hide_lams) abs_divide abs_neg_one round_def
      div_by_1 div_minus_right inverse_eq_divide minus_diff_eq of_int_round_abs_le)

lemma \<mu>_i_im1_code[code_unfold]: 
  "\<mu>_i_im1 F G = \<mu>_ij (get_nth_i F) (get_nth_im1 G)" 
  unfolding \<mu>_i_im1_def g_im1_def sqnorm_g_im1_def \<mu>_ij_def
  by (auto split: prod.splits)

lemma scalar_prod_int_rat[simp]: "dim_vec x = dim_vec y \<Longrightarrow> x \<bullet>i y = map_vec of_int x \<bullet> y" 
  unfolding scalar_prod_int_rat_def by (intro comm_scalar_prod[of _ "dim_vec x"], auto intro: carrier_vecI) 

definition int_times_rat :: "int \<Rightarrow> rat \<Rightarrow> rat" where "int_times_rat i x = of_int i * x" 

lemma scalar_prod_int_rat_code[code]: "v \<bullet>i w = (\<Sum>i = 0..<dim_vec v. int_times_rat (v $ i) (w $ i))"  
  unfolding scalar_prod_int_rat_def Let_def scalar_prod_def int_times_rat_def
  by (rule sum.cong, auto)

lemma int_times_rat_code[code abstract]: "quotient_of (int_times_rat i x) =
  (case quotient_of x of (n,d) \<Rightarrow> Rat.normalize (i * n, d))"  
  unfolding int_times_rat_def rat_times_code by auto

locale LLL =
  fixes n :: nat (* n-dimensional vectors, *) and m :: nat (* number of vectors *)
   and fs_init :: "int vec list" (* initial basis *) and \<alpha> :: rat (* approximation factor *)
begin

sublocale vec_module "TYPE(int)" n.

                   
sublocale gs: gram_schmidt n "TYPE(rat)" .
        
abbreviation RAT where "RAT \<equiv> map (map_vec rat_of_int)" 
abbreviation SRAT where "SRAT xs \<equiv> set (RAT xs)" 
abbreviation Rn where "Rn \<equiv> carrier_vec n :: rat vec set" 
  
definition GSO where "GSO F = gs.gso (RAT F)"

definition g_repr :: "nat \<Rightarrow> g_repr \<Rightarrow> int vec list \<Rightarrow> bool" where
  "g_repr i G F = (i \<le> m \<and> list_repr i G (map (\<lambda> x. (x,sq_norm x)) (map (GSO F) [0..<m])))" 

abbreviation (input) "f_repr \<equiv> list_repr"
    
lemma g_i_GSO: "g_repr i G F \<Longrightarrow> i < m \<Longrightarrow> g_i G = GSO F i" 
  unfolding g_repr_def g_i_def by (cases F, auto simp: get_nth_i)

lemma sqnorm_g_i_GSO: "g_repr i G F \<Longrightarrow> i < m \<Longrightarrow> sqnorm_g_i G = sq_norm (GSO F i)" 
  unfolding g_repr_def sqnorm_g_i_def by (cases G, auto simp: get_nth_i)
    
lemma g_im1_GSO: "g_repr i G F \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> g_im1 G = GSO F (i - 1)" 
  unfolding g_repr_def g_im1_def by (cases G, cases i, auto simp: get_nth_im1)

lemma sqnorm_g_im1_GSO: "g_repr i G F \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> sqnorm_g_im1 G = sq_norm (GSO F (i - 1))" 
  unfolding g_repr_def sqnorm_g_im1_def by (cases G, cases i, auto simp: get_nth_im1)
        
lemma inc_i_gso: assumes "i < m" "g_repr i G F"  
shows "g_repr (Suc i) (inc_i G) F" 
  using assms unfolding g_repr_def by (auto simp: inc_i)

lemma \<mu>_i_im1: assumes gr: "f_repr i Fr F" and gso:"g_repr i G F"
  and n:"m = length F" and i:"i \<noteq> 0" "i < m"
  and dim: "F ! i \<in> carrier_vec n" "gs.gso (RAT F) (i - 1) \<in> carrier_vec n"
  shows "\<mu>_i_im1 Fr G = gs.\<mu> (RAT F) i (i - 1)" 
  unfolding g_repr_def \<mu>_i_im1_def gs.\<mu>.simps
            get_nth_i[OF gr,unfolded length_map,OF i(2)[unfolded n]]
            of_list_repr[OF gr] g_im1_GSO[OF gso i(1)]
            sqnorm_g_im1_GSO[OF gso i(1)] GSO_def
  using i n dim by auto

text \<open>lattice of initial basis\<close>
definition "L = lattice_of fs_init" 

text \<open>maximum squared norm of initial basis\<close>
definition "A = max_list (map (nat \<circ> sq_norm) fs_init)" 

text \<open>maximum absolute value in initial basis\<close>
definition "M = Max ({abs (fs_init ! i $ j) | i j. i < m \<and> j < n} \<union> {0})" 

text \<open>This is the core invariant which enables to prove functional correctness.
  It moreover states that the norms stay small.\<close>

definition g_bound :: "rat vec list \<Rightarrow> bool" where 
  "g_bound gs = (\<forall> i < m. sq_norm (gs ! i) \<le> of_nat A)" 

text \<open>The bounds for the $f_i$ distinguishes whether we are inside or outside the inner for-loop.\<close>

definition f_bound :: "bool \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "f_bound outside ii fs = (\<forall> i < m. sq_norm (fs ! i) \<le> (if i \<noteq> ii \<or> outside then int (A * m) else 
     int (4 ^ (m - 1) * A ^ m * m * m)))" 

definition "mu_small F i = (\<forall> j < i. abs (gs.\<mu> (RAT F) i j) \<le> 1/2)" 

definition LLL_invariant :: "bool \<Rightarrow> estate \<Rightarrow> int vec list \<Rightarrow> rat vec list \<Rightarrow> bool" where 
  "LLL_invariant outside estate F G = (case estate of (upw,i,Fr,Gr) \<Rightarrow> 
  snd (gram_schmidt_int n F) = G \<and>
  gs.lin_indpt_list (RAT F) \<and> 
  lattice_of F = L \<and>
  gs.reduced \<alpha> i G (gs.\<mu> (RAT F)) \<and>
  i \<le> m \<and>
  length F = m \<and>
  f_repr i Fr F \<and> 
  g_repr i Gr F \<and> 
  f_bound outside i F \<and> g_bound G \<and>
  (upw \<or> mu_small F i)
  )" 

lemma LLL_invD: assumes "LLL_invariant outside (upw,i,Fr,Gr) F G"
  shows "F = of_list_repr Fr" 
  "snd (gram_schmidt_int n F) = G" 
  "set F \<subseteq> carrier_vec n"
  "length F = m"
  "lattice_of F = L" 
  "gs.weakly_reduced \<alpha> i G"
  "i \<le> m"
  "f_repr i Fr F"
  "g_repr i Gr F" 
  "gs.lin_indpt_list (RAT F)" 
  "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))" 
  "f_bound outside i F"
  "g_bound G"
  "upw \<or> mu_small F i" 
  using assms gs.lin_indpt_list_def of_list_repr[of i Fr F] 
  unfolding LLL_invariant_def split gs.reduced_def by auto

lemma LLL_invI: assumes  
  "f_repr i Fr F"
  "g_repr i Gr F" 
  "snd (gram_schmidt_int n F) = G" 
  "lattice_of F = L" 
  "gs.weakly_reduced \<alpha> i G"
  "i \<le> m"
  "length F = m" 
  "gs.lin_indpt_list (RAT F)"
  "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))" 
  "f_bound outside i F" 
  "g_bound G" 
  "upw \<or> mu_small F i" 
shows "LLL_invariant outside (upw,i,Fr,Gr) F G" 
  unfolding LLL_invariant_def Let_def split using assms of_list_repr[OF assms(1)] by auto

lemma f_bound_True_arbitrary: assumes "f_bound True ii fs"
  shows "f_bound outside j fs" 
  unfolding f_bound_def 
proof (intro allI impI, rule ccontr, goal_cases)
  case (1 i)
  from 1 have nz: "\<parallel>fs ! i\<parallel>\<^sup>2 \<noteq> 0" by (auto split: if_splits)
  hence gt: "\<parallel>fs ! i\<parallel>\<^sup>2 > 0" using sq_norm_vec_ge_0[of "fs ! i"] by auto
  from assms(1)[unfolded f_bound_def, rule_format, OF 1(1)]
  have one: "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> int (A * m) * 1" by auto
  from less_le_trans[OF gt one] have A0: "A \<noteq> 0" by (cases "A = 0", auto)
  note one
  also have "int (A * m) * 1 \<le> int (A * m) * int (4 ^ (m - 1) * A ^ (m - 1) * m)"
    by (rule mult_left_mono, unfold of_nat_mult, intro mult_ge_one, insert 1 A0, auto)  
  also have "\<dots> = int (4 ^ (m - 1) * A ^ (Suc (m - 1)) * m * m)" unfolding of_nat_mult by simp
  also have "Suc (m - 1) = m" using 1 by simp
  finally show ?case using one 1 by (auto split: if_splits)
qed

lemma gram_schmidt_int_connect: fixes F :: "int vec list" 
  assumes "gs.lin_indpt_list (RAT F)" "snd (gram_schmidt_int n F) = G" "length F = m" 
  shows "G = map (gs.gso (RAT F)) [0..<m]"
proof -
  from assms have gsw: "snd (gram_schmidt_wit n (RAT F)) = G" 
    by (auto simp: gram_schmidt_int_def)
  from gram_schmidt.main_connect[OF assms(1) _ gsw[unfolded gram_schmidt_wit_def], of m] assms(3)
  show "G = map (gs.gso (RAT F)) [0..<m]" by auto
qed
  
lemma LLL_connect: fixes F :: "int vec list" 
  assumes inv: "LLL_invariant outside (upw,i,Fr,Gr) F G" 
  shows "G = map (gs.gso (RAT F)) [0..<m]"
  using gram_schmidt_int_connect[of F G] LLL_invD[OF inv] by auto

lemma gs_gs_identical: assumes "\<And> i. i \<le> x \<Longrightarrow> f1 ! i = f2 ! i"
  shows "gs.gso f1 x = gs.gso f2 x"
  using assms
proof(induct x rule:nat_less_induct[rule_format])
  case (1 x)
  hence fg:"(+) (f1 ! x) = (+) (f2 ! x)" by auto
  show ?case
    apply(subst (1 2) gs.gso.simps) unfolding gs.\<mu>.simps
    apply(rule cong[OF fg cong[OF refl[of "gs.sumlist"]]])
    using 1 by auto
qed
  
lemma gs_\<mu>_identical: assumes "\<And> k. j < i \<Longrightarrow> k \<le> j \<Longrightarrow> f1 ! k = f2 ! k"
  and "j < i \<Longrightarrow> f1 ! i = f2 ! i" 
  shows "gs.\<mu> f1 i j = gs.\<mu> f2 i j"
proof -
  from gs_gs_identical[of j f1 f2] assms have id: "j < i \<Longrightarrow> gs.gso f1 j = gs.gso f2 j" by auto
  show ?thesis unfolding gs.\<mu>.simps using assms id by auto
qed

lemma g_i: assumes inv: "LLL_invariant outside (upw,i,Fr,Gr) F G" and i: "i < m"  
  shows "g_i Gr = G ! i" 
    "sqnorm_g_i Gr = sq_norm (G ! i)"
proof -
  note conn = LLL_connect[OF inv]
  note inv = LLL_invD[OF inv]    
  note conn = conn[folded inv(1)]
  from inv i have Gr: "g_repr i Gr F" 
    and len: "length F = m" by auto
  from g_i_GSO[OF Gr i] sqnorm_g_i_GSO[OF Gr i]
  have "g_i Gr = GSO F i \<and> sqnorm_g_i Gr = sq_norm (GSO F i)" by simp
  also have "GSO F i = G ! i" unfolding GSO_def conn using i len by simp
  finally show "g_i Gr = G ! i" 
    "sqnorm_g_i Gr = sq_norm (G ! i)" by auto
qed
  
lemma g_im1: assumes inv: "LLL_invariant outside (upw,i,Fr,Gr) F G" and i: "i < m" "i \<noteq> 0" 
  shows "g_im1 Gr = G ! (i - 1)" 
    "sqnorm_g_im1 Gr = sq_norm (G ! (i - 1))"
proof -
  note conn = LLL_connect[OF inv]
  note inv = LLL_invD[OF inv]    
  note conn = conn[folded inv(1)]
  from inv i have Gr: "g_repr i Gr F" 
    and len: "length F = m" by auto
  from g_im1_GSO[OF Gr i(2)] sqnorm_g_im1_GSO[OF Gr i(2)]
  have "g_im1 Gr = GSO F (i - 1) \<and> sqnorm_g_im1 Gr = sq_norm (GSO F (i - 1))" by simp
  also have "GSO F (i - 1) = G ! (i - 1)" unfolding GSO_def conn using i len by simp
  finally show "g_im1 Gr = G ! (i - 1)" 
    "sqnorm_g_im1 Gr = sq_norm (G ! (i - 1))" by auto
qed
    
definition reduction where "reduction = (4+\<alpha>)/(4*\<alpha>)"

definition d :: "int vec list \<Rightarrow> nat \<Rightarrow> int" where "d fs k = gs.Gramian_determinant fs k"

definition D :: "int vec list \<Rightarrow> nat" where "D fs = nat (\<Prod> i < m. d fs i)" 

definition logD :: "int vec list \<Rightarrow> nat"
  where "logD fs = (if \<alpha> = 4/3 then (D fs) else nat (floor (log (1 / of_rat reduction) (D fs))))" 

definition LLL_measure :: "estate \<Rightarrow> nat" where 
  "LLL_measure state = (case state of (upw,i,fs,gs) \<Rightarrow> 2 * logD (of_list_repr fs) + m - i)" 

lemma of_int_Gramian_determinant:
  assumes "k \<le> length F" "\<And>i. i < length F \<Longrightarrow> dim_vec (F ! i) = n"
  shows "gs.Gramian_determinant (map of_int_hom.vec_hom F) k = of_int (gs.Gramian_determinant F k)"
  unfolding gs.Gramian_determinant_def of_int_hom.hom_det[symmetric]
proof (rule arg_cong[of _ _ det])
  let ?F = "map of_int_hom.vec_hom F"
  have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by auto
  show "gs.Gramian_matrix ?F k = map_mat of_int (gs.Gramian_matrix F k)" 
    unfolding gs.Gramian_matrix_def Let_def
  proof (subst of_int_hom.mat_hom_mult[of _ k n _ k], (auto)[2], rule cong)
    show id: "mat k n (\<lambda> (i,j). ?F ! i $ j) = map_mat of_int (mat k n (\<lambda> (i, j). F ! i $ j))" (is "?L = map_mat _ ?R")
    proof (rule eq_matI, goal_cases)
      case (1 i j)
      hence ij: "i < k" "j < n" "i < length F" "dim_vec (F ! i) = n" using assms by auto
      show ?case using ij by simp 
    qed auto
    show "?L\<^sup>T = map_mat of_int ?R\<^sup>T" unfolding id by (rule eq_matI, auto)
  qed
qed

lemma Gramian_determinant: assumes "LLL_invariant outside (upw,i,Fr,Gr) F G" 
  and k: "k \<le> m" 
shows "of_int (gs.Gramian_determinant F k) = (\<Prod> j<k. sq_norm (G ! j))" 
  "gs.Gramian_determinant F k > 0" 
proof -
  let ?f = "(\<lambda>i. of_int_hom.vec_hom (F ! i))" 
  note LLL = LLL_connect[OF assms(1)]
  note LLLD = LLL_invD[OF assms(1)]
  let ?F = "map of_int_hom.vec_hom F" 
  from LLL have lenGs: "length G = m" by auto
  from LLLD(2-)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have main: "snd (gs.main ?F) = G" and len: "length ?F = m" and F: "set ?F \<subseteq> Rn" 
    and indep: "gs.lin_indpt_list ?F" by (auto intro: nth_equalityI)
  note conn = indep len main
  have Fi: "\<And> i. i < m \<Longrightarrow> F ! i \<in> carrier_vec n" using len F unfolding set_conv_nth by auto
  have det: "gs.Gramian_determinant ?F k = (\<Prod>j<k. \<parallel>G ! j\<parallel>\<^sup>2)" "(0 :: rat) < gs.Gramian_determinant ?F k" 
    using gs.Gramian_determinant[OF conn k] by auto
  have hom: "gs.Gramian_determinant ?F k = of_int (gs.Gramian_determinant F k)"
    by (auto intro!: of_int_Gramian_determinant simp add: LLLD(4) k Fi)
  show "of_int (gs.Gramian_determinant F k) = (\<Prod> j<k. sq_norm (G ! j))" 
    "gs.Gramian_determinant F k > (0 :: int)" using det[unfolded hom] by auto
qed

lemma LLL_d_pos [intro]: assumes inv: "LLL_invariant outside state F G" 
  and k: "k \<le> m" 
shows "d F k > 0"
proof -
  obtain upw i Gr gso where trip: "state = (upw,i, Gr, gso)" by (cases state, auto)
  note inv = inv[unfolded trip]
  from Gramian_determinant[OF inv k] show ?thesis unfolding trip d_def by auto
qed

lemma LLL_D_pos: assumes inv: "LLL_invariant outside state F G" 
shows "D F > 0"
proof -
  have "(\<Prod> j < m. d F j) > 0"
    by (rule prod_pos, insert LLL_d_pos[OF inv], auto)
  thus ?thesis unfolding D_def by auto
qed

lemma increase_i: assumes LLL: "LLL_invariant True (False, i,Fr,Gr) F G" 
  and i: "i < m" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (G ! (i - 1)) \<le> \<alpha> * sq_norm (G ! i)"
shows "LLL_invariant True (True, increase_i (i,Fr,Gr)) F G"
proof -
  note inv = LLL_invD[OF LLL]
  from inv have Gr: "g_repr i Gr F" and Fr: "f_repr i Fr F"
    and red: "gs.weakly_reduced \<alpha> i G" 
    and sred: "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))" by auto
  from inv i inc_i_gso[OF i Gr] inc_i[OF Fr]
  have Gr': "g_repr (Suc i) (inc_i Gr) F" and Fr': "f_repr (Suc i) (inc_i Fr) F" 
    by auto
  from red red_i have red: "gs.weakly_reduced \<alpha> (Suc i) G" 
    unfolding gs.weakly_reduced_def
    by (intro allI impI, rename_tac ii, case_tac "Suc ii = i", auto)
  from inv(14) have sred_i: "\<And> j. j < i \<Longrightarrow> \<bar>gs.\<mu> (RAT F) i j\<bar> \<le> 1 / 2" 
    unfolding mu_small_def by auto
  from sred sred_i have sred: "gs.reduced \<alpha> (Suc i) G (gs.\<mu> (RAT F))"
    unfolding gs.reduced_def
    by (intro conjI[OF red] allI impI, rename_tac ii j, case_tac "ii = i", auto)
  show ?thesis unfolding increase_i_def split
    by (rule LLL_invI[OF Fr' Gr'], insert inv red sred i, auto simp: f_bound_def)
qed

definition "mu_bound_row F bnd i = (\<forall> j \<le> i. (gs.\<mu> (RAT F) i j)^2 \<le> bnd)" 

lemma mu_bound_rowI: assumes "\<And> j. j \<le> i \<Longrightarrow> (gs.\<mu> (RAT F) i j)^2 \<le> bnd"
  shows "mu_bound_row F bnd i" 
  using assms unfolding mu_bound_row_def by auto

lemma mu_bound_rowD: assumes "mu_bound_row F bnd i" "j \<le> i"
  shows "(gs.\<mu> (RAT F) i j)^2 \<le> bnd"
  using assms unfolding mu_bound_row_def by auto

lemma mu_bound_row_1: assumes "mu_bound_row F bnd i" 
  shows "bnd \<ge> 1" using mu_bound_rowD[OF assms, of i]
  by (auto simp: gs.\<mu>.simps)

lemma reduced_mu_bound_row: assumes red: "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))"  
  and ii: "ii < i" 
shows "mu_bound_row F 1 ii"
proof (intro mu_bound_rowI)
  fix j
  assume "j \<le> ii"
  show "(gs.\<mu> (RAT F) ii j)^2 \<le> 1"
  proof (cases "j < ii")
    case True
    from red[unfolded gs.reduced_def, THEN conjunct2, rule_format, OF ii True]
    have "abs (gs.\<mu> (RAT F) ii j) \<le> 1/2" by auto
    from mult_mono[OF this this]
    show ?thesis by (auto simp: power2_eq_square)
  qed (auto simp: gs.\<mu>.simps)
qed

context fixes F G :: "rat vec list" 
  assumes lin_indep: "gs.lin_indpt_list F" 
  and len: "length F = m" 
  and G: "G = map (gs.gso F) [0..<m]"  
begin

lemma sq_norm_fs_via_sum_mu_gso: assumes i: "i < m" 
  shows "\<parallel>F ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (gs.\<mu> F i j)\<^sup>2 * \<parallel>G ! j\<parallel>\<^sup>2)" 
proof -
  let ?mu = "gs.\<mu> F i" 
  let ?G = "gs.gso F" 
  have snd: "snd (gs.main F) = G" unfolding G using lin_indep len gs.main_connect by simp
  have "F ! i = gs.sumlist (map (\<lambda>j. ?mu j \<cdot>\<^sub>v ?G j) [0..<Suc i])" 
    using gs.fi_is_sum_of_mu_gso[OF lin_indep len refl i]  .
  also have "\<dots> = gs.sumlist (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0 ..< Suc i])" 
    by (rule arg_cong[of _ _ "gs.sumlist"], rule map_cong[OF refl], unfold G, insert i, auto)
  also have "sq_norm \<dots> = sum_list (map sq_norm (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0..<Suc i]))" 
    unfolding map_map o_def sq_norm_smult_vec
    unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod conjugate_id
  proof (rule gs.scalar_prod_lincomb_orthogonal)
    show "Suc i \<le> length G" unfolding G using i by auto
    show "set G \<subseteq> Rn" unfolding G using gs.gso_carrier[OF lin_indep len refl] by auto
    show "orthogonal G" 
      using gs.gram_schmidt[OF lin_indep len snd] by auto
  qed
  also have "map sq_norm (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0..<Suc i]) = map (\<lambda>j. (?mu j)^2 * sq_norm (G ! j)) [0..<Suc i]" 
    unfolding map_map o_def sq_norm_smult_vec by (rule map_cong, auto simp: power2_eq_square)
  finally show ?thesis . 
qed

lemma sq_norm_fs_mu_G_bound: assumes i: "i < m" 
  and FF: "F = RAT FF" 
  and mu_bound: "mu_bound_row FF bnd i" 
  and g_bound: "g_bound G" 
shows "\<parallel>F ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * A) * bnd" 
proof -
  have "\<parallel>F ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (gs.\<mu> F i j)\<^sup>2 * \<parallel>G ! j\<parallel>\<^sup>2)" 
    by (rule sq_norm_fs_via_sum_mu_gso[OF i])
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<Suc i]. bnd * of_nat A)" 
  proof (rule sum_list_ge_mono, force, unfold length_map length_upt,
    subst (1 2) nth_map_upt, force, goal_cases)
    case (1 j)
    hence ji: "j \<le> i" by auto
    from g_bound[unfolded g_bound_def] i ji 
    have GB: "sq_norm (G ! j) \<le> of_nat A" by auto
    show ?case 
      by (rule mult_mono, insert mu_bound_rowD[OF mu_bound ji]
          GB order.trans[OF zero_le_power2], auto simp: FF)
  qed
  also have "\<dots> = of_nat (Suc i) * (bnd * of_nat A)" unfolding sum_list_triv length_upt by simp
  also have "\<dots> = of_nat (Suc i * A) * bnd" unfolding of_nat_mult by simp
  finally show ?thesis .
qed
end

lemma LLL_inv_sq_norm_fs_mu_G_bound: assumes Linv: "LLL_invariant outside (upw,ii,Fr,Gr) F G" 
  and i: "i < m" 
  and mu_bound: "mu_bound_row F bnd i" 
shows "rat_of_int \<parallel>F ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * A) * bnd" 
proof -
  note inv = LLL_invD[OF Linv]
  have "\<parallel>RAT F ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * A) * bnd" 
    by (rule sq_norm_fs_mu_G_bound[OF inv(10) _ LLL_connect[OF Linv] i refl mu_bound inv(13), 
      unfolded length_map, OF inv(4)])
  also have "\<parallel>RAT F ! i\<parallel>\<^sup>2 = of_int \<parallel>F ! i\<parallel>\<^sup>2" unfolding sq_norm_of_int[symmetric]
    using inv(4) i by auto
  finally show ?thesis by auto
qed

lemma basis_reduction_add_row_main: assumes Linv: "LLL_invariant False (True,i,Fr,Gr) F G"
  and i: "i < m"  and j: "j < i" 
  and res: "basis_reduction_add_row_main (i,Fr,Gr) fj mu = (i',Fr',Gr')"
  and fj: "fj = F ! j" 
  and mu: "mu = gs.\<mu> (RAT F) i j" 
  and c: "c = floor_ceil (gs.\<mu> (RAT F) i j)" 
  and mu_bnd: "mu_bound_row F bnd i" 
  and bnd: "bnd \<le> 4 ^ (m - 2) * of_nat (A ^ (m - 1) * m)" 
shows "\<exists> v. LLL_invariant False (True,i',Fr',Gr') (F[ i := v]) G \<and> i' = i \<and> Gr' = Gr \<and> abs (gs.\<mu> (RAT (F[ i := v])) i j) \<le> inverse 2 
  \<and> (\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> (i' \<noteq> i \<or> j' > j) 
      \<longrightarrow> gs.\<mu> (RAT (F[ i := v])) i' j' = gs.\<mu> (RAT F) i' j')
  \<and> (\<forall> j'. j' \<le> j \<longrightarrow> gs.\<mu> (RAT (F[ i := v])) i j' = gs.\<mu> (RAT F) i j' - of_int c * gs.\<mu> (RAT F) j j')
  \<and> (mu_bound_row (F[ i := v]) (4 * bnd) i)"
proof -
  define M where "M = map (\<lambda>i. map (gs.\<mu> (RAT F) i) [0..<m]) [0..<m]"
  note inv = LLL_invD[OF Linv]
  note Gr = inv(1)
  have ji: "j \<le> i" "j < m" and jstrict: "j < i" 
    and add: "set F \<subseteq> carrier_vec n" "i < length F" "j < length F" "i \<noteq> j" 
    and len: "length F = m" and red: "gs.weakly_reduced \<alpha> i G"
    and gs:"snd (gram_schmidt_int n F) = G" 
    and Fr: "f_repr i Fr F"
    and Gr: "g_repr i Gr F" 
    and indep: "gs.lin_indpt_list (RAT F)" 
    using inv j i by auto 
  let ?R = rat_of_int
  let ?RV = "map_vec ?R"   
  from add[unfolded set_conv_nth]
  have Fij: "F ! i \<in> carrier_vec n" "F ! j \<in> carrier_vec n" by auto
  let ?x = "F ! i - c \<cdot>\<^sub>v F ! j"  
  define F1 where "F1 = F[i := ?x]" 
  let ?g = "gs.gso (RAT F)"
  from add[unfolded set_conv_nth]
  have Fi:"\<And> i. i < length (RAT F) \<Longrightarrow> (RAT F) ! i \<in> carrier_vec n" by auto
  with len j i
  have gs_carr: "?g j \<in> carrier_vec n"
                "?g i \<in> carrier_vec n"
                "\<And> i. i < j \<Longrightarrow> ?g i \<in> carrier_vec n"
                "\<And> j. j < i \<Longrightarrow> ?g j \<in> carrier_vec n"
    by (intro gs.gso_carrier',force)+
  have RAT_F1: "RAT F1 = (RAT F)[i := (RAT F) ! i - ?R c \<cdot>\<^sub>v (RAT F) ! j]" 
    unfolding F1_def
  proof (rule nth_equalityI[rule_format], goal_cases)
    case (2 k)
    show ?case 
    proof (cases "k = i")
      case False
      thus ?thesis using 2 by auto
    next
      case True
      hence "?thesis = (?RV (F ! i - c \<cdot>\<^sub>v F ! j) =
          ?RV (F ! i) - ?R c \<cdot>\<^sub>v ?RV (F ! j))" 
        using 2 add by auto
      also have "\<dots>" by (rule eq_vecI, insert Fij, auto)
      finally show ?thesis by simp
    qed
  qed auto
  hence RAT_F1_i:"RAT F1 ! i = (RAT F) ! i - ?R c \<cdot>\<^sub>v (RAT F) ! j" (is "_ = _ - ?mui")
    using i len by auto
  have uminus: "F ! i - c \<cdot>\<^sub>v F ! j = F ! i + -c \<cdot>\<^sub>v F ! j" 
    by (subst minus_add_uminus_vec, insert Fij, auto)
  obtain G1 where gs': "snd (gram_schmidt_int n F1) = G1" by force
  have F1_F: "lattice_of F1 = lattice_of F" unfolding F1_def uminus
    by (rule lattice_of_add[OF add, of _ "- c"], auto)
  from len have len':"length (RAT F) = m" by auto
  from add have add':"set (map ?RV F) \<subseteq> carrier_vec n" by auto
  from add len
  have "k < length F \<Longrightarrow> \<not> k \<noteq> i \<Longrightarrow> F1 ! k \<in> carrier_vec n" for k
    unfolding F1_def
    by (metis (no_types, lifting) nth_list_update nth_mem subset_eq carrier_dim_vec index_minus_vec(2) 
        index_smult_vec(2))
  hence "k < length F \<Longrightarrow> F1 ! k \<in> carrier_vec n" for k
    unfolding F1_def using add len by (cases "k \<noteq> i",auto)
  with len have F1: "set F1 \<subseteq> carrier_vec n" "length F1 = m" unfolding F1_def by (auto simp: set_conv_nth)
  hence F1': "length (RAT F1) = m" "SRAT F1 \<subseteq> Rn" by auto
  from indep have dist: "distinct (RAT F)" by (auto simp: gs.lin_indpt_list_def)
  have Fij': "(RAT F) ! i \<in> Rn" "(RAT F) ! j \<in> Rn" using add'[unfolded set_conv_nth] i `j < m` len by auto
  have uminus': "(RAT F) ! i - rat_of_int c \<cdot>\<^sub>v (RAT F) ! j = (RAT F) ! i + - rat_of_int c \<cdot>\<^sub>v (RAT F) ! j" 
    by (subst minus_add_uminus_vec[where n = n], insert Fij', auto) 
  have span_F_F1: "gs.span (SRAT F) = gs.span (SRAT F1)" unfolding RAT_F1 uminus' 
    by (rule gs.add_vec_span, insert len add, auto)
  have **: "of_int_hom.vec_hom (F ! i) + - rat_of_int c \<cdot>\<^sub>v (RAT F) ! j
    =  of_int_hom.vec_hom (F ! i - c \<cdot>\<^sub>v F ! j)"
    by (rule eq_vecI, insert Fij len i j, auto)
  from i j len have "j < length (RAT F)" "i < length (RAT F)" "i \<noteq> j" by auto
  from gs.lin_indpt_list_add_vec[OF this indep, of "- of_int c"]
  have "gs.lin_indpt_list ((RAT F) [i := (RAT F) ! i + - of_int c \<cdot>\<^sub>v (RAT F) ! j])" (is "gs.lin_indpt_list ?F1") .
  also have "?F1 = RAT F1" unfolding F1_def using i len Fij' **
    by (auto simp: map_update)
  finally have indep_F1: "gs.lin_indpt_list (RAT F1)" .
  note conn1 = indep len' gs[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  note conn2 = indep_F1 F1'(1) gs'[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  from gs.main_connect[OF conn1] gs.main_connect[OF conn2]
  have G_def: "G = map ?g [0 ..< m]" "G = gram_schmidt n (RAT F)"
   and G1_def: "G1 = map (gs.gso (RAT F1)) [0..< m]" "G1 = gram_schmidt n (RAT F1)"
   by (auto simp:o_def)
  from gs.gram_schmidt[OF conn1] gs.gram_schmidt[OF conn2] span_F_F1 len
  have span_G_G1: "gs.span (set G) = gs.span (set G1)"
   and lenG: "length G = m" 
   and Gi: "i < length G \<Longrightarrow> G ! i \<in> Rn"
   and G1i: "i < length G1 \<Longrightarrow> G1 ! i \<in> Rn" for i
    by auto
  have eq: "x \<noteq> i \<Longrightarrow> RAT F1 ! x = (RAT F) ! x" for x unfolding RAT_F1 by auto
  hence eq_part: "x < i \<Longrightarrow> gs.gso (RAT F1) x = gs.gso (RAT F) x" for x
    by (intro gs_gs_identical, insert len, auto)
  have G: "i < m \<Longrightarrow> (RAT F) ! i \<in> Rn"
       "i < m \<Longrightarrow> F ! i \<in> carrier_vec n" for i by(insert add len', auto)
  note carr1[intro] = this[OF i] this[OF ji(2)]
  from Gi[unfolded gs.main_connect[OF conn1]] G1i[unfolded gs.main_connect[OF conn2]]
  have "x < m \<Longrightarrow> ?g x \<in> Rn" 
       "x < m \<Longrightarrow> gs.gso (RAT F1) x \<in> Rn"
       "x < m \<Longrightarrow> dim_vec (gs.gso (RAT F1) x) = n"
       "x < m \<Longrightarrow> dim_vec (gs.gso (RAT F) x) = n"
       for x by (auto simp:o_def)
  hence carr2[intro!]:"?g i \<in> Rn" "gs.gso (RAT F1) i \<in> Rn"
                 "?g ` {0..<i} \<subseteq> Rn"
                 "?g ` {0..<Suc i} \<subseteq> Rn" using i by auto
  have F1_RV: "?RV (F1 ! i) = RAT F1 ! i" using i F1 by auto
  have F_RV: "?RV (F ! i) = (RAT F) ! i" using i len by auto
  have "x < i \<Longrightarrow> gs.gso (RAT F1) x = gs.gso (RAT F) x" for x using eq
    by (rule gs_gs_identical, auto)
  hence span_G1_G: "gs.span (gs.gso (RAT F1) ` {0..<i})
          = gs.span (gs.gso (RAT F) ` {0..<i})" (is "?ls = ?rs")
    apply(intro cong[OF refl[of "gs.span"]],rule image_cong[OF refl]) using eq by auto
  have "(RAT F1) ! i - gs.gso (RAT F1) i = ((RAT F) ! i - gs.gso (RAT F1) i) - ?mui"
    unfolding RAT_F1_i using carr1 carr2
    by (intro eq_vecI, auto)
  hence in1:"((RAT F) ! i - gs.gso (RAT F1) i) - ?mui \<in> ?rs"
    using gram_schmidt.oc_projection_exist[OF conn2 i]
    unfolding span_G1_G by auto
  from \<open>j < i\<close> have Gj_mem: "(RAT F) ! j \<in> (\<lambda> x. ((RAT F) ! x)) ` {0 ..< i}" by auto  
  have id1: "set (take i (map of_int_hom.vec_hom F)) = (\<lambda>x. of_int_hom.vec_hom (F ! x)) ` {0..<i}"
    using \<open>i \<le> m\<close> len
    by (subst nth_image[symmetric], force+)
  have "(RAT F) ! j \<in> ?rs \<longleftrightarrow> (RAT F) ! j \<in> gs.span ((\<lambda>x. ?RV (F ! x)) ` {0..<i})"
    unfolding gs.partial_span[OF conn1 \<open>i \<le> m\<close>] id1 ..
  also have "(\<lambda>x. ?RV (F ! x)) ` {0..<i} = (\<lambda>x. ((RAT F) ! x)) ` {0..<i}" using \<open>i < m\<close> len by force
  also have "(RAT F) ! j \<in> gs.span \<dots>"
    by (rule gs.span_mem[OF _ Gj_mem], insert \<open>i < m\<close> G, auto)
  finally have "(RAT F) ! j \<in> ?rs" .
  hence in2:"?mui \<in> ?rs"
    apply(intro gs.prod_in_span) by force+
  have ineq:"((RAT F) ! i - gs.gso (RAT F1) i) + ?mui - ?mui = ((RAT F) ! i - gs.gso (RAT F1) i)"
    using carr1 carr2 by (intro eq_vecI, auto)
  have cong': "A = B \<Longrightarrow> A \<in> C \<Longrightarrow> B \<in> C" for A B :: "'a vec" and C by auto
  have *: "gs.gso (RAT F) ` {0..<i} \<subseteq> Rn" by auto
  have in_span: "(RAT F) ! i - gs.gso (RAT F1) i \<in> ?rs"
    by (rule cong'[OF eq_vecI gs.span_add1[OF * in1 in2,unfolded ineq]], insert carr1 carr2, auto)
  { 
    fix x assume x:"x < i" hence "x < m" "i \<noteq> x" using i by auto
    from gram_schmidt.orthogonal[OF conn2,OF i this] this
    have "gs.gso (RAT F1) i \<bullet> gs.gso (RAT F1) x = 0" by auto
  }
  hence G1_G: "gs.gso (RAT F1) i = gs.gso (RAT F) i"
    apply(intro gram_schmidt.oc_projection_unique[OF conn1 i gs.gso_carrier[OF conn2 i]])
    using in_span by (auto simp: eq_part[symmetric])
  have eq_fs:"x < m \<Longrightarrow> gs.gso (RAT F1) x = gs.gso (RAT F) x"
    for x proof(induct x rule:nat_less_induct[rule_format])
    case (1 x)
    hence ind: "m < x \<Longrightarrow> gs.gso (RAT F1) m = gs.gso (RAT F) m"
       for m by auto
    { assume "x > i"
      hence ?case apply(subst (1 2) gs.gso.simps) unfolding gs.\<mu>.simps
                  apply(rule cong[OF _ cong[OF refl[of "gs.sumlist"]]])
                  using ind eq by auto
    } note eq_rest = this
    show ?case by (rule linorder_class.linorder_cases[of x i],insert G1_G eq_part eq_rest,auto)
  qed
  with G_def G1_def cof_vec_space.gram_schmidt_result
  have Hs:"G1 = G" by (auto simp:o_def)
  hence red: "gs.weakly_reduced \<alpha> i G1" using red by auto
  let ?Mi = "M ! i ! j"  
  let ?x' = "get_nth_i Fr - floor_ceil ?Mi \<cdot>\<^sub>v F ! j"       
  define Fr1 where "Fr1 = update_i Fr ?x'"
  have Hr: "update_i Fr (?x') = Fr1" unfolding Fr1_def by simp
  have Gjn: "dim_vec (F ! j) = n" using Fij(2) carrier_vecD by blast
  define E where "E = addrow_mat m (- ?R c) i j"
  define M' where "M' = gs.M (RAT F) m"
  define N' where "N' = gs.M (RAT F1) m"
  have E: "E \<in> carrier_mat m m" unfolding E_def by simp
  have M: "M' \<in> carrier_mat m m" unfolding gram_schmidt.M_def M'_def by auto
  have N: "N' \<in> carrier_mat m m" unfolding gram_schmidt.M_def N'_def by auto
  let ?GsM = "gs.Fs G" 
  have Gs: "?GsM \<in> carrier_mat m n" using G_def by auto
  hence GsT: "?GsM\<^sup>T \<in> carrier_mat n m" by auto
  have Gnn: "gs.Fs (RAT F) \<in> carrier_mat m n" unfolding mat_of_rows_def using len by auto
  have "gs.Fs (RAT F1) = addrow (- ?R c) i j (gs.Fs (RAT F))" 
    unfolding RAT_F1 by (rule eq_matI, insert Gjn ji(2), auto simp: len mat_of_rows_def)
  also have "\<dots> = E * gs.Fs (RAT F)" unfolding E_def
    by (rule addrow_mat, insert j i, auto simp: mat_of_rows_def len)
  finally have HEG: "gs.Fs (RAT F1) = E * gs.Fs (RAT F)" . (* lemma 16.12(i), part 1 *)
  have "(E * M') * gs.Fs G = E * (M' * gs.Fs G)" 
    by (rule assoc_mult_mat[OF E M Gs])
  also have "M' * ?GsM = gs.Fs (RAT F)" using gs.matrix_equality[OF conn1] M'_def by simp
  also have "E * \<dots> = gs.Fs (RAT F1)" unfolding HEG ..
  also have "\<dots> = N' * gs.Fs G1" using gs.matrix_equality[OF conn2] N'_def by simp
  also have "gs.Fs G1 = ?GsM" unfolding Hs ..
  finally have "(E * M') * ?GsM = N' * ?GsM" .
  from arg_cong[OF this, of "\<lambda> x. x * ?GsM\<^sup>T"] E M N 
  have EMN: "(E * M') * (?GsM * ?GsM\<^sup>T) = N' * (?GsM * ?GsM\<^sup>T)" 
    by (subst (1 2) assoc_mult_mat[OF _ Gs GsT, of _ m, symmetric], auto)
  have "det (?GsM * ?GsM\<^sup>T) = gs.Gramian_determinant G m" 
    unfolding gs.Gramian_determinant_def
    by (subst gs.Gramian_matrix_alt_def, auto simp: Let_def G_def)
  also have "\<dots> > 0" 
    by (rule gs.Gramian_determinant(2)[OF gs.orthogonal_imp_lin_indpt_list \<open>length G = m\<close>],
    insert gs.gram_schmidt(2-)[OF conn1], auto)
  finally have "det (?GsM * ?GsM\<^sup>T) \<noteq> 0" by simp
  from vec_space.det_nonzero_congruence[OF EMN this _ _ N] Gs E M
  have EMN: "E * M' = N'" by auto (* lemma 16.12(i), part 2 *) 
  from inv have sred: "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))" by auto
  {
    fix i' j'
    assume ij: "i' < m" "j' < m" and choice: "i' \<noteq> i \<or> j < j'" 
    have "gs.\<mu> (RAT F1) i' j' 
      = N' $$ (i',j')" using ij F1 unfolding N'_def gs.M_def by auto
    also have "\<dots> = addrow (- ?R c) i j M' $$ (i',j')" unfolding EMN[symmetric] E_def
      by (subst addrow_mat[OF M], insert ji, auto)
    also have "\<dots> = (if i = i' then - ?R c * M' $$ (j, j') + M' $$ (i', j') else M' $$ (i', j'))" 
      by (rule index_mat_addrow, insert ij M, auto)
    also have "\<dots> = M' $$ (i', j')"
    proof (cases "i = i'")
      case True
      with choice have jj: "j < j'" by auto
      have "M' $$ (j, j') = gs.\<mu> (RAT F) j j'" 
        using ij ji len unfolding M'_def gs.M_def by auto
      also have "\<dots> = 0" unfolding gs.\<mu>.simps using jj by auto
      finally show ?thesis using True by auto
    qed auto
    also have "\<dots> = gs.\<mu> (RAT F) i' j'"
      using ij len unfolding M'_def gs.M_def by auto
    also note calculation
  } note mu_no_change = this
  {
    fix j'
    assume jj': "j' \<le> j" with j i have j': "j' < m" by auto
    have "gs.\<mu> (RAT F1) i j' 
      = N' $$ (i,j')" using jj' j i F1 unfolding N'_def gs.M_def by auto
    also have "\<dots> = addrow (- ?R c) i j M' $$ (i,j')" unfolding EMN[symmetric] E_def
      by (subst addrow_mat[OF M], insert ji, auto)
    also have "\<dots> = - ?R c * M' $$ (j, j') + M' $$ (i, j')" 
      by (rule index_mat_addrow, insert j' i M, auto)
    also have "\<dots> = M' $$ (i, j') - ?R c * M' $$ (j, j')" by simp
    also have "M' $$ (i, j') = gs.\<mu> (RAT F) i j'"
      using i j' len unfolding M'_def gs.M_def by auto
    also have "M' $$ (j, j') = gs.\<mu> (RAT F) j j'" 
      using i j j' len unfolding M'_def gs.M_def by auto
    finally have "gs.\<mu> (RAT F1) i j' = gs.\<mu> (RAT F) i j' - ?R c * gs.\<mu> (RAT F) j j'" by auto
  } note mu_change = this  
  have sred: "gs.reduced \<alpha> i G1 (gs.\<mu> (RAT F1))"
    unfolding gs.reduced_def 
  proof (intro conjI[OF red] impI allI, goal_cases)
    case (1 i' j)
    with mu_no_change[of i' j] sred[unfolded gs.reduced_def, THEN conjunct2, rule_format, of i' j] i 
    show ?case by auto
  qed
  (* now let us head for the implementation *)
  have Mij: "mu = M ! i ! j" unfolding M_def mu using `i < m` ji(2) by auto
  from c Mij mu have cc: "c = floor_ceil (M ! i ! j)" by auto
  have x: "?x = ?x'" by (subst get_nth_i[OF Fr], insert add, auto simp: cc Mij j)
  have mudiff:"mu - of_int c = gs.\<mu> (RAT F1) i j"
    unfolding mu
    by (subst mu_change, auto simp: gs.\<mu>.simps)
  have small: "abs (mu - of_int c) \<le> inverse 2" unfolding res j Mij cc
    by (rule floor_ceil)
  (* (squared) mu bound will increase at most by factor 4 *)
  {
    let ?mu = "gs.\<mu> (RAT F)" 
    have "mu_bound_row F1 (4 * bnd) i" 
    proof (intro mu_bound_rowI)
      fix k
      assume ki: "k \<le> i" 
      from mu_bound_rowD[OF mu_bnd] have bnd_i: "\<And> j. j \<le> i \<Longrightarrow> (?mu i j)^2 \<le> bnd" by auto
      have bnd_ik: "(?mu i k)\<^sup>2 \<le> bnd" using bnd_i[OF ki] by auto
      have bnd_ij: "(?mu i j)\<^sup>2 \<le> bnd" using bnd_i[OF \<open>j \<le> i\<close>] by auto
      from mu_bound_row_1[OF mu_bnd] have bnd1: "bnd \<ge> 1" "bnd \<ge> 0" by auto
      show "(gs.\<mu> (RAT F1) i k)\<^sup>2 \<le> 4 * bnd"
      proof (cases "k > j")
        case True
        show ?thesis
          by (subst mu_no_change[OF i], (insert True ki i bnd1, auto)[3], intro order.trans[OF bnd_ik], auto)
      next
        case False
        hence kj: "k \<le> j" by auto
        show ?thesis
        proof (cases "k = j")
          case True 
          show ?thesis using mult_mono[OF small small] unfolding mudiff True using bnd1 
            by (auto simp: power2_eq_square)
        next
          case False
          with kj have k_j: "k < j" by auto
          define M where "M = max (abs (?mu i k)) (max (abs (?mu i j)) (1/2))" 
          have M0: "M \<ge> 0" unfolding M_def by auto
          let ?new_mu = "?mu i k - ?R c * ?mu j k" 
          have "abs ?new_mu \<le> abs (?mu i k) + abs (?R c * ?mu j k)" by simp
          also have "\<dots> = abs (?mu i k) + abs (?R c) * abs (?mu j k)" unfolding abs_mult ..
          also have "\<dots> \<le> abs (?mu i k) + (abs (?mu i j) + 1/2) * (1/2)" 
          proof (rule add_left_mono[OF mult_mono], unfold c mu[symmetric])
            show "\<bar>?R (floor_ceil mu)\<bar> \<le> \<bar>mu\<bar> + 1 / 2" unfolding floor_ceil_def by linarith
            from inv(11)[unfolded gs.reduced_def, THEN conjunct2, rule_format, OF \<open>j < i\<close> k_j]
            show "\<bar>?mu j k\<bar> \<le> 1/2" .
          qed auto
          also have "\<dots> \<le> M + (M + M) * (1/2)" 
            by (rule add_mono[OF _ mult_right_mono[OF add_mono]], auto simp: M_def)
          also have "\<dots> = 2 * M" by auto
          finally have le: "abs ?new_mu \<le> 2 * M" .
          have "(gs.\<mu> (RAT F1) i k)\<^sup>2 = ?new_mu\<^sup>2" 
            unfolding mu_change[OF kj] by auto
          also have "\<dots> \<le> (2 * M)^2" unfolding abs_le_square_iff[symmetric] using le M0 by auto
          also have "\<dots> = 4 * M^2" by simp
          also have "\<dots> \<le> 4 * bnd" 
          proof (rule mult_left_mono)            
            show "M^2 \<le> bnd" using bnd_ij bnd_ik bnd1 unfolding M_def
              by (auto simp: max_def power2_eq_square)
          qed auto
          finally show ?thesis .
        qed
      qed
    qed
  } note mu_bound_factor = this
  {
    assume c0: "c = 0" 
    have "Fr1 = update_i Fr (F ! i)" unfolding Fr1_def x[symmetric] c0 
      using \<open>F ! i \<in> carrier_vec n\<close> \<open>F ! j \<in> carrier_vec n\<close> by auto
    from update_i[OF Fr, of "(F ! i)", folded this] i len
    have "list_repr i Fr1 (F[i := (F ! i)])" by auto
    also have "F[i := F ! i] = F" 
      by (rule nth_equalityI, force, intro allI, rename_tac j, insert i len, case_tac "j = i", auto)
    finally have "f_repr i Fr1 F" .
    with Fr have "Fr1 = Fr" unfolding list_repr_def by (cases Fr, cases Fr1, auto)
  } note c0 = this
  from res[unfolded basis_reduction_add_row_main.simps Let_def fj Mij Hr]
  have res: "i' = i" "Fr' = Fr1" "Gr' = Gr" using Mij c0 i len cc
    by (auto simp: j split: if_splits)
  {
    from Gr[unfolded g_repr_def] i
    have "list_repr i Gr (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F) [0..<m]))" 
      (is "list_repr _ _ (map ?f (map (GSO F) ?is))")
      by auto
    also have "map (GSO F) ?is = map (GSO F1) ?is" (is "?l = ?r")
    proof (rule nth_equalityI, force, unfold length_map, intro allI impI, goal_cases)
      case (1 ii)
      hence ii: "ii < m" using i by auto
      from 1 have id: "?is ! ii = ii"
        by (metis add.commute add.right_neutral diff_zero length_upt nth_upt)
      have "GSO F ii = GSO F1 ii" using arg_cong[OF Hs[unfolded G1_def G_def], of "\<lambda> xs. xs ! ii"] ii
        unfolding GSO_def by auto
      thus ?case unfolding nth_map[OF 1] id .
    qed
    finally have "list_repr i Gr (map ?f (map (GSO F1) [0..<m]))" .
    hence gso'': "g_repr i Gr F1" unfolding g_repr_def using i by simp
    have repr': "f_repr i Fr1 F1" unfolding F1_def Fr1_def x map_update
      by (rule update_i[OF Fr], insert add, auto)
    from inv(12) have fbnd: "f_bound False i F" .
    have fbnd: "f_bound False i F1"
      unfolding f_bound_def
    proof (intro allI impI, goal_cases)
      case (1 j)
      show ?case
      proof (cases "j = i")
        case False
        with 1 fbnd[unfolded f_bound_def] have "\<parallel>F ! j\<parallel>\<^sup>2 \<le> int (A * m)" by auto
        thus ?thesis unfolding F1_def using False 1 inv(2-) by auto
      next
        case True        
        have "of_int \<parallel>F1 ! i\<parallel>\<^sup>2 = \<parallel>RAT F1 ! i\<parallel>\<^sup>2" using i F1' by (auto simp: sq_norm_of_int)
        also have "... \<le> (rat_of_nat (Suc i * A) * 4) * bnd" 
          using sq_norm_fs_mu_G_bound[OF indep_F1 F1'(1) G1_def(1)[unfolded Hs] i refl mu_bound_factor inv(13)]
          by (auto simp: ac_simps)
        also have "\<dots> \<le> (rat_of_nat (Suc i * A) * 4) * (4 ^ (m - 2) * rat_of_nat (A ^ (m - 1) * m))"
          by (rule mult_left_mono[OF bnd], auto)
        also have "\<dots> = rat_of_int (int (Suc i * A) * 4 * (4 ^ (m - 2) * int (A ^ (m - 1) * m)))" 
          unfolding of_int_mult of_nat_mult by simp
        finally have "\<parallel>F1 ! i\<parallel>\<^sup>2 \<le> int (Suc i * A) * 4 * (4 ^ (m - 2) * int (A ^ (m - 1) * m))" by linarith
        also have "\<dots> = int (Suc i * (4 * 4 ^ (m - 2)) * (A * A ^ (m - 1)) * m)" (is "_ = int ?x") 
          unfolding of_nat_mult by simp
        also have "?x = Suc i * 4 ^ (Suc (m - 2)) * A ^ (Suc (m - 1)) * m" unfolding power_Suc ..
        also have "Suc (m - 2) = m - 1" using j i by simp
        also have "Suc (m - 1) = m" using i by simp
        finally have "\<parallel>F1 ! i\<parallel>\<^sup>2 \<le> int (Suc i) * int (4 ^ (m - 1) * A ^ m * m)" unfolding of_nat_mult by simp 
        also have "\<dots> \<le> m * int (4 ^ (m - 1) * A ^ m * m)" 
          by (rule mult_mono, insert i, auto)
        finally have "\<parallel>F1 ! i\<parallel>\<^sup>2 \<le> int (4 ^ (m - 1) * A ^ m * m * m)" unfolding of_nat_mult by (simp add: ac_simps)
        thus ?thesis unfolding True by auto
      qed
    qed
    have "LLL_invariant False (True,i, Fr1, Gr) F1 G" unfolding Hs[symmetric]
      apply (rule LLL_invI[OF repr' gso'' G1_def(2)[folded snd_gram_schmidt_int,symmetric] _ red inv(7) _ _ sred])
      by (insert F1 F1_F inv(5) fbnd indep_F1 Hs inv(13), auto)
  } note inv_gso = this
  show ?thesis using mu_bound_factor small mu_change inv_gso mudiff mu_no_change unfolding res j F1_def by auto
qed

lemma basis_reduction_add_rows: fixes Gr assumes Linv: "LLL_invariant False (True,i,Fr,Gr) F G"
  and i: "i < m" 
  and res: "basis_reduction_add_rows (i,Fr,Gr) = (i',Fr',Gr')"
  and row_bnd: "mu_bound_row F (4^(m - 1 - i) * bnd) i" 
  and bnd: "bnd = of_nat (A ^ (m - 1) * m)" 
shows "\<exists> F' fi. LLL_invariant True (False, i,Fr',Gr) F' G \<and> i' = i \<and> Gr' = Gr \<and> F' = F[i := fi]"
(* unused: and 
  (\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> i' \<noteq> i \<longrightarrow> 
    gs.\<mu> (RAT F') i' j' = gs.\<mu> (RAT F) i' j') *)
proof -
  note inv = LLL_invD[OF Linv]
  let ?xs = "map (gs.gso (RAT F)) [0..<i]"
  from inv(8)[unfolded list_repr_def] inv(4) i
  have id: "fst Fr = rev (take i F)"  
    by (auto simp: rev_map[symmetric] take_map o_def)
  from inv(9) have id': "fst Gr = rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) ?xs)" 
    unfolding g_repr_def list_repr_def GSO_def by (auto simp: take_map)
  note res = res[unfolded basis_reduction_add_rows_def split Let_def]
  define ii where "ii = i" 
  hence id'': "[0..< i] = [0 ..< ii]" by auto
  have id': "fst Gr = rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0 ..< ii]))" 
    using i unfolding id' id'' by auto
  have id: "fst Fr = rev (take ii F)" unfolding id ii_def by auto
  let ?small = "\<lambda> F j. abs (gs.\<mu> (RAT F) i j) \<le> 1/2" 
  have small: "\<forall> j. ii \<le> j \<longrightarrow> j < i \<longrightarrow> ?small F j" unfolding ii_def by auto
  from row_bnd have row_bnd: "mu_bound_row F (4 ^ (m - 1 - ii) * bnd) i" unfolding ii_def .
  from res[unfolded id id'] have
    "basis_reduction_add_row_i_all_main (i, Fr, Gr) (rev (take ii F))
     (rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0..<ii]))) =
    (i', Fr', Gr')" "ii \<le> i" unfolding ii_def by auto 
  hence "\<exists> F' fi. LLL_invariant True (False,i,Fr',Gr) F' G \<and> i' = i \<and> Gr' = Gr \<and> F' = F[i := fi] \<and>
  (\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> i' \<noteq> i \<longrightarrow> 
    gs.\<mu> (RAT F') i' j' = gs.\<mu> (RAT F) i' j')" using Linv small row_bnd
  proof (induct ii arbitrary: Fr F)
    case (Suc ii Fr F)
    note inv = LLL_invD[OF Suc(4)]
    let ?fs = "gs.gso (RAT F) ii" 
    let ?fsn = "(?fs, \<parallel>?fs\<parallel>\<^sup>2)"       
    let ?main = "basis_reduction_add_row_main (i, Fr, Gr) (F ! ii)
        (\<mu>_ij (get_nth_i Fr) ?fsn)" 
    obtain i'' Fr'' Gr'' where main: "?main = (i'', Fr'', Gr'')" 
      by (cases ?main, auto)
    from Suc(3) have ii: "ii < i" "(ii < i) = True" by auto
    have Gi: "F ! i \<in> carrier_vec n" using inv(3,4) i by auto
    have gs_gs: "gram_schmidt.gso n (RAT F) ii \<in> Rn" 
      by (rule gram_schmidt.gso_carrier', insert inv(3,4) i ii, auto)
    from get_nth_i[OF inv(8)] inv(4) i Gi gs_gs
    have pair: "\<mu>_ij (get_nth_i Fr) ?fsn = 
      gs.\<mu> (RAT F) i ii" 
      unfolding \<mu>_ij_def split gs.\<mu>.simps ii if_True id
      by auto
    define c where "c = floor_ceil (gs.\<mu> (RAT F) i ii)" 
    have "4 * (4 ^ (m - 1 - Suc ii) * bnd) = 4 ^ (Suc (m - 1 - Suc ii)) * bnd" by simp
    also have "Suc (m - 1 - Suc ii) = m - 1 - ii" using Suc(2-) i by simp 
    finally have four: "4 * (4 ^ (m - 1 - Suc ii) * bnd) = 4 ^ (m - 1 - ii) * bnd" by simp
    have upper: "4 ^ (m - 1 - Suc ii) * bnd \<le> 4 ^ (m - 2) * bnd" 
      by (rule mult_right_mono, rule pow_mono_exp, auto simp: bnd)
    from basis_reduction_add_row_main[OF Suc(4) i ii(1) main refl pair c_def, of "4 ^ (m - 1 - Suc ii) * bnd",
      unfolded four, OF Suc(6), folded bnd, OF upper]
    obtain v where
        Linv: "LLL_invariant False (True,i, Fr'', Gr) (F[i := v]) G" 
      and id: "i'' = i" "Gr'' = Gr" 
      and small: "?small (F[i := v]) ii" 
      and id': "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> (i' \<noteq> i \<or> ii < j') \<longrightarrow>
        gs.\<mu> (RAT (F[i := v])) i' j' =
        gs.\<mu> (RAT F) i' j'" 
      and bnd': "mu_bound_row (F[i := v]) (4 ^ (m - 1 - ii) * bnd) i" by auto   
    let ?G = "F[i := v]" 
    from inv Suc(3) have lt: "ii < length F" by auto
    have "(rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0..<Suc ii])))
      = (?fsn # rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0..<ii])))" 
      by auto
    from id Suc(2)[unfolded rev_take_Suc[OF lt] this basis_reduction_add_row_i_all_main.simps split Let_def main]
    have "basis_reduction_add_row_i_all_main ((i, Fr'', Gr)) (rev (take ii F))
      (rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0..<ii]))) =
      (i', Fr', Gr')" by auto
    also have "rev (take ii F) = rev (take ii ?G)" using ii by auto
    also have "map (gs.gso (RAT F)) [0..<ii] = map (gs.gso (RAT ?G)) [0..<ii]"
      by (rule nth_equalityI, auto intro!: gs_gs_identical, insert inv(4) i ii, auto)
    finally have res: "basis_reduction_add_row_i_all_main ((i, Fr'', Gr)) (rev (take ii ?G))
      (rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT ?G)) [0..<ii]))) =
      (i', Fr', Gr')" by auto
    from ii have ii_le: "ii \<le> i" by auto
    have small: "\<forall>j\<ge>ii. j < i \<longrightarrow> ?small ?G j" 
    proof (intro allI impI)
      fix j
      assume *: "ii \<le> j" "j < i"       
      show "?small ?G j"
      proof (cases "j = ii")
        case True
        with small show ?thesis by auto
      next
        case False
        with * Suc(5)[rule_format, of j] 
        have small: "?small F j" by auto
        with id'[rule_format, OF i, of j] i * False
        show ?thesis by auto
      qed
    qed
    from Suc(1)[OF res ii_le Linv small bnd'] obtain G' fi where
      Linv: "LLL_invariant True (False,i, Fr', Gr) G' G" 
      and i': "i' = i" 
      and fi: "G' = F[i := v, i := fi]" 
      and gso': "Gr' = Gr" 
      and id: "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> i' \<noteq> i \<Longrightarrow>
           gs.\<mu> (RAT G') i' j' =
           gs.\<mu> (RAT ?G) i' j'" by blast
    from fi have fi: "G' = F[i := fi]" by auto
    show ?case
    proof (intro exI conjI, rule Linv, rule i', rule gso', rule fi, intro allI impI, goal_cases)
      case (1 i' j')
      show ?case unfolding id[OF 1] 
        by (rule id'[rule_format], insert 1 i', auto)
    qed
  next
    case 0 
    hence Linv: "LLL_invariant False (True,i, Fr', Gr') F G" 
      and *: "\<forall>j<i. \<bar>gs.\<mu> (RAT F) i j\<bar> * 2 \<le> 1" "i' = i" "Gr' = Gr" by auto
    from * have mu_small: "mu_small F i" unfolding mu_small_def by auto
    note inv = LLL_invD[OF Linv]
    from inv(12) have f_bound: "f_bound False i F" by auto
    {
      fix ii
      assume ii: "ii < m" 
      have "\<parallel>F ! ii\<parallel>\<^sup>2 \<le> int (A * m)" 
      proof (cases "ii = i")
        case False
        thus ?thesis using ii f_bound[unfolded f_bound_def] by auto
      next
        case True
        have row: "mu_bound_row F 1 i" 
        proof (intro mu_bound_rowI)
          fix j
          assume j: "j \<le> i" 
          from *(1)[rule_format, of j]
          have "abs (gs.\<mu> (RAT F) i j) \<le> 1" using j by (cases "j = i", force simp: gs.\<mu>.simps, auto)
          from mult_mono[OF this this] show "(gs.\<mu> (RAT F) i j)\<^sup>2 \<le> 1" by (auto simp: power2_eq_square)
        qed          
        have "rat_of_int \<parallel>F ! i\<parallel>\<^sup>2 \<le> rat_of_int (int (Suc i * A))" 
          using LLL_inv_sq_norm_fs_mu_G_bound[OF Linv i row] i by auto
        hence "\<parallel>F ! i\<parallel>\<^sup>2 \<le> int (Suc i * A)" by linarith
        also have "\<dots> = int A * int (Suc i)" unfolding of_nat_mult by simp
        also have "\<dots> \<le> int A * int m" 
          by (rule mult_left_mono, insert i, auto)
        also have "\<dots> = int (A * m)" by simp
        finally show ?thesis unfolding True .
      qed
    }
    hence f_bound: "f_bound True i F" unfolding f_bound_def by auto
    have "LLL_invariant True (False, i, Fr', Gr') F G"
      by (rule LLL_invI, insert f_bound inv mu_small, blast+)
    thus ?case by (intro exI[of _ F] exI[of _ "F ! i"], insert *, auto)
  qed
  thus ?thesis by blast
qed

(* lemma 16.16 (ii), one case *)
lemma d_swap_unchanged: assumes len: "length F1 = m" 
  and i0: "i \<noteq> 0" and i: "i < m" and ki: "k \<noteq> i" and km: "k \<le> m"   
  and swap: "F2 = F1[i := F1 ! (i - 1), i - 1 := F1 ! i]"
shows "d F1 k = d F2 k"
proof -
  let ?F1_M = "mat k n (\<lambda>(i, y). F1 ! i $ y)" 
  let ?F2_M = "mat k n (\<lambda>(i, y). F2 ! i $ y)" 
  have "\<exists> P. P \<in> carrier_mat k k \<and> det P \<in> {-1, 1} \<and> ?F2_M = P * ?F1_M" 
  proof cases
    assume ki: "k < i" 
    hence H: "?F2_M = ?F1_M" unfolding swap
      by (intro eq_matI, auto)
    let ?P = "1\<^sub>m k" 
    have "?P \<in> carrier_mat k k" "det ?P \<in> {-1, 1}" "?F2_M = ?P * ?F1_M" unfolding H by auto
    thus ?thesis by blast
  next
    assume "\<not> k < i" 
    with ki have ki: "k > i" by auto
    let ?P = "swaprows_mat k i (i - 1)" 
    from i0 ki have neq: "i \<noteq> i - 1" and kmi: "i - 1 < k" by auto
    have *: "?P \<in> carrier_mat k k" "det ?P \<in> {-1, 1}" using det_swaprows_mat[OF ki kmi neq] ki by auto
    from i len have iH: "i < length F1" "i - 1 < length F1" by auto 
    have "?P * ?F1_M = swaprows i (i - 1) ?F1_M" 
      by (subst swaprows_mat[OF _ ki kmi], auto)
    also have "\<dots> = ?F2_M" unfolding swap
      by (intro eq_matI, rename_tac ii jj, 
          case_tac "ii = i", (insert iH, simp add: nth_list_update)[1],
          case_tac "ii = i - 1", insert iH neq ki, auto simp: nth_list_update)
    finally show ?thesis using * by metis
  qed
  then obtain P where P: "P \<in> carrier_mat k k" and detP: "det P \<in> {-1, 1}" and H': "?F2_M = P * ?F1_M" by auto
  have "d F2 k = det (gs.Gramian_matrix F2 k)" 
    unfolding d_def gs.Gramian_determinant_def by simp
  also have "\<dots> = det (?F2_M * ?F2_M\<^sup>T)" unfolding gs.Gramian_matrix_def Let_def by simp
  also have "?F2_M * ?F2_M\<^sup>T = ?F2_M * (?F1_M\<^sup>T * P\<^sup>T)" unfolding H'
    by (subst transpose_mult[OF P], auto)
  also have "\<dots> = P * (?F1_M * (?F1_M\<^sup>T * P\<^sup>T))" unfolding H' 
    by (subst assoc_mult_mat[OF P], auto)
  also have "det \<dots> = det P * det (?F1_M * (?F1_M\<^sup>T * P\<^sup>T))" 
    by (rule det_mult[OF P], insert P, auto)
  also have "?F1_M * (?F1_M\<^sup>T * P\<^sup>T) = (?F1_M * ?F1_M\<^sup>T) * P\<^sup>T" 
    by (subst assoc_mult_mat, insert P, auto)
  also have "det \<dots> = det (?F1_M * ?F1_M\<^sup>T) * det P" 
    by (subst det_mult, insert P, auto simp: det_transpose)
  also have "det (?F1_M * ?F1_M\<^sup>T) = det (gs.Gramian_matrix F1 k)" unfolding gs.Gramian_matrix_def Let_def by simp
  also have "\<dots> = d F1 k" 
    unfolding d_def gs.Gramian_determinant_def by simp
  finally have "d F2 k = (det P * det P) * d F1 k" by simp
  also have "det P * det P = 1" using detP by auto
  finally show "d F1 k = d F2 k" by simp
qed

lemma LLL_inv_A_pos: assumes LLL: "LLL_invariant outside (upw, i, Fr, Gr) F G" 
  and m: "m \<noteq> 0" 
shows "A > 0" 
proof -
  let ?r = rat_of_int
  note inv = LLL_invD[OF LLL]
  note conn = LLL_connect[OF LLL]
  from inv(3,4) have F: "RAT F ! 0 \<in> Rn" "F ! 0 \<in> carrier_vec n" using m unfolding set_conv_nth by auto
  from m have upt: "[0..< m] = 0 # [1 ..< m]" using upt_add_eq_append[of 0 1 "m - 1"] by auto
  from inv(4) m have "map_vec ?r (F ! 0) \<noteq> 0\<^sub>v n" using gs.lin_indpt_list_nonzero[OF inv(10)]
    unfolding set_conv_nth by force
  hence F0: "F ! 0 \<noteq> 0\<^sub>v n" by auto
  hence "sq_norm (F ! 0) \<noteq> 0" using F by simp
  hence 1: "sq_norm (F ! 0) \<ge> 1" using sq_norm_vec_ge_0[of "F ! 0"] by auto
  from inv(13) m have "sq_norm (G ! 0) \<le> of_nat A" unfolding g_bound_def by auto
  also have "G ! 0 = RAT F ! 0" unfolding conn upt using F by (simp add: gs.gso.simps[of _ 0])
  also have "RAT F ! 0 = map_vec ?r (F ! 0)" using inv(4) m by auto
  also have "sq_norm \<dots> = ?r (sq_norm (F ! 0))" by (simp add: sq_norm_of_int)
  finally show ?thesis using 1 by (cases A, auto)
qed

(* equation (3) in front of Lemma 16.18 *)
lemma d_approx: assumes LLL: "LLL_invariant outside (upw, ix, Fr, Gr) F G" 
  and i: "i < m" 
shows "rat_of_int (d F i) \<le> rat_of_nat (A^i)" 
proof -
  note inv = LLL_invD[OF LLL]
  note conn = LLL_connect[OF LLL]
  from LLL_inv_A_pos[OF LLL] i have A: "0 < A" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (d F i) = (\<Prod>j<i. \<parallel>G ! j\<parallel>\<^sup>2)" unfolding d_def using i
    by (auto simp: Gramian_determinant [OF LLL])
  also have "\<dots> \<le> (\<Prod>j<i. of_nat A)" using i
    by (intro prod_mono ballI conjI prod_nonneg, insert inv(13)[unfolded g_bound_def], auto)
  also have "\<dots> = (of_nat A)^i" unfolding prod_constant by simp
  also have "\<dots> = of_nat (A^i)" by simp
  finally show ?thesis by simp
qed

lemma D_approx: assumes "LLL_invariant outside (upw, i, Fr, Gr) F G" 
  shows "D F \<le> A ^ (m * m)" 
proof - 
  note inv = LLL_invD[OF assms]
  note conn = LLL_connect[OF assms]
  from LLL_inv_A_pos[OF assms] have A: "m \<noteq> 0 \<Longrightarrow> 0 < A" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (\<Prod>i<m. d F i) = (\<Prod>i<m. rat_of_int (d F i))" by simp
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat A) ^ i)" 
    by (rule prod_mono, insert d_approx[OF assms] LLL_d_pos[OF assms], auto simp: less_le)
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat A ^ m))" 
    by (rule prod_mono, insert A, auto intro: pow_mono_exp)
  also have "\<dots> = (of_nat A)^(m * m)" unfolding prod_constant power_mult by simp
  also have "\<dots> = of_nat (A ^ (m * m))" by simp
  finally have "(\<Prod>i<m. d F i) \<le> A ^ (m * m)" by linarith
  also have "(\<Prod>i<m. d F i) = D F" unfolding D_def 
    by (subst nat_0_le, rule prod_nonneg, insert LLL_d_pos[OF assms], auto simp: le_less)  
  finally show "D F \<le> A ^ (m * m)" by linarith 
qed

definition base where "base = real_of_rat ((4 * \<alpha>) / (4 + \<alpha>))" 
end

locale LLL_with_assms = LLL + 
  assumes \<alpha>: "\<alpha> \<ge> 4/3"
    and lin_dep: "gs.lin_indpt_list (RAT fs_init)" 
    and len: "length fs_init = m" 
begin
lemma \<alpha>0: "\<alpha> > 0" "\<alpha> \<noteq> 0" 
  using \<alpha> by auto

lemma reduction: "0 < reduction" "reduction \<le> 1" 
  "\<alpha> > 4/3 \<Longrightarrow> reduction < 1" 
  "\<alpha> = 4/3 \<Longrightarrow> reduction = 1" 
  using \<alpha> unfolding reduction_def by auto

lemma base: "\<alpha> > 4/3 \<Longrightarrow> base > 1" using reduction(1,3) unfolding reduction_def base_def by auto

lemma LLL_measure_approx: assumes inv: "LLL_invariant outside (upw, i, Fr, Gr) F G"
  and "\<alpha> > 4/3" "m \<noteq> 0" 
shows "LLL_measure (upw,i, Fr, Gr) \<le> m + 2 * m * m * log base A"
proof -   
  have b1: "base > 1" using base assms by auto
  have id: "base = 1 / real_of_rat reduction" unfolding base_def reduction_def using \<alpha>0 by
    (auto simp: field_simps of_rat_divide)
  from LLL_D_pos[OF inv] have D1: "real (D F) \<ge> 1" by auto
  note invD = LLL_invD[OF inv]  
  from invD
  have F: "set F \<subseteq> carrier_vec n" and len: "length F = m" by auto
  have A0: "A > 0" using LLL_inv_A_pos[OF assms(1,3)] .
  from D_approx[OF inv] 
  have D: "D F \<le> A ^ (m * m)" .
  hence "real (D F) \<le> real (A ^ (m * m))" by linarith
  also have "\<dots> = real A ^ (m * m)" by simp
  finally have log: "log base (real (D F)) \<le> log base (real A ^ (m * m))"   
    by (subst log_le_cancel_iff[OF b1], insert D1 A0, auto)

  have "real (logD F) = real (nat \<lfloor>log base (real (D F))\<rfloor>)" 
    unfolding logD_def id using assms by auto
  also have "\<dots> \<le> log base (real (D F))" using b1 D1 by auto
  also have "\<dots> \<le> log base (real A ^ (m * m))" by fact
  also have "\<dots> = (m * m) * log base (real A)" 
    by (rule log_nat_power, insert A0, auto)
  finally have main: "logD F \<le> m * m * log base A" by simp

  have "real (LLL_measure (upw, i, Fr, Gr)) = real (2 * logD F + m - i)"
    unfolding LLL_measure_def split invD(1) by simp
  also have "\<dots> \<le> 2 * real (logD F) + m" using invD by simp
  also have "\<dots> \<le> 2 * (m * m * log base A) + m" using main by auto
  finally show ?thesis by simp
qed


lemma basis_reduction_step: assumes Linv: "LLL_invariant True (upw, i,Fr,Gr) F G"
  and i: "i < m"
  and res: "basis_reduction_step \<alpha> (upw,i,Fr,Gr) = state"
shows "(\<exists> F' G'. LLL_invariant True state F' G')" 
  and "LLL_measure state < LLL_measure (upw, i,Fr,Gr)" 
proof (atomize(full), cases "i = 0")
  case i0: False
  define state' where "state' = (if upw then basis_reduction_add_rows (i, Fr, Gr) else (i, Fr, Gr))" 
  obtain i1 Fr1 Gr1 where state': "state' = (i1, Fr1, Gr1)" by (cases state', auto)
  from i0 have "(i = 0) = False" by auto
  note res = res[unfolded basis_reduction_step_def split fst_conv state'[unfolded state'_def] Let_def this if_False] 
  note inv = LLL_invD[OF Linv]
  from LLL_inv_A_pos[OF Linv] i have A0: "A > 0" by auto
  {
    fix j
    assume ji: "j < i" 
    have "(gs.\<mu> (RAT F) i j)\<^sup>2 \<le> gs.Gramian_determinant (RAT F) j * \<parallel>RAT F ! i\<parallel>\<^sup>2"
      by (rule gs.mu_bound_Gramian_determinant[OF inv(10), unfolded length_map, OF inv(4) refl _ ji i],
      insert ji i inv(2-), auto simp: set_conv_nth)
    also have "gs.Gramian_determinant (RAT F) j = of_int (d F j)" unfolding d_def 
      by (subst of_int_Gramian_determinant, insert ji i inv(2-), auto simp: set_conv_nth)
    also have "\<parallel>RAT F ! i\<parallel>\<^sup>2 = of_int \<parallel>F ! i\<parallel>\<^sup>2" using i inv(2-) by (auto simp: sq_norm_of_int)
    also have "of_int (d F j) * \<dots> \<le> rat_of_nat (A^j) * of_int \<parallel>F ! i\<parallel>\<^sup>2"
      by (rule mult_right_mono, insert ji i d_approx[OF Linv, of j], auto)
    also have "\<dots> \<le> rat_of_nat (A^(m-2)) * of_int (int (A * m))" 
      by (intro mult_mono, unfold of_nat_le_iff of_int_le_iff, rule pow_mono_exp,
      insert inv(12)[unfolded f_bound_def, rule_format, of i] A0 ji i, auto)
    also have "\<dots> = rat_of_nat (A^(m-2) * A * m)" by simp
    also have "A^(m-2) * A = A^(Suc (m - 2))" by simp
    also have "Suc (m - 2) = m - 1" using ji i by auto
    finally have "(gs.\<mu> (RAT F) i j)\<^sup>2 \<le> of_nat (A ^ (m - 1) * m)" .
  } note mu_bound = this
  have mu_bnd: "mu_bound_row F (4 ^ (m - 1 - i) * of_nat (A ^ (m - 1) * m)) i" (is "mu_bound_row _ ?bnd i")
  proof (rule mu_bound_rowI)
    fix j
    assume j: "j \<le> i" 
    have "(gs.\<mu> (RAT F) i j)\<^sup>2 \<le> 1 * of_nat (A ^ (m - 1) * m)" 
    proof (cases "j = i")
      case False
      with mu_bound[of j] j show ?thesis by auto
    next
      case True
      show ?thesis unfolding True gs.\<mu>.simps using i A0 by auto
    qed
    also have "\<dots> \<le> 4 ^ (m - 1 - i) * of_nat (A ^ (m - 1) * m)" 
      by (rule mult_right_mono, auto)
    finally show "(gs.\<mu> (RAT F) i j)\<^sup>2 \<le> ?bnd" . 
  qed
  have f_bnd: "f_bound False i F" using f_bound_True_arbitrary[OF inv(12)] .
  with inv have inv: "LLL_invariant False (upw,i,Fr,Gr) F G" by (intro LLL_invI, blast+)
  have "\<exists> F1. LLL_invariant True (False, i, Fr1, Gr1) F1 G \<and> i1 = i" 
  proof (cases upw)
    case False
    with state'_def[unfolded state']
    show ?thesis by (intro exI[of _ F], insert Linv, auto)
  next
    case True
    with inv have inv: "LLL_invariant False (True, i, Fr, Gr) F G" by auto
    from state'_def[unfolded state'] True
    have "basis_reduction_add_rows (i, Fr, Gr) = (i1, Fr1, Gr1)" by auto
    from basis_reduction_add_rows[OF inv i this mu_bnd refl]
    show ?thesis by auto
  qed
  then obtain F1 
    where Linv': "LLL_invariant True (False, i, Fr1, Gr1) F1 G" and ii: "i1 = i" by auto
  from LLL_invD(14)[OF Linv', unfolded mu_small_def]
  have mu_F1_i: "\<And> j. j<i \<Longrightarrow> \<bar>gs.\<mu> (RAT F1) i j\<bar> \<le> 1 / 2" by auto
  from mu_F1_i[of "i-1"] have m12: "\<bar>gs.\<mu> (RAT F1) i (i - 1)\<bar> \<le> inverse 2" using i0
    by auto
  note d = d_def  
  note Gd = Gramian_determinant(1)
  note Gd12 = Gd[OF inv] Gd[OF Linv']
  have d_eq: "k \<le> m \<Longrightarrow> d F k = d F1 k" for k (* Lemma 16.16 (i) *)
    unfolding d using Gd12[of k] by auto
  have D_eq: "D F = D F1" unfolding D_def
    by (rule arg_cong[of _ _ nat], rule prod.cong, insert d_eq, auto)
  hence logD_eq: "logD F = logD F1" unfolding logD_def by simp
  note inv = LLL_invD[OF inv] 
  note inv' = LLL_invD[OF Linv']
  from inv have repr: "f_repr i Fr F" by auto
  note res = res[unfolded basis_reduction_step_def this split ii]
  let ?x = "G ! (i - 1)" let ?y = "G ! i" 
  let ?x' = "sqnorm_g_im1 Gr1" let ?y' = "sqnorm_g_i Gr1" 
  let ?cond = "\<alpha> * sq_norm ?y < sq_norm ?x" 
  let ?cond' = "\<alpha> * ?y' < ?x'"
  from inv' have red: "gs.weakly_reduced \<alpha> i G" 
    and repr: "f_repr i Fr1 F1" and gS: "snd (gram_schmidt_int n F1) = G" 
    and len: "length F1 = m" and HC: "set F1 \<subseteq> carrier_vec n" 
    and gso: "g_repr i Gr1 F1" and L: "lattice_of F1 = L" 
    and f_bound: "f_bound True i F1" 
    using i by auto 
  from g_i[OF Linv' i] have y: "?y' = sq_norm ?y" by auto
  from g_im1[OF Linv' i i0] have x: "?x' = sq_norm ?x" by auto
  hence cond: "?cond' = ?cond" using y by auto
  from i0 have "(i = 0) = False" by auto
  note res = res[unfolded cond fst_conv this if_False]
  show "(\<exists>H. Ex (LLL_invariant True state H)) \<and> LLL_measure state < LLL_measure (upw, i, Fr, Gr)"
  proof (cases ?cond)
    case False
    from len inc_i[OF repr] repr i have repr': "f_repr (Suc i) (inc_i Fr1) F1" by auto
    from of_list_repr[OF repr'] have Hr': "of_list_repr (inc_i Fr1) = F1" by auto
    from False have le: "sq_norm (G ! (i - 1)) \<le> \<alpha> * sq_norm (G ! i)" by force
    have red: "gs.weakly_reduced \<alpha> (Suc i) G" 
      unfolding gs.weakly_reduced_def
    proof (intro allI impI)
      fix k
      assume ki: "Suc k < Suc i" 
      show "sq_norm (G ! k) \<le> \<alpha> * sq_norm (G ! Suc k)" 
      proof (cases "Suc k < i")
        case True
        from red[unfolded gs.weakly_reduced_def, rule_format, OF True] show ?thesis .
      next
        case False
        with i0 ki have id: "k = i - 1" "Suc k = i" by auto
        with le show ?thesis by auto
      qed
    qed      
    from res False ii
    have state: "state = (True,increase_i (i, Fr1, Gr1))" by auto
    have invS: "LLL_invariant True state F1 G" unfolding state
      by (rule increase_i[OF Linv' i], insert False mu_F1_i, auto)
    obtain Fr' Gr' where state: "state = (True, Suc i, Fr', Gr')" using state
      by (cases state, auto simp: increase_i_def)
    have "LLL_measure state < LLL_measure (upw,i, Fr, Gr)" unfolding LLL_measure_def logD_eq split state
      LLL_invD(1)[OF invS[unfolded state], symmetric] inv(1)[symmetric]
      using i by simp
    thus ?thesis using invS by blast
  next
    case True
    from i0 inv' True i have swap: "set F1 \<subseteq> carrier_vec n" "i < length F1" "i - 1 < length F1" "i \<noteq> i - 1" 
      unfolding LLL_invariant_def Let_def by auto
    define F2 where "F2 = F1[i := F1 ! (i - 1), i - 1 := F1 ! i]"
    define Fr2 where "Fr2 = dec_i (update_im1 (update_i Fr1 (get_nth_im1 Fr1)) (get_nth_i Fr1))"
    from dec_i[OF update_im1[OF update_i[OF repr]], of "get_nth_im1 Fr1" "get_nth_i Fr1", folded Fr2_def] swap(2) i0 
    have "list_repr (i - 1) Fr2 (F1[i := get_nth_im1 Fr1, i - 1 := get_nth_i Fr1])" by auto
    hence repr': "f_repr (i - 1) Fr2 F2" unfolding F2_def
      using get_nth_im1[OF repr] get_nth_i[OF repr] i0 swap(2) by (auto simp: map_update)
    note Hr' = of_list_repr[OF repr']
    obtain G2 where gH': "snd (gram_schmidt_int n F2) = G2" by force
    let ?mu = "\<mu>_i_im1 Fr1 Gr1" 
    have mu: "?mu = gs.\<mu> (RAT F1) i (i - 1)" 
      by (rule \<mu>_i_im1[OF inv'(8,9) _ i0 i], insert inv' swap, auto)
    let ?gso' = "let gi = g_i Gr1; 
        gim1 = g_im1 Gr1;
        fim1 = get_nth_im1 Fr1;
        ni = sqnorm_g_i Gr1;
        nim1 = sqnorm_g_im1 Gr1;
        new_gim1 = gi + ?mu \<cdot>\<^sub>v gim1;
        new_nim1 = ni + square_rat ?mu * nim1;
        new_gi = gim1 - (fim1 \<bullet>i new_gim1 / new_nim1) \<cdot>\<^sub>v new_gim1;
        new_ni = ni * nim1 / new_nim1
          in dec_i (update_im1 (update_i Gr1 (new_gi,new_ni)) (new_gim1,new_nim1))" 
    define Gr2 where gso': "Gr2 = ?gso'"
    have span': "gs.span (SRAT F1) = gs.span (SRAT F2)" 
      by (rule arg_cong[of _ _ gs.span], unfold F2_def, insert swap, auto)
    from res gH' Fr2_def Hr' gso' True ii
    have state: "state = (False, i - 1, Fr2, Gr2)" by (auto simp: Let_def)
    have lF2: "lattice_of F2 = lattice_of F1" unfolding F2_def
      by (rule lattice_of_swap[OF swap refl])
    have len': "length F2 = m" using inv' unfolding F2_def by auto
    have F2: "set F2 \<subseteq> carrier_vec n" using swap unfolding F2_def set_conv_nth
      by (auto, rename_tac k, case_tac "k = i", force, case_tac "k = i - 1", auto)
    let ?rv = "map_vec rat_of_int" 
    from inv'(10) have indepH: "gs.lin_indpt_list (RAT F1)" .
    from i i0 len have "i < length (RAT F1)" "i - 1 < length (RAT F1)" by auto
    with distinct_swap[OF this] len have "distinct (RAT F2) = distinct (RAT F1)" unfolding F2_def
      by (auto simp: map_update)
    with len' F2 span' indepH have indepH': "gs.lin_indpt_list (RAT F2)" unfolding F2_def using i i0
      by (auto simp: gs.lin_indpt_list_def)
    note conn1 = indepH inv'(2) len
    note conn2 = indepH' gH' len'
    from gram_schmidt_int_connect[OF conn1]
    have Gs_fs: "G = map (gs.gso (RAT F1)) [0..<m]" .
    from gram_schmidt_int_connect[OF conn2]
    have G2_F2: "G2 = map (gs.gso (RAT F2)) [0..<m]" .
    have F2_F1: "k < i - 1 \<Longrightarrow> F2 ! k = F1 ! k" for k unfolding F2_def by auto
    { 
      fix k
      assume ki: "k < i - 1" 
      with i have kn: "k < m" by simp
      have "G2 ! k = gs.gso (RAT F2) k" unfolding G2_F2 using kn by auto
      also have "\<dots> = gs.gso (RAT F1) k" 
        by (rule gs_gs_identical, insert ki kn len, auto simp: F2_def)
      also have "\<dots> = G ! k" unfolding Gs_fs using kn by auto
      finally have "G2 ! k = G ! k" .
    } note G2_G = this
    have take_eq: "take (Suc i - 1 - 1) F2 = take (Suc i - 1 - 1) F1" 
      by (intro nth_equalityI, insert len len' i swap(2-), auto intro!: F2_F1) 
    from inv' have "gs.weakly_reduced \<alpha> i G" by auto
    hence "gs.weakly_reduced \<alpha> (i - 1) G" unfolding gs.weakly_reduced_def by auto
    hence red: "gs.weakly_reduced \<alpha> (i - 1) G2"
      unfolding gs.weakly_reduced_def using G2_G by auto
    from inv' have L: "lattice_of F2 = L" unfolding lF2 by auto
    have ii: "g_repr (i - 1) = g_repr ((Suc i - 1) - 1)" using True by auto
    have i1n: "i - 1 < m" using i by auto
    let ?R = rat_of_int
    let ?RV = "map_vec ?R"  
    let ?f1 = "\<lambda> i. RAT F1 ! i"
    let ?f2 = "\<lambda> i. RAT F2 ! i" 
    have heq:"F1 ! (i - 1) = F2 ! i" "take (i-1) F1 = take (i-1) F2"
             "?f2 (i - 1) = ?f1 i" "?f2 i = ?f1 (i - 1)"
      unfolding F2_def using i len i0 by auto
    let ?g2 = "gs.gso (RAT F2)" 
    let ?g1 = "gs.gso (RAT F1)"
    let ?mu1 = "gs.\<mu> (RAT F1)" 
    let ?mu2 = "gs.\<mu> (RAT F2)"
    from gH'[unfolded gram_schmidt_int_def gram_schmidt_wit_def] indepH' len'
    have connH':  
      "gs.lin_indpt_list (RAT F2)" "length (RAT F2) = m" "snd (gs.main (RAT F2)) = G2" 
      by (auto intro: nth_equalityI)
    from gS[unfolded gram_schmidt_int_def gram_schmidt_wit_def] indepH len
    have connH:  
      "gs.lin_indpt_list (RAT F1)" "length (RAT F1) = m" "snd (gs.main (RAT F1)) = G" 
      by (auto intro: nth_equalityI)
    have norm_pos2: "j < m \<Longrightarrow> sq_norm (?g2 j) > 0" for j 
      using gs.sq_norm_pos[OF connH',of j] unfolding G2_F2 o_def by simp
    have norm_pos1: "j < m \<Longrightarrow> sq_norm (?g1 j) > 0" for j 
      using gs.sq_norm_pos[OF connH,of j] unfolding Gs_fs o_def by simp
    have gs: "\<And> j. j < m \<Longrightarrow> ?g1 j \<in> Rn" using gs.gso_carrier[OF connH] .
    have gs2: "\<And> j. j < m \<Longrightarrow> ?g2 j \<in> Rn" using gs.gso_carrier[OF connH'] .
    have g: "\<And> j. j < m \<Longrightarrow> ?f1 j \<in> Rn" using gs.f_carrier[OF connH] .
    have g2: "\<And> j. j < m \<Longrightarrow> ?f2 j \<in> Rn" using gs.f_carrier[OF connH'] .
    let ?fs1 = "?f1 ` {0..< (i - 1)}" 
    have G: "?fs1 \<subseteq> Rn" using g i by auto
    let ?gs1 = "?g1 ` {0..< (i - 1)}" 
    have G': "?gs1 \<subseteq> Rn" using gs i by auto
    let ?S = "gs.span ?fs1" 
    let ?S' = "gs.span ?gs1" 
    have S'S: "?S' = ?S" 
      by (rule gs.partial_span'[OF connH], insert i, auto)
    have "gs.is_oc_projection (?g2 (i - 1)) (gs.span (?g2 ` {0..< (i - 1)})) (?f2 (i - 1))" 
      by (rule gs.gso_oc_projection_span(2)[OF connH' \<open>i - 1 < m\<close>])
    also have "?f2 (i - 1) = ?f1 i" unfolding F2_def using len i by auto
    also have "gs.span (?g2 ` {0 ..< (i - 1)}) = gs.span (?f2 ` {0 ..< (i - 1)})" 
      by (rule gs.partial_span'[OF connH'], insert i, auto)
    also have "?f2 ` {0 ..< (i - 1)} = ?fs1" 
      by (rule image_cong[OF refl], insert len i, auto simp: F2_def)
    finally have claim1: "gs.is_oc_projection (?g2 (i - 1)) ?S (?f1 i)" .
    have list_id: "[0..<Suc (i - 1)] = [0..< i - 1] @ [i - 1]" 
      "[0..< Suc i] = [0..< i] @ [i]" "map f [x] = [f x]" for f x using i by auto
    (* f1i_sum is claim 2 *)
    have f1i_sum: "?f1 i = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i]) + ?g1 i" (is "_ = ?sum + _") 
      unfolding gs.fi_is_sum_of_mu_gso[OF connH i] map_append list_id
      by (subst gs.M.sumlist_snoc, insert i gs, auto simp: gs.\<mu>.simps)

    have f1im1_sum: "?f1 (i - 1) = gs.sumlist (map (\<lambda>j. ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0..<i - 1]) + ?g1 (i - 1)" (is "_ = ?sum1 + _")
      unfolding gs.fi_is_sum_of_mu_gso[OF connH \<open>i - 1 < m\<close>] map_append list_id
      by (subst gs.M.sumlist_snoc, insert i gs, auto simp: gs.\<mu>.simps)

    have sum: "?sum \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
    have sum1: "?sum1 \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
    from gs.span_closed[OF G] have S: "?S \<subseteq> Rn" by auto
    from gs i have gs': "\<And> j. j < i - 1 \<Longrightarrow> ?g1 j \<in> Rn" and gsi: "?g1 (i - 1) \<in> Rn" by auto
    have "[0 ..< i] = [0 ..< Suc (i - 1)]" using i0 by simp
    also have "\<dots> = [0 ..< i - 1] @ [i - 1]" by simp
    finally have list: "[0 ..< i] = [0 ..< i - 1] @ [i - 1]" .

    { (* d does not change for k \<noteq> i *)
      fix k
      assume kn: "k \<le> m" and ki: "k \<noteq> i" 
      from d_swap_unchanged[OF len i0 i ki kn F2_def] d_eq[OF kn] 
      have "d F k = d F2 k" by simp
    } note d = this

    (* new value of g (i-1) *)
    have g2_im1: "?g2 (i - 1) = ?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)" (is "_ = _ + ?mu_f1")
    proof (rule gs.is_oc_projection_eq[OF connH claim1 _ S g[OF i]])
      show "gs.is_oc_projection (?g1 i + ?mu_f1) ?S (?f1 i)" unfolding gs.is_oc_projection_def
      proof (intro conjI allI impI)
        let ?sum' = "gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
        have sum': "?sum' \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
        show inRn: "(?g1 i + ?mu_f1) \<in> Rn" using gs[OF i] gsi i by auto
        have carr: "?sum \<in> Rn" "?g1 i \<in> Rn" "?mu_f1 \<in> Rn" "?sum' \<in> Rn" using sum' sum gs[OF i] gsi i by auto
        have "?f1 i - (?g1 i + ?mu_f1) = (?sum + ?g1 i) - (?g1 i + ?mu_f1)"
          unfolding f1i_sum by simp
        also have "\<dots> = ?sum - ?mu_f1" using carr by auto
        also have "?sum = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1] @ [?mu_f1])" 
          unfolding list by simp 
        also have "\<dots> = ?sum' + ?mu_f1" 
          by (subst gs.sumlist_append, insert gs' gsi, auto)
        also have "\<dots> - ?mu_f1 = ?sum'" using sum' gsi by auto
        finally have id: "?f1 i - (?g1 i + ?mu_f1) = ?sum'" .
        show "?f1 i - (?g1 i + ?mu_f1) \<in> gs.span ?S" unfolding id gs.span_span[OF G]
        proof (rule gs.sumlist_in_span[OF G])
          fix v
          assume "v \<in> set (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
          then obtain j where j: "j < i - 1" and v: "v = ?mu1 i j \<cdot>\<^sub>v ?g1 j" by auto
          show "v \<in> ?S" unfolding v
            by (rule gs.smult_in_span[OF G], unfold S'S[symmetric], rule gs.span_mem, insert gs i j, auto)
        qed
        fix x
        assume "x \<in> ?S"
        hence x: "x \<in> ?S'" using S'S by simp
        show "(?g1 i + ?mu_f1) \<bullet> x = 0"
        proof (rule gs.orthocompl_span[OF _ G' inRn x])
          fix x
          assume "x \<in> ?gs1"
          then obtain j where j: "j < i - 1" and x_id: "x = ?g1 j" by auto
          from j i x_id gs[of j] have x: "x \<in> Rn" by auto
          {
            fix k
            assume k: "k > j" "k < m" 
            have "?g1 k \<bullet> x = 0" unfolding x_id 
              by (rule gs.orthogonal[OF connH], insert k, auto)
          }
          from this[of i] this[of "i - 1"] j i 
          have main: "?g1 i \<bullet> x = 0" "?g1 (i - 1) \<bullet> x = 0" by auto
          have "(?g1 i + ?mu_f1) \<bullet> x = ?g1 i \<bullet> x + ?mu_f1 \<bullet> x" 
            by (rule add_scalar_prod_distrib[OF gs[OF i] _ x], insert gsi, auto)
          also have "\<dots> = 0" using main
            by (subst smult_scalar_prod_distrib[OF gsi x], auto)
          finally show "(?g1 i + ?mu_f1) \<bullet> x = 0" .
        qed
      qed
    qed
    { (* 16.13 (i): for g, only g_i and g_{i-1} can change *)
      fix k
      assume kn: "k < m" 
        and ki: "k \<noteq> i" "k \<noteq> i - 1"
      have "?g2 k = gs.oc_projection (gs.span (?g2 ` {0..<k})) (?f2 k)" 
        by (rule gs.gso_oc_projection_span[OF connH' kn])
      also have "gs.span (?g2 ` {0..<k}) = gs.span (?f2 ` {0..<k})" 
        by (rule gs.partial_span'[OF connH'], insert kn, auto)
      also have "?f2 ` {0..<k} = ?f1 ` {0..<k}"
      proof(cases "k\<le>i")
        case True hence "k < i - 1" using ki by auto
        then show ?thesis apply(intro image_cong) unfolding F2_def using len i by auto
      next
        case False 
        have "?f2 ` {0..<k} = Fun.swap i (i - 1) ?f1 ` {0..<k}"
          unfolding Fun.swap_def F2_def o_def using len i 
          by (intro image_cong, insert len kn, force+)
        also have "\<dots> = ?f1 ` {0..<k}"
          apply(rule swap_image_eq) using False by auto
        finally show ?thesis.
      qed
      also have "gs.span \<dots> = gs.span (?g1 ` {0..<k})" 
        by (rule sym, rule gs.partial_span'[OF connH], insert kn, auto)
      also have "?f2 k = ?f1 k" using ki kn len unfolding F2_def by auto
      also have "gs.oc_projection (gs.span (?g1 ` {0..<k})) \<dots> = ?g1 k" 
        by (subst gs.gso_oc_projection_span[OF connH kn], auto)
      finally have "?g2 k = ?g1 k" . 
    } note g2_g1_identical = this

    (* calculation of new mu-values *)
    { (* no change of mu for lines before line i - 1 *)
      fix jj ii
      assume ii: "ii < i - 1"  
      have "?mu2 ii jj = ?mu1 ii jj" using ii i len
        by (subst gs_\<mu>_identical[of _ _ "RAT F1" "RAT F2"], auto simp: F2_def)
    } note mu'_mu_small_i = this
    { (* swap of mu-values in lines i - 1 and i for j < i - 1 *)
      fix jj
      assume jj: "jj < i - 1"  
      hence id1: "jj < i - 1 \<longleftrightarrow> True" "jj < i \<longleftrightarrow> True" by auto
      have id2: "?g2 jj = ?g1 jj" by (subst g2_g1_identical, insert jj i, auto)       
      have "?mu2 i jj = ?mu1 (i - 1) jj" "?mu2 (i - 1) jj = ?mu1 i jj" 
        unfolding gs.\<mu>.simps id1 id2 if_True using len i i0 by (auto simp: F2_def)
    } note mu'_mu_i_im1_j = this

    have im1: "i - 1 < m" using i by auto

    (* calculation of new value of g_i *)
    let ?g2_im1 = "?g2 (i - 1)" 
    have g2_im1_Rn: "?g2_im1 \<in> Rn" using i by (auto intro!: gs.gso_carrier[OF connH'])
    {
      let ?mu2_f2 = "\<lambda> j. - ?mu2 i j \<cdot>\<^sub>v ?g2 j" 
      let ?sum = "gs.sumlist (map (\<lambda>j. - ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
      have mhs: "?mu2_f2 (i - 1) \<in> Rn" using i by (auto intro!: gs.gso_carrier[OF connH'])
      have sum': "?sum \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
      have gim1: "?f1 (i - 1) \<in> Rn" using g i by auto
      have "?g2 i = ?f2 i + gs.sumlist (map ?mu2_f2 [0 ..< i-1] @ [?mu2_f2 (i-1)])" 
        unfolding gs.gso.simps[of _ i] list by simp
      also have "?f2 i = ?f1 (i - 1)" unfolding F2_def using len i i0 by auto
      also have "map ?mu2_f2 [0 ..< i-1] = map (\<lambda>j. - ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1]"
        by (rule map_cong[OF refl], subst g2_g1_identical, insert i, auto simp: mu'_mu_i_im1_j)
      also have "gs.sumlist (\<dots> @ [?mu2_f2 (i - 1)]) = ?sum + ?mu2_f2 (i - 1)" 
        by (subst gs.sumlist_append, insert gs i mhs, auto)
      also have "?f1 (i - 1) + \<dots> = (?f1 (i - 1) + ?sum) + ?mu2_f2 (i - 1)"
        using gim1 sum' mhs by auto
      also have "?f1 (i - 1) + ?sum = ?g1 (i - 1)" unfolding gs.gso.simps[of _ "i - 1"] by simp
      also have "?mu2_f2 (i - 1) = - (?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1" unfolding gs.\<mu>.simps using i0 by simp
      also have "\<dots> = - ((?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1)" by auto
      also have "?g1 (i - 1) + \<dots> = ?g1 (i - 1) - ((?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1)"
        by (rule sym, rule minus_add_uminus_vec[of _ n], insert gsi g2_im1_Rn, auto)
      also have "?f2 i = ?f1 (i - 1)" by fact
      finally have "?g2 i = ?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / sq_norm (?g2 (i - 1))) \<cdot>\<^sub>v ?g2 (i - 1)" .
    } note g2_i = this

    let ?n1 = "\<lambda> i. sq_norm (?g1 i)" 
    let ?n2 = "\<lambda> i. sq_norm (?g2 i)" 

    (* calculation of new norms *)
    { (* norm of g (i - 1) *)
      have "sq_norm (?g2 (i - 1)) = sq_norm (?g1 i + ?mu_f1)" unfolding g2_im1 by simp
      also have "\<dots> = (?g1 i + ?mu_f1) \<bullet> (?g1 i + ?mu_f1)" 
        by (simp add: sq_norm_vec_as_cscalar_prod)
      also have "\<dots> = (?g1 i + ?mu_f1) \<bullet> ?g1 i + (?g1 i + ?mu_f1) \<bullet> ?mu_f1" 
        by (rule scalar_prod_add_distrib, insert gs i, auto)
      also have "(?g1 i + ?mu_f1) \<bullet> ?g1 i = ?g1 i \<bullet> ?g1 i + ?mu_f1 \<bullet> ?g1 i" 
        by (rule add_scalar_prod_distrib, insert gs i, auto)
      also have "(?g1 i + ?mu_f1) \<bullet> ?mu_f1 = ?g1 i \<bullet> ?mu_f1 + ?mu_f1 \<bullet> ?mu_f1" 
        by (rule add_scalar_prod_distrib, insert gs i, auto)
      also have "?mu_f1 \<bullet> ?g1 i = ?g1 i \<bullet> ?mu_f1"
        by (rule comm_scalar_prod, insert gs i, auto)
      also have "?g1 i \<bullet> ?g1 i = sq_norm (?g1 i)" 
        by (simp add: sq_norm_vec_as_cscalar_prod)
      also have "?g1 i \<bullet> ?mu_f1 = ?mu1 i (i - 1) * (?g1 i \<bullet> ?g1 (i - 1))" 
        by (rule scalar_prod_smult_right, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
      also have "?g1 i \<bullet> ?g1 (i - 1) = 0" 
        using corthogonalD[OF gs.gram_schmidt(2)[OF connH], of i "i - 1"] i len i0 unfolding Gs_fs 
        by (auto simp: o_def)
      also have "?mu_f1 \<bullet> ?mu_f1 = ?mu1 i (i - 1) * (?mu_f1 \<bullet> ?g1 (i - 1))" 
        by (rule scalar_prod_smult_right, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
      also have "?mu_f1 \<bullet> ?g1 (i - 1) = ?mu1 i (i - 1) * (?g1 (i - 1) \<bullet> ?g1 (i - 1))" 
        by (rule scalar_prod_smult_left, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
      also have "?g1 (i - 1) \<bullet> ?g1 (i - 1) = sq_norm (?g1 (i - 1))" 
        by (simp add: sq_norm_vec_as_cscalar_prod)
      finally have "?n2 (i - 1) = ?n1 i + (?mu1 i (i - 1) * ?mu1 i (i - 1)) * ?n1 (i - 1)" 
        by (simp add: ac_simps o_def)
    } note sq_norm_g2_im1 = this

    from norm_pos1[OF i] norm_pos1[OF im1] norm_pos2[OF i] norm_pos2[OF im1]
    have norm0: "?n1 i \<noteq> 0" "?n1 (i - 1) \<noteq> 0" "?n2 i \<noteq> 0" "?n2 (i - 1) \<noteq> 0" by auto
    hence norm0': "\<parallel>G2 ! (i - 1)\<parallel>\<^sup>2 \<noteq> 0" unfolding G2_F2 using i by auto

    { (* new norm of g i *)
      have si: "Suc i \<le> m" and im1: "i - 1 \<le> m" using i by auto
      note det1 = gs.Gramian_determinant[OF connH si]
      note det2 = gs.Gramian_determinant[OF connH' si]
      note det3 = gs.Gramian_determinant[OF connH im1]
      from det3 have 0: "(\<Prod>j < i-1. \<parallel>G ! j\<parallel>\<^sup>2) \<noteq> 0" by linarith
      have "rat_of_int (d F2 (Suc i)) = rat_of_int (d F1 (Suc i))" 
        using d_swap_unchanged[OF len i0 i _ si F2_def] by auto
      also have "rat_of_int (d F2 (Suc i)) = gs.Gramian_determinant (RAT F2) (Suc i)" unfolding d_def 
        by (subst of_int_Gramian_determinant[symmetric], insert connH' i g F2, auto simp: set_conv_nth)
      also have "\<dots> = (\<Prod>j<Suc i. \<parallel>G2 ! j\<parallel>\<^sup>2)" unfolding det2 ..
      also have "rat_of_int (d F1 (Suc i)) = gs.Gramian_determinant (RAT F1) (Suc i)" unfolding d_def 
        by (subst of_int_Gramian_determinant[symmetric], insert connH i g, auto)
      also have "\<dots> = (\<Prod>j<Suc i. \<parallel>G ! j\<parallel>\<^sup>2)" unfolding det1 ..
      also have "{..<Suc i} = insert i (insert (i-1) {..<i-1})" (is "_ = ?set") by auto
      also have "(\<Prod>j\<in> ?set. \<parallel>G2 ! j\<parallel>\<^sup>2) = \<parallel>G2 ! i\<parallel>\<^sup>2 * \<parallel>G2 ! (i - 1)\<parallel>\<^sup>2 * (\<Prod>j < i-1. \<parallel>G2 ! j\<parallel>\<^sup>2)" using i0
        by (subst prod.insert; (subst prod.insert)?; auto)
      also have "(\<Prod>j\<in> ?set. \<parallel>G ! j\<parallel>\<^sup>2) = \<parallel>G ! i\<parallel>\<^sup>2 * \<parallel>G ! (i - 1)\<parallel>\<^sup>2 * (\<Prod>j < i-1. \<parallel>G ! j\<parallel>\<^sup>2)" using i0
        by (subst prod.insert; (subst prod.insert)?; auto)
      also have "(\<Prod>j < i-1. \<parallel>G2 ! j\<parallel>\<^sup>2) = (\<Prod>j < i-1. \<parallel>G ! j\<parallel>\<^sup>2)" 
        by (rule prod.cong, insert G2_G, auto)
      finally have "\<parallel>G2 ! i\<parallel>\<^sup>2 = \<parallel>G ! i\<parallel>\<^sup>2 * \<parallel>G ! (i - 1)\<parallel>\<^sup>2 / \<parallel>G2 ! (i - 1)\<parallel>\<^sup>2" 
        using 0 norm0' by (auto simp: field_simps)
      also have "G2 ! i = ?g2 i" using G2_F2 i by auto
      also have "G2 ! (i - 1) = ?g2 (i - 1)" using G2_F2 i by auto
      also have "G ! i = ?g1 i" using Gs_fs i by auto
      also have "G ! (i-1) = ?g1 (i-1)" using Gs_fs i by auto
      finally have "?n2 i = ?n1 i * ?n1 (i - 1) / ?n2 (i - 1)" .
    } note sq_norm_g2_i = this

    (* mu values in rows > i do not change with j \<notin> {i, i - 1} *)
    {
      fix ii j
      assume ii: "ii > i" "ii < m" 
       and ji: "j \<noteq> i" "j \<noteq> i - 1" 
      {
        assume j: "j < ii" 
        have "?mu2 ii j = (?f2 ii \<bullet> ?g2 j) / sq_norm (?g2 j)" 
          unfolding gs.\<mu>.simps using j by auto
        also have "?f2 ii = ?f1 ii" using ii len unfolding F2_def by auto
        also have "?g2 j = ?g1 j" using g2_g1_identical[of j] j ii ji by auto
        finally have "?mu2 ii j = ?mu1 ii j" 
          unfolding gs.\<mu>.simps using j by auto
      }
      hence "?mu2 ii j = ?mu1 ii j" by (cases "j < ii", auto simp: gs.\<mu>.simps)
    } note mu_no_change_large_row = this

    { (* the new value of mu i (i - 1) *)
      have "?mu2 i (i - 1) = (?f2 i \<bullet> ?g2 (i - 1)) / sq_norm (?g2 (i - 1))" 
        unfolding gs.\<mu>.simps using i0 by auto
      also have "?f2 i \<bullet> ?g2 (i - 1) = ?f1 (i - 1) \<bullet> ?g2 (i - 1)" 
        using len i i0 unfolding F2_def by auto
      also have "\<dots> = ?f1 (i - 1) \<bullet> (?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
        unfolding g2_im1 by simp
      also have "\<dots> = ?f1 (i - 1) \<bullet> ?g1 i + ?f1 (i - 1) \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
        by (rule scalar_prod_add_distrib[of _ n], insert i gs g, auto)
      also have "?f1 (i - 1) \<bullet> ?g1 i = 0" 
        by (subst gs.fi_scalar_prod_gso[OF connH im1 i], insert i0, auto simp: gs.\<mu>.simps)
      also have "?f1 (i - 1) \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)) = 
         ?mu1 i (i - 1) * (?f1 (i - 1) \<bullet> ?g1 (i - 1))"  
        by (rule scalar_prod_smult_distrib, insert gs g i, auto)
      also have "?f1 (i - 1) \<bullet> ?g1 (i - 1) = sq_norm (?g1 (i - 1))" 
        by (subst gs.fi_scalar_prod_gso[OF connH im1 im1], auto simp: gs.\<mu>.simps)
      finally 
      have "?mu2 i (i - 1) = ?mu1 i (i - 1) * ?n1 (i - 1) / ?n2 (i - 1)" 
        by (simp add: sq_norm_vec_as_cscalar_prod)
    } note mu'_mu_i_im1 = this

    { (* the new values of mu ii (i - 1) for ii > i *)
      fix ii assume iii: "ii > i" and ii: "ii < m" 
      hence iii1: "i - 1 < ii" by auto
      have "?mu2 ii (i - 1) = (?f2 ii \<bullet> ?g2 (i - 1)) / ?n2 (i - 1)" 
        unfolding gs.\<mu>.simps using i0 iii1 by auto
      also have "?f2 ii \<bullet> ?g2 (i-1) = ?f1 ii \<bullet> ?g2 (i - 1)" 
        using len i i0 iii ii unfolding F2_def by auto
      also have "\<dots> = ?f1 ii \<bullet> (?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
        unfolding g2_im1 by simp
      also have "\<dots> = ?f1 ii \<bullet> ?g1 i + ?f1 ii \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
        by (rule scalar_prod_add_distrib[of _ n], insert i ii gs g, auto)
      also have "?f1 ii \<bullet> ?g1 i = ?mu1 ii i * ?n1 i" 
        by (rule gs.fi_scalar_prod_gso[OF connH ii i])
      also have "?f1 ii \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)) = 
         ?mu1 i (i - 1) * (?f1 ii \<bullet> ?g1 (i - 1))"  
        by (rule scalar_prod_smult_distrib, insert gs g i ii, auto)
      also have "?f1 ii \<bullet> ?g1 (i - 1) = ?mu1 ii (i - 1) * ?n1 (i - 1)" 
        by (rule gs.fi_scalar_prod_gso[OF connH ii im1])
      finally have "?mu2 ii (i - 1) = ?mu1 ii (i - 1) * ?mu2 i (i - 1) + ?mu1 ii i * ?n1 i / ?n2 (i - 1)" 
        unfolding mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
    } note mu'_mu_large_row_im1 = this    

    { (* the new values of mu ii i for ii > i *)
      fix ii assume iii: "ii > i" and ii: "ii < m" 
      have "?mu2 ii i = (?f2 ii \<bullet> ?g2 i) / ?n2 i" 
        unfolding gs.\<mu>.simps using i0 iii by auto
      also have "?f2 ii \<bullet> ?g2 i = ?f1 ii \<bullet> ?g2 i" 
        using len i i0 iii ii unfolding F2_def by auto
      also have "\<dots> = ?f1 ii \<bullet> (?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / ?n2 (i - 1)) \<cdot>\<^sub>v ?g2 (i - 1))" 
        unfolding g2_i by simp
      also have "?f1 (i - 1) = ?f2 i" using i i0 len unfolding F2_def by auto
      also have "?f2 i \<bullet> ?g2 (i - 1) / ?n2 (i - 1) = ?mu2 i (i - 1)" 
        unfolding gs.\<mu>.simps using i i0 by auto
      also have "?f1 ii \<bullet> (?g1 (i - 1) - ?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1))
         = ?f1 ii \<bullet> ?g1 (i - 1) - ?f1 ii \<bullet> (?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1))" 
        by (rule scalar_prod_minus_distrib[OF g gs], insert gs2 ii i, auto)
      also have "?f1 ii \<bullet> ?g1 (i - 1) = ?mu1 ii (i - 1) * ?n1 (i - 1)" 
        by (rule gs.fi_scalar_prod_gso[OF connH ii im1])
      also have "?f1 ii \<bullet> (?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1)) = 
         ?mu2 i (i - 1) * (?f1 ii \<bullet> ?g2 (i - 1))" 
        by (rule scalar_prod_smult_distrib, insert gs gs2 g i ii, auto)
      also have "?f1 ii \<bullet> ?g2 (i - 1) = (?f1 ii \<bullet> ?g2 (i - 1) / ?n2 (i - 1)) * ?n2 (i - 1)" 
        using norm0 by (auto simp: field_simps)
      also have "?f1 ii \<bullet> ?g2 (i - 1) = ?f2 ii \<bullet> ?g2 (i - 1)" 
        using len ii iii unfolding F2_def by auto
      also have "\<dots> / ?n2 (i - 1) = ?mu2 ii (i - 1)" unfolding gs.\<mu>.simps using iii by auto
      finally 
      have "?mu2 ii i = 
         (?mu1 ii (i - 1) * ?n1 (i - 1) - ?mu2 i (i - 1) * ?mu2 ii (i - 1) * ?n2 (i - 1)) / ?n2 i" by simp
      also have "\<dots> = (?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu2 ii (i - 1)) * ?n2 (i - 1) / ?n1 i" 
        unfolding sq_norm_g2_i mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
      also have "\<dots> = (?mu1 ii (i - 1) * ?n2 (i - 1) - 
        ?mu1 i (i - 1) * ((?mu1 ii i * ?n1 i + ?mu1 i (i - 1) * ?mu1 ii (i - 1) * ?n1 (i - 1)))) / ?n1 i" 
        unfolding mu'_mu_large_row_im1[OF iii ii] mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
      also have "\<dots> = ?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu1 ii i" 
        unfolding sq_norm_g2_im1 using norm0 by (auto simp: field_simps)
      finally have "?mu2 ii i = ?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu1 ii i" .
    } note mu'_mu_large_row_i = this

    note new_mu_lemmas = 
        mu'_mu_large_row_i
        mu'_mu_large_row_im1 
        mu_no_change_large_row
        mu'_mu_i_im1
        mu'_mu_small_i
        mu'_mu_i_im1_j
    note new_norm_and_g_lemmas = 
      sq_norm_g2_i
      sq_norm_g2_im1
      g2_g1_identical
    text \<open>With @{thm new_mu_lemmas} one has the full information to calculate the new mu-values without
          using the definition of mu.
        So, these theorems permit to change the implementation where the $g$'s are no longer required,
        but where one only stores the norms of the $g$'s and the $\mu$-values.\<close>

    (* stay reduced *)
    from inv' have sred: "gs.reduced \<alpha> i G (gs.\<mu> (RAT F1))" by auto
    have sred: "gs.reduced \<alpha> (i - 1) G2 (gs.\<mu> (RAT F2))"
      unfolding gs.reduced_def
    proof (intro conjI[OF red] allI impI, goal_cases)
      case (1 i' j)
      with sred have "\<bar>?mu1 i' j\<bar> \<le> 1 / 2" unfolding gs.reduced_def by auto
      thus ?case using mu'_mu_small_i[OF 1(1)] by simp
    qed

    (* implementation is correct *)
    {
      from i1n have i1n': "i - 1 \<le> m" by simp
      have upd_im1: "list_repr i ba xs \<Longrightarrow> ys = (xs [i - 1 := x]) \<Longrightarrow> list_repr i (update_im1 ba x) ys" 
        for ba xs x ys using update_im1[of i ba xs] i0 by force
      from gso[unfolded g_repr_def] 
      have gsoH: "list_repr i Gr1 (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m]))" by auto
      let ?f_im1 = "get_nth_im1 Fr1"
      let ?g2'_im1 = "g_i Gr1 + ?mu \<cdot>\<^sub>v g_im1 Gr1" 
      let ?norm_im1 = "sq_norm (?g2 (i - 1))" 
      define n2_im1 where "n2_im1 = sqnorm_g_i Gr1 + square_rat ?mu * sqnorm_g_im1 Gr1"
      define n2_i where "n2_i = sqnorm_g_i Gr1 * sqnorm_g_im1 Gr1 / n2_im1"
      let ?g2'_i = "g_im1 Gr1 - (?f_im1 \<bullet>i ?g2'_im1 / n2_im1) \<cdot>\<^sub>v ?g2'_im1" 
      define g2'_i where "g2'_i = ?g2'_i" 
      define g2'_im1 where "g2'_im1 = ?g2'_im1"
      have "?g2 (i - 1) = ?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)" by fact
      also have "?g1 i = g_i Gr1" unfolding g_i[OF Linv' i] Gs_fs o_def using i by simp
      also have "?g1 (i - 1) = g_im1 Gr1" unfolding g_im1[OF Linv' i i0] Gs_fs o_def using i by simp
      finally have g2im1: "?g2 (i - 1) = g2'_im1"
        unfolding mu g2'_im1_def by blast
      note sqnorms = sqnorm_g_i_GSO[OF gso i] sqnorm_g_im1_GSO[OF gso i0] GSO_def
      have "?norm_im1 = sq_norm (?g1 i) + square_rat ?mu * sq_norm (?g1 (i - 1))" 
        unfolding g2'_im1_def[symmetric] g2im1[symmetric] sq_norm_g2_im1 by (simp add: mu)
      also have "\<dots> = n2_im1" unfolding n2_im1_def sqnorms ..
      finally have n2_im1: "?norm_im1 = n2_im1" .
      have n2_i: "n2_i = sq_norm (?g2 i)" 
        unfolding n2_i_def n2_im1[symmetric] sqnorms sq_norm_g2_i by simp
      have "?f_im1 \<in> carrier_vec n" using inv'(3-4) \<open>i - 1 < m\<close> unfolding get_nth_im1[OF inv'(8) i0] 
        by auto
      hence dim: "dim_vec ?f_im1 = n" "dim_vec ?g2'_im1 = n" unfolding g2'_im1_def[symmetric] g2im1[symmetric]
        using \<open>?g2_im1 \<in> Rn\<close> by auto
      have "?g2 i = ?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / sq_norm (?g2 (i - 1))) \<cdot>\<^sub>v ?g2 (i - 1)"
        by (rule g2_i)
      also have "sq_norm (?g2 (i - 1)) = n2_im1" unfolding n2_im1 ..
      also have "?g2 (i - 1) = g2'_im1" by (simp add: g2im1[symmetric])
      also have "?g1 (i - 1) = g_im1 Gr1" by fact
      also have "?f1 (i - 1) = map_vec of_int ?f_im1" 
        unfolding get_nth_im1[OF repr i0] o_def using len i by simp
      finally have g2i: "?g2 i = g2'_i" using dim unfolding g2'_i_def g2'_im1_def by simp
      have "map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m])
        [i := (g2'_i, n2_i), i - 1 := (g2'_im1, n2_im1)]
        = map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) ((map (GSO F1) [0..<m])[i := g2'_i, i - 1 := g2'_im1])" 
        unfolding map_update n2_i n2_im1[symmetric] g2im1 g2i by auto
      also have GSOH: "map (GSO F1) [0..<m] = map ?g1 [0..<m]" 
        by (rule map_cong[OF refl], auto simp: GSO_def len intro!: gs_gs_identical)
      also have id: "\<dots> [i := g2'_i, i - 1 := g2'_im1] = map ?g2 [0..<m]" (is "?Gs = ?Gs2") 
      proof -
        {
          fix k
          assume k: "k < m" 
          consider (ki) "k = i" | (im1) "k = i - 1" | (other) "k \<notin> {i-1, i}" by auto
          hence "?Gs ! k = ?g2 k" 
          proof (cases)
            case other
            hence "?Gs ! k = ?g1 k" using k by simp
            also have "\<dots> = ?g2 k" using g2_g1_identical[OF k] other by auto
            finally show ?thesis .
          next
            case ki
            have "?g2 i = g2'_i" unfolding g2i ..
            also have "\<dots> = ?Gs ! k" using i len i0 ki by simp
            finally show ?thesis unfolding ki by simp
          next
            case im1
            hence "?Gs ! k = g2'_im1" using i len by simp
            also have "\<dots> = ?g2 (i - 1)" unfolding g2im1 ..
            finally show ?thesis unfolding im1 by simp
          qed
          also have "?g2 k = ?Gs2 ! k" using k by simp
          finally have "?Gs ! k = ?Gs2 ! k" by simp
        } note main = this
        show ?thesis
          by (rule nth_equalityI, force, insert main, auto)
      qed
      also have "\<dots> = map (GSO F2) [0..<m]" 
        by (rule map_cong[OF refl], auto simp: GSO_def len' intro!: gs_gs_identical)
      finally 
      have "map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F2) [0..<m]) 
       = map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m])[i := (g2'_i, n2_i), i - 1 := (g2'_im1, n2_im1)]"
        unfolding GSOH o_def by auto
      hence "g_repr (i - 1) Gr2 F2" unfolding gso' Let_def g_repr_def 
        unfolding n2_im1_def[symmetric]
        unfolding n2_i_def[symmetric]
        unfolding g2'_i_def[symmetric]
        unfolding g2'_im1_def[symmetric] 
        apply (intro conjI i1n')
        apply(rule dec_i[OF _ i0]) by(auto simp: i intro!:upd_im1 update_i[OF gsoH])
    } note g_repr = this

    { (* 16.13 (ii) : norm of g (i - 1) decreases by reduction factor *)
      note sq_norm_g2_im1
      also have "sq_norm (?g1 i) + (?mu1 i (i - 1) * ?mu1 i (i - 1)) * sq_norm (?g1 (i - 1)) 
        < 1/\<alpha> * (sq_norm (?g1 (i - 1))) + (1/2 * 1/2) * (sq_norm (?g1 (i - 1)))"
      proof (rule add_less_le_mono[OF _ mult_mono])
        from True[unfolded mult.commute[of \<alpha>] Gs_fs,
            THEN linordered_field_class.mult_imp_less_div_pos[OF \<alpha>0(1)]]
        show "sq_norm (?g1 i) < 1/\<alpha> * (sq_norm (?g1 (i - 1)))" 
          unfolding Gs_fs o_def using len i by auto
        from m12 have abs: "abs (?mu1 i (i - 1)) \<le> 1/2" unfolding mu by auto
        have "?mu1 i (i - 1) * ?mu1 i (i - 1) \<le> abs (?mu1 i (i - 1)) * abs (?mu1 i (i - 1))" by auto
        also have "\<dots> \<le> 1/2 * 1/2" using mult_mono[OF abs abs] by auto
        finally show "?mu1 i (i - 1) * ?mu1 i (i - 1) \<le> 1/2 * 1/2" by auto
      qed auto
      also have "\<dots> = reduction * sq_norm (?g1 (i - 1))" unfolding reduction_def  
        using \<alpha>0 by (simp add: ring_distribs add_divide_distrib)
      finally have "sq_norm (?g2 (i - 1)) < reduction * sq_norm (?g1 (i - 1))" .
    } note g_reduction = this (* Lemma 16.13 (ii) *)

    { (* bound for norm of g(i) *)
      define u where "u = gs.sumlist (map (\<lambda>j. gs.\<mu> (RAT F1) (i - 1) j \<cdot>\<^sub>v ?g1 j) [0..<i - 1])" 
      define U where "U = ?f1 ` {0 ..< i - 1} \<union> {?f1 i}" 
      have g2i: "?g2 i \<in> Rn" using i connH' by simp
      have U: "U \<subseteq> Rn" unfolding U_def using g i by auto
      have uU: "u \<in> gs.span U"
      proof -
        have im1: "i - 1 \<le> m" using i by auto
        have "u \<in> gs.span (?g1 ` {0 ..< i - 1})" unfolding u_def 
          by (rule gs.sumlist_in_span[OF G'], insert gs.span_mem G', auto) 
        also have "gs.span (?g1 ` {0 ..< i - 1}) = gs.span (?f1 ` {0 ..< i - 1})" 
          unfolding gs.partial_span[OF connH im1]
          by (rule arg_cong[of _ _ gs.span], subst nth_image[symmetric], insert i len, auto)
        also have "\<dots> \<subseteq> gs.span U" unfolding U_def 
          by (rule gs.span_is_monotone, auto)
        finally show ?thesis .
      qed
      have u: "u \<in> Rn" using uU U by simp
      have id_u: "u + (?g1 (i - 1) - ?g2 i) = u + ?g1 (i - 1) - ?g2 i" 
        using u g2i \<open>?g1 (i - 1) \<in> Rn\<close> by auto
      from gs.gso_oc_projection_span(2)[OF connH' i]
      have "gs.is_oc_projection (?g2 i) (gs.span (gs.gso (RAT F2) ` {0 ..< i}))  (?f1 (i - 1))" 
        unfolding F2_def using len i i0 by simp
      also have "?f1 (i - 1) = u + ?g1 (i - 1) " 
        unfolding gs.fi_is_sum_of_mu_gso[OF connH \<open>i - 1 < m\<close>] list_id map_append u_def using gs' gsi
        by (subst gs.M.sumlist_snoc, auto simp: gs.\<mu>.simps)
      also have "gs.span (gs.gso (RAT F2) ` {0 ..< i}) = gs.span (set (take i (RAT F2)))" 
        unfolding gs.partial_span[OF connH' \<open>i \<le> m\<close>] ..
      also have "set (take i (RAT F2)) = ?f2 ` {0 ..< i}" using len' i 
        by (subst nth_image[symmetric], auto)
      also have "{0 ..< i} = {0 ..< i - 1} \<union> {(i - 1)}" using i0 by auto
      also have "?f2 ` \<dots> = ?f2 ` {0 ..< i - 1} \<union> {?f2 (i - 1)}" by auto
      also have "\<dots> = U" unfolding U_def F2_def 
        by (rule arg_cong2[of _ _ _ _ "(\<union>)"], insert i len, force+)
      finally have "gs.is_oc_projection (?g2 i) (gs.span U) (u + ?g1 (i - 1))" .        
      hence proj: "gs.is_oc_projection (?g2 i) (gs.span U) (?g1 (i - 1))"
        unfolding gs.is_oc_projection_def using gs.span_add[OF U uU, of "?g1 (i - 1) - ?g2 i"] 
        \<open>?g1 (i - 1) \<in> Rn\<close> g2i u id_u by (auto simp: U)
      from gs.is_oc_projection_sq_norm[OF this gs.span_is_subset2[OF U] \<open>?g1 (i - 1) \<in> Rn\<close>]
      have "sq_norm (?g2 i) \<le> sq_norm (?g1 (i - 1))" .
    } note sq_norm_g2_i = this (* Lemma 16.13 (iii) *)

    (* numbers stay small *)
    from inv' have short: "\<And> k. k < m \<Longrightarrow> \<parallel>G ! k\<parallel>\<^sup>2 \<le> of_nat A" by (auto simp: g_bound_def)
    from short[of "i - 1"] i 
    have short_im1: "sq_norm (?g1 (i - 1)) \<le> of_nat A" unfolding Gs_fs by auto
    have g_bound: "g_bound G2" unfolding g_bound_def
    proof (intro allI impI)
      fix k 
      assume km: "k < m" 
      consider (ki) "k = i" | (im1) "k = i - 1" | (other) "k \<noteq> i" "k \<noteq> i-1" by blast
      thus "\<parallel>G2 ! k\<parallel>\<^sup>2 \<le> of_nat A"
      proof cases
        case other
        from short[OF km] have "\<parallel>G ! k\<parallel>\<^sup>2 \<le> of_nat A" by auto
        also have "G ! k = G2 ! k" using km g2_g1_identical[OF km other] unfolding G2_F2 Gs_fs by auto
        finally show ?thesis by simp
      next
        case im1
        have "\<parallel>G2 ! k\<parallel>\<^sup>2 = sq_norm (?g2 (i - 1))" unfolding im1 G2_F2 using i by auto
        also have "\<dots> < reduction * sq_norm (?g1 (i - 1))" by fact
        also have "\<dots> \<le> 1 * sq_norm (?g1 (i - 1))" 
          by (rule mult_right_mono, auto simp: reduction)
        also have "\<dots> \<le> of_nat A" using short_im1 by auto
        finally show ?thesis by simp
      next
        case ki
        have "\<parallel>G2 ! k\<parallel>\<^sup>2 = sq_norm (?g2 i)" unfolding ki G2_F2 using i by auto
        also have "\<dots> \<le> sq_norm (?g1 (i - 1))" by fact
        also have "\<dots> \<le> of_nat A" by fact
        finally show ?thesis .
      qed
    qed
    {
      fix j
      assume j: "j < m" 
      note short = f_bound[unfolded f_bound_def, rule_format]
      consider "j \<noteq> i" "j \<noteq> i - 1" | "j = i" | "j = i - 1" by auto
      hence "\<parallel>F2 ! j\<parallel>\<^sup>2 \<le> int (A * m)" using short[OF j] short[OF i] short[OF \<open>i - 1 < m\<close>] len j i i0
        unfolding F2_def by (cases, auto)
    }
    hence f_bound: "f_bound True (i - 1) F2" unfolding f_bound_def by auto

    have mu_small: "mu_small F2 (i - 1)" 
      unfolding mu_small_def
    proof (intro allI impI, goal_cases)
      case (1 j)
      show ?case  using inv'(14) 1 unfolding mu'_mu_i_im1_j[OF 1] mu_small_def by auto
    qed      
        
    (* invariant is established *)
    have newInv: "LLL_invariant True (False, i - 1, Fr2, Gr2) F2 G2" 
      by (rule LLL_invI[OF repr' g_repr gH' L red], insert mu_small g_bound f_bound connH' len' span' i m12 F2 sred, auto)

    (* show decrease in measure *)
    { (* 16.16 (ii), the decreasing case *)
      fix k
      assume k: "k = i" 
      hence kn: "k \<le> m" using i by auto
      from Gd[OF newInv, folded d_def, folded state, OF kn] k
      have "?R (d F2 k) = (\<Prod>j<i. sq_norm (G2 ! j) )" by auto
      also have "\<dots> = prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1} \<union> {i - 1})" 
        by (rule sym, rule prod.cong, (insert i0, auto)[1], insert G2_F2 i, auto simp: o_def)
      also have "\<dots> = sq_norm (?g2 (i - 1)) * prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1})" 
        by simp
      also have "\<dots> < (reduction * sq_norm (?g1 (i - 1))) * prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1})"
        by (rule mult_strict_right_mono[OF g_reduction prod_pos], insert norm_pos2 i, auto)
      also have "prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1}) = prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1})" 
        by (rule prod.cong[OF refl], subst g2_g1_identical, insert i, auto)
      also have "(reduction * sq_norm (?g1 (i - 1))) * prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1})
        = reduction * prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1} \<union> {i - 1})" by simp
      also have "prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1} \<union> {i - 1}) = (\<Prod>j<i. sq_norm (?g1 j))"
        by (rule prod.cong, insert i0, auto)
      also have "\<dots> = ?R (d F1 k)" unfolding d_def Gd[OF Linv' kn] unfolding k
        by (rule prod.cong[OF refl], insert i, auto simp: Gs_fs o_def)
      also have "\<dots> = ?R (d F k)" unfolding d_eq[OF kn] by simp
      finally have "d F2 k < real_of_rat reduction * d F k"
        using of_rat_less of_rat_mult of_rat_of_int_eq by metis
    } note d_i = this[OF refl]
    have pos: "k < m \<Longrightarrow> 0 < d F2 k" "k < m \<Longrightarrow> 0 \<le> d F2 k" for k 
      using LLL_d_pos[OF newInv, folded state, of k] by auto
    have prodpos:"0< (\<Prod>i<m. d F2 i)" apply (rule prod_pos)
      using LLL_d_pos[OF newInv, folded state] by auto
    have prod_pos':"0 < (\<Prod>x\<in>{0..<m} - {i}. real_of_int (d F2 x))" apply (rule prod_pos)
      using LLL_d_pos[OF newInv, folded state] pos by auto
    have prod_nonneg:"0 \<le> (\<Prod>x\<in>{0..<m} - {i}. real_of_int (d F2 x))" apply (rule prod_nonneg)
      using LLL_d_pos[OF newInv, folded state] pos by auto
    have prodpos2:"0<(\<Prod>ia<m. d F ia)" apply (rule prod_pos)
      using LLL_d_pos[OF assms(1)] by auto
    have "D F2 = real_of_int (\<Prod>i<m. d F2 i)" unfolding D_def using prodpos by simp
    also have "(\<Prod>i<m. d F2 i) = (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d F2 j)"
      by (rule prod.cong, insert i, auto)
    also have "real_of_int \<dots> = real_of_int (\<Prod> j \<in> {0 ..< m} - {i}. d F2 j) * real_of_int (d F2 i)" 
      by (subst prod.union_disjoint, auto)
    also have "\<dots> < (\<Prod> j \<in> {0 ..< m} - {i}. d F2 j) * (of_rat reduction * d F i)"
      by(rule mult_strict_left_mono[OF d_i],insert prod_pos',auto)
    also have "(\<Prod> j \<in> {0 ..< m} - {i}. d F2 j) = (\<Prod> j \<in> {0 ..< m} - {i}. d F j)"
      by (rule prod.cong, insert d, auto)
    also have "\<dots> * (of_rat reduction * d F i) 
      = of_rat reduction * (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d F j)" 
      by (subst prod.union_disjoint, auto)
    also have "(\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d F j) = (\<Prod> j<m. d F j)" 
      by (subst prod.cong, insert i, auto)
    finally have D: "D F2 < real_of_rat reduction * D F"
      unfolding D_def using prodpos2 by auto
    have logD: "logD F2 < logD F" 
    proof (cases "\<alpha> = 4/3")
      case True
      show ?thesis using D unfolding reduction(4)[OF True] logD_def unfolding True by simp
    next
      case False
      hence False': "\<alpha> = 4/3 \<longleftrightarrow> False" by simp
      from False \<alpha> have "\<alpha> > 4/3" by simp
      with reduction have reduction1: "reduction < 1" by simp
      let ?new = "real (D F2)" 
      let ?old = "real (D F)" 
      let ?log = "log (1/of_rat reduction)" 
      note pos = LLL_D_pos[OF newInv[folded state]] LLL_D_pos[OF assms(1)]
      from reduction have "real_of_rat reduction > 0" by auto
      hence gediv:"1/real_of_rat reduction > 0" by auto
      have "(1/of_rat reduction) * ?new \<le> ((1/of_rat reduction) * of_rat reduction) * ?old"
        unfolding mult.assoc real_mult_le_cancel_iff2[OF gediv] using D by simp
      also have "(1/of_rat reduction) * of_rat reduction = 1" using reduction by auto
      finally have "(1/of_rat reduction) * ?new \<le> ?old" by auto
      hence "?log ((1/of_rat reduction) * ?new) \<le> ?log ?old"
        by (subst log_le_cancel_iff, auto simp: pos reduction1 reduction)
      hence "floor (?log ((1/of_rat reduction) * ?new)) \<le> floor (?log ?old)" 
        by (rule floor_mono)
      hence "nat (floor (?log ((1/of_rat reduction) * ?new))) \<le> nat (floor (?log ?old))" by simp
      also have "\<dots> = logD F" unfolding logD_def False' by simp
      also have "?log ((1/of_rat reduction) * ?new) = 1 + ?log ?new" 
        by (subst log_mult, insert reduction reduction1, auto simp: pos )
      also have "floor (1 + ?log ?new) = 1 + floor (?log ?new)" by simp
      also have "nat (1 + floor (?log ?new)) = 1 + nat (floor (?log ?new))" 
        by (subst nat_add_distrib, insert pos reduction reduction1, auto)
      also have "nat (floor (?log ?new)) = logD F2" unfolding logD_def False' by simp
      finally show "logD F2 < logD F" by simp
    qed
    hence "LLL_measure state < LLL_measure (upw, i, Fr, Gr)" unfolding LLL_measure_def state split
      inv(1)[symmetric] of_list_repr[OF repr']
      using i logD by simp
    thus ?thesis using newInv unfolding state by auto
  qed
next
  case i0: True
  with Linv have Linv: "LLL_invariant True (False, i, Fr, Gr) F G" 
    unfolding LLL_invariant_def mu_small_def split by auto
  from res i0 have state: "state = (True, increase_i (i, Fr, Gr))" unfolding basis_reduction_step_def by auto
  with increase_i[OF Linv i] i0 
  have inv': "LLL_invariant True state F G" by auto
  from LLL_invD[OF Linv] have Gr: "of_list_repr Fr = F" by simp
  from LLL_invD[OF inv'[unfolded increase_i_def state split]] 
  have Gr': "of_list_repr (inc_i Fr) = F" by simp
  have id: "of_list_repr (inc_i Fr) = of_list_repr Fr" by (simp add: Gr Gr')
  have dec: "LLL_measure state < LLL_measure (upw, i, Fr, Gr)" using i unfolding state i0 
    unfolding LLL_measure_def by (simp add: increase_i_def id)
  show "(\<exists>H. Ex (LLL_invariant True state H)) \<and> LLL_measure state < LLL_measure (upw, i, Fr, Gr)" 
    by (intro conjI exI dec, rule inv')
qed

lemma basis_reduction_main: fixes F G assumes "LLL_invariant True state F G"
  and "basis_reduction_main \<alpha> m state = state'" 
shows "\<exists> F' G'. LLL_invariant True state' F' G' \<and> (fst o snd) state' = m" 
proof (cases "m = 0")
  case True
  from assms(2)[unfolded True basis_reduction_main.simps[of _ 0 state]] 
  have state': "state' = state" by auto
  obtain upw i Fr Gr where state: "state = (upw,i,Fr,Gr)" by (cases state, auto)
  from LLL_invD[OF assms(1)[unfolded state]] True have i: "i = 0" by auto
  show ?thesis using assms(1) unfolding state' state i True by auto
next
  case ne: False  
  note [simp] = basis_reduction_main.simps
  show ?thesis using assms(1-2) 
  proof (induct state arbitrary: F G rule: wf_induct[OF wf_measure[of LLL_measure]])
    case (1 state F G)
    note inv = 1(2)
    note IH = 1(1)[rule_format]
    note res = 1(3)
    obtain upw i Fr1 Gr1 where state: "state = (upw,i,Fr1,Gr1)" by (cases state, auto)
    note inv = inv[unfolded state]
    note res = res[unfolded state]
    show ?case
    proof (cases "i < m")
      case True
      with inv have i: "i < m" unfolding LLL_invariant_def by auto
      obtain state'' where b: "basis_reduction_step \<alpha> (upw, i, Fr1, Gr1) = state''" by auto
      from res True b
      have res: "basis_reduction_main \<alpha> m  state'' = state'" by simp
      note bsr = basis_reduction_step[OF inv i b]
      from bsr(1) obtain F' G' where inv: "LLL_invariant True state'' F' G'" by auto
      from bsr(2) have "(state'' ,state) \<in> measure LLL_measure" by (auto simp: state)
      from IH[OF this inv] b res state show ?thesis by auto
    next
      case False
      define G1 where Gr: "G1 = of_list_repr Fr1" 
      note inv = inv[unfolded LLL_invariant_def split Gr[symmetric] Let_def]
      from False res have state': "state' = (upw,i, Fr1, Gr1)" by simp
      from False inv have i: "i = m" unfolding LLL_invariant_def by auto
      show ?thesis using 1(2) unfolding state' state i by auto
    qed
  qed
qed

lemma initial_state: assumes "initial_state n fs_init = state" 
shows "\<exists> F' G'. LLL_invariant True state F' G'" 
proof -
  let ?F = "RAT fs_init"
  define Fr0::f_repr where "Fr0 = ([], fs_init)"
  have FrF: "RAT (snd Fr0) = ?F" unfolding Fr0_def by auto
  from lin_dep 
  have F: "set fs_init \<subseteq> carrier_vec n" 
    unfolding gs.lin_indpt_list_def by auto
  have repr: "f_repr 0 Fr0 fs_init" unfolding list_repr_def Fr0_def by auto
  obtain G where gs: "snd (gram_schmidt_int n fs_init) = G" (is "snd ?gs = G") by force
  from gram_schmidt.mn[OF lin_dep _ gs[unfolded gram_schmidt_int_def gram_schmidt_wit_def]] len
  have mn: "m \<le> n" by auto
  have G':"length (RAT fs_init) = m" "m \<le> m" "m \<le> n" 
    "set ?F \<subseteq> carrier_vec n" using F len mn by auto 
  define Gr0 where "Gr0 = gram_schmidt_triv n (RAT fs_init)"
  let ?Gr0 = "([], Gr0)" 
  have RAT_carr:"set (RAT fs_init) \<subseteq> Rn" using F len by auto
  have take: "RAT fs_init = take m (RAT fs_init)" using len by auto
  from gram_schmidt.partial_connect[OF G' 
      gs[unfolded gram_schmidt_int_def gram_schmidt_wit_def] take RAT_carr]
  have gso_init:"Gr0 = map (\<lambda> x. (x, sq_norm x)) (map (GSO fs_init) [0..<m])"
    and GG: "G = map (gs.gso (RAT fs_init)) [0..<m]" 
    unfolding Gr0_def FrF GSO_def gram_schmidt_triv using len by auto
  from gram_schmidt_int_connect[OF lin_dep gs len]
  have gso0: "g_repr 0 ?Gr0 fs_init" unfolding gso_init g_repr_def list_repr_def gs by auto
  {
    fix i
    assume i: "i < m" 
    let ?N = "map (nat o sq_norm) fs_init"
    let ?r = rat_of_int
    from i have mem: "nat (sq_norm (fs_init ! i)) \<in> set ?N" using G'(1) unfolding set_conv_nth by force
    from mem_set_imp_le_max_list[OF _ mem]
    have FA: "nat (sq_norm (fs_init ! i)) \<le> A" unfolding A_def by force
    hence "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int A" using i by auto
    also have "\<dots> \<le> int (A * m)" using i by fastforce
    finally have f_bnd:  "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int (A * m)" .
    from FA have "rat_of_nat (nat (sq_norm (fs_init ! i))) \<le> rat_of_nat A" by simp
    also have "rat_of_nat (nat (sq_norm (fs_init ! i))) = ?r (sq_norm (fs_init ! i))" 
      using sq_norm_vec_ge_0[of "fs_init ! i"] by auto
    also have "\<dots> = sq_norm (RAT fs_init ! i)" unfolding sq_norm_of_int[symmetric] using G' i by auto
    finally have "sq_norm (RAT fs_init ! i) \<le> rat_of_nat A" .
    with gs.sq_norm_gso_le_f[OF lin_dep G'(1) refl i]
    have "\<parallel>gs.gso (RAT fs_init) i\<parallel>\<^sup>2 \<le> rat_of_nat A" by simp
    also have "gs.gso (RAT fs_init) i = G ! i" unfolding GG using i by auto
    finally have g_bnd: "\<parallel>G ! i\<parallel>\<^sup>2 \<le> rat_of_nat A" .
    note f_bnd g_bnd
  }
  hence bounds: "g_bound G \<and> f_bound True 0 fs_init" unfolding g_bound_def f_bound_def by auto
  have "LLL_invariant True (False, 0, Fr0, ?Gr0) fs_init G"
    by (rule LLL_invI[OF repr gso0 gs L_def[symmetric] _ _ len lin_dep], auto simp:gs.weakly_reduced_def 
        gs.reduced_def len bounds mu_small_def)
  also have "(False, 0, Fr0, ?Gr0) = state" unfolding assms(1)[symmetric] initial_state_def Let_def
    Fr0_def Gr0_def ..
  finally show ?thesis by blast
qed

lemma basis_reduction_state: assumes "basis_reduction_state n \<alpha> fs_init = state" 
  shows "\<exists>F' G'. LLL_invariant True state F' G' \<and> (fst o snd) state = m" 
proof -
  let ?state = "initial_state n fs_init" 
  from initial_state[OF refl]
  obtain F' G' where inv: "LLL_invariant True ?state F' G'" by auto
  from assms(1)[unfolded basis_reduction_state_def len]
  have res: "basis_reduction_main \<alpha> m ?state = state" .
  from basis_reduction_main[OF inv res] show ?thesis by blast
qed

lemma reduce_basis: assumes res: "reduce_basis n \<alpha> fs_init = (F', G')" 
  shows "lattice_of F' = L" (is ?g1)
  "gs.reduced \<alpha> m G' (gs.\<mu> (RAT F'))" (is ?g2)
  "G' = gram_schmidt n (RAT F')" (is ?g3)
  "gs.lin_indpt_list (RAT F')" (is ?g4)
  "length F' = m" (is ?g5)
proof -  
  obtain upw i Fr Gr where 1: "basis_reduction_state n \<alpha> fs_init = (upw, i, Fr, Gr)" (is "?main = _") 
    by (cases ?main) auto
  from basis_reduction_state[OF 1] obtain F1 G1
    where Linv: "LLL_invariant True (upw, i, Fr, Gr) F1 G1" 
     and i_n: "i = m" by auto
  from res[unfolded reduce_basis_def 1] have R: "F' = of_list_repr Fr" 
    and Rs: "G' = map fst (of_list_repr Gr)" by auto
  note inv = LLL_invD[OF Linv]
  from inv(1) R have RH: "F' = F1" unfolding of_list_repr_def by auto
  with inv have Hs: "G1 = snd (gram_schmidt_int n F')" by auto
  from inv(9)[unfolded g_repr_def] 
  have "list_repr i Gr (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m]))" by auto
  from Rs[unfolded of_list_repr[OF this]] have Rs: "G' = map (GSO F1) [0..<m]" by (auto simp: o_def)
  also have "\<dots> = G1" unfolding LLL_connect[OF Linv] unfolding GSO_def by simp
  finally have RsHs: "G' = G1" by auto
  from RsHs inv(4,5,6,10,11) Rs R Hs RH i_n show ?g1 ?g2 ?g3 ?g4 ?g5 by (auto simp: snd_gram_schmidt_int)
qed
  
lemma short_vector: assumes "short_vector \<alpha> fs_init = v" 
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"  
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)" 
  "v \<noteq> 0\<^sub>v j" 
proof -
  let ?L = "lattice_of fs_init" 
  have a1: "\<alpha> \<ge> 1" using \<alpha> by auto 
  obtain F1 G1 where reduce: "reduce_basis n \<alpha> fs_init = (F1, G1)" by force
  from reduce_basis[OF reduce] len have 
    L: "lattice_of F1 = L" 
    and red: "gs.weakly_reduced \<alpha> m G1" 
    and Gs: "G1 = gram_schmidt n (RAT F1)" 
    and basis: "gs.lin_indpt_list (RAT F1)" 
    and lenH: "length F1 = m" 
    and H: "set F1 \<subseteq> carrier_vec n" 
    by (auto simp: gs.lin_indpt_list_def gs.reduced_def)
  from lin_dep have G: "set fs_init \<subseteq> carrier_vec n" unfolding gs.lin_indpt_list_def by auto
  with m0 len have "dim_vec (hd fs_init) = n" by (cases fs_init, auto)
  note res = assms[unfolded short_vector_def this reduce]
  from res m0 lenH have v: "v = F1 ! 0" by (cases F1, auto)
  from gs.main_connect[OF basis refl] Gs 
  have gs: "snd (gs.main (RAT F1)) = G1" by auto
  let ?r = "rat_of_int" 
  let ?rv = "map_vec ?r" 
  let ?F = "RAT F1" 
  let ?h = "?rv h" 
  { assume h:"h \<in> L - {0\<^sub>v n}" (is ?h_req)
    from h[folded L] have h: "h \<in> lattice_of F1" "h \<noteq> 0\<^sub>v n" by auto
    {
      assume f: "?h = 0\<^sub>v n" 
      have "?h = ?rv (0\<^sub>v n)" unfolding f by (intro eq_vecI, auto)
      hence "h = 0\<^sub>v n"
        using of_int_hom.vec_hom_zero_iff[of h] of_int_hom.vec_hom_inj by auto
      with h have False by simp
    } hence h0: "?h \<noteq> 0\<^sub>v n" by auto
    with lattice_of_of_int[OF H h(1)]
    have "?h \<in> gs.lattice_of ?F - {0\<^sub>v n}" by auto
  } 
  from gs.weakly_reduced_imp_short_vector[OF basis _ gs red this a1] lenH
  show "h \<in> L - {0\<^sub>v n} \<Longrightarrow> ?r (sq_norm v) \<le> \<alpha> ^ (m - 1) * ?r (sq_norm h)"
    unfolding L v by (auto simp: sq_norm_of_int)
  from m0 H lenH show vn: "v \<in> carrier_vec n" unfolding v by (cases F1, auto)
  have vL: "v \<in> L" unfolding L[symmetric] v using m0 H lenH
    by (intro basis_in_latticeI, cases F1, auto)
  {
    assume "v = 0\<^sub>v n" 
    hence "hd ?F = 0\<^sub>v n" unfolding v using m0 lenH by (cases F1, auto)
    with gs.lin_indpt_list_nonzero[OF basis] have False using m0 lenH by (cases F1, auto)
  }
  with vL show v: "v \<in> L - {0\<^sub>v n}" by auto
  have jn:"0\<^sub>v j \<in> carrier_vec n \<Longrightarrow> j = n" unfolding zero_vec_def carrier_vec_def by auto
  with v vn show "v \<noteq> 0\<^sub>v j" by auto
qed
end
end