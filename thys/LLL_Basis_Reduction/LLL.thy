(*
    Authors:    Jose Divasón
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
    
fun basis_reduction_add_row_main :: "state \<Rightarrow> int vec \<Rightarrow> rat \<Rightarrow> state \<times> int" where 
  "basis_reduction_add_row_main (i,F,G) fj mu = (let     
     c = floor_ceil mu
     in if c = 0 then
       ((i,F,G), c)
     else 
     let 
     fi = get_nth_i F - (c \<cdot>\<^sub>v fj);
     F' = update_i F fi
     in ((i,F',G), c))"

fun basis_reduction_add_row_i_all_main :: "state \<Rightarrow> int vec list \<Rightarrow> (rat vec \<times> rat) list \<Rightarrow> state" where
  "basis_reduction_add_row_i_all_main state (Cons fj fjs) (Cons gj gjs) = (case state of (i,F,G) \<Rightarrow> 
    let fi = get_nth_i F in
    basis_reduction_add_row_i_all_main (fst (basis_reduction_add_row_main state fj (\<mu>_ij fi gj))) fjs gjs)"
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
    new_gim1 = gi + mu \<cdot>\<^sub>v gim1;
    norm_gim1 = sq_norm new_gim1;
    new_gi = gim1 - (fim1 \<bullet>i new_gim1 / norm_gim1) \<cdot>\<^sub>v new_gim1;
    norm_gi = sq_norm new_gi;
    G' = dec_i (update_im1 (update_i G (new_gi,norm_gi)) (new_gim1,norm_gim1));
    F' = dec_i (update_im1 (update_i F fim1) fi)
  in (i - 1, F', G'))"

context 
  fixes \<alpha> :: rat
  and m :: nat
begin
definition basis_reduction_step :: "state \<Rightarrow> state" where
  "basis_reduction_step state = (if fst state = 0 then increase_i state
     else let state' = basis_reduction_add_rows state in
     case state' of (i, F, G) \<Rightarrow>
      if sqnorm_g_im1 G > \<alpha> * sqnorm_g_i G 
      then basis_reduction_swap state'
      else increase_i state'  
     )" 

partial_function (tailrec) basis_reduction_main :: "state \<Rightarrow> state" where
  [code]: "basis_reduction_main state = (case state of (i,F,G) \<Rightarrow>
     if i < m 
     then basis_reduction_main (basis_reduction_step state) 
     else state)"
end

definition initial_state :: "nat \<Rightarrow> int vec list \<Rightarrow> state" where
  "initial_state n F = (let G = gram_schmidt_triv n (map (map_vec of_int) F);
     Fr = ([], F);
     Gr = ([], G)
     in (0, Fr, Gr))" 

definition basis_reduction_state :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> state" where 
  "basis_reduction_state n \<alpha> F = (basis_reduction_main \<alpha> (length F) (initial_state n F))" 

definition reduce_basis :: "nat \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> int vec list \<times> rat vec list" where
  "reduce_basis n \<alpha> F = (\<lambda> state. ((of_list_repr o fst o snd) state, 
     (map fst o of_list_repr o snd o snd) state))
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
   and L :: "int vec set" (* lattice *) and \<alpha> :: rat (* approximation factor *)
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

context fixes A :: nat
begin

text \<open>This is the core invariant which enables to prove functional correctness.
  It moreover states that the norms of the GSO vectors stay small.\<close>

definition g_bound :: "rat vec list \<Rightarrow> bool" where 
  "g_bound gs = (\<forall> i < m. sq_norm (gs ! i) \<le> of_nat A)" 

definition LLL_partial_invariant :: "state \<Rightarrow> int vec list \<Rightarrow> rat vec list \<Rightarrow> bool" where 
  "LLL_partial_invariant state F G = (case state of (i,Fr,Gr) \<Rightarrow> 
  snd (gram_schmidt_int n F) = G \<and>
  gs.lin_indpt_list (RAT F) \<and> 
  lattice_of F = L \<and>
  gs.reduced \<alpha> i G (gs.\<mu> (RAT F)) \<and>
  i \<le> m \<and>
  length F = m \<and>
  f_repr i Fr F \<and> 
  g_repr i Gr F \<and> g_bound G
  )" 

definition f_bound :: "int vec list \<Rightarrow> bool" where 
  "f_bound fs = (\<forall> i < m. sq_norm (fs ! i) \<le> int (A * m))" 

text \<open>The full invariant also states that the norms of the f-vectors stay small.\<close>

definition LLL_invariant :: "state \<Rightarrow> int vec list \<Rightarrow> rat vec list \<Rightarrow> bool" where
  "LLL_invariant state F G = (LLL_partial_invariant state F G \<and> f_bound F)" 

lemmas LLL_invariants_def = LLL_invariant_def LLL_partial_invariant_def 

lemma LLL_invD: assumes "LLL_invariant (i,Fr,Gr) F G"
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
  "f_bound F"
  "g_bound G"
  using assms gs.lin_indpt_list_def of_list_repr[of i Fr F] 
  unfolding LLL_invariants_def split gs.reduced_def by auto

lemma LLL_pinvD: assumes "LLL_partial_invariant (i,Fr,Gr) F G"
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
  "g_bound G"
  using assms gs.lin_indpt_list_def of_list_repr[of i Fr F] 
  unfolding LLL_invariants_def split gs.reduced_def by auto

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
  "f_bound F" 
  "g_bound G" 
shows "LLL_invariant (i,Fr,Gr) F G" 
  unfolding LLL_invariants_def Let_def split using assms of_list_repr[OF assms(1)] by auto

lemma LLL_pinvI: assumes  
  "f_repr i Fr F"
  "g_repr i Gr F" 
  "snd (gram_schmidt_int n F) = G" 
  "lattice_of F = L" 
  "gs.weakly_reduced \<alpha> i G"
  "i \<le> m"
  "length F = m" 
  "gs.lin_indpt_list (RAT F)"
  "gs.reduced \<alpha> i G (gs.\<mu> (RAT F))" 
  "g_bound G" 
shows "LLL_partial_invariant (i,Fr,Gr) F G" 
  unfolding LLL_invariants_def Let_def split using assms of_list_repr[OF assms(1)] by auto
  
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
  assumes inv: "LLL_partial_invariant (i,Fr,Gr) F G" 
  shows "G = map (gs.gso (RAT F)) [0..<m]"
  using gram_schmidt_int_connect[of F G] LLL_pinvD[OF inv] by auto
  

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

lemma g_i: assumes inv: "LLL_partial_invariant (i,Fr,Gr) F G" and i: "i < m"  
  shows "g_i Gr = G ! i" 
    "sqnorm_g_i Gr = sq_norm (G ! i)"
proof -
  note conn = LLL_connect[OF inv]
  note inv = LLL_pinvD[OF inv]    
  note conn = conn[folded inv(1)]
  from inv i have Gr: "g_repr i Gr F" 
    and len: "length F = m" by auto
  from g_i_GSO[OF Gr i] sqnorm_g_i_GSO[OF Gr i]
  have "g_i Gr = GSO F i \<and> sqnorm_g_i Gr = sq_norm (GSO F i)" by simp
  also have "GSO F i = G ! i" unfolding GSO_def conn using i len by simp
  finally show "g_i Gr = G ! i" 
    "sqnorm_g_i Gr = sq_norm (G ! i)" by auto
qed
  
lemma g_im1: assumes inv: "LLL_partial_invariant (i,Fr,Gr) F G" and i: "i < m" "i \<noteq> 0" 
  shows "g_im1 Gr = G ! (i - 1)" 
    "sqnorm_g_im1 Gr = sq_norm (G ! (i - 1))"
proof -
  note conn = LLL_connect[OF inv]
  note inv = LLL_pinvD[OF inv]    
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

definition dk :: "int vec list \<Rightarrow> nat \<Rightarrow> int" where "dk fs k = (gs.Gramian_determinant fs k)"

definition D :: "int vec list \<Rightarrow> nat" where "D fs = nat (\<Prod> i < m. dk fs i)" 

definition logD :: "int vec list \<Rightarrow> nat"
  where "logD fs = (if \<alpha> = 4/3 then (D fs) else nat (floor (log (1 / of_rat reduction) (D fs))))" 

definition LLL_measure :: "state \<Rightarrow> nat" where 
  "LLL_measure state = (case state of (i,fs,gs) \<Rightarrow> 2 * logD (of_list_repr fs) + m - i)" 

lemma Gramian_determinant: assumes "LLL_partial_invariant (i,Fr,Gr) F G" 
  and k: "k \<le> m" 
shows "of_int (gs.Gramian_determinant F k) = (\<Prod> j<k. sq_norm (G ! j))" 
  "gs.Gramian_determinant F k > 0" 
proof -
  let ?f = "(\<lambda>i. of_int_hom.vec_hom (F ! i))" 
  note LLL = LLL_connect[OF assms(1)]
  note LLLD = LLL_pinvD[OF assms(1)]
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
    unfolding gs.Gramian_determinant_def of_int_hom.hom_det[symmetric]
  proof (rule arg_cong[of _ _ det])
    have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by auto
    show "gs.Gramian_matrix ?F k = map_mat of_int (gs.Gramian_matrix F k)" 
      unfolding gs.Gramian_matrix_def Let_def
    proof (subst of_int_hom.mat_hom_mult[of _ k n _ k], (auto)[2], rule cong) 
      show id: "mat k n (\<lambda> (i,j). ?F ! i $ j) = map_mat of_int (mat k n (\<lambda> (i, j). F ! i $ j))" (is "?L = map_mat _ ?R")
      proof (rule eq_matI, goal_cases)
        case (1 i j)
        hence ij: "i < k" "j < n" "i < length F" "dim_vec (F ! i) = n" using len k Fi[of i] by auto
        show ?case using ij by simp 
      qed auto
      show "?L\<^sup>T = map_mat of_int ?R\<^sup>T" unfolding id by (rule eq_matI, auto)
    qed
  qed
  show "of_int (gs.Gramian_determinant F k) = (\<Prod> j<k. sq_norm (G ! j))" 
    "gs.Gramian_determinant F k > (0 :: int)" using det[unfolded hom] by auto
qed

lemma LLL_dk_pos [intro]: assumes inv: "LLL_partial_invariant state F G" 
  and k: "k \<le> m" 
shows "dk F k > 0"
proof -
  obtain i Gr gso where trip: "state = (i, Gr, gso)" by (cases state, auto)
  note inv = inv[unfolded trip]
  from Gramian_determinant[OF inv k] show ?thesis unfolding trip dk_def by auto
qed

lemma LLL_D_pos: assumes inv: "LLL_partial_invariant state F G" 
shows "D F > 0"
proof -
  have "(\<Prod> j < m. dk F j) > 0"
    by (rule prod_pos, insert LLL_dk_pos[OF inv], auto)
  thus ?thesis unfolding D_def by auto
qed

lemma increase_i: assumes LLL: "LLL_invariant (i,Fr,Gr) F G" 
  and i: "i < m" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (G ! (i - 1)) \<le> \<alpha> * sq_norm (G ! i)"
  and sred_i: "\<And> j. j < i \<Longrightarrow> \<bar>gs.\<mu> (RAT F) i j\<bar> \<le> 1 / 2" 
shows "LLL_invariant (increase_i (i,Fr,Gr)) F G"
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
  from sred sred_i have sred: "gs.reduced \<alpha> (Suc i) G (gs.\<mu> (RAT F))"
    unfolding gs.reduced_def
    by (intro conjI[OF red] allI impI, rename_tac ii j, case_tac "ii = i", auto)
  show ?thesis unfolding increase_i_def split
    by (rule LLL_invI[OF Fr' Gr'], insert inv red sred i, auto)
qed

lemma basis_reduction_add_row_main: assumes Linv: "LLL_partial_invariant (i,Fr,Gr) F G"
  and i: "i < m"  and j: "j < i" 
  and res: "basis_reduction_add_row_main (i,Fr,Gr) fj mu = ((i',Fr',Gr'), c)"
  and fj: "fj = F ! j" 
  and mu: "mu = gs.\<mu> (RAT F) i j" 
shows "\<exists> v. LLL_partial_invariant (i',Fr',Gr') (F[ i := v]) G \<and> i' = i \<and> Gr' = Gr \<and> abs (mu - of_int c) \<le> inverse 2 
  \<and> mu - of_int c = gs.\<mu> (RAT (F[ i := v])) i j
  \<and> (\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> (i' \<noteq> i \<or> j' > j) 
      \<longrightarrow> gs.\<mu> (RAT (F[ i := v])) i' j' = gs.\<mu> (RAT F) i' j')"
proof -
  define M where "M = map (\<lambda>i. map (gs.\<mu> (RAT F) i) [0..<m]) [0..<m]"
  note inv = LLL_pinvD[OF Linv]
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
  } note mu_change = this
  have sred: "gs.reduced \<alpha> i G1 (gs.\<mu> (RAT F1))"
    unfolding gs.reduced_def 
  proof (intro conjI[OF red] impI allI, goal_cases)
    case (1 i' j)
    with mu_change[of i' j] sred[unfolded gs.reduced_def, THEN conjunct2, rule_format, of i' j] i 
    show ?case by auto
  qed
  (* now let us head for the implementation *)
  have Mij: "mu = M ! i ! j" unfolding M_def mu using `i < m` ji(2) by auto
  from res[unfolded Mij] have c: "c = floor_ceil (M ! i ! j)" 
    by (auto simp: Let_def split: if_splits)
  have x: "?x = ?x'" by (subst get_nth_i[OF Fr], insert add, auto simp: c Mij j)
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
  have res: "i' = i" "Fr' = Fr1" "Gr' = Gr" using Mij c0 i len
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
    have "LLL_partial_invariant (i, Fr1, Gr) F1 G" unfolding Hs[symmetric]
      apply (rule LLL_pinvI[OF repr' gso'' G1_def(2)[folded snd_gram_schmidt_int,symmetric] _ red inv(7) _ _ sred])
      by (insert F1 F1_F inv(5) indep_F1 Hs inv(12), auto)
  } note inv_gso = this
  { 
    fix ia assume "ia \<le> j" hence "ia < i" using ji j by auto
    hence "(RAT F1) ! ia = (RAT F) ! ia"
      using F1_def i len by auto 
  }
  hence fs_eq:"gs.gso (RAT F1) j = gs.gso (RAT F) j"
    by (intro gs_gs_identical, auto)
  have dima:"dim_vec a = dim_vec b \<Longrightarrow> ?RV (a + b) = ?RV a + ?RV b" for a b by auto
  from gs.gso_times_self_is_norm[OF conn1 ji(2)]
  have gs_norm:"(RAT F) ! j \<bullet> gs.gso (RAT F) j = \<parallel>gs.gso (RAT F) j\<parallel>\<^sup>2" by auto
  have fc:"floor_ceil (0::rat) = 0" unfolding floor_ceil_def by linarith
  { 
    assume "sq_norm_vec (gs.gso (RAT F) j) = 0"
    hence "gs.gso (RAT F) j = 0\<^sub>v n" using gs_carr(1) sq_norm_vec_eq_0 len by force
    hence "c = 0" unfolding c M_def gs.\<mu>.simps using j i fc by auto
  } note zero = this
  from \<open>j < i\<close> have if_True: "(if j < i then t else e) = t" for t e by simp
  have id1: "?RV (F ! j) = (RAT F) ! j" using ji len by auto
  have id: "(RAT F1) ! i = (RAT F) ! i - ?R c \<cdot>\<^sub>v ?RV (F ! j)" unfolding F1_def using i len Fij by auto
  have mudiff: "mu = (RAT F) ! i \<bullet> gs.gso (RAT F) j / \<parallel>gs.gso (RAT F) j\<parallel>\<^sup>2" 
    unfolding mu gs.\<mu>.simps if_True id using i ji(2) by auto
  have mudiff:"mu - of_int c = gs.\<mu> (RAT F1) i j"
    unfolding mudiff unfolding gs.\<mu>.simps fs_eq if_True id
    apply (subst minus_scalar_prod_distrib, (insert Fij gs_carr, auto)[3])
    apply (subst scalar_prod_smult_left, (insert Fij gs_carr, auto)[1])
    apply (unfold id1 gs_norm)
    using zero divide_diff_eq_iff by fastforce
  have "abs (mu - of_int c) \<le> inverse 2" unfolding res j Mij c
    by (rule floor_ceil)
  thus ?thesis using mu_change inv_gso mudiff unfolding res j F1_def by auto
qed

lemma sq_norm_fs_via_sum_mu_gso: assumes Lpinv: "LLL_partial_invariant (ii,Fr,Gr) F G"
  and i: "i < m" 
  shows "rat_of_int \<parallel>F ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (gs.\<mu> (RAT F) i j)\<^sup>2 * \<parallel>G ! j\<parallel>\<^sup>2)" 
proof -
  let ?mu = "gs.\<mu> (RAT F) i" 
  let ?G = "gs.gso (RAT F)" 
  note inv = LLL_pinvD[OF Lpinv]
  have GF': "G = map ?G [0..<m]" using gram_schmidt_int_connect[of F G] inv by auto
  let ?r = "rat_of_int" 
  have "?r \<parallel>(F ! i)\<parallel>\<^sup>2 = sq_norm (map_vec ?r (F ! i))" unfolding sq_norm_of_int ..
  also have "map_vec ?r (F ! i) = RAT F ! i" using i inv by auto 
  also have "\<dots> = gs.sumlist (map (\<lambda>j. ?mu j \<cdot>\<^sub>v ?G j) [0..<Suc i])" 
    using gs.fi_is_sum_of_mu_gso[OF inv(10) _ refl i] inv(4) i by auto
  also have "\<dots> = gs.sumlist (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0 ..< Suc i])" 
    by (rule arg_cong[of _ _ "gs.sumlist"], rule map_cong[OF refl], unfold GF', insert i, auto)
  also have "sq_norm \<dots> = sum_list (map sq_norm (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0..<Suc i]))" 
    unfolding map_map o_def sq_norm_smult_vec
    unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod conjugate_id
  proof (rule gs.scalar_prod_lincomb_orthogonal)
    show "Suc i \<le> length G" unfolding GF' using i by auto
    show "set G \<subseteq> Rn" unfolding GF' using gs.gso_carrier[OF inv(10) _ refl] inv(4) by auto
    show "orthogonal G" 
      using gs.gram_schmidt[OF inv(10) _ inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]] inv(4)
      by auto
  qed
  also have "map sq_norm (map (\<lambda>j. ?mu j \<cdot>\<^sub>v G ! j) [0..<Suc i]) = map (\<lambda>j. (?mu j)^2 * sq_norm (G ! j)) [0..<Suc i]" 
    unfolding map_map o_def sq_norm_smult_vec by (rule map_cong, auto simp: power2_eq_square)
  finally show ?thesis . 
qed

lemma sq_norm_fs_mu_G_bound: assumes Lpinv: "LLL_partial_invariant (ii,Fr,Gr) F G"
  and i: "i < m" 
  and mu_bound: "\<And> j. j \<le> i \<Longrightarrow> (gs.\<mu> (RAT F) i j)^2 \<le> a" 
shows "rat_of_int \<parallel>F ! i\<parallel>\<^sup>2 \<le> of_nat (Suc i * A) * a" 
proof -
  have "rat_of_int \<parallel>F ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (gs.\<mu> (RAT F) i j)\<^sup>2 * \<parallel>G ! j\<parallel>\<^sup>2)" 
    by (rule sq_norm_fs_via_sum_mu_gso[OF Lpinv i])
  also have "\<dots> \<le> (\<Sum>j\<leftarrow>[0..<Suc i]. a * of_nat A)" 
  proof (rule sum_list_ge_mono, force, unfold length_map length_upt,
    subst (1 2) nth_map_upt, force, goal_cases)
    case (1 j)
    hence ji: "j \<le> i" by auto
    from LLL_pinvD[OF Lpinv] have "g_bound G" by auto
    from this[unfolded g_bound_def] i ji 
    have GB: "sq_norm (G ! j) \<le> of_nat A" by auto
    show ?case 
      by (rule mult_mono, insert mu_bound[OF ji] GB order.trans[OF zero_le_power2], auto)
  qed
  also have "\<dots> = of_nat (Suc i) * (a * of_nat A)" unfolding sum_list_triv length_upt by simp
  also have "\<dots> = of_nat (Suc i * A) * a" unfolding of_nat_mult by simp
  finally show ?thesis .
qed


lemma basis_reduction_add_rows: fixes Gr assumes Linv: "LLL_invariant (i,Fr,Gr) F G"
  and i: "i < m" 
  and res: "basis_reduction_add_rows (i,Fr,Gr) = (i',Fr',Gr')"
shows "\<exists> F' fi. LLL_invariant (i,Fr',Gr) F' G \<and> i' = i \<and> Gr' = Gr \<and> F' = F[i := fi] \<and>
  (\<forall> j < i. abs (gs.\<mu> (RAT F') i j) \<le> 1/2)"
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
  from Linv have Lpinv: "LLL_partial_invariant (i, Fr, Gr) F G" unfolding LLL_invariants_def by auto
  from res[unfolded id id'] have
    "basis_reduction_add_row_i_all_main (i, Fr, Gr) (rev (take ii F))
     (rev (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (gs.gso (RAT F)) [0..<ii]))) =
    (i', Fr', Gr')" "ii \<le> i" unfolding ii_def by auto 
  hence "\<exists> F' fi. LLL_partial_invariant (i,Fr',Gr) F' G \<and> i' = i \<and> Gr' = Gr \<and> F' = F[i := fi] \<and>
  (\<forall> j < i. abs (gs.\<mu> (RAT F') i j) \<le> 1/2) \<and>
  (\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> i' \<noteq> i \<longrightarrow> 
    gs.\<mu> (RAT F') i' j' = gs.\<mu> (RAT F) i' j')" using Lpinv small 
  proof (induct ii arbitrary: Fr F)
    case (Suc ii Fr F)
    note inv = LLL_pinvD[OF Suc(4)]
    let ?fs = "gs.gso (RAT F) ii" 
    let ?fsn = "(?fs, \<parallel>?fs\<parallel>\<^sup>2)"       
    let ?main = "basis_reduction_add_row_main (i, Fr, Gr) (F ! ii)
        (\<mu>_ij (get_nth_i Fr) ?fsn)" 
    obtain i'' Fr'' Gr'' c where main: "?main = ((i'', Fr'', Gr''),c)" 
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
    from basis_reduction_add_row_main[OF Suc(4) i ii(1) main refl pair]
    obtain v where
        Linv: "LLL_partial_invariant (i, Fr'', Gr) (F[i := v]) G" 
      and id: "i'' = i" "Gr'' = Gr" 
      and small: "?small (F[i := v]) ii" 
      and id': "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> (i' \<noteq> i \<or> ii < j') \<longrightarrow>
        gs.\<mu> (RAT (F[i := v])) i' j' =
        gs.\<mu> (RAT F) i' j'" by auto
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
    from Suc(1)[OF res ii_le Linv small] obtain G' fi where
      Linv: "LLL_partial_invariant (i, Fr', Gr) G' G" 
      and i': "i' = i" 
      and fi: "G' = F[i := v, i := fi]" 
      and gso': "Gr' = Gr" 
      and small: "(\<forall>j<i. ?small G' j)" 
      and id: "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> i' \<noteq> i \<Longrightarrow>
           gs.\<mu> (RAT G') i' j' =
           gs.\<mu> (RAT ?G) i' j'" by blast
    from fi have fi: "G' = F[i := fi]" by auto
    show ?case
    proof (intro exI conjI, rule Linv, rule i', rule gso', rule fi, rule small, intro allI impI, goal_cases)
      case (1 i' j')
      show ?case unfolding id[OF 1] 
        by (rule id'[rule_format], insert 1 i', auto)
    qed
  next
    case 0
    thus ?case by (intro exI[of _ F] exI[of _ "F ! i"], auto)
  qed
  then obtain F' fi where Lpinv: "LLL_partial_invariant (i,Fr',Gr) F' G" 
    and *: "i' = i" "Gr' = Gr" and F': "F' = F[i := fi]" 
    and mu: "\<And> j. j < i \<Longrightarrow> abs (gs.\<mu> (RAT F') i j) \<le> 1/2" 
    and **: "(\<forall> i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> i' \<noteq> i \<longrightarrow> 
     gs.\<mu> (RAT F') i' j' = gs.\<mu> (RAT F) i' j')" by blast
  let ?mu = "gs.\<mu> (RAT F') i" 
  let ?G = "gs.gso (RAT F')" 
  from LLL_invD[OF Linv] have g_bound: "g_bound G" 
    and f_bound: "f_bound F" by auto
  note inv = LLL_pinvD[OF Lpinv]
  have GF': "G = map ?G [0..<m]" using gram_schmidt_int_connect[of F' G] inv by auto
  let ?r = "rat_of_int" 
  have "?r (sq_norm (F' ! i)) \<le> of_nat (Suc i * A) * 1"
  proof (rule sq_norm_fs_mu_G_bound[OF Lpinv i])
    fix j 
    assume ji: "j \<le> i" 
    hence "j < Suc i" by simp
    with mu[of j] have "abs (?mu j) \<le> 1" by (cases "j = i", auto simp: gs.\<mu>.simps[of _ _ i])
    thus "(?mu j)^2 \<le> 1" unfolding power2_eq_square
      by (metis abs_ge_zero abs_mult_self_eq mult_le_one)
  qed
  also have "\<dots> = of_nat A * of_nat (Suc i)" unfolding of_nat_mult by simp 
  also have "\<dots> \<le> of_nat A * of_nat m" 
    by (rule mult_left_mono, insert i, auto)
  also have "\<dots> = of_nat (A * m)" by simp
  finally have "?r \<parallel>(F' ! i)\<parallel>\<^sup>2 \<le> rat_of_int (A * m)" by simp
  hence Fi: "\<parallel>(F' ! i)\<parallel>\<^sup>2 \<le> int (A * m)" by linarith
  from f_bound Fi have f_bound: "f_bound F'" unfolding f_bound_def F' 
    by (auto, rename_tac ii, case_tac "ii = i", auto)
  show ?thesis using f_bound g_bound * Lpinv mu F' mu ** unfolding LLL_invariant_def split
    by (intro exI[of _ F'] exI[of _ fi], auto)
qed

context
  assumes \<alpha>: "\<alpha> \<ge> 4/3"
begin
lemma \<alpha>0: "\<alpha> > 0" "\<alpha> \<noteq> 0" 
  using \<alpha> by auto

lemma reduction: "0 < reduction" "reduction \<le> 1" 
  "\<alpha> > 4/3 \<Longrightarrow> reduction < 1" 
  "\<alpha> = 4/3 \<Longrightarrow> reduction = 1" 
  using \<alpha> unfolding reduction_def by auto

(* lemma 16.16 (ii), one case *)
lemma dk_swap_unchanged: assumes len: "length F1 = m" 
  and i0: "i \<noteq> 0" and i: "i < m" and ki: "k \<noteq> i" and km: "k \<le> m"   
  and swap: "F2 = F1[i := F1 ! (i - 1), i - 1 := F1 ! i]"
shows "dk F1 k = dk F2 k"
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
  have "dk F2 k = det (gs.Gramian_matrix F2 k)" 
    unfolding dk_def gs.Gramian_determinant_def by simp
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
  also have "\<dots> = dk F1 k" 
    unfolding dk_def gs.Gramian_determinant_def by simp
  finally have "dk F2 k = (det P * det P) * dk F1 k" by simp
  also have "det P * det P = 1" using detP by auto
  finally show "dk F1 k = dk F2 k" by simp
qed


lemma basis_reduction_step: assumes inv: "LLL_invariant (i,Fr,Gr) F G"
  and i: "i < m"
  and res: "basis_reduction_step \<alpha> (i,Fr,Gr) = state"
shows "(\<exists> F' G'. LLL_invariant state F' G')" 
  and "LLL_measure state < LLL_measure (i,Fr,Gr)" 
proof (atomize(full), cases "i = 0")
  case i0: False
  note res = res[unfolded basis_reduction_step_def split] 
  obtain i1 Fr1 Gr1 where 
    il: "basis_reduction_add_rows (i,Fr,Gr) = ((i1, Fr1, Gr1))" (is "?b = _")
    by (cases ?b, auto)
  from basis_reduction_add_rows[OF inv i il] i0 obtain F1 
    where Linv': "LLL_invariant (i, Fr1, Gr1) F1 G" and ii: "i1 = i" 
      and mu_F1_i: "\<And> j. j<i \<Longrightarrow> \<bar>gs.\<mu> (RAT F1) i j\<bar> \<le> 1 / 2" 
      and m12: "\<bar>gs.\<mu> (RAT F1) i (i - 1)\<bar> \<le> inverse 2"
    by auto
  have I: "LLL_invariant state F G \<Longrightarrow> LLL_partial_invariant state F G" for state F G
    unfolding LLL_invariant_def by auto
  note dk = dk_def  
  note Gd = Gramian_determinant(1)[OF I]
  note Gd12 = Gd[OF inv] Gd[OF Linv']
  have dk_eq: "k \<le> m \<Longrightarrow> dk F k = dk F1 k" for k (* Lemma 16.16 (i) *)
    unfolding dk using Gd12[of k] by auto
  have D_eq: "D F = D F1" unfolding D_def
    by (rule arg_cong[of _ _ nat], rule prod.cong, insert dk_eq, auto)
  hence logD_eq: "logD F = logD F1" unfolding logD_def by simp
  note inv = LLL_invD[OF inv] 
  note inv' = LLL_invD[OF Linv']
  from inv have repr: "f_repr i Fr F" by auto
  note res = res[unfolded basis_reduction_step_def this split il id Let_def]
  let ?x = "G ! (i - 1)" let ?y = "G ! i" 
  let ?x' = "sqnorm_g_im1 Gr1" let ?y' = "sqnorm_g_i Gr1" 
  let ?cond = "\<alpha> * sq_norm ?y < sq_norm ?x" 
  let ?cond' = "\<alpha> * ?y' < ?x'"
  from inv' have red: "gs.weakly_reduced \<alpha> i G" 
    and repr: "f_repr i Fr1 F1" and gS: "snd (gram_schmidt_int n F1) = G" 
    and len: "length F1 = m" and HC: "set F1 \<subseteq> carrier_vec n" 
    and gso: "g_repr i Gr1 F1" and L: "lattice_of F1 = L" 
    and f_bound: "f_bound F1" 
    using i by auto 
  note g_i = g_i[OF I]
  note g_im1 = g_im1[OF I]
  from g_i[OF Linv' i] have y: "?y' = sq_norm ?y" by auto
  from g_im1[OF Linv' i i0] have x: "?x' = sq_norm ?x" by auto
  hence cond: "?cond' = ?cond" using y by auto
  from i0 have "(i = 0) = False" by auto
  note res = res[unfolded cond fst_conv this if_False]
  show "(\<exists>H. Ex (LLL_invariant state H)) \<and> LLL_measure state < LLL_measure (i, Fr, Gr)"
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
    have state: "state = increase_i (i, Fr1, Gr1)" by auto
    have invS: "LLL_invariant state F1 G" unfolding state
      by (rule increase_i[OF Linv' i], insert False mu_F1_i, auto)
    obtain Fr' Gr' where state: "state = (Suc i, Fr', Gr')" using state
      by (cases state, auto simp: increase_i_def)
    have "LLL_measure state < LLL_measure (i, Fr, Gr)" unfolding LLL_measure_def logD_eq split state
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
        new_gim1 = gi + ?mu \<cdot>\<^sub>v gim1;
        norm_gim1 = sq_norm new_gim1;
        new_gi = gim1 - (fim1 \<bullet>i new_gim1 / norm_gim1) \<cdot>\<^sub>v new_gim1;
        norm_gi = sq_norm new_gi
          in dec_i (update_im1 (update_i Gr1 (new_gi,norm_gi)) (new_gim1,norm_gim1))" 
    define Gr2 where gso': "Gr2 = ?gso'"
    have span': "gs.span (SRAT F1) = gs.span (SRAT F2)" 
      by (rule arg_cong[of _ _ gs.span], unfold F2_def, insert swap, auto)
    from res gH' Fr2_def Hr' gso' True ii
    have state: "state = (i - 1, Fr2, Gr2)" by (auto simp: Let_def)
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
    have gs: "\<And> j. j < m \<Longrightarrow> ?g1 j \<in> Rn" using gs.gso_carrier[OF connH] .
    have g: "\<And> j. j < m \<Longrightarrow> ?f1 j \<in> Rn" using gs.f_carrier[OF connH] .
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
    have "?f1 i = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i] @ [?g1 i])" 
      unfolding gs.fi_is_sum_of_mu_gso[OF connH \<open>i < m\<close>] by (simp add: gs.\<mu>.simps)
    also have "\<dots> = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i]) + ?g1 i" 
      by (subst gs.sumlist_append, insert i gs, auto)
    finally have claim2: "?f1 i = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i]) + ?g1 i" (is "_ = ?sum + _") .
    have sum: "?sum \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
    from gs.span_closed[OF G] have S: "?S \<subseteq> Rn" by auto
    from gs i have gs': "\<And> j. j < i - 1 \<Longrightarrow> ?g1 j \<in> Rn" and gsi: "?g1 (i - 1) \<in> Rn" by auto
    have "[0 ..< i] = [0 ..< Suc (i - 1)]" using i0 by simp
    also have "\<dots> = [0 ..< i - 1] @ [i - 1]" by simp
    finally have list: "[0 ..< i] = [0 ..< i - 1] @ [i - 1]" .
    have g2_im1: "?g2 (i - 1) = ?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)" (is "_ = _ + ?mu_f1") 
    proof (rule gs.is_oc_projection_eq[OF connH claim1 _ S g[OF i]])
      show "gs.is_oc_projection (?g1 i + ?mu_f1) ?S (?f1 i)" unfolding gs.is_oc_projection_def
      proof (intro conjI allI impI)
        let ?sum' = "gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
        have sum': "?sum' \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
        show inRn: "(?g1 i + ?mu_f1) \<in> Rn" using gs[OF i] gsi i by auto
        have carr: "?sum \<in> Rn" "?g1 i \<in> Rn" "?mu_f1 \<in> Rn" "?sum' \<in> Rn" using sum' sum gs[OF i] gsi i by auto
        have "?f1 i - (?g1 i + ?mu_f1) = (?sum + ?g1 i) - (?g1 i + ?mu_f1)"
          unfolding claim2 by simp
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
    { (* 16.13 (i) *)
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
    {
      fix jj
      assume jj: "jj < i - 1"  
      hence id1: "jj < i - 1 \<longleftrightarrow> True" "jj < i \<longleftrightarrow> True" by auto
      have id2: "?g2 jj = ?g1 jj" by (subst g2_g1_identical, insert jj i, auto)       
      have "?mu2 i jj = ?mu1 (i - 1) jj" 
        unfolding gs.\<mu>.simps id1 id2 if_True using len i i0 by (auto simp: F2_def)
    } note mu'_mu_i = this
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
        by (rule map_cong[OF refl], subst g2_g1_identical, insert i, auto simp: mu'_mu_i)
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
    {
      from i1n have i1n': "i - 1 \<le> m" by simp
      have upd_im1: "list_repr i ba xs \<Longrightarrow> ys = (xs [i - 1 := x]) \<Longrightarrow> list_repr i (update_im1 ba x) ys" 
        for ba xs x ys using update_im1[of i ba xs] i0 by force
      from gso[unfolded g_repr_def] 
      have gsoH: "list_repr i Gr1 (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m]))" by auto
      let ?f_im1 = "get_nth_im1 Fr1"
      let ?g2'_im1 = "g_i Gr1 + ?mu \<cdot>\<^sub>v g_im1 Gr1" 
      let ?norm_im1 = "sq_norm ?g2'_im1" 
      let ?g2'_i = "g_im1 Gr1 - (?f_im1 \<bullet>i ?g2'_im1 / ?norm_im1) \<cdot>\<^sub>v ?g2'_im1" 
      define g2'_i where "g2'_i = ?g2'_i" 
      define g2'_im1 where "g2'_im1 = ?g2'_im1"
      have "?g2 (i - 1) = ?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)" by fact
      also have "?g1 i = g_i Gr1" unfolding g_i[OF Linv' i] Gs_fs o_def using i by simp
      also have "?g1 (i - 1) = g_im1 Gr1" unfolding g_im1[OF Linv' i i0] Gs_fs o_def using i by simp
      finally have g2im1: "?g2 (i - 1) = g2'_im1"
        unfolding mu g2'_im1_def by blast
      have "?f_im1 \<in> carrier_vec n" using inv'(3-4) \<open>i - 1 < m\<close> unfolding get_nth_im1[OF inv'(8) i0] 
        by auto
      hence dim: "dim_vec ?f_im1 = n" "dim_vec ?g2'_im1 = n" unfolding g2'_im1_def[symmetric] g2im1[symmetric]
        using \<open>?g2_im1 \<in> Rn\<close> by auto
      have "?g2 i = ?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / sq_norm (?g2 (i - 1))) \<cdot>\<^sub>v ?g2 (i - 1)"
        by (rule g2_i)
      also have "?g2 (i - 1) = g2'_im1" by (simp add: g2im1[symmetric])
      also have "?g1 (i - 1) = g_im1 Gr1" by fact
      also have "?f1 (i - 1) = map_vec of_int ?f_im1" 
        unfolding get_nth_im1[OF repr i0] o_def using len i by simp
      finally have g2i: "?g2 i = g2'_i" using dim unfolding g2'_i_def g2'_im1_def by simp
      have "map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m])
        [i := (g2'_i, sq_norm g2'_i), i - 1 := (g2'_im1, sq_norm g2'_im1)]
        = map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) ((map (GSO F1) [0..<m])[i := g2'_i, i - 1 := g2'_im1])" 
        unfolding map_update by auto
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
       = map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m])[i := (g2'_i, \<parallel>g2'_i\<parallel>\<^sup>2), i - 1 := (g2'_im1, \<parallel>g2'_im1\<parallel>\<^sup>2)]"
        unfolding GSOH o_def by auto
      hence "g_repr (i - 1) Gr2 F2" unfolding gso' Let_def unfolding g_repr_def Let_def g2'_i_def[symmetric]
        unfolding g2'_im1_def[symmetric] apply (intro conjI i1n')
        apply(rule dec_i[OF _ i0]) by(auto simp: i intro!:upd_im1 update_i[OF gsoH])
    } note g_repr = this
    from inv' have sred: "gs.reduced \<alpha> i G (gs.\<mu> (RAT F1))" by auto
    have sred: "gs.reduced \<alpha> (i - 1) G2 (gs.\<mu> (RAT F2))"
      unfolding gs.reduced_def
    proof (intro conjI[OF red] allI impI, goal_cases)
      case (1 i' j)
      with sred have "\<bar>gs.\<mu> (RAT F1) i' j\<bar> \<le> 1 / 2" unfolding gs.reduced_def by auto
      also have "gs.\<mu> (RAT F1) i' j = gs.\<mu> (RAT F2) i' j" using 1 i len
        by (subst gs_\<mu>_identical[of _ _ "RAT F1" "RAT F2"], auto simp: F2_def)
      finally show ?case by auto
    qed
    (* now show decrease in measure *)
    { (* 16.13 (ii) *)
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
      finally have "sq_norm (?g2 (i - 1)) = 
        sq_norm (?g1 i) + (?mu1 i (i - 1) * ?mu1 i (i - 1)) * sq_norm (?g1 (i - 1))" 
        by (simp add: ac_simps o_def)
      also have "\<dots> < 1/\<alpha> * (sq_norm (?g1 (i - 1))) + (1/2 * 1/2) * (sq_norm (?g1 (i - 1)))"
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

    {
      have list_id: "[0..<Suc (i - 1)] = [0..< i - 1] @ [i - 1]" "map f [x] = [f x]" for f x by auto
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

    have f_bound: "f_bound F2" unfolding f_bound_def
    proof (intro allI impI)
      fix j
      assume j: "j < m" 
      note short = f_bound[unfolded f_bound_def, rule_format]
      consider "j \<noteq> i" "j \<noteq> i - 1" | "j = i" | "j = i - 1" by auto
      thus "\<parallel>F2 ! j\<parallel>\<^sup>2 \<le> int (A * m)" using short[OF j] short[OF i] short[OF \<open>i - 1 < m\<close>] len j i i0
        unfolding F2_def by (cases, auto)
    qed
        
    (* invariant is established *)
    have newInv: "LLL_invariant (i - 1, Fr2, Gr2) F2 G2" 
      by (rule LLL_invI[OF repr' g_repr gH' L red], insert g_bound f_bound connH' len' span' i m12 F2 sred, auto)

    have norm_pos: "j < m \<Longrightarrow> sq_norm (?g2 j) > 0" for j 
      using gs.sq_norm_pos[OF connH',of j] unfolding G2_F2 o_def by simp
    { (* 16.16 (ii), the decreasing case *)
      fix k
      assume k: "k = i" 
      hence kn: "k \<le> m" using i by auto
      from Gd[OF newInv, folded dk_def, folded state, OF kn] k
      have "?R (dk F2 k) = (\<Prod>j<i. sq_norm (G2 ! j) )" by auto
      also have "\<dots> = prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1} \<union> {i - 1})" 
        by (rule sym, rule prod.cong, (insert i0, auto)[1], insert G2_F2 i, auto simp: o_def)
      also have "\<dots> = sq_norm (?g2 (i - 1)) * prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1})" 
        by simp
      also have "\<dots> < (reduction * sq_norm (?g1 (i - 1))) * prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1})"
        by (rule mult_strict_right_mono[OF g_reduction prod_pos], insert norm_pos i, auto)
      also have "prod (\<lambda> j. sq_norm (?g2 j)) ({0 ..< i-1}) = prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1})" 
        by (rule prod.cong[OF refl], subst g2_g1_identical, insert i, auto)
      also have "(reduction * sq_norm (?g1 (i - 1))) * prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1})
        = reduction * prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1} \<union> {i - 1})" by simp
      also have "prod (\<lambda> j. sq_norm (?g1 j)) ({0 ..< i-1} \<union> {i - 1}) = (\<Prod>j<i. sq_norm (?g1 j))"
        by (rule prod.cong, insert i0, auto)
      also have "\<dots> = ?R (dk F1 k)" unfolding dk_def Gd[OF Linv' kn] unfolding k
        by (rule prod.cong[OF refl], insert i, auto simp: Gs_fs o_def)
      also have "\<dots> = ?R (dk F k)" unfolding dk_eq[OF kn] by simp
      finally have "dk F2 k < real_of_rat reduction * dk F k"
        using of_rat_less of_rat_mult of_rat_of_int_eq by metis
    } note dk_i = this[OF refl]
    {
      fix k
      assume kn: "k \<le> m" and ki: "k \<noteq> i" 
      from dk_swap_unchanged[OF len i0 i ki kn F2_def] dk_eq[OF kn] 
      have "dk F k = dk F2 k" by simp
    } note dk = this
    note LLL_dk_pos = LLL_dk_pos[OF I]
    have pos: "k < m \<Longrightarrow> 0 < dk F2 k" "k < m \<Longrightarrow> 0 \<le> dk F2 k" for k 
      using LLL_dk_pos[OF newInv, folded state, of k] by auto
    have prodpos:"0< (\<Prod>i<m. dk F2 i)" apply (rule prod_pos)
      using LLL_dk_pos[OF newInv, folded state] by auto
    have prod_pos':"0 < (\<Prod>x\<in>{0..<m} - {i}. real_of_int (dk F2 x))" apply (rule prod_pos)
      using LLL_dk_pos[OF newInv, folded state] pos by auto
    have prod_nonneg:"0 \<le> (\<Prod>x\<in>{0..<m} - {i}. real_of_int (dk F2 x))" apply (rule prod_nonneg)
      using LLL_dk_pos[OF newInv, folded state] pos by auto
    have prodpos2:"0<(\<Prod>ia<m. dk F ia)" apply (rule prod_pos)
      using LLL_dk_pos[OF assms(1)] by auto
    have "D F2 = real_of_int (\<Prod>i<m. dk F2 i)" unfolding D_def using prodpos by simp
    also have "(\<Prod>i<m. dk F2 i) = (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. dk F2 j)"
      by (rule prod.cong, insert i, auto)
    also have "real_of_int \<dots> = real_of_int (\<Prod> j \<in> {0 ..< m} - {i}. dk F2 j) * real_of_int (dk F2 i)" 
      by (subst prod.union_disjoint, auto)
    also have "\<dots> < (\<Prod> j \<in> {0 ..< m} - {i}. dk F2 j) * (of_rat reduction * dk F i)"
      by(rule mult_strict_left_mono[OF dk_i],insert prod_pos',auto)
    also have "(\<Prod> j \<in> {0 ..< m} - {i}. dk F2 j) = (\<Prod> j \<in> {0 ..< m} - {i}. dk F j)"
      by (rule prod.cong, insert dk, auto)
    also have "\<dots> * (of_rat reduction * dk F i) 
      = of_rat reduction * (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. dk F j)" 
      by (subst prod.union_disjoint, auto)
    also have "(\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. dk F j) = (\<Prod> j<m. dk F j)" 
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
      note LLL_D_pos = LLL_D_pos[OF I]
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
    hence "LLL_measure state < LLL_measure (i, Fr, Gr)" unfolding LLL_measure_def state split
      inv(1)[symmetric] of_list_repr[OF repr']
      using i logD by simp
    thus ?thesis using newInv unfolding state by auto
  qed
next
  case i0: True
  from res i0 have state: "state = increase_i (i, Fr, Gr)" unfolding basis_reduction_step_def by auto
  with increase_i[OF inv i] i0 
  have inv': "LLL_invariant state F G" by auto
  from LLL_invD[OF inv] have Gr: "of_list_repr Fr = F" by simp
  from LLL_invD[OF inv'[unfolded increase_i_def state split]] 
  have Gr': "of_list_repr (inc_i Fr) = F" by simp
  have id: "of_list_repr (inc_i Fr) = of_list_repr Fr" by (simp add: Gr Gr')
  have dec: "LLL_measure state < LLL_measure (i, Fr, Gr)" using i unfolding state i0 
    unfolding LLL_measure_def by (simp add: increase_i_def id)
  show "(\<exists>H. Ex (LLL_invariant state H)) \<and> LLL_measure state < LLL_measure (i, Fr, Gr)" 
    by (intro conjI exI dec, rule inv')
qed

lemma LLL_invariant_A_pos: assumes LLL: "LLL_partial_invariant (i, Fr, Gr) F G" 
  and m: "m \<noteq> 0" 
shows "A > 0" 
proof -
  let ?r = rat_of_int
  note inv = LLL_pinvD[OF LLL]
  note conn = LLL_connect[OF LLL]
  from inv(3,4) have F: "RAT F ! 0 \<in> Rn" "F ! 0 \<in> carrier_vec n" using m unfolding set_conv_nth by auto
  from m have upt: "[0..< m] = 0 # [1 ..< m]" using upt_add_eq_append[of 0 1 "m - 1"] by auto
  from inv(4) m have "map_vec ?r (F ! 0) \<noteq> 0\<^sub>v n" using gs.lin_indpt_list_nonzero[OF inv(10)]
    unfolding set_conv_nth by force
  hence F0: "F ! 0 \<noteq> 0\<^sub>v n" by auto
  hence "sq_norm (F ! 0) \<noteq> 0" using F by simp
  hence 1: "sq_norm (F ! 0) \<ge> 1" using sq_norm_vec_ge_0[of "F ! 0"] by auto
  from inv(12) m have "sq_norm (G ! 0) \<le> of_nat A" unfolding g_bound_def by auto
  also have "G ! 0 = RAT F ! 0" unfolding conn upt using F by (simp add: gs.gso.simps[of _ 0])
  also have "RAT F ! 0 = map_vec ?r (F ! 0)" using inv(4) m by auto
  also have "sq_norm \<dots> = ?r (sq_norm (F ! 0))" by (simp add: sq_norm_of_int)
  finally show ?thesis using 1 by (cases A, auto)
qed

(* equation (3) in front of Lemma 16.18 *)
lemma dk_approx: assumes LLL: "LLL_partial_invariant (ix, Fr, Gr) F G" 
  and i: "i < m" 
shows "rat_of_int (dk F i) \<le> rat_of_nat (A^i)" 
proof -
  note inv = LLL_pinvD[OF LLL]
  note conn = LLL_connect[OF LLL]
  from LLL_invariant_A_pos[OF LLL] i have A: "0 < A" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (dk F i) = (\<Prod>j<i. \<parallel>G ! j\<parallel>\<^sup>2)" unfolding dk_def using i
    by (auto simp: Gramian_determinant [OF LLL])
  also have "\<dots> \<le> (\<Prod>j<i. of_nat A)" using i
    by (intro prod_mono ballI conjI prod_nonneg, insert inv(12)[unfolded g_bound_def], auto)
  also have "\<dots> = (of_nat A)^i" unfolding prod_constant by simp
  also have "\<dots> = of_nat (A^i)" by simp
  finally show ?thesis by simp
qed

lemma D_approx: assumes "LLL_partial_invariant (i, Fr, Gr) F G" 
  shows "D F \<le> A ^ (m * m)" 
proof - 
  note inv = LLL_pinvD[OF assms]
  note conn = LLL_connect[OF assms]
  from LLL_invariant_A_pos[OF assms] have A: "m \<noteq> 0 \<Longrightarrow> 0 < A" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (\<Prod>i<m. dk F i) = (\<Prod>i<m. rat_of_int (dk F i))" by simp
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat A) ^ i)" 
    by (rule prod_mono, insert dk_approx[OF assms] LLL_dk_pos[OF assms], auto simp: less_le)
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat A ^ m))" 
    by (rule prod_mono, insert A, auto intro: pow_mono_exp)
  also have "\<dots> = (of_nat A)^(m * m)" unfolding prod_constant power_mult by simp
  also have "\<dots> = of_nat (A ^ (m * m))" by simp
  finally have "(\<Prod>i<m. dk F i) \<le> A ^ (m * m)" by linarith
  also have "(\<Prod>i<m. dk F i) = D F" unfolding D_def 
    by (subst nat_0_le, rule prod_nonneg, insert LLL_dk_pos[OF assms], auto simp: le_less)  
  finally show "D F \<le> A ^ (m * m)" by linarith 
qed

lemma LLL_measure_approx: assumes inv: "LLL_partial_invariant (i, Fr, Gr) F G"
  and "\<alpha> > 4/3" "m \<noteq> 0" 
shows "LLL_measure (i, Fr, Gr) \<le> m + 2 * m * m * log ((4 * of_rat \<alpha>) / (4 + of_rat \<alpha>)) A"
proof -   
  have id: "1 / real_of_rat reduction = (4 * of_rat \<alpha>) / (4 + of_rat \<alpha>)" 
    unfolding reduction_def of_rat_divide of_rat_add of_rat_mult by simp
  define b where "b = (1 / real_of_rat reduction)" 
  have b1: "b > 1" using reduction(3)[OF assms(2)] reduction(1) unfolding b_def by auto
  from LLL_D_pos[OF inv] have D1: "real (D F) \<ge> 1" by auto
  note invD = LLL_pinvD[OF inv]  
  from invD
  have F: "set F \<subseteq> carrier_vec n" and len: "length F = m" by auto
  have A0: "A > 0" using LLL_invariant_A_pos[OF assms(1,3)] .
  from D_approx[OF inv] 
  have D: "D F \<le> A ^ (m * m)" .
  hence "real (D F) \<le> real (A ^ (m * m))" by linarith
  also have "\<dots> = real A ^ (m * m)" by simp
  finally have log: "log b (real (D F)) \<le> log b (real A ^ (m * m))"   
    by (subst log_le_cancel_iff[OF b1], insert D1 A0, auto)

  have "real (logD F) = real (nat \<lfloor>log b (real (D F))\<rfloor>)" 
    unfolding logD_def b_def using assms by auto
  also have "\<dots> \<le> log b (real (D F))" using b1 D1 by auto
  also have "\<dots> \<le> log b (real A ^ (m * m))" by fact
  also have "\<dots> = (m * m) * log b (real A)" 
    by (rule log_nat_power, insert A0, auto)
  finally have main: "logD F \<le> m * m * log b A" by simp

  have "real (LLL_measure (i, Fr, Gr)) = real (2 * logD F + m - i)"
    unfolding LLL_measure_def split invD(1) by simp
  also have "\<dots> \<le> 2 * real (logD F) + m" using invD by simp
  also have "\<dots> \<le> 2 * (m * m * log b A) + m" using main by auto
  finally show ?thesis unfolding b_def id by simp
qed
end
end

lemma basis_reduction_main: fixes F G assumes "LLL_invariant A state F G"
  and "basis_reduction_main \<alpha> m state = state'" 
  and \<alpha>: "\<alpha> \<ge> 4/3"
shows "\<exists> F' G'. LLL_invariant A state' F' G' \<and> fst state' = m" 
proof (cases "m = 0")
  case True
  from assms(2)[unfolded True basis_reduction_main.simps[of _ 0 state]] 
  have state': "state' = state" by auto
  obtain i Fr Gr where state: "state = (i,Fr,Gr)" by (cases state, auto)
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
    obtain i Fr1 Gr1 where state: "state = (i,Fr1,Gr1)" by (cases state, auto)
    note inv = inv[unfolded state]
    note res = res[unfolded state]
    show ?case
    proof (cases "i < m")
      case True
      with inv have i: "i < m" unfolding LLL_invariant_def by auto
      obtain state'' where b: "basis_reduction_step \<alpha> (i, Fr1, Gr1) = state''" by auto
      from res True b
      have res: "basis_reduction_main \<alpha> m  state'' = state'" by simp
      note bsr = basis_reduction_step[OF \<alpha> inv i b]
      from bsr(1) obtain F' G' where inv: "LLL_invariant A state'' F' G'" by auto
      from bsr(2) have "(state'' ,state) \<in> measure LLL_measure" by (auto simp: state)
      from IH[OF this inv] b res state show ?thesis by auto
    next
      case False
      define G1 where Gr: "G1 = of_list_repr Fr1" 
      note inv = inv[unfolded LLL_invariant_def split Gr[symmetric] Let_def]
      from False res have state': "state' = (i, Fr1, Gr1)" by simp
      from False inv have i: "i = m" unfolding LLL_invariants_def by auto
      show ?thesis using 1(2) unfolding state' state i by auto
    qed
  qed
qed

context fixes F
  assumes \<alpha>: "\<alpha> \<ge> 4/3" 
    and lin_dep: "gs.lin_indpt_list (RAT F)" 
    and len: "length F = m" 
    and L: "lattice_of F = L" 
begin

lemma initial_state: assumes "initial_state n F = state" 
  and A: "A = max_list (map (nat o sq_norm) F)" 
shows "\<exists> F' G'. LLL_invariant A state F' G'" 
proof -
  let ?F = "RAT F"
  define Fr0::f_repr where "Fr0 = ([], F)"
  have FrF: "RAT (snd Fr0) = ?F" unfolding Fr0_def by auto
  from lin_dep 
  have F: "set F \<subseteq> carrier_vec n" 
    unfolding gs.lin_indpt_list_def by auto
  have repr: "f_repr 0 Fr0 F" unfolding list_repr_def Fr0_def by auto
  obtain G where gs: "snd (gram_schmidt_int n F) = G" (is "snd ?gs = G") by force
  from gram_schmidt.mn[OF lin_dep _ gs[unfolded gram_schmidt_int_def gram_schmidt_wit_def]] len
  have mn: "m \<le> n" by auto
  have G':"length (RAT F) = m" "m \<le> m" "m \<le> n" 
    "set ?F \<subseteq> carrier_vec n" using F len mn by auto 
  define Gr0 where "Gr0 = gram_schmidt_triv n (RAT F)"
  let ?Gr0 = "([], Gr0)" 
  have RAT_carr:"set (RAT F) \<subseteq> Rn" using F len by auto
  have take: "RAT F = take m (RAT F)" using len by auto
  from gram_schmidt.partial_connect[OF G' 
      gs[unfolded gram_schmidt_int_def gram_schmidt_wit_def] take RAT_carr]
  have gso_init:"Gr0 = map (\<lambda> x. (x, sq_norm x)) (map (GSO F) [0..<m])"
    and GG: "G = map (gs.gso (RAT F)) [0..<m]" 
    unfolding Gr0_def FrF GSO_def gram_schmidt_triv using len by auto
  from gram_schmidt_int_connect[OF lin_dep gs len]
  have gso0: "g_repr 0 ?Gr0 F" unfolding gso_init g_repr_def list_repr_def gs by auto
  have short: "g_bound A G \<and> f_bound A F" unfolding g_bound_def f_bound_def
  proof (intro allI impI conjI)
    fix i
    assume i: "i < m" 
    let ?N = "map (nat o sq_norm) F"
    let ?r = rat_of_int
    from i have mem: "nat (sq_norm (F ! i)) \<in> set ?N" using G'(1) unfolding set_conv_nth by force
    from mem_set_imp_le_max_list[OF _ mem]
    have FA: "nat (sq_norm (F ! i)) \<le> A" unfolding A by force
    hence "\<parallel>F ! i\<parallel>\<^sup>2 \<le> int A" using i by auto
    also have "\<dots> \<le> int (A * m)" using i by fastforce
    finally show "\<parallel>F ! i\<parallel>\<^sup>2 \<le> int (A * m)" .
    from FA have "rat_of_nat (nat (sq_norm (F ! i))) \<le> rat_of_nat A" by simp
    also have "rat_of_nat (nat (sq_norm (F ! i))) = ?r (sq_norm (F ! i))" 
      using sq_norm_vec_ge_0[of "F ! i"] by auto
    also have "\<dots> = sq_norm (RAT F ! i)" unfolding sq_norm_of_int[symmetric] using G' i by auto
    finally have "sq_norm (RAT F ! i) \<le> rat_of_nat A" .
    with gs.sq_norm_gso_le_f[OF lin_dep G'(1) refl i]
    have "\<parallel>gs.gso (RAT F) i\<parallel>\<^sup>2 \<le> rat_of_nat A" by simp
    also have "gs.gso (RAT F) i = G ! i" unfolding GG using i by auto
    finally show "\<parallel>G ! i\<parallel>\<^sup>2 \<le> rat_of_nat A" .
  qed
  have "LLL_invariant A (0, Fr0, ?Gr0) F G"
    by (rule LLL_invI[OF repr gso0 gs L _ _ _ lin_dep], auto simp:gs.weakly_reduced_def 
        gs.reduced_def len short)
  also have "(0, Fr0, ?Gr0) = state" unfolding assms(1)[symmetric] initial_state_def Let_def
    Fr0_def Gr0_def ..
  finally show ?thesis by blast
qed


lemma basis_reduction_state: assumes "basis_reduction_state n \<alpha> F = state" 
  and A: "A = max_list (map (nat o sq_norm) F)" 
  shows "\<exists>F' G'. LLL_invariant A state F' G' \<and> fst state = m" 
proof -
  let ?state = "initial_state n F" 
  from initial_state[OF refl A]
  obtain F' G' where inv: "LLL_invariant A ?state F' G'" by auto
  from assms(1)[unfolded basis_reduction_state_def len]
  have res: "basis_reduction_main \<alpha> m ?state = state" .
  from basis_reduction_main[OF inv res \<alpha>] show ?thesis by blast
qed

lemma reduce_basis: assumes res: "reduce_basis n \<alpha> F = (F', G')" 
  shows "lattice_of F' = L" (is ?g1)
  "gs.reduced \<alpha> m G' (gs.\<mu> (RAT F'))" (is ?g2)
  "G' = gram_schmidt n (RAT F')" (is ?g3)
  "gs.lin_indpt_list (RAT F')" (is ?g4)
  "length F' = m" (is ?g5)
proof -  
  obtain i Fr Gr where 1: "basis_reduction_state n \<alpha> F = (i, Fr, Gr)" (is "?main = _") 
    by (cases ?main) auto
  from basis_reduction_state[OF 1 refl] obtain F1 G1 A
    where Linv: "LLL_invariant A (i, Fr, Gr) F1 G1" 
     and i_n: "i = m" by auto
  hence Lpinv: "LLL_partial_invariant A (i, Fr, Gr) F1 G1" unfolding LLL_invariant_def by auto
  from res[unfolded reduce_basis_def 1] have R: "F' = of_list_repr Fr" 
    and Rs: "G' = map fst (of_list_repr Gr)" by auto
  note inv = LLL_invD[OF Linv]
  from inv(1) R have RH: "F' = F1" unfolding of_list_repr_def by auto
  with inv have Hs: "G1 = snd (gram_schmidt_int n F')" by auto
  from inv(9)[unfolded g_repr_def] 
  have "list_repr i Gr (map (\<lambda>x. (x, \<parallel>x\<parallel>\<^sup>2)) (map (GSO F1) [0..<m]))" by auto
  from Rs[unfolded of_list_repr[OF this]] have Rs: "G' = map (GSO F1) [0..<m]" by (auto simp: o_def)
  also have "\<dots> = G1" unfolding LLL_connect[OF Lpinv] unfolding GSO_def by simp
  finally have RsHs: "G' = G1" by auto
  from RsHs inv(4,5,6,10,11) Rs R Hs RH i_n show ?g1 ?g2 ?g3 ?g4 ?g5 by (auto simp: snd_gram_schmidt_int)
qed
  
lemma short_vector: assumes "short_vector \<alpha> F = v" 
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"  
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)" 
  "v \<noteq> 0\<^sub>v j" 
proof -
  let ?L = "lattice_of F" 
  have a1: "\<alpha> \<ge> 1" using \<alpha> by auto 
  obtain F1 G1 where reduce: "reduce_basis n \<alpha> F = (F1, G1)" by force
  from reduce_basis[OF reduce] len have 
    L: "lattice_of F1 = L" 
    and red: "gs.weakly_reduced \<alpha> m G1" 
    and Gs: "G1 = gram_schmidt n (RAT F1)" 
    and basis: "gs.lin_indpt_list (RAT F1)" 
    and lenH: "length F1 = m" 
    and H: "set F1 \<subseteq> carrier_vec n" 
    by (auto simp: gs.lin_indpt_list_def gs.reduced_def)
  from lin_dep have G: "set F \<subseteq> carrier_vec n" unfolding gs.lin_indpt_list_def by auto
  with m0 len have "dim_vec (hd F) = n" by (cases F, auto)
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
end