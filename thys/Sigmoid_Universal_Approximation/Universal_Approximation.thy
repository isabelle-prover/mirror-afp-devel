section \<open>Universal Approximation Theorem\<close>

theory Universal_Approximation
  imports Asymptotic_Qualitative_Properties 
begin

text \<open>
  In this theory, we formalize the Universal Approximation Theorem (UAT)
  for continuous functions on a closed interval \([a,b]\).  The theorem
  states that any continuous function \(f\colon [a,b]\to \mathbb{R}\) can be
  uniformly approximated by a finite linear combination of shifted and
  scaled sigmoidal functions.  The classical result was first proved by
  Cybenko~\cite{Cybenko} and later constructively by Costarelli and Spigler~\cite{CostarelliSpigler},
  the latter approach forms the basis of our formalization.
  Their paper is available online at
  \url{https://link.springer.com/article/10.1007/s10231-013-0378-y}.
\<close>


lemma uniform_continuity_interval:
  fixes f :: "real \<Rightarrow> real"
  assumes "a < b"
  assumes "continuous_on {a..b} f"
  assumes  "\<epsilon> > 0"
shows "\<exists>\<delta>>0. (\<forall>x y. x \<in> {a..b} \<and> y \<in> {a..b} \<and> \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>f x - f y\<bar> < \<epsilon>)"
proof -
  have "uniformly_continuous_on {a..b} f"
    using assms(1,2) compact_uniformly_continuous by blast
  thus ?thesis
    unfolding uniformly_continuous_on_def
    by (metis assms(3) dist_real_def)
qed

definition bounded_function :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "bounded_function f \<longleftrightarrow> bdd_above (range (\<lambda>x. \<bar>f x\<bar>))"

definition unif_part :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real list" where
  "unif_part a b N =
     map (\<lambda>k. a + (real k -1 ) * ((b - a) / real N )) [0..<N+2]"

value "unif_part (0::real) 1 4"
(* Output: [-.25, 0,  0.25, 0.5, 0.75, 1] :: real list *)

theorem sigmoidal_approximation_theorem:
  assumes sigmoidal_function: "sigmoidal \<sigma>"                             (* \<sigma> is a sigmoidal*)
  assumes bounded_sigmoidal: "bounded_function \<sigma>"                       (* \<sigma> is a bounded*)
  assumes a_lt_b: "a < b"                                               (* a and b define a valid interval *)
  assumes contin_f: "continuous_on {a..b} f"                            (* f is continuous on the closed interval [a, b] *)
  assumes eps_pos: "0 < \<epsilon>"
  defines "xs N \<equiv> unif_part a b N"
  shows "\<exists>N::nat. \<exists>(w::real) > 0.(N > 0) \<and>
           (\<forall>x \<in> {a..b}. 
               \<bar>(\<Sum>k\<in>{2..N+1}. (f(xs N ! k) - f(xs N ! (k - 1))) * \<sigma>(w * (x - xs N ! k)))
                              + f(a) * \<sigma>(w * (x - xs N ! 0)) - f x\<bar> < \<epsilon>)"
proof-
  (* Define \<eta> based on \<epsilon>, supremum norms of f and \<sigma> *)
  obtain \<eta> where \<eta>_def: "\<eta> = \<epsilon> / ((Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})) + (2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))) + 2)"
    by blast

  have \<eta>_pos: "\<eta> > 0"
    unfolding \<eta>_def
  proof -
    have sup_abs_nonneg: "Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b}) \<ge> 0"
    proof -
      have "\<forall>x \<in> {a..b}. \<bar>f x\<bar> \<ge> 0"
        by simp
      hence "bdd_above ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})"
        by (metis a_lt_b bdd_above_Icc contin_f continuous_image_closed_interval continuous_on_rabs order_less_le)
      thus ?thesis
        by (meson a_lt_b abs_ge_zero atLeastAtMost_iff cSUP_upper2 order_le_less)
    qed

    have sup_\<sigma>_nonneg: "Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV) \<ge> 0"
    proof -
      have "\<forall>x \<in> {a..b}. \<bar>\<sigma> x\<bar> \<ge> 0"
        by simp
      hence "bdd_above ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)"
        using bounded_function_def bounded_sigmoidal by presburger
      thus ?thesis
        by (meson abs_ge_zero cSUP_upper2 iso_tuple_UNIV_I)
    qed

    obtain denom where denom_def: "denom = (Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})) + (2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))) + 2"
      by blast
    have denom_pos: "denom > 0"
    proof -
      have two_sup_\<sigma>_nonneg: "0 \<le> 2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))"
        by(rule mult_nonneg_nonneg, simp, simp add: sup_\<sigma>_nonneg)            
      have "0 \<le> (Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})) + 2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))"
        by(rule add_nonneg_nonneg, smt sup_abs_nonneg, smt two_sup_\<sigma>_nonneg)   
      then have "denom \<ge> 2" unfolding denom_def
        by linarith 
      thus "denom > 0" by linarith
    qed
    then show "0 < \<epsilon> / ((SUP x \<in> {a..b}. \<bar>f x\<bar>) + 2 * (SUP x \<in> UNIV . \<bar>\<sigma> x\<bar>) + 2)"
      using eps_pos sup_\<sigma>_nonneg sup_abs_nonneg by auto
  qed


  have "\<exists>\<delta>>0. \<forall>x y. x \<in> {a..b} \<and> y \<in> {a..b} \<and> \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>f x - f y\<bar> < \<eta>"
    by(rule uniform_continuity_interval,(simp add: assms(3,4))+, simp add: \<eta>_pos)
  then obtain \<delta> where \<delta>_pos: "\<delta> > 0"
    and \<delta>_prop: "\<forall>x \<in> {a..b}. \<forall>y \<in> {a..b}. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>f x - f y\<bar> < \<eta>"
    by blast  

  obtain N where N_def: "N = (nat (\<lfloor>max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>))\<rfloor>) + 1)"
    by simp


  have N_defining_properties: "N > 2 * (b - a) / \<delta> \<and> N > 3 \<and> N > 1 / \<eta>"
    unfolding N_def
  proof - 
    have "max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>)) \<ge> 2 * (b - a) / \<delta> \<and> 
          max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>)) \<ge> 2               \<and>
          max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>)) \<ge> 1 / \<eta>"
       unfolding max_def by simp
    then show "2 * (b - a) / \<delta> <  nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>))\<rfloor> + 1 \<and>
                                     3 < nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>))\<rfloor> + 1 \<and>
                          1 / \<eta> <  nat \<lfloor>max 3 (max (2 * (b - a) / \<delta>) (1 / \<eta>))\<rfloor> + 1"
      by (smt (verit, best) floor_le_one numeral_Bit1 numeral_less_real_of_nat_iff numeral_plus_numeral of_nat_1 of_nat_add of_nat_nat one_plus_numeral real_of_int_floor_add_one_gt)
  qed
  then have N_gt_3: "N > 3"
    by simp
  then have N_pos: "N > 0"
    by simp



  obtain h where h_def: "h = (b-a)/N"
    by simp
  then have h_pos: "h > 0"
    using N_defining_properties a_lt_b by force

  have h_lt_\<delta>_half: "h < \<delta> / 2"
  proof -
    have "N > 2 * (b - a) / \<delta>"
      using N_defining_properties by force
    then have "N /2 >  (b - a) / \<delta>"
      by (simp add: mult.commute)
    then have " (N /2) * \<delta> >  (b - a)"
      by (smt (verit, ccfv_SIG) \<delta>_pos divide_less_cancel nonzero_mult_div_cancel_right)
    then have " (\<delta> /2) * N >  (b - a)"
      by (simp add: mult.commute)
    then have " (\<delta> /2)  >  (b - a) / N"
      by (smt (verit, ccfv_SIG) \<delta>_pos a_lt_b divide_less_cancel nonzero_mult_div_cancel_right zero_less_divide_iff)
    then show "h < \<delta> / 2"
      using h_def by blast
  qed

  

  have one_over_N_lt_eta: "1 / N < \<eta>"
  proof -
  have f1: "real N \<ge> max (2 * (b - a) / \<delta> - 1) (1 / \<eta>)"
    unfolding N_def  by linarith  
  have "real N \<ge> 1 / \<eta>"
    unfolding max_def using f1 max.bounded_iff by blast 
  hence f2: "1 / real N \<le> \<eta>"
    using \<eta>_pos by (smt (verit, ccfv_SIG) divide_divide_eq_right le_divide_eq_1 mult.commute zero_less_divide_1_iff)
  then show "1 / real N < \<eta>"
    using N_defining_properties nle_le by fastforce
  qed




  have xs_eqs: "xs N = map (\<lambda>k. a +  (real k - 1) * ((b - a) /  N)) [0..<N+2]"
    using unif_part_def xs_def by presburger

    
  then have xs_els: "\<And>k. k \<in> {0..N+1} \<longrightarrow>  xs N ! k = a +  (real k-1) * h"
    by (metis (no_types, lifting) Suc_1 add_0 add_Suc_right atLeastAtMost_iff diff_zero h_def linorder_not_le not_less_eq_eq nth_map_upt)

  have zeroth_element: "xs N !0 = a-h"
    by (simp add: xs_els)                      
  have first_element: "xs N !1 = a"
    by (simp add: xs_els)                      
  have last_element: "xs N !(N+1) = b"
  proof - 
    have "xs N !(N+1) = a +  N * h"
      using xs_els by force
    then show ?thesis
      by (simp add: N_pos h_def)
  qed

  have difference_of_terms: "\<And>j k . j \<in> {1..N+1} \<and>  k \<in> {1..N+1} \<and> j\<le> k \<longrightarrow> xs N ! k - xs N ! j = h*(real k-j)"
  proof(clarify)
    fix j k
    assume j_type: "j \<in> {1..N + 1}"
    assume k_type: "k \<in> {1..N + 1}"
    assume j_leq_k: "j \<le> k"
    have j_th_el: "xs N ! j  = (a +  (real j-1) * h)"
      using j_type xs_els by auto
    have k_th_el: "xs N  ! k  = (a +  (real k-1) * h)"
      using k_type xs_els by auto
    then show "xs N ! k - xs N ! j = h * (real k - j)"
      by (smt (verit, del_insts) j_th_el left_diff_distrib' mult.commute)
  qed
  then have difference_of_adj_terms: "\<And>k .  k \<in> {1..N+1}  \<longrightarrow> xs N ! k - xs N ! (k-1) = h"
  proof -
    fix k :: nat
    have "k = 1 \<longrightarrow> k \<in> {1..N + 1} \<longrightarrow> xs N ! k - xs N ! (k - 1) = h"
      using first_element zeroth_element by auto
    then show "k \<in> {1..N + 1} \<longrightarrow> xs N ! k - xs N ! (k - 1) = h"
      using difference_of_terms le_diff_conv by fastforce
  qed
  have adj_terms_lt: "\<And>k .  k \<in> {1..N+1}  \<longrightarrow>  \<bar>xs N ! k - xs N ! (k - 1)\<bar> < \<delta>"
  proof(clarify)
    fix k 
    assume k_type: "k \<in> {1..N + 1}"
    then have "\<bar>xs N ! k - xs N ! (k - 1)\<bar> = h"
      using difference_of_adj_terms h_pos by auto
    also have "... < \<delta> /2"
      using h_lt_\<delta>_half by auto
    also have "... < \<delta>"
      by (simp add: \<delta>_pos)
    finally show "\<bar>xs N ! k - xs N  ! (k - 1)\<bar> < \<delta>".
  qed


  from difference_of_terms have list_increasing: "\<And>j k . j \<in> {1..N+1} \<and> k \<in> {1..N+1} \<and> j \<le> k \<longrightarrow>  xs N ! j \<le> xs N !k"
    by (smt (verit, ccfv_SIG) h_pos of_nat_eq_iff of_nat_mono zero_less_mult_iff)
  have els_in_ab: "\<And>k. k \<in> {1..N+1} \<longrightarrow> xs N ! k \<in> {a..b}"
    using first_element last_element list_increasing by force



  (* Apply Lemma 2.1 to xs N and h to aquire \<omega>. *)
  (* In the notes \<omega> is \overline{w} of "fix w \<ge> \overline{w}(1/N,h) \<equiv> \overline{w}(1/N) > 0, 
      where \overline{w}(1/N) is obtained by Lemma 2.1 with 1/N, h > 0 and with x_k..."*)
  from sigmoidal_function N_pos h_pos have "\<exists>\<omega> > 0. \<forall>w \<ge> \<omega>. \<forall>k < length (xs N).
             (\<forall>x. x - xs N !k \<ge> h   \<longrightarrow> \<bar>\<sigma> (w * (x - xs N !k)) - 1\<bar> < 1/N) \<and>
             (\<forall>x. x - xs N!k \<le> -h  \<longrightarrow> \<bar>\<sigma> (w * (x - xs N!k))\<bar> < 1/N)"
    by(subst sigmoidal_uniform_approximation, simp_all)    
  then obtain \<omega> where \<omega>_pos: "\<omega> > 0"
    and \<omega>_prop: "\<forall>w \<ge> \<omega>. \<forall>k < length (xs N).
                   (\<forall>x. x - xs N !k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (x - xs N !k)) - 1\<bar> < 1/N) \<and>
                   (\<forall>x. x - xs N !k \<le> -h \<longrightarrow> \<bar>\<sigma> (w * (x - xs N!k))\<bar> < 1/N)"
    by blast
  then obtain w where w_def: "w \<ge> \<omega>" and w_prop: "\<forall>k < length (xs N).
                   (\<forall>x. x - xs N !k \<ge> h \<longrightarrow> \<bar>\<sigma> (w * (x - xs N !k)) - 1\<bar> < 1/N) \<and>
                   (\<forall>x. x - xs N !k \<le> -h \<longrightarrow> \<bar>\<sigma> (w * (x - xs N!k))\<bar> < 1/N)"
                  and w_pos: "w > 0"
    by auto

  

  (* Define G_Nf (Equation 2.2) *)  
  obtain G_Nf where G_Nf_def:
    "G_Nf \<equiv> (\<lambda>x. 
       (\<Sum>k\<in>{2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
       + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0)))"
    by blast


  (* Goal: Show G_Nf approximates f within \<epsilon> on [a..b] *)

  show "\<exists>N w. 0 < w \<and> 0 < N \<and> (\<forall>x\<in>{a..b}. \<bar>(\<Sum>k = 2..N + 1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) + f a * \<sigma> (w * (x - xs N ! 0)) - f x\<bar> < \<epsilon>)"
  proof (intro exI[where x=N] exI[where x=w] conjI allI impI insert w_pos N_pos xs_def, safe)
    fix  x::real
    assume x_in_ab: "x \<in> {a..b}"

   
    

    (*From the paper: Let x \<in> [a,b] be fixed and for some i \<in> {1, \<sqdot>\<sqdot>\<sqdot> , N }, such that x \<in> [ x_{i−1} ,x_i ]
     In our notation: ...................................................., such that x \<in> [ xs N!{i} ,xs_(i+1)]*)
  
    have "\<exists>i. i \<in> {1..N} \<and> x \<in> {xs N ! i .. xs N ! (i+1)}"
    proof -
      have intervals_cover: "{xs N ! 1 .. xs N ! (N+1)} \<subseteq> (\<Union>i\<in>{1..N}. {xs N! i .. xs N! (i+1)})"
      proof
        fix x::real
        assume x_def: "x \<in> {xs N! 1 .. xs N ! (N+1)}"
        then have lower_bound: "x \<ge> xs N ! 1" 
          by simp
        from x_def have upper_bound: "x \<le> xs N! (N+1)"
          by simp




        obtain j where j_def: "j = (GREATEST j. xs N ! j \<le> x \<and>  j \<in> {1..N+1})"
          by blast      
        have nonempty_definition: "{j \<in> {1..N+1}. xs N ! j \<le> x} \<noteq> {}"
          using lower_bound by force
        then have j_exists:"\<exists>j \<in> {1..N+1}. xs N ! j \<le> x"
          by blast
        then have j_bounds: "j \<in> {1..N+1}"
          by (smt (verit) GreatestI_nat  atLeastAtMost_iff j_def)
        have xs_j_leq_x: "xs N ! j \<le> x"
          by (smt (verit, del_insts) GreatestI_ex_nat GreatestI_nat atLeastAtMost_iff ex_least_nat_le j_def j_exists)

        show "x \<in> (\<Union>i \<in> {1..N}. {xs N ! i..xs N ! (i + 1)})"
        proof(cases "j = N+1")
          show "j = N + 1 \<Longrightarrow> x \<in> (\<Union>i \<in> {1..N}. {xs N ! i..xs N ! (i + 1)})"
            using N_pos els_in_ab last_element upper_bound xs_j_leq_x by force
        next
          assume j_not_SucN:"j \<noteq> N + 1"
          then have j_type: "j \<in> {1..N}"
            by (metis Suc_eq_plus1 atLeastAtMost_iff j_bounds le_Suc_eq)
          then have Suc_j_type: "j + 1 \<in> {2..N+1}"
            by (metis Suc_1 Suc_eq_plus1 atLeastAtMost_iff diff_Suc_Suc diff_is_0_eq)
          have equal_sets: "{j \<in> {1..N+1}. xs N ! j \<le> x} = {j \<in> {1..N}. xs N ! j \<le> x}"
          proof 
            show "{j \<in> {1..N}. xs N ! j \<le> x} \<subseteq> {j \<in> {1..N + 1}. xs N ! j \<le> x}"
              by auto
            show "{j \<in> {1..N + 1}. xs N ! j \<le> x} \<subseteq> {j \<in> {1..N}. xs N ! j \<le> x}"
              by (safe, metis (no_types, lifting) Greatest_equality Suc_eq_plus1 j_not_SucN atLeastAtMost_iff j_def le_Suc_eq)
          qed

          have xs_j1_not_le_x: "\<not> (xs N ! (j+1) \<le> x)"
          proof(rule ccontr)
            assume BWOC: "\<not> \<not> xs N ! (j + 1) \<le> x"
            then have Suc_j_type':"j+1 \<in> {1..N}"   (*This is not a mistake, by using the previous line BWOC we can conclude this, but in fact j+1 could be N+1.*)
              using Suc_j_type equal_sets add.commute by auto         
            from j_def show False
                using equal_sets  
                by (smt (verit, del_insts) BWOC Greatest_le_nat One_nat_def Suc_eq_plus1 Suc_j_type' Suc_n_not_le_n  atLeastAtMost_iff mem_Collect_eq)
          qed
          then have "x \<in> {xs N ! j .. xs N ! (j+1)}"
            by (simp add: xs_j_leq_x)
          then show ?thesis
            using j_type by blast
        qed
      qed
      then show ?thesis
        using first_element last_element x_in_ab by fastforce
    qed               
    then obtain i where i_def: "i \<in> {1..N} \<and> x \<in> {xs N ! i .. xs N ! (i+1)}"
      by blast
    then have i_ge_1: "i \<ge> 1"
      using atLeastAtMost_iff by blast

    have i_leq_N: "i \<le> N"
      using i_def by presburger
    then have xs_i: "xs N ! i = a + (real i - 1) * h"
      using xs_els by force
    have xs_Suc_i: "xs N ! (i + 1) = a + real i * h"
    proof - 
      have "(i+1) \<in> {0..N+1} \<longrightarrow> xs N ! (i+1) = a + (real (i+1) - 1) * h"
        using xs_els by blast
      then show ?thesis
        using i_leq_N by fastforce
    qed

    from i_def have x_lower_bound_aux: "x \<ge>  (xs N ! i)"
      using atLeastAtMost_iff by blast
    then have x_lower_bound: "x \<ge> a + real (i-1) * h"
      by (metis xs_i i_ge_1 of_nat_1 of_nat_diff)

    from i_def have x_upper_bound_aux: "xs N! (i+1) \<ge>  x"
      using atLeastAtMost_iff by blast
    then have x_upper_bound: "a + real i * h \<ge> x"
      using xs_Suc_i by fastforce


    (* General definition of L(i) := L_i for all i \<ge> 1 *)
    obtain L where L_def:
    "\<And>i. L i = (if i = 1 \<or> i = 2 then 
                  (\<lambda>x. f(a) + (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3)) +
                              (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))) 
                else 
                  (\<lambda>x. (\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1)))) + f(a) +
                       (f (xs N ! i) - f (xs N ! (i-1))) * \<sigma> (w * (x - xs N ! i)) +
                       (f (xs N ! (i+1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i+1)))))"
      by force

    (* Define I_1(x) as the difference between G_Nf and L_i *)
    obtain I_1 where I_1_def: "\<And>i.1 \<le> i \<and> i \<le> N \<longrightarrow> I_1 i =  (\<lambda>x. \<bar>G_Nf x - L i x\<bar>)"
      by force

    (* Define I_2(x) as the difference between L_i and f *)
    obtain I_2 where I_2_def: "\<And>i. 1 \<le> i \<and> i \<le> N \<longrightarrow> I_2 i = (\<lambda>x. \<bar>L i x - f x\<bar>)"
      by force

    have triange_inequality_main: "\<And>i x. 1 \<le> i \<and> i \<le> N \<longrightarrow> \<bar>G_Nf x - f x\<bar> \<le> I_1 i x + I_2 i x"
      using I_1_def I_2_def by force

    (*Before we can bound I1, we need to first satisfy the assumptions of Lemma 2.1*)
    
    (*Show that x -   x_k    \<ge> h for k \<in> {-1,..,i-2} 
i.e.  Show that x -   xs N!k   \<ge> h for k \<in> { 0,...,i-1} *)

      
    have x_minus_xk_ge_h_on_Left_Half:
      "\<forall>k. k \<in> {0..i-1} \<longrightarrow> x - xs N ! k \<ge> h"
    proof (clarify)
      fix k
      assume k_def: "k \<in> {0..i-1}"
      then have k_pred_lt_i_pred: "real k- 1 < real i-1"
        using i_ge_1 by fastforce
      have "x - xs N!k = x - (a + (real k - 1) * h)"
      proof(cases "k=0")
        show "k = 0 \<Longrightarrow> x - xs N ! k = x - (a + (real k - 1) * h)"
          by (simp add: zeroth_element) 
      next
        assume k_nonzero: "k \<noteq> 0"
        then have k_def2: "k \<in> {1..N+1}"
          using i_def k_def less_diff_conv2 by auto
        then have "x - xs N ! k = x - (a + (real k - 1) * h)"
          by (simp add: xs_els)
        then show ?thesis
          using k_nonzero by force
      qed
      also have "... \<ge> h"
      proof(cases "k=0")
        show "k = 0 \<Longrightarrow> h \<le> x - (a + (real k - 1) * h)"
          using x_in_ab by force
      next
        assume k_nonzero: "k \<noteq> 0" 
        then have k_type: "k \<in> {1..N}"
          using i_leq_N k_def by fastforce
        have difference_of_terms: "(xs N!i) - (a+(real k - 1)*h) = ((real i-1) - (real k-1))*h"
          by (simp add: xs_i left_diff_distrib')
        then have first_inequality: "x - (a + (real k - 1) * h) \<ge> (xs N!i) - (a+(real k - 1)*h)"
          using i_def by auto
        have second_inequality: "(xs N!i) - (a+(real k - 1)*h) \<ge> h"
          using difference_of_terms h_pos k_def k_nonzero by force
        then show ?thesis
          using first_inequality by auto
      qed
      finally show "h \<le> x - xs N ! k".
    qed

            
    (* Show that x - xs_k \<le> -h for k \<in> {i+1..N} 
       Show that x - xs N!k \<le> -h for k \<in> {i+2..N+1} *)
    have x_minus_xk_le_neg_h_on_Right_Half:
      "\<forall>k. k \<in> {i+2..N+1} \<longrightarrow> x - xs N ! k \<le> -h"
    proof (clarify)
      fix k
      assume k_def: "k \<in> {i+2..N+1}"
      then have i_lt_k_pred: "i < k-1"
        by (metis Suc_1 add_Suc_right atLeastAtMost_iff less_diff_conv less_eq_Suc_le)
      then have k_nonzero: "k \<noteq> 0"
        by linarith
      from i_lt_k_pred have i_minus_k_pred_leq_Minus_One: "i - real (k - 1) \<le> -1"
        by simp
      have "x - xs N!k = x - (a + (real k - 1) * h)"
      proof-
        have k_def2: "k \<in> {1..N+1}"
          using i_def k_def less_diff_conv2 by auto
        then have "x - xs N ! k = x - (a + (real k - 1) * h)"
          using xs_els by force
        then show ?thesis
          using i_lt_k_pred by force
      qed
      also have "... \<le> -h"
      proof -       
        have x_upper_limit: "(xs N!(i+1)) = (a+(real i)*h)"
          using i_def xs_els by fastforce
        then have difference_of_terms: "(xs N!(i+1)) - (a+(real k - 1)*h) = ((real i) - (real k-1))*h"
          by (smt (verit, ccfv_threshold) diff_is_0_eq i_lt_k_pred left_diff_distrib' nat_less_real_le nle_le of_nat_1 of_nat_diff of_nat_le_0_iff)
        then have first_inequality: "x - (a + (real k - 1) * h) \<le> (xs N!(i+1)) - (a+(real k - 1)*h)"
          using i_def by fastforce
        have second_inequality: "(xs N!(i+1)) - (a+(real k - 1)*h) \<le> -h"
          by (metis diff_is_0_eq' difference_of_terms h_pos i_lt_k_pred i_minus_k_pred_leq_Minus_One linorder_not_le mult.left_commute mult.right_neutral mult_minus1_right nle_le not_less_zero of_nat_1 of_nat_diff ordered_comm_semiring_class.comm_mult_left_mono)
        then show ?thesis
          by (smt (z3) combine_common_factor difference_of_terms first_inequality x_upper_limit)
      qed
      finally show "x - xs N ! k \<le> -h".
    qed

    
    have I1_final_bound: "I_1 i x < (1+ (Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b}))) * \<eta>"
    proof - 
      (*Decompose I_1 into summation terms: the first step of the centered equation after the statement:
      "by conditions 1 and 2 of Lemma 2.1, it follows that..."*)
   
      have I1_decomp: 
    "I_1 i x \<le> (\<Sum>k\<in>{2..i-1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>)
              + \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar>
              + (\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
      proof (cases "i < 3")
        assume i_lt_3: "i < 3"
        then have i_is_1_or_2: "i = 1 \<or> i = 2"
          using i_ge_1 by linarith
        then have empty_summation:
            "(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) = 0"
          by fastforce
        have Lix: "L i x = f(a) + (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3)) + (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))"
          using L_def i_is_1_or_2 by presburger
        have "I_1 i x = \<bar>G_Nf x - L i x\<bar>"
          by (meson I_1_def i_ge_1 i_leq_N)
        also have "... = \<bar>(\<Sum>k\<in>{2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
                                                              + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0))
                                                                                         - f(a)
                                               - (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3)) 
                                               - (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))\<bar>"
          by (simp add: G_Nf_def Lix)
        also have " ... = \<bar>(\<Sum>k\<in>{3..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
                                                              + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0))
                                                                                         - f(a)
                                               - (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3))\<bar>"
        proof - 
          from N_pos have "(\<Sum>k\<in>{2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) = 
                                (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))  +
                (\<Sum>k\<in>{3..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))"
            by(subst sum.atLeast_Suc_atMost, auto)
          then show ?thesis
            by linarith
        qed
        also have "... = \<bar>(\<Sum>k\<in>{4..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
                                                              + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0))
                                                                                         - f(a)\<bar>"
        proof - 
          from N_gt_3 have "(\<Sum>k\<in>{3..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) = 
                                (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3))  +
                (\<Sum>k\<in>{4..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))"
            by(subst sum.atLeast_Suc_atMost, simp_all)
          then show ?thesis
            by linarith
        qed
        also have "... = \<bar>(\<Sum>k\<in>{4..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
                                                              + f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
        proof -
          have "\<forall>real1 real2 real3. (real1::real) + real2 * real3 - real2 = real1 + real2 * (real3 - 1)"
            by (simp add: right_diff_distrib')
          then show ?thesis
            using first_element by presburger
        qed
        also have "... \<le> \<bar>(\<Sum>k\<in>{4..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))\<bar>
                                                              + \<bar>f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
          by linarith
        also have "... \<le> (\<Sum>k\<in>{4..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
          using add_mono by blast
        also have "... = (\<Sum>k\<in>{4..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a)\<bar> * \<bar>(\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
          by (simp add: abs_mult)
        also have "... \<le> (\<Sum>k\<in>{i+2..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a)\<bar> * \<bar>(\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
        proof(cases "i=1")
          assume i_is_1: "i = 1"
          have union: "{i+2} \<union> {4..N+1} =  {i+2..N+1}"
          proof(safe)
            show "\<And>n. i + 2 \<in> {i+2..N + 1}"
              using N_gt_3 i_is_1 by presburger
            show "\<And>n. n \<in> {4..N + 1} \<Longrightarrow> n \<in> {i+2..N + 1}"
              using i_is_1 by auto
            show  "\<And>n. n \<in> {i+2..N + 1} \<Longrightarrow> n \<notin> {4..N + 1} \<Longrightarrow> n \<notin> {} \<Longrightarrow> n = i + 2"
              using i_is_1 by presburger
          qed
          have "(\<Sum>k\<in>{4..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a)\<bar> * \<bar>(\<sigma> (w * (x - xs N ! 0)) - 1)\<bar> \<le>
                (\<Sum>k\<in>{i+2}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                               +
                (\<Sum>k\<in>{4..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a)\<bar> * \<bar>(\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
            by auto
          also have "... = (\<Sum>k\<in>{i+2..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                                                              + \<bar>f (a)\<bar> * \<bar>(\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>"
          proof - 
            have "(\<Sum>k\<in>{i+2}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) +
                  (\<Sum>k\<in>{4..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) =
                  (\<Sum>k\<in>({i+2} \<union> {4..N+1}). \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
              by (subst sum.union_disjoint, simp_all, simp add: i_is_1)
            then show ?thesis
              using union by presburger
          qed
          finally show ?thesis.
        next
          show "i \<noteq> 1 \<Longrightarrow>
                  (\<Sum>k = 4..N + 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) + \<bar>f a\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar>
                \<le> (\<Sum>k = i + 2..N + 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) + \<bar>f a\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar>"
            using i_is_1_or_2 by auto           
        qed
        finally show ?thesis
          using empty_summation by linarith
      next  
        assume main_case: "\<not> i < 3"
        then have three_leq_i: "i \<ge> 3"
          by simp
        have disjoint: "{2..i-1} \<inter> {i..N+1} = {}"
          by auto

        have union: "{2..i-1} \<union> {i..N+1} = {2..N+1}"
        proof(safe)
          show "\<And>n. n \<in> {2..i - 1} \<Longrightarrow> n \<in> {2..N+1}"
            using i_leq_N by force
          show "\<And>n. n\<in> {i..N + 1} \<Longrightarrow> n \<in> {2..N + 1}"
            using three_leq_i by force
          show "\<And>n. n \<in> {2..N + 1} \<Longrightarrow> n  \<notin> {i..N + 1} \<Longrightarrow> n \<in> {2..i - 1}"
            by (metis Nat.le_diff_conv2 Suc_eq_plus1 atLeastAtMost_iff i_ge_1 not_less_eq_eq)   
        qed


        have sum_of_terms: "(\<Sum>k\<in>{2..i-1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) +
                            (\<Sum>k\<in>{i..N+1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) = 
                             (\<Sum>k\<in>{2..N+1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))"
          using sum.union_disjoint by (smt (verit, ccfv_threshold) disjoint union finite_atLeastAtMost)
  

        have "I_1 i x = \<bar>G_Nf x - L i x\<bar>"
          using I_1_def i_ge_1 i_leq_N by presburger
        also have "... = \<bar>G_Nf x - ((\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1)))) + f(a) +
                       (f (xs N ! i) - f (xs N ! (i-1))) * \<sigma> (w * (x - xs N ! i)) +
                       (f (xs N ! (i+1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i+1))))\<bar>"
          by (smt (verit, ccfv_SIG) main_case L_def less_add_one nat_1_add_1 numeral_Bit1 numeral_le_iff numerals(1) semiring_norm(70) three_leq_i)
        also have "... = \<bar>(\<Sum>k\<in>{2..i-1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) +
                          (\<Sum>k\<in>{i..N+1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))  + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0)) - 
                          (\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) ) - f(a) -  (f (xs N ! i) - f (xs N ! (i - 1)))* \<sigma> (w * (x - xs N ! i)) -
                                                                                     (f (xs N ! (i+1)) - f (xs N ! i))* \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          by (smt (verit, ccfv_SIG) G_Nf_def sum_mono sum_of_terms)

        also have "... = \<bar>((\<Sum>k\<in>{2..i-1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))
                         -(\<Sum>k\<in>{2..i-1}.   (f (xs N ! k) - f (xs N ! (k - 1))) ))+
                          (\<Sum>k\<in>{i..N+1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))  + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0))
                          - f(a) -  (f (xs N ! i) - f (xs N ! (i - 1)))* \<sigma> (w * (x - xs N ! i)) -
                           (f (xs N ! (i+1)) - f (xs N ! i))* \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          by linarith
        also have "... = \<bar>(\<Sum>k\<in>{2..i-1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))
                                          -(f (xs N ! k) - f (xs N ! (k - 1))) )+
                          (\<Sum>k\<in>{i..N+1}.   (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))  + f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0))
      - f(a) -  (f (xs N ! (i)) - f (xs N ! (i - 1)))* \<sigma> (w * (x - xs N ! (i))) -
                 (f (xs N ! (i+1)) - f (xs N ! (i)))* \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          by (simp add: sum_subtractf)
        also have "... = \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) +
                  (\<Sum>k\<in>{i..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) +
                  f (xs N ! 1) * \<sigma> (w * (x - xs N ! 0)) -
                  f(a) -
                  (f (xs N ! (i)) - f (xs N ! (i - 1))) * \<sigma> (w * (x - xs N ! (i))) -
                  (f (xs N ! (i+1)) - f (xs N ! (i))) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          by (simp add: right_diff_distrib')
        also have "... = \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) +
                  (\<Sum>k\<in>{i..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) +
                  f (a) * \<sigma> (w * (x - xs N ! 0)) -
                  f(a) -
                  (f (xs N ! (i)) - f (xs N ! (i - 1))) * \<sigma> (w * (x - xs N ! (i))) -
                  (f (xs N ! (i+1)) - f (xs N ! (i))) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          using first_element by fastforce
        also have "... = \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) +
          (\<Sum>k\<in>{i..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) +
          f (a) * (\<sigma> (w * (x - xs N ! 0)) -1)          
         -(f (xs N ! (i)) - f (xs N ! (i - 1))) * \<sigma> (w * (x - xs N ! (i))) 
         -(f (xs N ! (i+1)) - f (xs N ! (i))) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
          by (simp add: add_diff_eq right_diff_distrib')
        also have "...= \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) +
                  f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1) +
                  (\<Sum>k\<in>{i+1..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))                 
                 - (f (xs N ! (i+1)) - f (xs N ! (i ))) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
        proof - 
          from i_leq_N have "(\<Sum>k\<in>{i..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) = 
                (f (xs N ! (i)) - f (xs N ! (i - 1))) * \<sigma> (w * (x - xs N ! (i))) +
                (\<Sum>k\<in>{i+1..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))"
            by(subst sum.atLeast_Suc_atMost, linarith, auto)
          then show ?thesis
            by linarith
        qed
        also have "...= \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) +
                          f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1) +
                         (\<Sum>k\<in>{i+2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))\<bar>"
        proof - 
          from i_leq_N have "(\<Sum>k\<in>{i+1..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) = 
                (f (xs N ! (i+1)) - f (xs N ! (i))) * \<sigma> (w * (x - xs N ! (i+1))) +
                (\<Sum>k\<in>{i+2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))"
            by(subst sum.atLeast_Suc_atMost, linarith, auto)
          then show ?thesis
            by linarith
        qed
        show ?thesis
        proof - 
          have inequality_pair: "\<bar>\<Sum>n = 2..i - 1. (f (xs N ! n) - f (xs N ! (n - 1))) * (\<sigma> (w * (x - xs N ! n)) - 1)\<bar> \<le> 
                                  (\<Sum>n = 2..i - 1. \<bar>(f (xs N ! n) - f (xs N ! (n - 1))) * (\<sigma> (w * (x - xs N ! n)) - 1)\<bar>) \<and> 
                                  \<bar>f a * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar> + \<bar>\<Sum>n = i + 2..N + 1. (f (xs N ! n) - f (xs N ! (n - 1))) * \<sigma> (w * (x - xs N ! n))\<bar> 
                               \<le> \<bar>f a * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar> + (\<Sum>n = i + 2..N + 1. \<bar>(f (xs N ! n) - f (xs N ! (n - 1))) * \<sigma> (w * (x - xs N ! n))\<bar>)"
            using add_le_cancel_left by blast
          have "I_1 i x = \<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) + 
                                                         f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1) + 
                           (\<Sum>k = i + 2..N+1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))\<bar>"
            using \<open>\<bar>(\<Sum>k = 2..i - 1. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) + f a * (\<sigma> (w * (x - xs N ! 0)) - 1) + (\<Sum>k = i + 1..N + 1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) - (f (xs N ! (i + 1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i + 1)))\<bar> = \<bar>(\<Sum>k = 2..i - 1. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)) + f a * (\<sigma> (w * (x - xs N ! 0)) - 1) + (\<Sum>k = i + 2..N + 1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))\<bar>\<close> 
                calculation by presburger           
          also have "... \<le>\<bar>(\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1))\<bar>
                        + \<bar>f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>
                         +\<bar>(\<Sum>k\<in>{i+2..N+1}. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k)))\<bar>"
            by linarith
          also have "...\<le> (\<Sum>k\<in>{2..i-1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)\<bar>)
                        + \<bar>f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar>
                         + (\<Sum>k\<in>{i+2..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))\<bar>)"
            using inequality_pair by linarith
          also have "...\<le> (\<Sum>k\<in>{2..i-1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>(\<sigma> (w * (x - xs N ! k)) - 1)\<bar>)
                        + \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar>
                         + (\<Sum>k\<in>{i+2..N+1}. \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
          proof - 
            have f1: "\<And>k. k \<in> {2..i-1} \<longrightarrow> \<bar>(f (xs N ! k) - f (xs N ! (k - 1))) * (\<sigma> (w * (x - xs N ! k)) - 1)\<bar>  \<le> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>"
              by (simp add: abs_mult)
            have f2: "\<And>k. k \<in> {i+2..N+1} \<longrightarrow>  \<bar>(f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))\<bar> \<le> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>"
              by (simp add: abs_mult)
            have f3: "\<bar>f (a) * (\<sigma> (w * (x - xs N ! 0)) - 1)\<bar> = \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar>"
              using abs_mult by blast
            then show ?thesis
              by (smt (verit, best) f1 f2 sum_mono)
          qed
          finally show ?thesis.
        qed
      qed
      also have "... <  (\<Sum>k\<in>{2..i-1}. \<eta> * (1/N)) +
                         \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> +
                        (\<Sum>k\<in>{i+2..N+1}. \<eta> *  (1/N))"
      proof(cases "i \<ge> 3")
        assume i_geq_3: "3 \<le> i"
        show "(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) + \<bar>f a\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> +
              (\<Sum>k = i + 2..N + 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
            < (\<Sum>k = 2..i - 1. \<eta> * (1 /  N)) + \<bar>f a\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> + 
              (\<Sum>k = i + 2..N + 1. \<eta> * (1 /  N))"        
        proof(cases "\<forall>k. k \<in> {2..i-1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar> = 0")
          assume all_terms_zero: "\<forall>k. k \<in> {2..i - 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar> = 0"
          from i_geq_3 have "(\<Sum>k\<in>{2..i-1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>)  < (\<Sum>k\<in>{2..i-1}. \<eta> * (1/N))"
            by (subst sum_strict_mono, force+, (simp add: N_pos \<eta>_pos all_terms_zero)+)
          show ?thesis
          proof(cases "i = N")
            assume "i = N"
            then show ?thesis
              using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 /  N))\<close> by auto
          next
            assume "i \<noteq> N"
            then have i_lt_N: "i < N"
              using i_leq_N le_neq_implies_less by blast
            show ?thesis
            proof(cases "\<forall>k. k \<in> {i+2..N+1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0")
              assume all_second_terms_zero: "\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = (0::real)"
              from i_lt_N have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1/N))"
                by(subst sum_strict_mono, force+, (simp add: \<eta>_pos all_second_terms_zero)+)
              then show ?thesis
              proof -
                show ?thesis
                  using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 / N))\<close> 
                        \<open>(\<Sum>k = i + 2..N + 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < (\<Sum>k = i + 2..N + 1. \<eta> * (1 /  N))\<close> by linarith                  
                qed
            next
              assume second_terms_not_all_zero: "\<not> (\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0)"
              obtain NonZeroTerms where NonZeroTerms_def: "NonZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> \<noteq> 0}"
                by blast
              obtain ZeroTerms where ZeroTerms_def: "ZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0}"
                by blast
              have zero_terms_eq_zero: "(\<Sum>k \<in> ZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 0"
                by (simp add: ZeroTerms_def)
              have disjoint: "ZeroTerms \<inter> NonZeroTerms = {}"
                using NonZeroTerms_def ZeroTerms_def by blast
              have union: "ZeroTerms \<union> NonZeroTerms = {i+2..N+1}"
              proof(safe)
                show "\<And>n. n \<in> ZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using ZeroTerms_def by force
                show "\<And>n. n \<in> NonZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using NonZeroTerms_def by blast
                show "\<And>n. n \<in> {i + 2..N + 1} \<Longrightarrow> n \<notin> NonZeroTerms \<Longrightarrow> n \<in> ZeroTerms"
                  using NonZeroTerms_def ZeroTerms_def by blast
              qed  
                
              have "(\<Sum>k\<in>{i+2..N+1}.   \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < 
                    (\<Sum>k\<in>{i+2..N+1}. \<eta> * ((1::real) / real N))"
              proof - 
                have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                    (\<Sum>k\<in>NonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)" 
                 proof -     
                  have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                        (\<Sum>k\<in>ZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                     + (\<Sum>k\<in>NonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
                    by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)
                  then show ?thesis
                    using zero_terms_eq_zero by linarith
                qed
                also have "... < (\<Sum>k\<in>NonZeroTerms. \<eta> * (1 /  N))"
                proof(rule sum_strict_mono)
                  show "finite NonZeroTerms"
                    by (metis finite_Un finite_atLeastAtMost union)
                  show "NonZeroTerms \<noteq> {}"
                    using NonZeroTerms_def second_terms_not_all_zero by blast
                  fix y 
                  assume y_subtype: "y \<in> NonZeroTerms"
                  then have y_type: "y \<in> {i+2..N+1}"
                    by (metis Un_iff union)
                  then have y_suptype: "y \<in> {1..N + 1}"
                    by simp 


                  have parts_lt_eta: "\<And>k. k\<in>{i+2..N+1} \<longrightarrow> \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> < \<eta>"
                  proof(clarify)
                    fix k 
                    assume k_type: "k \<in> {i + 2..N + 1}"
                    then have "k - 1  \<in> {i+1..N}"
                      by force
                    then have "\<bar>(xs N ! k) - (xs N ! (k - 1))\<bar> < \<delta> \<longrightarrow> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using \<delta>_prop atLeastAtMost_iff els_in_ab le_diff_conv by auto          
                    then show "\<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using adj_terms_lt i_leq_N k_type by fastforce
                  qed
                  then have f_diff_lt_eta: "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> < \<eta>"
                    using y_type by blast
                  have lt_minus_h: "x - xs N!y \<le> -h"
                    using x_minus_xk_le_neg_h_on_Right_Half y_type by blast
                  then have sigma_lt_inverseN: "\<bar>\<sigma> (w * (x - xs N ! y))\<bar>  <  1 / N"
                  proof -
                    have "\<not> Suc N < y"
                      using y_suptype by force
                    then show ?thesis
                      by (smt (z3) Suc_1 Suc_eq_plus1 lt_minus_h add.commute add.left_commute diff_zero length_map length_upt not_less_eq w_prop xs_eqs)
                  qed
                 

                  show "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! y))\<bar> < \<eta> * (1 / N)"
                    using f_diff_lt_eta mult_strict_mono sigma_lt_inverseN by fastforce
                qed
                also have "... \<le> (\<Sum>k\<in>NonZeroTerms. \<eta> * (1 /  N)) +  (\<Sum>k\<in>ZeroTerms. \<eta> * (1 / N))"
                  using \<eta>_pos by force
                also have "... = (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1 /  N))"
                  by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)               
                finally show ?thesis.
              qed
              then show ?thesis
                using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 / N))\<close> by linarith
            qed
          qed
        next
          (*Now we will assume that the terms at the bottom (Bot) can be nonzero as well!*)
          assume first_terms_not_all_zero: "\<not> (\<forall>k. k \<in> {2..i - 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar> = 0)"
          obtain BotNonZeroTerms where BotNonZeroTerms_def: "BotNonZeroTerms = {k \<in> {2..i - 1}. \<bar>\<sigma> (w * (x - xs N ! k))  - 1\<bar> \<noteq> 0}"
            by blast
          obtain BotZeroTerms where BotZeroTerms_def: "BotZeroTerms = {k \<in> {2..i - 1}. \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar> = 0}"
            by blast
          have bot_zero_terms_eq_zero: "(\<Sum>k \<in> BotZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) -1\<bar>) = 0"
            by (simp add: BotZeroTerms_def)
          have bot_disjoint: "BotZeroTerms \<inter> BotNonZeroTerms = {}"
            using BotNonZeroTerms_def BotZeroTerms_def by blast

          have bot_union: "BotZeroTerms \<union> BotNonZeroTerms = {2..i - 1}"
          proof(safe)
            show "\<And>n. n \<in> BotZeroTerms \<Longrightarrow> n \<in> {2..i - 1}"
              using BotZeroTerms_def by force
            show "\<And>n. n \<in> BotNonZeroTerms \<Longrightarrow> n \<in> {2..i - 1}"
              using BotNonZeroTerms_def by blast
            show "\<And>n. n \<in> {2..i - 1} \<Longrightarrow> n \<notin> BotNonZeroTerms \<Longrightarrow> n \<in> BotZeroTerms"
              using BotNonZeroTerms_def BotZeroTerms_def by blast
          qed  

          have "(\<Sum>k\<in>{2..i - 1}.   \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) -1\<bar>) < 
                    (\<Sum>k\<in>{2..i - 1}. \<eta> * (1 / N))"
          proof - 
            have disjoint_sum: "sum (\<lambda>k. \<eta> * (1 /  N)) BotNonZeroTerms + sum (\<lambda>k. \<eta> * (1 /  N)) BotZeroTerms = sum (\<lambda>k. \<eta> * (1 /  N)) {2..i - 1}"
            proof - 
               from bot_disjoint have "sum (\<lambda>k. \<eta> * (1 / real N)) BotNonZeroTerms + sum (\<lambda>k. \<eta> * (1 /  N)) BotZeroTerms =
                  sum (\<lambda>k. \<eta> * (1 / real N)) (BotNonZeroTerms \<union> BotZeroTerms)"
                 by(subst sum.union_disjoint, (metis(mono_tags) bot_union finite_Un finite_atLeastAtMost)+, auto) 
               then show ?thesis
                 by (metis add.commute bot_disjoint bot_union finite_Un finite_atLeastAtMost sum.union_disjoint)
             qed

            
            have "(\<Sum>k\<in>{2..i - 1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) = 
                (\<Sum>k\<in>BotNonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>)" 
             proof -     
              have "(\<Sum>k\<in>{2..i - 1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) -1\<bar>) = 
                    (\<Sum>k\<in>BotZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) -1\<bar>)
                 + (\<Sum>k\<in>BotNonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) -1\<bar>)"
                by (smt bot_disjoint finite_Un finite_atLeastAtMost bot_union sum.union_disjoint)
              then show ?thesis
                using bot_zero_terms_eq_zero by linarith
            qed
            also have "... < (\<Sum>k\<in>BotNonZeroTerms. \<eta> * (1 / N))"
            proof(rule sum_strict_mono)
              show "finite BotNonZeroTerms"
                by (metis finite_Un finite_atLeastAtMost bot_union)
              show "BotNonZeroTerms \<noteq> {}"
                using BotNonZeroTerms_def first_terms_not_all_zero by blast
              fix y
              assume y_subtype: "y \<in> BotNonZeroTerms"
              then have y_type: "y \<in> {2..i - 1}"
                by (metis Un_iff bot_union)
              then have y_suptype: "y \<in> {1..N + 1}"
                using i_leq_N by force
              have parts_lt_eta: "\<And>k. k\<in>{2..i - 1} \<longrightarrow> \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> < \<eta>"
              proof(clarify)
                fix k 
                assume k_type: "k \<in> {2..i - 1}"
                then have "\<bar>(xs N ! k) - (xs N ! (k - 1))\<bar> < \<delta> \<longrightarrow> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                  by (metis \<delta>_prop add.commute add_le_imp_le_diff atLeastAtMost_iff diff_le_self dual_order.trans els_in_ab i_leq_N nat_1_add_1 trans_le_add2)
                then show "\<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                  using adj_terms_lt i_leq_N k_type by fastforce
              qed
              then have f_diff_lt_eta: "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> < \<eta>"
                using y_type by blast
              have lt_minus_h: "x - xs N!y \<ge> h"
                using x_minus_xk_ge_h_on_Left_Half y_type by force
              then have bot_sigma_lt_inverseN: "\<bar>\<sigma> (w * (x - xs N ! y)) -1 \<bar>  <  (1 /  N)"
                by (smt (z3) Suc_eq_plus1 add_2_eq_Suc' atLeastAtMost_iff diff_zero length_map length_upt less_Suc_eq_le w_prop xs_eqs y_suptype)
              then show "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! y)) - 1\<bar> < \<eta> * (1 /  N)"
                by (smt (verit, del_insts) f_diff_lt_eta mult_strict_mono)

            qed
            also have "... \<le> (\<Sum>k\<in>BotNonZeroTerms. \<eta> * (1 / N)) +  (\<Sum>k\<in>BotZeroTerms. \<eta> * (1 / N))"
              using \<eta>_pos by force
            also have "... = (\<Sum>k\<in>{2..i - 1}. \<eta> * (1 / N))"
              using sum.union_disjoint disjoint_sum by force
            finally show ?thesis.
          qed
        
          show ?thesis
          proof(cases "i = N")
            assume "i = N"
            then show ?thesis
              using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 / N))\<close> by auto              
          next
            assume "i \<noteq> N"
            then have i_lt_N: "i < N"
              using i_leq_N le_neq_implies_less by blast
            show ?thesis
            proof(cases "\<forall>k. k \<in> {i+2..N+1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0")
              assume all_second_terms_zero: "\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0"
              from i_lt_N have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1/N))"
                by (subst sum_strict_mono, fastforce+, (simp add: \<eta>_pos all_second_terms_zero)+)
              then show ?thesis
                using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 / N))\<close> by linarith
            next
              (*This is, in a sense, the most "normal" case to consider because we're assuming i is not an edge  case (i\<notin>{1,2,N}) and that neither the top nor bottom sum is identically zero!*)
              assume second_terms_not_all_zero: "\<not> (\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0)"
              obtain TopNonZeroTerms where TopNonZeroTerms_def: "TopNonZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> \<noteq> 0}"
                by blast
              obtain TopZeroTerms where TopZeroTerms_def: "TopZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0}"
                by blast
              have zero_terms_eq_zero: "(\<Sum>k\<in>TopZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 0"
                by (simp add: TopZeroTerms_def)
              have disjoint: "TopZeroTerms \<inter> TopNonZeroTerms = {}"
                using TopNonZeroTerms_def TopZeroTerms_def by blast
              have union: "TopZeroTerms \<union> TopNonZeroTerms = {i+2..N+1}"
              proof(safe)
                show "\<And>n. n \<in> TopZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using TopZeroTerms_def by force
                show "\<And>n. n \<in> TopNonZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using TopNonZeroTerms_def by blast
                show "\<And>n. n \<in> {i + 2..N + 1} \<Longrightarrow> n \<notin> TopNonZeroTerms \<Longrightarrow> n \<in> TopZeroTerms"
                  using TopNonZeroTerms_def TopZeroTerms_def by blast
              qed  
            
              have "(\<Sum>k\<in>{i+2..N+1}.   \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < 
                    (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1 / N))"
              proof - 
                have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                    (\<Sum>k\<in>TopNonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)" 
                 proof -     
                  have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                        (\<Sum>k\<in>TopZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                     + (\<Sum>k\<in>TopNonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
                    by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)
                  then show ?thesis
                    using zero_terms_eq_zero by linarith
                qed
                also have "... < (\<Sum>k\<in>TopNonZeroTerms. \<eta> * (1 / N))"
                proof(rule sum_strict_mono)
                  show "finite TopNonZeroTerms"
                    by (metis finite_Un finite_atLeastAtMost union)
                  show "TopNonZeroTerms \<noteq> {}"
                    using TopNonZeroTerms_def second_terms_not_all_zero by blast
                  fix y 
                  assume y_subtype: "y \<in> TopNonZeroTerms"
                  then have y_type: "y \<in> {i+2..N+1}"
                    by (metis Un_iff union)
                  then have y_suptype: "y \<in> {1..N + 1}"
                    by simp 
                  have parts_lt_eta: "\<And>k. k\<in>{i+2..N+1} \<longrightarrow> \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> < \<eta>"
                  proof(clarify)
                    fix k 
                    assume k_type: "k \<in> {i + 2..N + 1}"
                    then have "k - 1  \<in> {i+1..N}"
                      by force
                    then have "\<bar>(xs N ! k) - (xs N ! (k - 1))\<bar> < \<delta> \<longrightarrow> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using \<delta>_prop atLeastAtMost_iff els_in_ab le_diff_conv by auto          
                    then show "\<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using adj_terms_lt i_leq_N k_type by fastforce
                  qed
                  then have f_diff_lt_eta: "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> < \<eta>"
                    using y_type by blast
                  have lt_minus_h: "x - xs N!y \<le> -h"
                    using x_minus_xk_le_neg_h_on_Right_Half y_type by blast
                  then have sigma_lt_inverseN: "\<bar>\<sigma> (w * (x - xs N ! y))\<bar>  <  1 / N"
                  proof -
                    have "\<not> Suc N < y"
                      using y_suptype by force
                    then show ?thesis
                      by (smt (z3) Suc_1 Suc_eq_plus1 lt_minus_h add.commute add.left_commute diff_zero length_map length_upt not_less_eq w_prop xs_eqs)
                  qed             
                  then show "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! y))\<bar> < \<eta> * (1 / N)"
                    by (smt (verit, best) f_diff_lt_eta mult_strict_mono)
                qed             
                also have "... \<le> (\<Sum>k\<in>TopNonZeroTerms. \<eta> * (1 / N)) +  (\<Sum>k\<in>TopZeroTerms. \<eta> * (1 / N))"
                  using \<eta>_pos by force
                also have "... = (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1 / N))"
                  by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)               
                finally show ?thesis.
              qed
              then show ?thesis
                using \<open>(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) < (\<Sum>k = 2..i - 1. \<eta> * (1 / N))\<close> by linarith                
            qed
          qed
        qed
      next
        assume "\<not> 3 \<le> i"
        then have i_leq_2: "i \<le> 2"
          by linarith
        then have first_empty_sum: "(\<Sum>k = 2..i - 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k)) - 1\<bar>) = 0"
          by force
        from i_leq_2 have second_empty_sum: "(\<Sum>k = 2..i - 1. \<eta> * (1 / N)) = 0"
          by force
        have i_lt_N: "i < N"
          using N_defining_properties i_leq_2 by linarith
    

        have "(\<Sum>k = i + 2..N + 1. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < 
              (\<Sum>k = i + 2..N + 1. \<eta> * (1 / N))"
        proof(cases "\<forall>k. k \<in> {i+2..N+1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0")
              assume all_second_terms_zero: "\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0"
              from i_lt_N have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1/N))"
                by (subst sum_strict_mono, fastforce+, (simp add: \<eta>_pos all_second_terms_zero)+)
              then show ?thesis.
            next
              assume second_terms_not_all_zero: "\<not> (\<forall>k. k \<in> {i + 2..N + 1} \<longrightarrow> \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0)"
              obtain NonZeroTerms where NonZeroTerms_def: "NonZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> \<noteq> 0}"
                by blast
              obtain ZeroTerms where ZeroTerms_def: "ZeroTerms = {k \<in> {i + 2..N + 1}. \<bar>\<sigma> (w * (x - xs N ! k))\<bar> = 0}"
                by blast
              have zero_terms_eq_zero: "(\<Sum>k\<in>ZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 0"
                by (simp add: ZeroTerms_def)
              have disjoint: "ZeroTerms \<inter> NonZeroTerms = {}"
                using NonZeroTerms_def ZeroTerms_def by blast
              have union: "ZeroTerms \<union> NonZeroTerms = {i+2..N+1}"
              proof(safe)
                show "\<And>n. n \<in> ZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using ZeroTerms_def by force
                show "\<And>n. n \<in> NonZeroTerms \<Longrightarrow> n \<in> {i + 2..N + 1}"
                  using NonZeroTerms_def by blast
                show "\<And>n. n \<in> {i + 2..N + 1} \<Longrightarrow> n \<notin> NonZeroTerms \<Longrightarrow> n \<in> ZeroTerms"
                  using NonZeroTerms_def ZeroTerms_def by blast
              qed  

   
              
              have "(\<Sum>k\<in>{i+2..N+1}.   \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) < 
                    (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1 / N))"
              proof - 
                have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                    (\<Sum>k\<in>NonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)" 
                proof -     
                  have "(\<Sum>k\<in>{i+2..N+1}. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>) = 
                        (\<Sum>k\<in>ZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)
                     + (\<Sum>k\<in>NonZeroTerms. \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! k))\<bar>)"
                    by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)
                  then show ?thesis
                    using zero_terms_eq_zero by linarith
                qed
                also have "... < (\<Sum>k\<in>NonZeroTerms. \<eta> * (1 / N))"
                proof(rule sum_strict_mono)
                  show "finite NonZeroTerms"
                    by (metis finite_Un finite_atLeastAtMost union)
                  show "NonZeroTerms \<noteq> {}"
                    using NonZeroTerms_def second_terms_not_all_zero by blast
                  fix y 
                  assume y_subtype: "y \<in> NonZeroTerms"
                  then have y_type: "y \<in> {i+2..N+1}"
                    by (metis Un_iff union)
                  then have y_suptype: "y \<in> {1..N + 1}"
                    by simp 

                  have parts_lt_eta: "\<And>k. k\<in>{i+2..N+1} \<longrightarrow> \<bar>(f (xs N ! k) - f (xs N ! (k - 1)))\<bar> < \<eta>"
                  proof(clarify)
                    fix k 
                    assume k_type: "k \<in> {i + 2..N + 1}"
                    then have "k - 1  \<in> {i+1..N}"
                      by force
                    then have "\<bar>(xs N ! k) - (xs N ! (k - 1))\<bar> < \<delta> \<longrightarrow> \<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using \<delta>_prop atLeastAtMost_iff els_in_ab le_diff_conv by auto          
                    then show "\<bar>f (xs N ! k) - f (xs N ! (k - 1))\<bar> < \<eta>"
                      using adj_terms_lt i_leq_N k_type by fastforce
                  qed
                  then have f_diff_lt_eta: "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> < \<eta>"
                    using y_type by blast
                  have lt_minus_h: "x - xs N!y \<le> -h"
                    using x_minus_xk_le_neg_h_on_Right_Half y_type by blast
                  then have sigma_lt_inverseN: "\<bar>\<sigma> (w * (x - xs N ! y))\<bar>  < 1 / N"
                  proof -
                    have "\<not> Suc N < y"
                      using y_suptype by force
                    then show ?thesis
                      by (smt (z3) Suc_1 Suc_eq_plus1 lt_minus_h add.commute add.left_commute diff_zero length_map length_upt not_less_eq w_prop xs_eqs)
                  qed
              

                  show "\<bar>f (xs N ! y) - f (xs N ! (y - 1))\<bar> * \<bar>\<sigma> (w * (x - xs N ! y))\<bar> < \<eta> * (1 / N)"
                    using f_diff_lt_eta mult_strict_mono sigma_lt_inverseN by fastforce
                qed
                also have "... \<le> (\<Sum>k\<in>NonZeroTerms. \<eta> * (1 /  N)) +  (\<Sum>k\<in>ZeroTerms. \<eta> * (1 / N))"
                  using \<eta>_pos by force
                also have "... = (\<Sum>k\<in>{i+2..N+1}. \<eta> * (1 / N))"
                  by (smt disjoint finite_Un finite_atLeastAtMost union sum.union_disjoint)               
                finally show ?thesis.
              qed
              then show ?thesis.                
            qed
            then show ?thesis
              using first_empty_sum second_empty_sum by linarith
          qed
     
      also have "... = \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> + (\<Sum>k\<in>{2..i-1}. \<eta> * (1/N)) + (\<Sum>k\<in>{i+2..N+1}. \<eta> *  (1/N))"
        by simp
      also have "... \<le> \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> + (\<Sum>k\<in>{2..N+1}. \<eta> *  (1/N))"
      proof -       
        have "(\<Sum>k\<in>{2..i-1}. \<eta> * (1/N)) + (\<Sum>k\<in>{i+2..N+1}. \<eta> *  (1/N)) \<le>  (\<Sum>k\<in>{2..N+1}. \<eta> *  (1/N))"
        proof(cases "i\<ge> 3")
          assume "3 \<le> i"
          have disjoint: "{2..i-1} \<inter> {i+2..N+1} = {}"
            by auto
          from i_leq_N have subset: "{2..i-1} \<union> {i+2..N+1} \<subseteq> {2..N+1}"
            by auto
          have sum_union: "sum (\<lambda>k. \<eta> * (1 / N)) {2..i-1} + sum (\<lambda>k. \<eta> * (1 / N)) {i+2..N+1} =
                           sum (\<lambda>k. \<eta> * (1 / N)) ({2..i-1} \<union> {i+2..N+1})"
            by (metis disjoint finite_atLeastAtMost sum.union_disjoint)
          from subset \<eta>_pos have "sum (\<lambda>k. \<eta> * (1 / N)) ({2..i-1} \<union> {i+2..N+1}) \<le> sum (\<lambda>k. \<eta> * (1 / N)) {2..N+1}"
            by(subst sum_mono2, simp_all)          
          then show ?thesis
            using sum_union by auto
        next
          assume "\<not> 3 \<le> i"
          then have i_leq_2: "i \<le> 2"
            by linarith
          then have first_term_zero: "(\<Sum>k = 2..i - 1. \<eta> * (1 / N)) = 0"
            by force
          from \<eta>_pos have "(\<Sum>k = i + 2..N + 1. \<eta> * (1 / N)) \<le> (\<Sum>k = 2..N + 1. \<eta> * (1 / N))"
            by(subst sum_mono2, simp_all)            
          then show ?thesis
            using first_term_zero by linarith
        qed
        then show ?thesis
          by linarith
      qed
      also have "... = \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> + (N * \<eta> *  (1/N))"
      proof - 
        have "(\<Sum>k\<in>{2..N+1}. \<eta> *  (1/N)) = (N * \<eta> *  (1/N))"
          by(subst sum_constant, simp)
        then show ?thesis
          by presburger
      qed
      also have "... = \<bar>f (a)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> + \<eta>"
        by (simp add: N_pos)
      also have "... \<le> \<bar>f (a)\<bar> * (1/N) +  \<eta>" (*\<diamond>(f(a) = 0)*)
      proof - 
        have "\<bar>\<sigma> (w * (x - xs N ! 0)) - 1\<bar> < 1/N"
          by (smt (z3) Suc_eq_plus1_left \<omega>_prop add_2_eq_Suc' add_gr_0 atLeastAtMost_iff diff_zero 
              length_map length_upt w_def x_in_ab xs_eqs zero_less_one zeroth_element)
        then show ?thesis
          by (smt (verit, ccfv_SIG) mult_less_cancel_left)
      qed
      also have "... \<le> \<bar>f (a)\<bar> * \<eta> +  \<eta>"     (*\<diamond>(f(a) = 0)*)
        by (smt (verit, best) mult_left_mono one_over_N_lt_eta)  
      also have "... =  (1 +  \<bar>f (a)\<bar>) * \<eta>"
        by (simp add: distrib_right)
      also have "... \<le> (1+ (SUP x \<in> {a..b}. \<bar>f x\<bar>)) * \<eta>"
      proof - 
        from a_lt_b have "\<bar>f (a)\<bar> \<le> (SUP x \<in> {a..b}. \<bar>f x\<bar>)"
          by (subst cSUP_upper, simp_all, metis bdd_above_Icc contin_f continuous_image_closed_interval continuous_on_rabs order_less_le)
        then show ?thesis
          by (simp add: \<eta>_pos)
      qed
      finally show ?thesis.
    qed
        
    have x_i_pred_minus_x_lt_delta: "\<bar>xs N !(i-1) - x\<bar> < \<delta>"  (*"... and as [this is true], we can estimate I_2:"*)
    proof - 
      have "\<bar>xs N !(i-1) - x\<bar> \<le> \<bar>xs N !(i-1) - xs N!i\<bar> + \<bar>xs N!i - x\<bar>"
        by linarith
      also have "... \<le> 2*h"
      proof - 
        have first_inequality: "\<bar>xs N !(i-1) - xs N!i\<bar> \<le> h"
          using difference_of_adj_terms h_pos i_ge_1 i_leq_N by fastforce
        have second_inequality: "\<bar>xs N!i - x\<bar> \<le> h"
          by (smt (verit) left_diff_distrib' mult_cancel_right1 x_lower_bound_aux x_upper_bound_aux xs_Suc_i xs_i)
        show ?thesis
          using first_inequality second_inequality by fastforce
      qed
      also have "... < \<delta>"
        using h_lt_\<delta>_half by auto
      finally show ?thesis.
    qed
    have I2_final_bound: "I_2 i x < (2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)) + 1) * \<eta>"
    proof(cases "i \<ge> 3")
     assume three_lt_i: "3 \<le> i"
     have telescoping_sum: "sum (\<lambda>k. f (xs N ! k) - f (xs N ! (k - 1))) {2..i-1} + f a = f (xs N ! (i-1))"
     proof(cases "i = 3")
       show "i = 3 \<Longrightarrow> (\<Sum>k = 2..i - 1. f (xs N ! k) - f (xs N ! (k - 1))) + f a = f (xs N ! (i - 1))"
         using first_element by force
     next
       assume "i \<noteq> 3"
       then have i_gt_3: "i > 3"
         by (simp add: le_neq_implies_less three_lt_i)
       have "sum (\<lambda>k. f (xs N ! k) - f (xs N ! (k - 1))) {2..i-1} = f(xs N!(i-1)) - f(xs N!(2-1))"
       proof -
         have f1: "1 \<le> i - Suc 1"
           using three_lt_i by linarith
         have index_shift: "(\<Sum>k \<in> {2..i-1}. f (xs N ! (k - 1))) = (\<Sum>k \<in> {1..i-2}. f (xs N ! k))"
           by (rule sum.reindex_bij_witness[of _ "\<lambda>j. j +1" "\<lambda>j. j -1"], simp_all, presburger+)
         have "sum (\<lambda>k. f (xs N ! k) - f (xs N ! (k - 1))) {2..i-1} =
              (\<Sum>k \<in> {2..i-1}. f (xs N ! k)) - (\<Sum>k \<in> {2..i-1}. f (xs N ! (k - 1)))"
           by (simp add: sum_subtractf)
         also have "... = (\<Sum>k \<in> {2..i-1}. f (xs N ! k)) - (\<Sum>k \<in> {1..i-2}. f (xs N ! k))"
           using index_shift by presburger
         also have "... = (\<Sum>k \<in> {2..i-1}. f (xs N ! k)) - (f (xs N ! 1) + (\<Sum>k \<in> {2..i-2}. f (xs N ! k)))"
           using f1 by (metis (no_types) Suc_1 sum.atLeast_Suc_atMost)
         also have "... = ((\<Sum>k \<in> {2..i-1}. f (xs N ! k)) -   (\<Sum>k \<in> {2..i-2}. f (xs N ! k))) - f (xs N ! 1)"
           by linarith
         also have "... = (f (xs N ! (i-1)) + (\<Sum>k \<in> {2..i-2}. f (xs N ! k)) -   (\<Sum>k \<in> {2..i-2}. f (xs N ! k))) - f (xs N ! 1)"
         proof -           
           have disjoint: "{2..i-2} \<inter> {i-1} = {}"
             by force
           have union: "{2..i-2} \<union> {i-1} = {2..i-1}"
           proof(safe)
             show "\<And>n. n \<in> {2..i - 2} \<Longrightarrow> n \<in> {2..i - 1}"
               by fastforce
             show "\<And>n. i - 1 \<in> {2..i - 1}"
               using three_lt_i by force
             show "\<And>n. n \<in> {2..i - 1} \<Longrightarrow> n \<notin> {2..i - 2} \<Longrightarrow> n \<notin> {} \<Longrightarrow> n = i - 1"
               by presburger
           qed
           have "(\<Sum>k \<in> {2..i-2}. f (xs N ! k)) + f (xs N ! (i-1)) = (\<Sum>k \<in> {2..i-2}. f (xs N ! k)) + (\<Sum>k \<in> {i-1}. f (xs N ! k))"
             by auto
           also have "... = (\<Sum>k \<in> {2..i-2} \<union> {i-1}. f (xs N ! k))"
             using disjoint by force
           also have "... = (\<Sum>k \<in> {2..i-1}. f (xs N ! k))"
             using union by presburger
           finally show ?thesis
             by linarith
         qed
         also have "... = f (xs N ! (i-1)) - f (xs N ! 1)"
           by auto
         finally show ?thesis
           by simp
       qed
       then show ?thesis
         using first_element by auto
     qed

     have I2_decomp: "I_2 i x = \<bar>L i x - f x\<bar>"
        using I_2_def i_ge_1 i_leq_N by presburger
     also have "... = \<bar> (((\<Sum>k\<in>{2..i-1}. (f (xs N ! k) - f (xs N ! (k - 1)))) + f(a)) +
                       (f (xs N ! i) - f (xs N ! (i-1))) * \<sigma> (w * (x - xs N ! i)) +
                       (f (xs N ! (i+1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i+1)))) - f x\<bar>"
       using L_def three_lt_i by auto

     also have "... = \<bar> f (xs N ! (i-1)) - f x +
                       (f (xs N ! i) - f (xs N ! (i-1))) * \<sigma> (w * (x - xs N ! i)) +
                       (f (xs N ! (i+1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
       using telescoping_sum  by fastforce
     also have "... \<le> \<bar> f (xs N ! (i-1)) - f x\<bar> +
                       \<bar>(f (xs N ! i) - f (xs N ! (i-1))) * \<sigma> (w * (x - xs N ! i))\<bar> +
                       \<bar>(f (xs N ! (i+1)) - f (xs N ! i)) * \<sigma> (w * (x - xs N ! (i+1)))\<bar>"
       by linarith
     also have "... = \<bar> f (xs N ! (i-1)) - f x\<bar> +
                       \<bar>(f (xs N ! i) - f (xs N ! (i-1)))\<bar> * \<bar> \<sigma> (w * (x - xs N ! i))\<bar> +
                       \<bar>(f (xs N ! (i+1)) - f (xs N ! i))\<bar> * \<bar>\<sigma> (w * (x - xs N ! (i+1)))\<bar>"
       by (simp add: abs_mult)
     also have "... <  \<eta> +  \<eta> * \<bar> \<sigma> (w * (x - xs N ! i))\<bar> +  \<eta> * \<bar>\<sigma> (w * (x - xs N ! (i+1)))\<bar>"
     proof - 
       from x_in_ab x_i_pred_minus_x_lt_delta 
       have first_inequality: "\<bar>f (xs N ! (i-1)) - f x\<bar> < \<eta>"
         by(subst \<delta>_prop, 
           metis Suc_eq_plus1 add_0 add_le_imp_le_diff atLeastAtMost_iff els_in_ab i_leq_N less_imp_diff_less linorder_not_le numeral_3_eq_3 order_less_le three_lt_i,
           simp_all)
       from els_in_ab i_leq_N le_diff_conv three_lt_i  
       have second_inequality: "\<bar>(f (xs N ! i) - f (xs N ! (i-1)))\<bar> < \<eta>"
         by(subst \<delta>_prop,
              simp_all,
              metis One_nat_def add.commute atLeastAtMost_iff adj_terms_lt i_ge_1 trans_le_add2)
       have third_inequality: "\<bar>(f (xs N ! (i+1)) - f (xs N ! i))\<bar> < \<eta>"
       proof(subst \<delta>_prop)
         show "xs N ! (i + 1) \<in> {a..b}" and "xs N ! i \<in> {a..b}" and True
           using els_in_ab i_ge_1 i_leq_N by auto
         show "\<bar>xs N ! (i + 1) - xs N ! i\<bar> < \<delta>" 
           using adj_terms_lt
           by (metis Suc_eq_plus1 Suc_eq_plus1_left Suc_le_mono add_diff_cancel_left' atLeastAtMost_iff i_leq_N le_add2)
       qed
       then show ?thesis
         by (smt (verit, best) first_inequality mult_right_mono second_inequality)
     qed
     also have "... = (\<bar> \<sigma> (w * (x - xs N ! i))\<bar> +  \<bar>\<sigma> (w * (x - xs N ! (i+1)))\<bar> + 1) * \<eta>"
       by (simp add: mult.commute ring_class.ring_distribs(1))
     also have "... \<le> (2* (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)) + 1) * \<eta>"
     proof - 
       from bounded_sigmoidal have first_inequality: "\<bar> \<sigma> (w * (x - xs N ! i))\<bar> \<le> (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))"
         by (metis UNIV_I bounded_function_def cSUP_upper2 dual_order.refl)
         
       from bounded_sigmoidal have second_inequality: "\<bar> \<sigma> (w * (x - xs N ! (i+1)))\<bar> \<le> (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV))"
         unfolding bounded_function_def
         by (subst cSUP_upper, simp_all)
       then show ?thesis
         using \<eta>_pos first_inequality by auto
     qed
     finally show ?thesis.
    next
      assume "\<not> 3 \<le> i"
      then have i_is_1_or_2: "i = 1 \<or> i = 2"
        using i_ge_1 by linarith
      have x_near_a: "\<bar>a - x\<bar> < \<delta>"
      proof(cases "i = 1")
        show "i = 1 \<Longrightarrow> \<bar>a - x\<bar> < \<delta>"
          using first_element h_pos x_i_pred_minus_x_lt_delta x_lower_bound_aux zeroth_element by auto
        show "i \<noteq> 1 \<Longrightarrow> \<bar>a - x\<bar> < \<delta>"
          using first_element i_is_1_or_2 x_i_pred_minus_x_lt_delta by auto
      qed

      have Lix: "L i x = f(a) + (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3)) + (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))"
          using L_def i_is_1_or_2 by presburger
      have "I_2 i x = \<bar>L i x - f x\<bar>"
        using I_2_def i_ge_1 i_leq_N by presburger
      also have "... = \<bar>(f a - f x) + (f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3)) + (f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))\<bar>"
        using Lix by linarith
      also have "... \<le> \<bar>(f a - f x)\<bar> + \<bar>(f (xs N ! 3) - f (xs N ! 2)) * \<sigma> (w * (x - xs N ! 3))\<bar> + \<bar>(f (xs N ! 2) - f (xs N ! 1)) * \<sigma> (w * (x - xs N ! 2))\<bar>"
        by linarith
      also have "... \<le> \<bar>(f a - f x)\<bar> + \<bar>f (xs N ! 3) - f (xs N ! 2)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 3))\<bar> + \<bar>f (xs N ! 2) - f (xs N ! 1)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 2))\<bar>"
        by (simp add: abs_mult)
      also have "... <  \<eta> +  \<eta> * \<bar> \<sigma> (w * (x - xs N ! 3))\<bar> + \<bar>f (xs N ! 2) - f (xs N ! 1)\<bar> * \<bar>\<sigma> (w * (x - xs N ! 2))\<bar>"
      proof - 
        from x_in_ab x_near_a have first_inequality: "\<bar>f a - f x\<bar> < \<eta>"
          by(subst \<delta>_prop, auto)
        have second_inequality: "\<bar>f (xs N ! 3) - f (xs N ! 2)\<bar> < \<eta>"
        proof(subst \<delta>_prop, safe)
          show "xs N ! 3 \<in> {a..b}"
            using N_gt_3 els_in_ab by force
          show "xs N ! 2 \<in> {a..b}"
            using N_gt_3 els_in_ab by force
          from N_gt_3 have "xs N ! 3 - xs N ! 2 = h"
            by(subst xs_els, auto, smt (verit, best) h_pos i_is_1_or_2 mult_cancel_right1 nat_1_add_1 of_nat_1 of_nat_add xs_Suc_i xs_i)
          then show "\<bar>xs N ! 3 - xs N ! 2\<bar> < \<delta>"
            using adj_terms_lt first_element zeroth_element by fastforce
        qed
        then show ?thesis
          by (smt (verit, best) first_inequality mult_right_mono)
      qed
      also have "... \<le>  \<eta> +  \<eta> * \<bar> \<sigma> (w * (x - xs N ! 3))\<bar> + \<eta> * \<bar>\<sigma> (w * (x - xs N ! 2))\<bar>"  (*\<diamond>(\<bar>\<sigma> (w * (x - xs N ! 2))\<bar>=0)*)
      proof - 
        have third_inequality: "\<bar>f (xs N ! 2) - f (xs N ! 1)\<bar> < \<eta>"
        proof(subst \<delta>_prop, safe)
          show "xs N ! 2 \<in> {a..b}"
            using N_gt_3 els_in_ab by force
          show "xs N ! 1 \<in> {a..b}"
            using N_gt_3 els_in_ab by force
          from N_pos first_element have "xs N ! 2 - xs N ! 1 = h"
            by(subst xs_els, auto)
          then show "\<bar>xs N ! 2 - xs N ! 1\<bar> < \<delta>"
            using adj_terms_lt first_element zeroth_element by fastforce
        qed
        show ?thesis
          by (smt (verit, best) mult_right_mono third_inequality)
      qed
      also have "... = (\<bar> \<sigma> (w * (x - xs N ! 3))\<bar> + \<bar>\<sigma> (w * (x - xs N ! 2))\<bar> + 1)*\<eta>"
        by (simp add: mult.commute ring_class.ring_distribs(1))
      also have "... \<le> (2*(Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)) + 1) * \<eta>"  
      proof - 
        from bounded_sigmoidal have first_inequality: "\<bar> \<sigma> (w * (x - xs N ! 3))\<bar> \<le> Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)"
          unfolding bounded_function_def
          by (subst cSUP_upper, simp_all)
        from bounded_sigmoidal have second_inequality: "\<bar> \<sigma> (w * (x - xs N ! 2))\<bar> \<le> Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)"
          unfolding bounded_function_def
          by (subst cSUP_upper, simp_all)
        then show ?thesis
          using \<eta>_pos first_inequality by force
      qed
      finally show ?thesis.
    qed

    have "\<bar>(\<Sum>k = 2..N + 1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) + f a * \<sigma> (w * (x - xs N ! 0)) - f x\<bar> \<le> I_1 i x + I_2 i x"
      using G_Nf_def i_ge_1 i_leq_N triange_inequality_main first_element by blast
    also have "... < (1+ (Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b}))) * \<eta> + (2 * (Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)) + 1) * \<eta>"
      using I1_final_bound I2_final_bound by linarith
    also have "... = ((Sup ((\<lambda>x. \<bar>f x\<bar>) ` {a..b})) + 2*(Sup ((\<lambda>x. \<bar>\<sigma> x\<bar>) ` UNIV)) + 2)* \<eta>"
      by (simp add: distrib_right)
    also have "... = \<epsilon>"
      using \<eta>_def \<eta>_pos by force
    finally show "\<bar>(\<Sum>k = 2..N + 1. (f (xs N ! k) - f (xs N ! (k - 1))) * \<sigma> (w * (x - xs N ! k))) + f a * \<sigma> (w * (x - xs N ! 0)) - f x\<bar> < \<epsilon>".
  qed
qed
  
end