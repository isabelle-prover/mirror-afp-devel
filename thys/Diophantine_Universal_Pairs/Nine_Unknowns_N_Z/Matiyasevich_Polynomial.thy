theory Matiyasevich_Polynomial
  imports M3_Polynomial Digit_Expansions.Binary_Operations Pi_to_M3_rat
begin

subsection \<open>The key property of $M_3$\<close>

context matiyasevich_polynomial
begin

(* The comments in the following lemma explain what the syntax abstraction
   used here means under the hood. *)
lemma relation_combining':
  fixes R S T A\<^sub>1 A\<^sub>2 A\<^sub>3 :: int
  assumes "S\<noteq>0"
  (* defines "\<gamma>' \<equiv> (\<lambda>n. (\<lambda>_. 0)(1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3, 4 := S, 5 := T, 6 := R, 11 := n))" *)
  defines "\<gamma>' \<equiv> \<lambda>(n :: int) fn. fn A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n :: int"
  (* shows "(S dvd T \<and> R > 0 \<and> is_square A\<^sub>1 \<and> is_square A\<^sub>2 \<and> is_square A\<^sub>3)
       = (\<exists>n. n\<ge>0 \<and> insertion (\<gamma>' n) M3_poly = 0)" (is "?LHS = ?RHS") *)
  shows "(S dvd T \<and> R > 0 \<and> is_square A\<^sub>1 \<and> is_square A\<^sub>2 \<and> is_square A\<^sub>3)
       = (\<exists>n. n\<ge>0 \<and> (\<gamma>' n) M3 = 0)" (is "?LHS = ?RHS")
proof -

  have U_not_0: "S^2 * (2*R - 1) \<noteq> 0"
    using \<open>S \<noteq> 0\<close> apply simp by presburger

  define \<phi> :: "nat \<Rightarrow> int mpoly" where
    "\<phi> = (\<lambda>_. 0)(0 := Var 0, 1 := Const A\<^sub>1, 2 := Const A\<^sub>2, 3 := Const A\<^sub>3)"
  define \<F> where "\<F> \<equiv> poly_subst \<phi> J3"
  define r where "r \<equiv> MPoly_Type.degree \<F> 0"
  define \<Pi> where "\<Pi> \<equiv> pi_relations.\<Pi> \<F> 0"

  define X where "X \<equiv> 1 + A\<^sub>1^2 + A\<^sub>2^2 + A\<^sub>3^2"
  define I where "I \<equiv> X^3"

  have F_repr: "\<F> = ((x^2+Const A\<^sub>1+Const A\<^sub>2*(Const X^2)-Const A\<^sub>3*(Const X^4))^2 + 4*x^2*Const A\<^sub>1
                      - 4*x^2*Const A\<^sub>2*Const X^2 - 4*Const A\<^sub>1*Const A\<^sub>2*Const X^2)^2
              - Const A\<^sub>1 * ((4*x*(x^2+Const A\<^sub>1+Const A\<^sub>2*Const X^2 - Const A\<^sub>3*Const X^4)
                              -  8*x*Const A\<^sub>2*Const X^2))^2"
    unfolding \<F>_def \<phi>_def J3_def X_def
    unfolding power2_eq_square power4_eq_xxxx section5_given.defs
    by (simp add: Const_add[symmetric] Const_mult[symmetric])

  have F_zeros_bound: "\<forall>x. insertion (\<lambda>_. x) \<F> = 0 \<longrightarrow> - I < x" 
  proof - 
    have aux0: "\<And>x. (\<lambda>_. 0::int)(0 := x, 1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3)
                     = insertion (\<lambda>_. x) \<circ> \<phi>"
      unfolding \<phi>_def by auto

    show ?thesis
      using J3_zeros_bound aux0[symmetric]
      unfolding \<F>_def I_def X_def insertion_poly_subst comp_def
      by simp
  qed

  have deg_phi: "MPoly_Type.degree (\<phi> i) 0 = (1 when i = 0)" for i
      unfolding \<phi>_def by simp

  have aux5: "MPoly_Type.degree P2 v2 \<le> k \<Longrightarrow>
      MPoly_Type.degree Q2 v2 \<le> k \<Longrightarrow> MPoly_Type.degree (Q2 + P2) v2 \<le> k" for k v2
    and P2 Q2 :: "int mpoly"
    by (simp add: le_trans[OF degree_add max.boundedI])

  have "r \<le> 8"
    unfolding r_def F_repr power2_eq_square
    apply (simp add: algebra_simps)
    apply (simp add: power2_eq_square[symmetric] power_Suc[symmetric] mult.assoc[symmetric])
    unfolding x_def Const_power Const_numeral[symmetric] mult.assoc Const_mult
    apply (rule le_trans[OF degree_diff max.boundedI])
    apply (rule aux5)+
    unfolding degree_Const apply simp_all
    apply (subst le_trans[OF degree_mult] le_trans[OF degree_pow]; simp)+
    apply (rule aux5)+
    unfolding degree_Const apply simp_all
    by (subst le_trans[OF degree_mult] le_trans[OF degree_pow]; simp)+

  have eq_coeff: "MPoly_Type.coeff \<F> (Poly_Mapping.single 0 8) = 1"
    unfolding F_repr power2_eq_square
    apply (simp add: algebra_simps)
    unfolding Notation.coeff_minus[symmetric] More_MPoly_Type.coeff_add[symmetric]
    apply (simp add: power2_eq_square[symmetric] power_Suc[symmetric] mult.assoc[symmetric])
    unfolding x_def
    apply (subst coeff_var_power_eq)
    apply (subst mult.assoc)+
    apply (subst coeff_var_power_le; simp)+
    unfolding Const_power Const_mult Const_numeral[symmetric]
    by (subst coeff_const; simp)+

  hence "MPoly_Type.degree \<F> 0 \<ge> 8"
    unfolding MPoly_Type.degree.rep_eq apply (intro Max_ge)
    subgoal by simp
    apply (rule insertI2)
    unfolding keys.rep_eq image_iff bex_simps(6) coeff_def
    apply (rule exI[of _ "Poly_Mapping.single 0 8"])
    by simp

  with \<open>r \<le> 8\<close> r_def have "r = 8" by auto
  
  interpret pi_relations: pi_relations \<F> 0
  proof (unfold_locales)
    show "vars \<F> \<subseteq> {0}"
      unfolding \<F>_def
      apply (rule subset_trans[OF vars_poly_subst[of \<phi> J3]])
      unfolding \<phi>_def
      using J3_vars by auto
  next
    have "MPoly_Type.coeff \<F> (Poly_Mapping.single 0 r) = 1"
      by (simp add: `r=8` eq_coeff)

    thus "MPoly_Type.coeff \<F> (Abs_poly_mapping (\<lambda>k. MPoly_Type.degree \<F> 0 when k = 0)) = 1"
      unfolding r_def single.abs_eq by simp
  qed

  define \<eta> :: "nat \<Rightarrow> nat \<Rightarrow> int" where "\<eta> \<equiv> \<lambda>n. (\<lambda>_. 0)(4:=S, 5:=T, 6:=R, 7:=I, 11:=n)"

  have insertion_F_squares:
    "(\<exists>x. insertion (\<lambda>_. x) \<F> = 0) = (is_square A\<^sub>1 \<and> is_square A\<^sub>2 \<and> is_square A\<^sub>3)"
  proof - 
    have insertion_equivalence: "insertion (\<lambda>_. x) \<circ> \<phi> 
                               = (\<lambda>_. 0)(0 := x, 1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3)" for x
        unfolding \<phi>_def comp_def by auto

    have "(\<exists>x. insertion (\<lambda>_. x) \<F> = 0)
        = (\<exists>y. insertion ((\<lambda>_. 0)(0 := y, 1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3)) J3 = 0)" (is "?F = ?J3")
    proof (rule iffI) 
      assume ?F
      then obtain x where x: "0 = insertion (\<lambda>_. x) (poly_subst \<phi> J3)"
        unfolding \<F>_def by auto

      hence "insertion (insertion (\<lambda>_. x) \<circ> \<phi>) J3 = 0"        
        using insertion_poly_subst[of "\<lambda>_. x" \<phi> J3] by auto

      with insertion_equivalence have 
        "insertion ((\<lambda>_. 0)(0 := x, 1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3)) J3 = 0"
        by auto 

      thus ?J3 by auto
    next 
      assume ?J3
      then obtain y where "insertion ((\<lambda>_. 0)(0 := y, 1 := A\<^sub>1, 2 := A\<^sub>2, 3 := A\<^sub>3)) J3 = 0"
        by auto

      hence "insertion (\<lambda>_. y) (poly_subst \<phi> J3) = 0"
        unfolding insertion_poly_subst insertion_equivalence by auto

      thus ?F unfolding \<F>_def by auto
    qed

    thus ?thesis
      unfolding J3_encodes_three_squares by auto
  qed

  hence M3_\<Pi>_equivalence: "insertion ((\<lambda>_. 0)(4:=S, 5:=T, 6:=R, 7:=I, 11:=n)) \<Pi>  
                          = M3 \<pi>" for n 
    unfolding \<Pi>_def I_def X_def
    using U\<^sub>0_def Pi_equals_M3_rationals[of A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R]
    using U_not_0
    unfolding U\<^sub>0_def X\<^sub>0_def
    using pi_relations.F_monom_over_v local.pi_relations.F_one
    unfolding \<F>_def \<phi>_def
    using \<open>r = 8\<close>
    unfolding r_def \<F>_def \<phi>_def
    by simp

  have direct_imp: "?LHS \<longrightarrow> ?RHS"
  proof
    assume asm: "?LHS"
    have "S dvd T" using asm by auto
    have "R > 0" using asm by auto
    have "\<exists>y. insertion (\<lambda>_. y) \<F> = 0"
      using insertion_F_squares asm by auto

    then obtain y where "insertion (\<lambda>_. y) \<F> = 0" by auto

    then obtain n where pi_result: "insertion (\<eta> n) \<Pi> = 0 
                                 \<and> int n = (2 * R - 1) * (y + I + T\<^sup>2) - (T div S)\<^sup>2"
      using pi_relations.\<Pi>_encodes_correctly[of S I T R, OF \<open>S \<noteq> 0\<close> F_zeros_bound \<open>S dvd T\<close> \<open>R > 0\<close>]
      unfolding \<eta>_def \<Pi>_def by auto

    show "?RHS" 
      apply (rule exI[of _ "int n"], simp)
      unfolding \<gamma>'_def
      unfolding M3_\<Pi>_equivalence[symmetric] 
      using pi_result unfolding \<eta>_def by auto
  qed
  
  have recipr_imp: "?RHS \<longrightarrow> ?LHS"
  proof (rule impI) 
    assume "?RHS"
    then obtain n where "n\<ge>0 \<and> M3 \<pi> = 0"
      unfolding \<gamma>'_def by auto

    hence "insertion (\<eta> (nat n)) \<Pi> = 0"
      unfolding \<eta>_def using M3_\<Pi>_equivalence by auto

    hence pi_relations: "S dvd T \<and> 0 < R \<and> (\<exists>x. insertion (\<lambda>_. x) \<F> = 0)"
      using pi_relations.\<Pi>_encodes_correctly_2[of S I T R, OF \<open>S \<noteq> 0\<close> F_zeros_bound]
      unfolding \<Pi>_def[symmetric] \<eta>_def by blast

    show "?LHS" using pi_relations insertion_F_squares by auto
  qed

  then show ?thesis using direct_imp by blast
qed

lemma relation_combining:
  assumes "S\<noteq>0"
  shows "(S dvd T \<and> R > 0 \<and> is_square A\<^sub>1 \<and> is_square A\<^sub>2 \<and> is_square A\<^sub>3)
         = (\<exists>n\<ge>0. M3 A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n = 0)"
  using relation_combining' assms by auto
end

end 
