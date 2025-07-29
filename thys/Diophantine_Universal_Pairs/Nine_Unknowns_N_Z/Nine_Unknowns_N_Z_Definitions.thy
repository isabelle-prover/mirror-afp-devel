theory Nine_Unknowns_N_Z_Definitions
  imports "../Coding_Theorem/Coding_Theorem_Definitions" "../Bridge_Theorem/Bridge_Theorem_Imp"
    "M3_Polynomial" "../Coding/Suitable_For_Coding" "../MPoly_Utils/Poly_Degree"
    "HOL-Eisbach.Eisbach"
begin

section \<open>Nine Unknowns over $\mathbb{N}$ and $\mathbb{Z}$\<close>

subsection \<open>Combining all previous constructions\<close>

text \<open>For any appropriately typed function F, we introduce the syntax 
  \<open>fn \<tau> \<equiv> fn a f g h k l w x y n\<close>, as well as \<open>(\<lambda>\<tau>. e) \<equiv> (\<lambda>f a f g h k l w x y n. e)\<close>.\<close>

syntax "tau" :: "(int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int" ("_ \<tau>" [1000] 1000)
syntax "tau_fn" :: "(int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int" ("\<lambda>\<tau>. _" [0] 0)

parse_translation \<open>
  [
    (
      \<^syntax_const>\<open>tau\<close>,
      fn ctxt => fn args =>
        list_comb (
          args |> hd,
          ["a", "f", "g", "h", "k", "l", "w", "x", "y", "n"] |> map (fn name => Free (name, @{typ int}))
        )
    ),
    (
      \<^syntax_const>\<open>tau_fn\<close>,
      fn ctxt => fn args =>
        ["a", "f", "g", "h", "k", "l", "w", "x", "y", "n"]
          |> List.foldr (fn (name, r) => Abs (name, @{typ int}, r)) (args |> hd)
    )
  ]
\<close>


locale combined_variables =
  fixes P :: "int mpoly"
begin

text \<open>Copy of the polynomials from Theorem I\<close>


definition P\<^sub>1 :: "int mpoly" where 
  "P\<^sub>1 \<equiv> suitable_for_coding P"

abbreviation "\<delta> \<equiv> coding_variables.\<delta> P\<^sub>1"
abbreviation "\<nu> \<equiv> coding_variables.\<nu> P\<^sub>1"

definition b :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "b \<tau> = coding_variables.b a f"
definition X :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "X \<tau> = coding_variables.X P\<^sub>1 a f g"
definition Y :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "Y \<tau> = coding_variables.Y P\<^sub>1 a f"

poly_extract b

(* The following is the manual equivalent of poly_extract Y *)
definition Y_poly :: "int mpoly" where 
  "Y_poly \<equiv> coding_variables.Y_poly P\<^sub>1"
lemma Y_correct: "insertion f Y_poly =  Y (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)"
  unfolding Y_def coding_variables.Y_correct Y_poly_def by simp


(* The following is the manual equivalent of poly_extract X *)
definition X_poly :: "int mpoly" where 
  "X_poly \<equiv> coding_variables.X_poly P\<^sub>1"
lemma X_correct: "insertion f X_poly =  X (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)"
  unfolding X_def coding_variables.X_correct X_poly_def by simp


(* The following lemma uses an abbreviation, which does not work for use in literal facts. *) 
lemma \<delta>_gt0: "\<delta> > 0"
  unfolding coding_variables.\<delta>_def P\<^sub>1_def
  by (simp add: suitable_for_coding_total_degree)


text \<open>Polynomials from Theorem II\<close>

definition L :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "L \<tau> = bridge_variables.L l (Y \<tau>)"
definition U :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "U \<tau> = bridge_variables.U l (X \<tau>) (Y \<tau>)"
definition V :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "V \<tau> = bridge_variables.V w g (Y \<tau>)"
definition A :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "A \<tau> = bridge_variables.A l w g (Y \<tau>) (X \<tau>)"
definition C :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "C \<tau> = bridge_variables.C l w h g (Y \<tau>) (X \<tau>)"
definition D :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "D \<tau> = bridge_variables.D l w h g (Y \<tau>) (X \<tau>)"
definition F :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "F \<tau> = bridge_variables.F l w h x g (Y \<tau>) (X \<tau>)"
definition I :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "I \<tau> = bridge_variables.I l w h x y g (Y \<tau>) (X \<tau>)"
definition W :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "W \<tau> = bridge_variables.W w (coding_variables.b a f)"
definition K :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "K \<tau> = bridge_variables.K k l w g (Y \<tau>) (X \<tau>)"

poly_extract L
poly_extract U
poly_extract V
poly_extract A
poly_extract C
poly_extract D
poly_extract F
poly_extract I
poly_extract W
poly_extract K

text \<open>Variables in the proof of Theorem III\<close>

definition M3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "M3 A\<^sub>1 A\<^sub>2 A\<^sub>3 S T Q' m = insertion_list [A\<^sub>1, A\<^sub>2, A\<^sub>3, S, T, Q', m] section5.M3_poly"

(* This poly_extract just recovers M3_poly as section5.M3_poly, up to an
   identity substitution. *)
(* This construction does simplify the lemma on the maximum variable index just afterwards. *)
poly_extract M3

lemma max_vars_M3: "max_vars M3_poly \<le> 6"
  unfolding M3_poly_def
  using max_vars_id[of 6, unfolded upt_def]
  by auto

definition \<mu> :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "\<mu> \<tau> = (coding_variables.\<gamma> P\<^sub>1) * (b \<tau>) ^ (coding_variables.\<alpha> P\<^sub>1)"

poly_extract \<mu>

definition A\<^sub>1 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "A\<^sub>1 \<tau> = b \<tau>"
definition A\<^sub>2 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "A\<^sub>2 \<tau> = (D \<tau>) * (F \<tau>) * (I \<tau>)"
definition A\<^sub>3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "A\<^sub>3 \<tau> = ((U \<tau>) ^ 4 * (V \<tau>)\<^sup>2 - 4) * (K \<tau>)\<^sup>2 + 4"
definition S :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "S \<tau> = bridge_variables.S l w g (Y \<tau>) (X \<tau>)"
definition T :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "T \<tau> = bridge_variables.T l w h g (Y \<tau>) (X \<tau>) (b \<tau>)"
definition R :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "R \<tau> = f\<^sup>2 * l\<^sup>2 * x\<^sup>2 * (8 * (\<mu> \<tau>)^3 * g * (K \<tau>)\<^sup>2 - g\<^sup>2 * (32 * ((C \<tau>) - (K \<tau>) * (L \<tau>))^2 * (\<mu> \<tau>)^3 + g\<^sup>2 * (K \<tau>)\<^sup>2))"
definition m :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "m \<tau> = n"

poly_extract A\<^sub>1
poly_extract A\<^sub>2
poly_extract A\<^sub>3
poly_extract S
poly_extract T
poly_extract R
poly_extract m


definition \<sigma> :: "(int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "(\<sigma> fn) \<tau> = fn (A\<^sub>1 \<tau>) (A\<^sub>2 \<tau>) (A\<^sub>3 \<tau>) (S \<tau>) (T \<tau>) (R \<tau>) (m \<tau>)"

definition Q :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "Q \<tau> = M3 (A\<^sub>1 \<tau>) (A\<^sub>2 \<tau>) (A\<^sub>3 \<tau>) (S \<tau>) (T \<tau>) (R \<tau>) (m \<tau>)"

lemma M_poly_degree_correct: "total_degree (coding_variables.M_poly P\<^sub>1) \<le> (1+(\<delta>+1)^\<nu>) * 2*\<delta>"
  using \<delta>_gt0 coding_variables.M_poly_degree_correct by blast 

lemma D_poly_degree_correct: "total_degree (coding_variables.D_poly P\<^sub>1) \<le> (\<delta>+1)^(\<nu>+1) * (2*\<delta>)"
  using \<delta>_gt0 coding_variables.D_poly_degree_correct by blast 

lemma K_poly_degree_correct: "total_degree (coding_variables.K_poly P\<^sub>1)
  \<le> max (\<delta>*(1+2*\<delta>) + (\<delta>+1)^(\<nu>+1) * 2*\<delta>) ((1 + (2*\<delta>+1)*(\<delta>+1)^\<nu>) * 2*\<delta>)"
  using \<delta>_gt0 coding_variables.K_poly_degree_correct by blast 


(* Because the polynomial Q is too complicated, we introduced these fixed degree_correct lemmas. *)
poly_degree X_poly
poly_degree Y_poly

lemma X_poly_degree_alt: "X_poly_degree = 12 * \<delta> + 12 * \<delta> * Suc \<delta> ^ \<nu> + 12 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu>" 
    if "\<delta> > 0"
proof - 
  have step0: "X_poly_degree 
    = \<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>) + (\<delta> + \<delta> + (Suc \<delta> ^ \<nu> + 2 * \<delta> * Suc \<delta> ^ \<nu>) * (\<delta> + \<delta>)) +
    max (max (max (Suc 0)
               (max (\<delta> + \<delta> * (2 * \<delta>) + (Suc \<delta> ^ \<nu> * 2 + \<delta> * Suc \<delta> ^ \<nu> * 2) * \<delta>)
                 (\<delta> + (\<delta> + (Suc \<delta> ^ \<nu> * 2 + 4 * (\<delta> * Suc \<delta> ^ \<nu>)) * \<delta>)) +
                (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>))))
          (max (2 * \<delta> + Suc \<delta> ^ \<nu> * 2 * \<delta>)
            (\<delta> + \<delta> + (Suc \<delta> ^ \<nu> + \<delta> * Suc \<delta> ^ \<nu>) * (\<delta> + \<delta>) +
             (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>)))) +
         (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>) +
          (\<delta> + \<delta> + (Suc \<delta> ^ \<nu> + 2 * \<delta> * Suc \<delta> ^ \<nu>) * (\<delta> + \<delta>))))
     (max (2 * \<delta> + Suc \<delta> ^ \<nu> * 2 * \<delta>)
       (\<delta> + \<delta> + (Suc \<delta> ^ \<nu> + \<delta> * Suc \<delta> ^ \<nu>) * (\<delta> + \<delta>) + (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>))))"
    by (simp add: X_poly_degree_def) (* takes long! *)
    
  have step1: "max (2 * \<delta> + Suc \<delta> ^ \<nu> * 2 * \<delta>) 
               (\<delta> + \<delta> + (Suc \<delta> ^ \<nu> + \<delta> * Suc \<delta> ^ \<nu>) * (\<delta> + \<delta>) + (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>))) 
        = 4 * \<delta> + 2 * (\<delta>^2 + 2*\<delta>) * Suc \<delta> ^ \<nu>" 
    using that apply (simp add: ab_semigroup_mult_class.mult_ac(1) mult_2)
    by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) add.commute add.left_commute 
        mult.commute mult_2_right mult_Suc power2_eq_square)

  have step2: "max (\<delta> + \<delta> * (2 * \<delta>) + (Suc \<delta> ^ \<nu> * 2 + \<delta> * Suc \<delta> ^ \<nu> * 2) * \<delta>)
               (\<delta> + (\<delta> + (Suc \<delta> ^ \<nu> * 2 + 4 * (\<delta> * Suc \<delta> ^ \<nu>)) * \<delta>))
        = 2 * \<delta>  + 2 * \<delta> * Suc \<delta> ^ \<nu> + 4 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu>"
  proof - 
    have aux1: "max (\<delta> + (\<delta> * (\<delta> * 2) + (\<delta> * (2 * Suc \<delta> ^ \<nu>) + \<delta> * (\<delta> * (2 * Suc \<delta> ^ \<nu>)))))
     (\<delta> * 2 + (\<delta> * (2 * Suc \<delta> ^ \<nu>) + \<delta> * (\<delta> * (4 * Suc \<delta> ^ \<nu>))))
    = \<delta> + \<delta> * (2 * Suc \<delta> ^ \<nu>) + 
      max (\<delta> * (\<delta> * 2) + \<delta> * (\<delta> * (2 * Suc \<delta> ^ \<nu>))) (\<delta> + \<delta> * (\<delta> * (4 * Suc \<delta> ^ \<nu>)))"
      using nat_add_max_right by presburger
    have aux2: "max (\<delta> * (\<delta> * 2) + \<delta> * (\<delta> * (2 * Suc \<delta> ^ \<nu>))) (\<delta> + \<delta> * (\<delta> * (4 * Suc \<delta> ^ \<nu>))) = 
          2 * \<delta>^2 * Suc \<delta> ^ \<nu> + max (2 * \<delta>^2) (\<delta> + 2 * \<delta>^2 * Suc \<delta> ^ \<nu>)" 
      by (simp add: mult.commute mult.left_commute power2_eq_square)
    have aux3: "max (2 * \<delta>\<^sup>2) (\<delta> + 2 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu>) = \<delta> + 2 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu>"
      apply (rule linorder_class.max.absorb2)
      by (simp add: trans_le_add2)
    show ?thesis 
      apply (simp add: algebra_simps)
      unfolding aux1 aux2 aux3
      by (simp add: algebra_simps)
  qed

  have step3: "max (Suc 0) (2 * \<delta> + 2 * \<delta> * Suc \<delta> ^ \<nu> + 4 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu> + (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>)))
            = \<delta> * 4 + \<delta> * 4 * Suc \<delta> ^ \<nu> + 4 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu>"
  proof - 
    have "max (Suc 0) (2 * \<delta> + 2 * \<delta> * Suc \<delta> ^ \<nu> + 4 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu> + (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>)))
        = (2 * \<delta> + 2 * \<delta> * Suc \<delta> ^ \<nu> + 4 * \<delta>\<^sup>2 * Suc \<delta> ^ \<nu> + (\<delta> + \<delta> + Suc \<delta> ^ \<nu> * (\<delta> + \<delta>)))"
    apply (rule linorder_class.max.absorb2)
    using Suc_leI add_gr_0 that by presburger
    thus ?thesis 
      by (simp add: algebra_simps)
  qed

  show ?thesis
    unfolding step0
    unfolding step1
    unfolding step2
    unfolding step3
    apply (simp add: algebra_simps)
    by algebra
qed

poly_degree A\<^sub>1_poly
poly_degree A\<^sub>2_poly
poly_degree A\<^sub>3_poly
poly_degree S_poly
poly_degree T_poly
poly_degree R_poly

lemma A\<^sub>1_vars: "max_vars A\<^sub>1_poly \<le> 8"
  unfolding A\<^sub>1_poly_def b_poly_def coding_variables.b_poly_def
  apply (rule le_trans[OF max_vars_poly_subst_list_bounded])
  by (rule le_trans[OF max_vars_poly_subst_list_general], auto)

lemma h0: "max_vars (4::int mpoly) \<le> 8"
  by (metis Const_numeral max_vars_Const zero_le)

lemma h1: "max_vars (8::int mpoly) \<le> 8"
  by (metis Const_numeral max_vars_Const zero_le)

lemma h2: "max_vars (32::int mpoly) \<le> 8"
  by (metis Const_numeral max_vars_Const zero_le)

lemma A\<^sub>2_vars: "max_vars A\<^sub>2_poly \<le> 8"
  unfolding A\<^sub>2_poly_def apply (rule le_trans[OF max_vars_mult], auto)+
  unfolding D_poly_def F_poly_def I_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def
  unfolding power2_eq_square
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, simp_all, all \<open>intro conjI\<close>)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma A\<^sub>3_vars: "max_vars A\<^sub>3_poly \<le> 8"
  unfolding A\<^sub>3_poly_def power2_eq_square
  apply (rule le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff]; auto simp: h0)+
  apply (all \<open>rule le_trans[OF max_vars_pow] le_trans[OF max_vars_mult]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  unfolding U_poly_def V_poly_def K_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def
  unfolding power2_eq_square
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma S_vars: "max_vars S_poly \<le> 8"
  unfolding S_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def
  unfolding power2_eq_square
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma T_vars: "max_vars T_poly \<le> 8"
  unfolding T_poly_def b_poly_def coding_variables.b_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def
  unfolding power2_eq_square
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma K_vars: "max_vars K_poly \<le> 8"
  unfolding K_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def power2_eq_square
  apply ((rule le_trans[OF max_vars_pow]
               le_trans[OF max_vars_mult max.boundedI] 
               le_trans[OF max_vars_add max.boundedI]
               le_trans[OF max_vars_diff' max.boundedI])
             | simp_all add: h1)+
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma L_vars: "max_vars L_poly \<le> 8"
  unfolding L_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def power2_eq_square
  apply ((rule le_trans[OF max_vars_pow]
               le_trans[OF max_vars_mult max.boundedI] 
               le_trans[OF max_vars_add max.boundedI]
               le_trans[OF max_vars_diff' max.boundedI])
             | simp_all add: h1)+
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma C_vars: "max_vars C_poly \<le> 8"
  unfolding C_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def power2_eq_square
  apply ((rule le_trans[OF max_vars_pow]
               le_trans[OF max_vars_mult max.boundedI] 
               le_trans[OF max_vars_add max.boundedI]
               le_trans[OF max_vars_diff' max.boundedI])
             | simp_all add: h1)+
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (rule le_trans[OF max_vars_poly_subst_list_general]
              le_trans[OF max_vars_pow]
              le_trans[OF max_vars_mult]
              le_trans[OF max_vars_add]
              le_trans[OF max_vars_diff], auto)+

lemma \<mu>_vars:
  "max_vars (poly_subst_list [Var 0, Var (Suc 0), Var 2, Var 3, Var 4, Var 5, Var 6, Var 7, Var 8, Var 9] \<mu>_poly) \<le> 8"
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  unfolding \<mu>_poly_def
  unfolding X_poly_def coding_variables.X_poly_def Y_poly_def coding_variables.Y_poly_def 
            b_poly_def power2_eq_square
  apply ((rule le_trans[OF max_vars_pow]
               le_trans[OF max_vars_mult max.boundedI] 
               le_trans[OF max_vars_add max.boundedI]
               le_trans[OF max_vars_diff' max.boundedI])
             | simp_all add: h1)+
  apply (all \<open>rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]]\<close>, auto)
  by (all \<open>rule le_trans[OF max_vars_poly_subst_list_general]\<close>, auto)

lemma R_vars: "max_vars R_poly \<le> 8"
  unfolding R_poly_def
  unfolding power2_eq_square
  by ((rule le_trans[OF max_vars_pow]
               le_trans[OF max_vars_mult max.boundedI] 
               le_trans[OF max_vars_add max.boundedI]
               le_trans[OF max_vars_diff' max.boundedI])
             | simp_all add: h1 h2 \<mu>_vars
             | rule le_trans[OF max_vars_poly_subst_list_bounded[of _ 8]], simp add: K_vars C_vars L_vars)+


lemma list_vars: "i \<le> 8 \<Longrightarrow> max_vars
          ([Var 0::int mpoly, Var (Suc 0), Var (Suc (Suc 0)), Var (Suc (Suc (Suc 0))),
            Var (Suc (Suc (Suc (Suc 0)))), Var (Suc (Suc (Suc (Suc (Suc 0))))),
            Var (Suc (Suc (Suc (Suc (Suc (Suc 0)))))),
            Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),
            Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))),
            Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))] !\<^sub>0
           i)
         \<le> 8"
  apply (simp add: nth0_def)
  by (smt (z3) add.right_neutral add_Suc_right le_Suc_eq less_eq_nat.simps(1) max_vars_Var nle_le
      nth_Cons_0 nth_Cons_Suc numeral_1_eq_Suc_0 numeral_Bit0)


lemmas aux_vars = A\<^sub>1_vars A\<^sub>2_vars A\<^sub>3_vars S_vars T_vars R_vars


lemma total_degree_three_squares_rw:
  fixes Pextra :: "'a::comm_semiring_1 mpoly"
  shows "ia \<le> 8 \<Longrightarrow>
        total_degree_env env
         ([Var 0, Var (Suc 0), Var (Suc (Suc 0)),
           Var (Suc (Suc (Suc 0))), Var (Suc (Suc (Suc (Suc 0)))),
           Var (Suc (Suc (Suc (Suc (Suc 0))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc 0)))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))),
           Pextra] !\<^sub>0
          ia)
        = total_degree_env env
         ([Var 0 :: 'a mpoly , Var (Suc 0), Var (Suc (Suc 0)), Var (Suc (Suc (Suc 0))),
           Var (Suc (Suc (Suc (Suc 0)))), Var (Suc (Suc (Suc (Suc (Suc 0))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc 0)))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),
           Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))]  !\<^sub>0
          ia)"
  unfolding total_degree_env_id[symmetric]
  apply (drule le_imp_less_Suc)
  using total_degree_env_reduce[of ia "map Var [0::nat, 1, 2, 3, 4, 5, 6, 7, 8]", simplified]
  by (metis One_nat_def Suc_1 Suc_numeral semiring_norm(2,5,8))

lemma final: "\<And>ia. ia \<le> 8 \<Longrightarrow>
          total_degree_env (\<lambda>_. Suc 0)
           ([Var 0::int mpoly, Var (Suc 0), Var (Suc (Suc 0)), Var (Suc (Suc (Suc 0))),
             Var (Suc (Suc (Suc (Suc 0)))), Var (Suc (Suc (Suc (Suc (Suc 0))))),
             Var (Suc (Suc (Suc (Suc (Suc (Suc 0)))))),
             Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))),
             Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))),
             Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) +
             (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) *
              Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) +
              (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) *
               Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) +
               Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) *
               Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))] !\<^sub>0
            ia)
          \<le> Suc 0"
  apply (simp add: total_degree_three_squares_rw)
  by (metis (no_types, lifting) Nil_is_map_conv One_nat_def le_add1 list.simps(9) plus_1_eq_Suc
      total_degree_env_mono3_map_Var)
(* End auxiliary lemmas *)

poly_extract Q


lemma Q_alt: "Q = \<sigma> M3"
  unfolding Q_def \<sigma>_def ..

lemma R_gt_0_consequences:
  fixes a :: nat and f g h k l w n :: int
  assumes "R \<tau> > 0" and "b \<tau> \<ge> 0" and "f > 0"
  shows "g \<ge> 1" and "g < 2 * \<mu> \<tau>" and "K \<tau> \<noteq> 0" 
    and "bridge_variables.d2f k l w h g (Y \<tau>) (X \<tau>)"
proof -
  have helper: "0 < int \<alpha> * \<beta> ^ \<gamma>" if "\<alpha> > 0" and "\<beta> > 0" for \<alpha> \<beta> \<gamma> 
    by (simp add: that(1-2))

  have "b \<tau> > 0"
  proof - 
    have "b \<tau> \<noteq> 0"
    unfolding b_def coding_variables.b_def
    using \<open>f > 0\<close> apply simp
    by (smt (verit, best) mult_pos_pos of_nat_less_0_iff)
    
    thus "b \<tau> > 0" using \<open>b \<tau> \<ge> 0\<close> by auto
  qed

  have "\<mu> \<tau> > 0" 
    unfolding \<mu>_def
    using helper[of "coding_variables.\<gamma> P\<^sub>1" "b \<tau>", 
                 OF coding_variables.\<gamma>_gt_0 \<open>b \<tau> > 0\<close>]
    unfolding b_def by auto
  hence "real_of_int (8*(\<mu> \<tau>)^3) > 0"
    by auto

  let ?R' = "8 * (\<mu> \<tau>)^3 * g * (K \<tau>)^2 - g^2 * (32 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 * (\<mu> \<tau>)^3 + g^2 * (K \<tau>)^2)"
  have R_gt_0_condition: "real_of_int ?R' > 0"
  proof - 
    have rewrite: "f^2 * l^2 * x^2 = (f * l * x) ^2" 
      by (simp add: power_mult_distrib)

    have helper: "0 < \<alpha>^2 * \<beta> \<Longrightarrow> 0 < \<beta>" for \<alpha> \<beta> :: int 
      by (smt (verit) mult_nonneg_nonpos power2_less_0)
      
    have "?R' > 0"
      using \<open>R \<tau> > 0\<close>
      unfolding R_def \<mu>_def K_def L_def C_def 
      unfolding rewrite using helper[of "f * l * x"]
      by metis

    thus ?thesis
      using of_int_pos by blast
  qed

  hence "g \<noteq> 0"
    by (auto)
  hence "real_of_int (g^2) > 0"
    by auto

  have inequality_divided: 
    "(K \<tau>)^2 / g > 4 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 + (g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
    (is "?A / g > ?B + ?C / (8*(\<mu> \<tau>)^3)")
  proof -
    have "0 < (8*(\<mu> \<tau>)^3) * g * (K \<tau>)^2 / (8*(\<mu> \<tau>)^3) - g^2 * (32 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 * (\<mu> \<tau>)^3 + g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      using divide_strict_right_mono[of 0 "real_of_int ?R'" "8*(\<mu> \<tau>)^3", OF R_gt_0_condition \<open>real_of_int (8*(\<mu> \<tau>)^3) > 0\<close>]
        by (simp add: diff_divide_distrib)
    hence aux1: "g * (K \<tau>)^2 > g^2 * (32 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 * (\<mu> \<tau>)^3 + g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      using \<open>0 < \<mu> \<tau>\<close> by auto
    
    have "(g * (K \<tau>)^2) / g^2 > (32 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 * (\<mu> \<tau>)^3 + g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      using divide_strict_right_mono[OF aux1 \<open>real_of_int (g^2) > 0\<close>]
      by (auto simp: \<open>g \<noteq> 0\<close>)
    hence "(K \<tau>)^2 / g > 4 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 + (g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      using \<open>\<mu> \<tau> > 0\<close>
      by (auto simp add: add_divide_distrib) (metis power2_eq_square real_divide_square_eq)
    then show ?thesis
      by auto
  qed

  have 1: "4 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 + (g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)
            \<ge> (g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      by simp

  have "(K \<tau>)^2 / g > 0"
  proof - 
    have 2: "(g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3) \<ge> 0"
      using \<open>(\<mu> \<tau>) > 0\<close> by (simp add: pos_imp_zdiv_nonneg_iff)

    show ?thesis using 1 2 inequality_divided
      by linarith
  qed

  show "(K \<tau>) \<noteq> 0" 
    using \<open>(K \<tau>)^2 / g > 0\<close> by fastforce


  have "g > 0"
    using \<open>(K \<tau>)^2 / g > 0\<close> \<open>(K \<tau>) \<noteq> 0\<close>
    by (simp add: zero_less_divide_iff)
  then show "g \<ge> 1"
    using \<open>g \<noteq> 0\<close> by auto
  from \<open>g > 0\<close> have "real_of_int g > 0"
    by auto

  show "g < 2 * \<mu> \<tau>"
  proof -
    from inequality_divided have "(K \<tau>)^2 / g > (g^2 * (K \<tau>)^2) / (8*(\<mu> \<tau>)^3)"
      by auto (smt (verit) power2_less_0)
    hence "(8*(\<mu> \<tau>)^3) * (K \<tau>)^2 > real_of_int g^3 * (K \<tau>)^2"
      using \<open>real_of_int (8*(\<mu> \<tau>)^3) > 0\<close> using \<open>real_of_int g > 0\<close>
      by (auto simp: divide_simps algebra_simps power2_eq_square power3_eq_cube)
    hence "real_of_int g < 2 * \<mu> \<tau>"
      apply (simp add: \<open>(K \<tau>) \<noteq> 0\<close>)
      apply (rule power_less_imp_less_base[of _ 3])
      using \<open>\<mu> \<tau> > 0\<close> by auto
    then show ?thesis
      by auto
  qed

  from inequality_divided have "4 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 < (K \<tau>)^2 / g"
    using \<open>g > 0\<close> \<open>\<mu> \<tau> > 0\<close> \<open>(K \<tau>) \<noteq> 0\<close> apply simp
    by (smt (verit, ccfv_SIG) diff_divide_distrib mult_sign_intros(1)
            of_int_1_le_iff power2_less_0 zero_le_power_eq_numeral zero_less_divide_iff)
  also have "... \<le> (K \<tau>)^2"
    using \<open>g \<ge> 1\<close>
    by (auto simp: algebra_simps divide_simps mult_le_cancel_right1)
  finally have "4 * ((C \<tau>) - (K \<tau>)*(L \<tau>))^2 < (K \<tau>)^2"
    by linarith
  then have "(2 * (C \<tau>) - 2 * (K \<tau>)*(L \<tau>))^2 < (K \<tau>)^2"
    by (auto simp: algebra_simps power2_eq_square)
  then show "bridge_variables.d2f k l w h g (Y \<tau>) (X \<tau>)" 
    unfolding bridge_variables.d2f_def C_def L_def K_def
    by (auto simp: algebra_simps)
qed

lemma R_gt_0_necessary_condition: 
  fixes a :: nat and f g h k l w x y :: int
  assumes "f > 0" and "x > 0" and "l > 0" and "g > 0" and "g < \<mu> \<tau>" and
          "bridge_variables.d2e k l w h g (Y \<tau>) (X \<tau>)"
  shows "R \<tau> > 0"
proof - 
  from assms have "\<mu> \<tau> > 0"
    by auto

  have "(K \<tau>)^2 \<ge> 0"
    by auto

  have 0: "(4 * g * (C \<tau> - K \<tau> * L \<tau>))^2 < (K \<tau>)^2"
    using assms(6)
    unfolding bridge_variables.d2e_def C_def K_def L_def
    by (auto simp: algebra_simps)
  hence "(K \<tau>)^2 > 0"
    by auto

  from 0 have "2 * 4^2 * g^2 * (C \<tau> - K \<tau> * L \<tau>)^2 < 2 * (K \<tau>)^2"
    by (auto simp: algebra_simps power2_eq_square)

  moreover have "8*g^4 / (8*(\<mu> \<tau>)^3) * (K \<tau>)^2 \<le> g * (K \<tau>)^2"
  proof -
    have "8*g^4 / (8*(\<mu> \<tau>)^3) < g"
      apply (simp add: power2_eq_square \<open>g < \<mu> \<tau>\<close>)
      using \<open>g < \<mu> \<tau>\<close> \<open>g > 0\<close> \<open>\<mu> \<tau> > 0\<close>
      apply (simp add: algebra_simps divide_simps power2_eq_square power4_eq_xxxx)
      using \<open>g < \<mu> \<tau>\<close> apply simp
      unfolding real_of_int_strict_inequality power3_eq_cube
      apply (simp add:  mult.commute mult.assoc mult_strict_right_mono)
      by (smt (verit, best) mult_le_less_imp_less mult_nonneg_nonneg of_int_le_0_iff real_of_int_inequality)
    thus ?thesis
      using \<open>(K \<tau>)^2 \<ge> 0\<close>
      apply simp
      by (metis less_eq_real_def mult_right_mono times_divide_eq_left zero_le_power2)
  qed

  ultimately have "2 * 4^2 * g^2 * (C \<tau> - K \<tau> * L \<tau>)^2 + 8*g^4 / (8*(\<mu> \<tau>) ^ 3) * (K \<tau>)^2 < 2 * (K \<tau>)^2 + g * (K \<tau>)^2"
    unfolding real_of_int_strict_inequality by auto

  also have "... < 8 * g * (K \<tau>)^2"
    using \<open>g > 0\<close> \<open>(K \<tau>)^2 > 0\<close> by (auto simp: algebra_simps)

  finally have "4 * g^2 * (C \<tau> - K \<tau> * L \<tau>)^2 + g^4 / (8*(\<mu> \<tau>) ^ 3) * (K \<tau>)^2 < g * (K \<tau>)^2"
    by (auto simp: algebra_simps)

  hence "8 * (\<mu> \<tau>)^3 * 4 * g^2 * (C \<tau> - K \<tau> * L \<tau>)^2 + g^4 * (K \<tau>)^2 < 8 * (\<mu> \<tau>)^3 * g * (K \<tau>)^2"
    using \<open>\<mu> \<tau> > 0\<close> unfolding real_of_int_strict_inequality 
    by (auto simp: divide_simps algebra_simps power2_eq_square)

  hence "8 * (\<mu> \<tau>)^3 * g * (K \<tau>)\<^sup>2 - g\<^sup>2 * (32 * (C \<tau> - K \<tau> * L \<tau>)^2 * (\<mu> \<tau>)^3 + g\<^sup>2 * (K \<tau>)\<^sup>2) > 0"
    by (auto simp: divide_simps power2_eq_square power4_eq_xxxx algebra_simps)

  thus ?thesis unfolding R_def using assms by auto
qed

end

end
