section \<open>Tightening\<close>

text \<open>replace \<open>p + c \<le> 0\<close> by \<open>p / g + \<lceil> c / g \<rceil> \<le> 0\<close> where 
  \<open>c\<close> is a constant and \<open>g\<close> is the gcd of the variable coefficients of \<open>p\<close>.\<close>

theory Diophantine_Tightening
  imports 
    Diophantine_Eqs_and_Ineqs
begin
 
definition tighten_ineq :: "'v dlineq \<Rightarrow> 'v dlineq" where
  "tighten_ineq p = (let g = gcd_coeffs_l p;
       c = constant_l p
     in if g = 1 then p else let d = - ((-c) div g)
       in change_const d (sdiv_l p g))" 

lemma tighten_ineq: assumes "vars_l p \<noteq> {}" 
  shows "satisfies_dlineq \<alpha> (tighten_ineq p) = satisfies_dlineq \<alpha> p" 
proof (rule ccontr)
  assume contra: "\<not> ?thesis" 
  let ?tp = "tighten_ineq p" 
  define g where "g = gcd_coeffs_l p" 
  define c where "c = constant_l p" 
  note def = tighten_ineq_def[of p, unfolded Let_def, folded g_def, folded c_def]
  define d where "d = - (- c div g)"
  define mc where "mc = -c" 
  define pg where "pg = sdiv_l p g" 
  define f where "f = (\<Sum>x\<in>vars_l pg. coeff_l pg x * \<alpha> x)" 
  from contra def have g1: "(g = 1) = False" by auto
  from def[unfolded this if_False, folded d_def pg_def]
  have tp: "?tp = change_const d pg" by auto
   
  from assms have g0: "g \<noteq> 0" unfolding g_def gcd_coeffs_l_def 
    by (transfer, auto)
  have "g \<ge> 0" unfolding g_def gcd_coeffs_l_def by simp
  with g0 g1 have g: "g > 0" by simp
  have p: "p = change_const c (smult_l g pg)" (is "_ = ?p")
  proof (intro lpoly_fun_of_eqI, goal_cases)
    case (1 x)
    show ?case
    proof (cases x)
      case None
      thus ?thesis unfolding c_def by transfer auto
    next
      case (Some y)
      hence "fun_of_lpoly (change_const c (smult_l g pg)) x
        = g * (fun_of_lpoly p x div g)" unfolding pg_def by transfer auto
      also have "\<dots> = fun_of_lpoly p x" 
      proof (rule dvd_mult_div_cancel)
        have "fun_of_lpoly p x \<in> coeff_l p ` vars_l p \<or> fun_of_lpoly p x = 0" unfolding Some
          by transfer auto
        thus "g dvd fun_of_lpoly p x" using g0 unfolding g_def gcd_coeffs_l_def by auto
      qed
      finally show ?thesis by auto
    qed
  qed

  have coeff: "coeff_l ?p x = g * coeff_l pg x" for x by transfer auto
  have coeff': "coeff_l ?tp x = coeff_l pg x" for x unfolding tp by transfer auto

  have "eval_l \<alpha> p = constant_l ?p + (\<Sum>x\<in>vars_l ?p. coeff_l ?p x * \<alpha> x)" unfolding p unfolding eval_l_def by auto
  also have "constant_l ?p = c" by transfer auto
  also have "vars_l ?p = vars_l pg" using g0 by transfer auto
  finally have evalp: "eval_l \<alpha> p = c + g * f" unfolding f_def coeff sum_distrib_left by (simp add: ac_simps)

  have "eval_l \<alpha> ?tp = constant_l ?tp + (\<Sum>x\<in>vars_l ?tp. coeff_l ?tp x * \<alpha> x)" unfolding eval_l_def by auto
  also have "vars_l ?tp = vars_l pg" unfolding tp by transfer auto
  also have "constant_l ?tp = d" unfolding tp by transfer auto
  finally have eval_tp: "eval_l \<alpha> ?tp = d + f" unfolding f_def coeff' by auto

  define mo where "mo = mc mod g" 
  define di where "di = mc div g" 
  have mc: "mc = g * di + mo" and mo: "0 \<le> mo" "mo < g" using g unfolding mo_def di_def by auto

  have sat_p: "satisfies_dlineq \<alpha> p = (g * f \<le> -c)" unfolding satisfies_dlineq_def evalp by auto
  have "satisfies_dlineq \<alpha> ?tp = (f \<le> - d)" unfolding satisfies_dlineq_def eval_tp by auto
  also have "\<dots> = (g * f \<le> g * (-d))" using g
    by (smt (verit, ccfv_SIG) mult_le_cancel_left_pos)
  finally have "?thesis \<longleftrightarrow> (g * f \<le> -c \<longleftrightarrow> g * f \<le> g * (-d))" unfolding sat_p by auto
  also have "\<dots> \<longleftrightarrow> True" unfolding d_def minus_minus mc_def[symmetric] di_def[symmetric] unfolding mc using mo
    by (smt (verit, del_insts) int_distrib(4) mult_le_cancel_left1)
  finally show False using contra by auto
qed

(* removes all trivial inequalities and applies tightening *)
definition tighten_ineqs :: "'v dlineq list \<Rightarrow> 'v :: linorder dlineq list option" where
  "tighten_ineqs cs = map_option (map tighten_ineq) (trivial_ineq_filter cs)" 

lemma tighten_ineqs: "tighten_ineqs cs = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set cs)" 
  "tighten_ineqs cs = Some ds \<Longrightarrow> 
     (\<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set cs) \<longleftrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ds)) \<and> 
     length ds \<le> length cs"
proof (atomize(full), goal_cases)
  case 1
  show ?case 
  proof (cases "trivial_ineq_filter cs")
    case None
    thus ?thesis unfolding tighten_ineqs_def using trivial_ineq_filter(1)[OF None] by auto
  next
    case (Some cs')
    from Some have "tighten_ineqs cs = Some (map tighten_ineq cs')" unfolding tighten_ineqs_def by auto
    with trivial_ineq_filter(2)[OF Some, of \<alpha>]
    show ?thesis using tighten_ineq[of _ \<alpha>] by auto
  qed
qed

end