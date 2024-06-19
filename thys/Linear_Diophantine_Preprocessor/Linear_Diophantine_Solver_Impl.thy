subsection \<open>Executable Algorithm\<close>

theory Linear_Diophantine_Solver_Impl
  imports 
    Linear_Diophantine_Solver
begin
 
definition simplify_dleq :: "'v dleq \<Rightarrow> 'v dleq + bool" where
  "simplify_dleq p = (let 
     g = gcd_coeffs_l p;
     c = constant_l p
  in if g = 0 then 
    Inr (c = 0)
   else if g = 1 then Inl p
   else if g dvd c then Inl (sdiv_l p g) else Inr False)" 

lemma simplify_dleq_0: assumes "simplify_dleq p = Inr True" 
  shows "p = 0" 
proof -
  from assms[unfolded simplify_dleq_def Let_def gcd_coeffs_l_def]
  have gcd: "Gcd (coeff_l p ` vars_l p) = 0" and const: "constant_l p = 0" 
    by (auto split: if_splits)
  from gcd have "coeff_l p ` vars_l p \<subseteq> {0}" by auto
  hence "vars_l p = {}" by transfer auto
  with const have "fun_of_lpoly p = (\<lambda> _. 0)" 
  proof (transfer, intro ext, goal_cases)
    case (1 c x)
    thus ?case by (cases x, auto)
  qed
  thus "p = 0" by transfer auto
qed

lemma simplify_dleq_fail: assumes "simplify_dleq p = Inr False" 
  shows "griggio_unsat p" 
proof -
  let ?g = "Gcd (coeff_l p ` vars_l p)" 
  from assms[unfolded simplify_dleq_def gcd_coeffs_l_def Let_def]
  consider (const) "?g = 0" "constant_l p \<noteq> 0" 
    | (gcd) "\<not> (?g dvd constant_l p)" 
    by (auto split: if_splits)
  thus ?thesis
  proof cases
    case const
    from const have "coeff_l p ` vars_l p \<subseteq> {0}" by auto
    hence "vars_l p = {}" by transfer auto
    moreover from const have "p \<noteq> 0" by transfer auto
    ultimately show ?thesis by (rule griggio_constant_unsat)
  next
    case gcd
    thus ?thesis by (rule griggio_gcd_unsat)
  qed
qed

definition dleq_normalized where "dleq_normalized p = (Gcd (coeff_l p ` vars_l p) = 1)" 

definition size_dleq :: "'v dleq \<Rightarrow> int" where "size_dleq p = sum (abs o coeff_l p) (vars_l p)" 

lemma size_dleq_pos: "size_dleq p \<ge> 0" unfolding size_dleq_def by simp

lemma simplify_dleq_keep: assumes "simplify_dleq p = Inl q" 
  shows 
    "\<exists> g \<ge> 1. normalize_dleq p = (g, q)" (* normalization rule is applicable on p *)
    "size_dleq p \<ge> size_dleq q" (* size does not increase *)
    "dleq_normalized q"   (* no trivial rule applicable on q *)
proof (atomize (full), unfold dleq_normalized_def, goal_cases)
  case 1
  let ?g = "Gcd (coeff_l p ` vars_l p)" 
  from assms[unfolded simplify_dleq_def gcd_coeffs_l_def Let_def] 
  have g: "?g \<noteq> 0" "?g dvd constant_l p" and p0: "p \<noteq> 0" 
    and choice: "?g = 1 \<and> q = p \<or> ?g \<noteq> 1 \<and> q = sdiv_l p ?g" 
    by (auto split: if_splits)
  from g have gG: "?g = Gcd (insert (constant_l p) (coeff_l p ` vars_l p))" (is "_ = ?G") by auto
  from g(1) have g1: "?g \<ge> 1" by (smt (verit) Gcd_int_greater_eq_0)
  obtain g' q' where norm: "normalize_dleq p = (g', q')" by force
  note norm_gcd = normalize_dleq_gcd[OF norm p0, folded gG]
  from choice show ?case
  proof 
    assume "?g = 1 \<and> q = p"
    hence g: "?g = 1" and id: "q = p" by auto
    with gG have "?G = 1" by auto
    with norm gG norm_gcd have "normalize_dleq p = (1, q')" by metis
    hence norm: "normalize_dleq p = (1,p)" by (transfer, auto)
    show ?thesis unfolding id apply (intro conjI exI[of _ ?g])
      subgoal unfolding g by auto
      subgoal unfolding g id using norm by auto
      subgoal by simp
      subgoal by (rule g)
      done
  next
    note g' = norm_gcd(1)
    assume "?g \<noteq> 1 \<and> q = sdiv_l p ?g" 
    with g' g have g'01: "g' \<noteq> 0" "g' \<noteq> 1" and q: "q = sdiv_l p g'" by auto 
    from norm have q': "q' = q" unfolding q
      by (transfer, auto)
    note norm_gcd = norm_gcd[unfolded q']
    note norm = norm[unfolded q']
    show ?thesis
    proof (intro conjI exI[of _ g'])
      show "1 \<le> g'" by fact
      show "normalize_dleq p = (g', q)" by fact
      from g'01 have "abs g' \<ge> 1" by linarith
      hence "abs (y div g') \<le> abs y" for y 
        by (smt (verit) div_by_1 div_nonpos_pos_le0 int_div_less_self norm_gcd(2) pos_imp_zdiv_nonneg_iff zdiv_mono2_neg)       
      hence le: "\<bar>coeff_l q x\<bar> \<le> \<bar>coeff_l p x\<bar>" for x unfolding q by (transfer, auto)
      have pq: "p = smult_l g' q" unfolding q using norm
        by (transfer, auto)
      have vars: "vars_l q = vars_l p" unfolding pq using g'01
        by (transfer, auto)
      show "size_dleq q \<le> size_dleq p" unfolding size_dleq_def vars
        by (rule sum_mono, auto simp: le)
      from gG have "?g = Gcd (range (fun_of_lpoly p))" unfolding g'[symmetric] using norm
        by transfer auto
      have "g' = ?g" by (rule g')
      also have "coeff_l p ` vars_l p = (\<lambda> x. g' * x) ` coeff_l q ` vars_l p" 
        unfolding pq by transfer auto
      also have "vars_l p = vars_l q" by (simp add: vars)
      also have "Gcd ((*) g' ` coeff_l q ` vars_l q) = g' * Gcd (coeff_l q ` vars_l q)" 
        by (metis Gcd_int_greater_eq_0 Gcd_mult abs_of_nonneg linordered_nonzero_semiring_class.zero_le_one norm_gcd(2) normalize_int_def order.trans zero_le_mult_iff)
      finally have "abs g' = abs g' * abs (Gcd (coeff_l q ` vars_l q))" by simp
      with g'01 show "Gcd (coeff_l q ` vars_l q) = 1" by simp
    qed
  qed
qed

fun simplify_dleqs :: "'v dleq list \<Rightarrow> 'v dleq list option" where
  "simplify_dleqs [] = Some []"          
| "simplify_dleqs (e # es) = (case simplify_dleq e of 
     Inr False \<Rightarrow> None
   | Inr True \<Rightarrow> simplify_dleqs es
   | Inl e' \<Rightarrow> map_option (Cons e') (simplify_dleqs es))" 


context griggio_input
begin

lemma simplify_dleqs: "simplify_dleqs es = None \<Longrightarrow> (Some ((S,set es \<union> F),X), None) \<in> griggio_step^*" 
  "simplify_dleqs es = Some fs \<Longrightarrow> 
    (Some ((S,set es \<union> F),X), Some ((S,set fs \<union> F),X)) \<in> griggio_step^* 
    \<and> Ball (set fs) dleq_normalized \<and> length fs \<le> length es \<and> 
     (length fs < length es \<or> fs = [] \<or> size_dleq (hd fs) \<le> size_dleq (hd es)) "
proof (atomize (full), induct es arbitrary: F fs)
  case (Cons e es F fs)
  let ?ST = "Some ((S, set (e # es) \<union> F), X)" 
  define ST where "ST = ?ST" 
  consider (F) "simplify_dleq e = Inr False" 
    | (T) "simplify_dleq e = Inr True"
    | (New) e' where "simplify_dleq e = Inl e'" 
    by (cases "simplify_dleq e", auto)
  thus ?case 
  proof cases
    case F
    from simplify_dleq_fail[OF F]
    have "griggio_unsat e" by auto
    from griggio_fail_step[OF this] F
    show ?thesis by auto
  next
    case T
    with simplify_dleq_0[OF T] 
    have e: "e = 0" and id: "simplify_dleqs (e # es) = simplify_dleqs es"  by auto
    with griggio_eq_step[OF griggio_trivial]
    have "(?ST, Some ((S, set es \<union> F), X)) \<in> griggio_step" by auto
    with Cons[of F fs] show ?thesis unfolding ST_def[symmetric] id by fastforce
  next
    case (New e')
    with simplify_dleq_keep[OF New] obtain g where g: "g \<ge> 1" 
      and norm: "normalize_dleq e = (g, e')" 
      and  res: "simplify_dleqs (e # es) = map_option (Cons e') (simplify_dleqs es)" 
      and e': "dleq_normalized e'" 
      and size: "size_dleq e' \<le> size_dleq e" 
      by auto
    from griggio_eq_step[OF griggio_normalize[OF norm g]]
    have "(?ST, Some ((S, set es \<union> insert e' F), X)) \<in> griggio_step" by auto
    with Cons[of "insert e' F"] e' size show ?thesis unfolding res ST_def[symmetric] 
      by force
  qed
qed simp

context
  fixes fresh_var :: "nat \<Rightarrow> 'v" 
begin

partial_function (option) dleq_solver_main 
  :: "nat \<Rightarrow> ('v \<times> 'v dleq) list \<Rightarrow> 'v dleq list \<Rightarrow> ('v \<times> (int,'v)lpoly) list option" where
  "dleq_solver_main n s es = (case simplify_dleqs es of 
       None \<Rightarrow> None
     | Some [] \<Rightarrow> Some s
     | Some (p # fs) \<Rightarrow> 
         let x = min_var p; c = abs (coeff_l p x)
         in if c = 1 then 
           let e = reorder_for_var x p; 
               \<sigma> = substitute_l x e in 
            dleq_solver_main n ((x, e) # map (map_prod id \<sigma>) s) (map \<sigma> fs) else 
           let y = fresh_var n; 
               q = reorder_nontriv_var x p y; 
               e = reorder_for_var x q;
               \<sigma> = substitute_l x e in 
           dleq_solver_main (Suc n) ((x, e) # map (map_prod id \<sigma>) s) (\<sigma> p # map \<sigma> fs))"

fun state_of where "state_of n s es = Some ((set s, set es), fresh_var ` {..<n})" 

lemma dleq_solver_main: assumes fresh_var: "range fresh_var \<inter> V = {}" "inj fresh_var"
  and inv: "invariant_state (state_of n s es)" 
shows "dleq_solver_main n s es = None \<Longrightarrow> (state_of n s es, None) \<in> griggio_step^*" 
  "dleq_solver_main n s es = Some s' \<Longrightarrow> \<exists> X. (state_of n s es, Some ((set s', {}), X)) \<in> griggio_step^*" 
  using inv
proof (atomize(full), induct es arbitrary: n s rule: wf_induct[OF wf_measures[of "[length, nat o size_dleq o hd]"]])
  case (1 es n s)
  note def[simp] = dleq_solver_main.simps[of n s es]
  show ?case
  proof (cases "simplify_dleqs es")
    case None
    with simplify_dleqs(1)[OF this, of "set s" "{}"]
    show ?thesis by auto
  next
    case (Some es')
    from simplify_dleqs(2)[OF this, of "set s" "{}"]
    have steps: "(state_of n s es, state_of n s es') \<in> griggio_step\<^sup>*" 
      and norm: "Ball (set es') dleq_normalized" 
      and size: "length es' \<le> length es" "length es' < length es \<or> es' = [] \<or> size_dleq (hd es') \<le> size_dleq (hd es)" 
      by auto
    from steps griggio_step 1(2) have inv: "invariant_state (state_of n s es')" 
      by (induct, auto)
    show ?thesis
    proof (cases es')
      case Nil
      with Some steps show ?thesis unfolding def by auto
    next
      case (Cons p fs)
      note steps = steps[unfolded Cons]
      note Some = Some[unfolded Cons]
      note norm = norm[unfolded Cons]
      note size = size[unfolded Cons]
      note inv = inv[unfolded Cons]
      let ?st = "state_of n s (p # fs)" 
      have np: "dleq_normalized p" using norm by auto
      hence vp: "vars_l p \<noteq> {}" unfolding dleq_normalized_def by auto
      hence p0: "p \<noteq> 0" by auto
      define x where "x = min_var p" 
      define c where "c = \<bar>coeff_l p x\<bar>" 
      from min_var(1)[of p, folded x_def, OF vp] have c0: "c > 0" "coeff_l p x \<noteq> 0" unfolding c_def by auto
      note def = def[unfolded Some option.simps list.simps, unfolded Let_def, folded x_def, folded c_def]
      show ?thesis
      proof (cases "c = 1")
        case c1: True
        define e where "e = reorder_for_var x p" 
        define \<sigma> where "\<sigma> = substitute_l x e" 
        from c1 have "(c = 1) = True" by auto  
        note def = def[unfolded this if_True, folded e_def, folded \<sigma>_def]
        let ?s' = "(x, e) # map (map_prod id \<sigma>) s" 
        let ?fs = "map \<sigma> fs" 
        let ?st' = "state_of n ?s' ?fs" 
        have step: "(?st, ?st') \<in> griggio_step" unfolding state_of.simps
          using griggio_solve[OF c1[unfolded c_def] e_def, folded \<sigma>_def]
          by (intro griggio_eq_step, auto)
        note inv' = griggio_step[OF step inv] 
        from size have "(?fs, es) \<in> measures [length, nat \<circ> size_dleq \<circ> hd]" by auto
        from 1(1)[rule_format, OF this inv', folded def] steps step 
        show ?thesis by (meson rtrancl.rtrancl_into_rtrancl rtrancl_trans)
      next
        case False
        with c0 have c1: "c > 1" by auto
        define y where "y = fresh_var n" 
        define q where "q = reorder_nontriv_var x p y"
        define e where "e = reorder_for_var x q"
        define \<sigma> where "\<sigma> = substitute_l x e"
        have y: "y \<notin> V \<union> fresh_var ` {..<n}" using fresh_var unfolding y_def inj_def by auto
        from inv y have yp: "y \<notin> vars_l p" by auto
        from c1 have "coeff_l p x \<noteq> 0" unfolding c_def by auto
        note c\<sigma>p = reorder_nontriv_var(1,3)[OF refl this yp q_def e_def fun_cong[OF \<sigma>_def]]
        have fs: "fresh_var ` {..<Suc n} = insert y (fresh_var ` {..< n})" 
          unfolding y_def using lessThan_Suc by force
        from c1 have "(c = 1) = False" by auto  
        note def = def[unfolded this if_False, folded y_def, folded q_def, folded e_def, folded \<sigma>_def]
        let ?s' = "(x, e) # map (map_prod id \<sigma>) s" 
        let ?fs = "\<sigma> p # map \<sigma> fs" 
        let ?st' = "state_of (Suc n) ?s' ?fs" 
        have step: "(?st, ?st') \<in> griggio_step" unfolding state_of.simps
          using griggio_complex_step[OF c0(2) q_def e_def y, folded \<sigma>_def,of "set s" "set fs"] 
          unfolding fs by auto
        note inv' = griggio_step[OF step inv] 
        have "(?fs, es) \<in> measures [length, nat \<circ> size_dleq \<circ> hd]"
        proof (cases "length (p # fs) < length es")
          case False
          let ?h = "hd es" 
          from False have len: "length es = Suc (length fs)" and ph: "size_dleq p \<le> size_dleq ?h" 
            using size by auto
          have main: "size_dleq (\<sigma> p) < size_dleq p" 
          proof -
            define p' where "p' = \<sigma> p" 
            define m where "m = coeff_l p x" 
            have m: "m \<noteq> 0" using c0 unfolding m_def by auto
            from c1[unfolded c_def] have x: "x \<in> vars_l p" by transfer auto
            have "vars_l p \<noteq> {x}" using np[unfolded dleq_normalized_def] c1[unfolded c_def]
              by auto
            with x obtain z where z: "z \<in> vars_l p - {x}" by auto
            have cy: "coeff_l (\<sigma> p) y = coeff_l p x" by (simp add: c\<sigma>p)
            with c0(2) have y': "y \<in> vars_l (\<sigma> p)" by transfer auto
            {
              fix u
              assume "u \<in> vars_l (\<sigma> p)" 
              hence "coeff_l (\<sigma> p) u \<noteq> 0" by (transfer, auto)
              hence "u \<noteq> x \<and> (u \<noteq> y \<longrightarrow> coeff_l p u \<noteq> 0)" unfolding c\<sigma>p(2) using yp x
                by (auto split: if_splits simp: m_def)
              hence "u \<noteq> x \<and> (u \<noteq> y \<longrightarrow> u \<in> vars_l p)" by transfer auto
              hence "u \<in> insert y (vars_l p) - {x}" by auto
            }
            hence vars: "vars_l (\<sigma> p) \<subseteq> insert y (vars_l p) - {x}" by auto
            have yz: "y \<noteq> z" using yp z by auto
            have "size_dleq p = c + sum (abs \<circ> coeff_l p) (vars_l p - {x})" 
              unfolding size_dleq_def c_def by (subst sum.remove[OF _ x], auto)
            also have "\<dots> = c + abs (coeff_l p z) + sum (abs \<circ> coeff_l p) (vars_l p - {x,z})" 
              by (subst sum.remove[OF _ z], force, subst sum.cong, auto)
            finally have size_one: "size_dleq p = c + \<bar>coeff_l p z\<bar> + sum (abs \<circ> coeff_l p) (vars_l p - {x, z})" .

            have "size_dleq (\<sigma> p) = c + sum (abs \<circ> coeff_l (\<sigma> p)) (vars_l (\<sigma> p) - {y})"
              unfolding size_dleq_def
              by (subst sum.remove[OF _ y'], auto simp: cy c_def)
            also have "\<dots> = c + \<bar>coeff_l (\<sigma> p) z\<bar> + sum (abs \<circ> coeff_l (\<sigma> p)) (vars_l (\<sigma> p) - {y, z})"
            proof (cases "z \<in> vars_l (\<sigma> p) - {y}")  
              case True
              show ?thesis by (subst sum.remove[OF _ True], force, subst sum.cong, auto)
            next
              case False
              hence "z \<notin> vars_l (\<sigma> p)" using yz by auto
              hence "coeff_l (\<sigma> p) z = 0" by transfer auto
              with False show ?thesis by (subst sum.cong, auto)
            qed
            also have "\<dots> < size_dleq p" 
            proof -
              have id: "coeff_l (\<sigma> p) z = coeff_l p z mod coeff_l p x" unfolding c\<sigma>p
                using yz z by auto
              have "\<bar>coeff_l (\<sigma> p) z\<bar> < c" unfolding id c_def unfolding m_def[symmetric] using m
                by (rule abs_mod_less)
              also have "\<dots> \<le> \<bar>coeff_l p z\<bar>" 
                using min_var(2)[of z p, folded x_def, folded c_def] using z by auto
              finally have less: "\<bar>coeff_l (\<sigma> p) z\<bar> < \<bar>coeff_l p z\<bar>" .

              from yp x have xy: "x \<noteq> y" by auto
              have x': "x \<notin> vars_l (\<sigma> p)" using fun_cong[OF c\<sigma>p(2)] xy by transfer auto
              have "sum (abs \<circ> coeff_l (\<sigma> p)) (vars_l (\<sigma> p) - {y, z}) 
                  = sum (abs \<circ> coeff_l (\<sigma> p)) (vars_l (\<sigma> p) - {x, y, z})" 
                by (rule sum.cong[OF _ refl], insert x', auto)
              also have "\<dots> \<le> sum (abs \<circ> coeff_l p) (vars_l (\<sigma> p) - {x, y, z})" 
              proof (rule sum_mono, goal_cases)
                case (1 u)
                with vars have uy: "u \<noteq> y" and "u \<in> vars_l p" by auto
                from min_var(2)[OF this(2), folded x_def, folded m_def]
                have "\<bar>m\<bar> \<le> \<bar>coeff_l p u\<bar>" by auto
                thus ?case unfolding o_def fun_cong[OF c\<sigma>p(2), folded m_def] using m uy 
                  by auto (smt (verit, ccfv_threshold) abs_mod_less)
              qed
              also have "\<dots> \<le> sum (abs \<circ> coeff_l p) (vars_l p - {x, z})" 
                by (rule sum_mono2, insert vars, auto)
              finally have le: "sum (abs \<circ> coeff_l (\<sigma> p)) (vars_l (\<sigma> p) - {y, z}) \<le> sum (abs \<circ> coeff_l p) (vars_l p - {x, z})" .

              from le less show ?thesis unfolding size_one by linarith
            qed
            finally show ?thesis .
          qed
          with ph have "size_dleq (\<sigma> p) < size_dleq ?h" by simp
          with len show ?thesis 
            using dual_order.strict_trans2 size_dleq_pos by auto
        qed simp
        from 1(1)[rule_format, OF this inv', folded def] steps step 
        show ?thesis
          by (meson rtrancl.rtrancl_into_rtrancl rtrancl_trans)
      qed
    qed
  qed
qed 

end (* fixing fresh_var *)

end (* locale *)

declare griggio_input.dleq_solver_main.simps[code]

definition fresh_var_gen :: "('v list \<Rightarrow> nat \<Rightarrow> 'v) \<Rightarrow> bool" where
  "fresh_var_gen fv = (\<forall> vs. range (fv vs) \<inter> set vs = {} \<and> inj (fv vs))" 


context
  fixes fresh_var :: "'v :: linorder list \<Rightarrow> nat \<Rightarrow> 'v" 
begin

definition dleq_solver :: "'v list \<Rightarrow> 'v dleq list \<Rightarrow> ('v \<times> (int,'v)lpoly) list option" where
  "dleq_solver v e = (let fv = fresh_var (v @ concat (map vars_l_list e))
    in griggio_input.dleq_solver_main fv 0 [] e)" 

lemma dleq_solver: assumes "fresh_var_gen fresh_var" 
  and "dleq_solver v e = res" 
shows 
  "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {})" (* completeness *)
  "res = Some s \<Longrightarrow> adjust_assign s \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {})" (* soundness *)
  "res = Some s \<Longrightarrow> \<sigma> = solution_subst s \<Longrightarrow> 
     f (\<lambda> i. eval_l \<alpha> (substitute_all_l \<sigma> (P i))) \<Longrightarrow>
    \<beta> = adjust_assign s \<alpha> \<Longrightarrow> 
    f (\<lambda> i. eval_l \<beta> (P i)) \<and> \<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {})" (* translation of solution: soundness *)
  "res = Some s \<Longrightarrow> \<sigma> = solution_subst s \<Longrightarrow> (\<And> i. vars_l (P i) \<subseteq> set v) \<Longrightarrow> 
     f (\<lambda> i. eval_l \<alpha> (P i)) \<and> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {}) \<Longrightarrow>    
    \<exists> \<gamma>. f (\<lambda> i. eval_l \<gamma> (substitute_all_l \<sigma> (P i)))" (* translation of solution: completeness *)
proof -
  define V where "V = v @ concat (map vars_l_list e)" 
  interpret griggio_input "set V" "set e" .
  define fv where "fv = fresh_var V" 
  from dleq_solver_def[of v e, folded V_def, folded fv_def, unfolded Let_def,
      unfolded assms(2)]
  have res: "res = dleq_solver_main fv 0 [] e" by auto
  from assms(1)[unfolded fresh_var_gen_def, rule_format, of V, folded fv_def]
  have fv: "range fv \<inter> set V = {}" "inj fv" by auto
  have eV: "\<Union> (vars_l ` set e) \<subseteq> set V" unfolding V_def by auto
  have inv: "invariant_state (state_of fv 0 [] e)" 
    by (simp, auto simp: V_def)
  note main = dleq_solver_main[OF fv inv, folded res]
  {
    assume "res = None" 
    from main(1)[OF this] griggio_fail[OF eV]
    show "\<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {})" by auto
  }
  {
    assume res: "res = Some s" 
    from main(2)[OF res] obtain X 
      where steps: "(Some (({}, set e), {}), Some ((set s, {}), X)) \<in> griggio_step\<^sup>*" by auto
    from griggio_success[OF eV steps refl refl]
    show "adjust_assign s \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e, {})" .
    {
      assume sig: "\<sigma> = solution_subst s" 
        and f: "f (\<lambda> i. eval_l \<alpha> (substitute_all_l \<sigma> (P i)))"
        and \<beta>: "\<beta> = adjust_assign s \<alpha>"
      from griggio_success_translations(1)[OF eV steps sig refl, of f \<alpha> P, OF f \<beta>]
      show "f (\<lambda> i. eval_l \<beta> (P i)) \<and> \<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e,{})" .
    }
    {
      assume vars: "\<And> i. vars_l (P i) \<subseteq> set v" and sig: "\<sigma> = solution_subst s" 
        and f: "f (\<lambda> i. eval_l \<alpha> (P i)) \<and> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set e,{})"
      from vars have "\<And> i. vars_l (P i) \<subseteq> set V" unfolding V_def by auto
      from griggio_success_translations(2)[OF eV steps sig refl, of f \<alpha> P, OF f this]
      show "\<exists> \<gamma>. f (\<lambda> i. eval_l \<gamma> (substitute_all_l \<sigma> (P i)))" .
    }
  }
qed

(* example application: eliminating linear equalities for constraints that
     consist of linear equalities and linear inequalities *)

definition equality_elim_for_inequalities :: "'v dleq list \<Rightarrow> 'v dlineq list \<Rightarrow> 
  ('v dleq list \<times> ((int,'v)assign \<Rightarrow> (int,'v)assign)) option" where
  "equality_elim_for_inequalities eqs ineqs = (let v = concat (map vars_l_list ineqs)
     in case dleq_solver v eqs of 
       None \<Rightarrow> None
   | Some s \<Rightarrow> let \<sigma> = substitute_all_l (solution_subst s);
                 adj = adjust_assign s
      in Some (map \<sigma> ineqs, adj))" 

lemma equality_elim_for_inequalities: assumes "fresh_var_gen fresh_var"
  and "equality_elim_for_inequalities eqs ineqs = res" 
shows "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, {})" 
  "res = Some (ineqs', adj) \<Longrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> (adj \<alpha>) \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)"  
  "res = Some (ineqs', adj) \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
  "res = Some (ineqs', adj) \<Longrightarrow> length ineqs' = length ineqs"
proof -
  define v where "v = concat (map vars_l_list ineqs)" 
  note res = equality_elim_for_inequalities_def[of eqs ineqs, unfolded assms(2) Let_def, folded v_def]
  note solver = dleq_solver[OF assms(1) refl, of v eqs]
  show "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, {})" 
    using solver(1) unfolding res by (auto split: option.splits)
  assume "res = Some (ineqs', adj)" 
  note res = res[unfolded this]
  from res obtain s where s: "dleq_solver v eqs = Some s" 
    by (cases "dleq_solver v eqs", auto)
  define \<sigma> where "\<sigma> = solution_subst s"
  note res = res[unfolded s option.simps, folded \<sigma>_def]
  from res have adj: "adj = adjust_assign s" 
    and ineqs': "ineqs' = map (substitute_all_l \<sigma>) ineqs" 
    by auto
  define P where "P i = (if i < length ineqs then ineqs ! i else 0)" for i
  define f where "f xs = (\<forall> i < length ineqs. xs i \<le> (0 :: int))" for xs
  note solver = solver(3-4)[OF s \<sigma>_def, where P = P and f = f]
  have "vars_l (P i) \<subseteq> set v" for i unfolding v_def P_def by (auto simp: set_conv_nth[of ineqs])
  note solver = solver(1)[OF _ refl, folded adj] solver(2)[OF this]
  have id: "f (\<lambda>i. eval_l \<alpha> (P i)) = (Ball (set ineqs) (satisfies_dlineq \<alpha>))" for \<alpha> 
    unfolding f_def P_def set_conv_nth by (auto simp: satisfies_dlineq_def)
  note solver = solver[unfolded id eval_substitute_all_l \<sigma>_def]
  from solver(1)[of \<alpha>]
  show "\<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> (adj \<alpha>) \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
    unfolding ineqs' \<sigma>_def
    by (auto simp: satisfies_dlineq_def eval_substitute_all_l)
  show "length ineqs' = length ineqs" unfolding ineqs' by simp
  assume no_sol: "\<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs')"
  show "\<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" (is "\<nexists> \<alpha>. ?Pr \<alpha>")
  proof
    assume "\<exists> \<alpha>. ?Pr \<alpha>" 
    then obtain \<alpha> where "?Pr \<alpha>" by blast
    with solver(2)[of \<alpha>] obtain \<gamma>
      where "Ball (set ineqs) (satisfies_dlineq (\<lambda>x. eval_l \<gamma> (solution_subst s x)))" 
      by blast
    with no_sol show False 
      unfolding ineqs' \<sigma>_def
      by (auto simp: satisfies_dlineq_def eval_substitute_all_l)
  qed
qed

end (* fix fresh-var gen *)


definition fresh_vars_nat :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "fresh_vars_nat xs = (let m = Suc (Max (set (0 # xs))) in (\<lambda> n. m + n))" 

lemma fresh_vars_nat: "fresh_var_gen fresh_vars_nat" 
proof -
  {
    fix xs x
    assume "Suc (Max (insert 0 (set xs)) + x) \<in> insert 0 (set xs)" 
    from Max_ge[OF _ this] have False by auto
  }
  thus ?thesis unfolding fresh_var_gen_def fresh_vars_nat_def Let_def
    by auto
qed

lemmas equality_elim_for_inequalities_nat = equality_elim_for_inequalities[OF fresh_vars_nat]

end