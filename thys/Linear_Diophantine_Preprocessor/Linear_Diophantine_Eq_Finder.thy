subsection \<open>Algorithm to Detect Implicit Equalities in \<open>\<int>\<close>\<close>

text \<open>Use the rational equality finder to identify integer equalities.

Basically, this is just a conversion between the different types of constraints.\<close>

theory Linear_Diophantine_Eq_Finder
  imports 
    Linear_Polynomial_Impl
    Equality_Detection_Impl (* rational equality finder *)
    Diophantine_Tightening (* for satisfies_dlineq *)
begin

definition linear_poly_of_lpoly :: "(int,var)lpoly \<Rightarrow> linear_poly" where
  [code del]: "linear_poly_of_lpoly p = (let cxs = map (\<lambda> v. (v, coeff_l p v)) (vars_l_list p)
     in sum_list (map (\<lambda> (x,c). lp_monom (of_int c) x) cxs))" 

lemma linear_poly_of_lpoly_impl[code]: 
  "linear_poly_of_lpoly (lpoly_of p) = (let cxs = vars_coeffs_impl p
     in sum_list (map (\<lambda> (x,c). lp_monom (of_int c) x) cxs))" 
  unfolding linear_poly_of_lpoly_def vars_coeffs_impl(5) ..

lemma valuate_sum_list: "valuate (sum_list ps) \<alpha> = sum_list (map (\<lambda> p. valuate p \<alpha>) ps)" 
  by (induct ps, auto simp: valuate_zero valuate_add)

lemma linear_poly_of_lpoly: "rat_of_int (eval_l \<alpha> p) = of_int (constant_l p) + valuate (linear_poly_of_lpoly p) (\<lambda> x. of_int (\<alpha> x))"
  unfolding eval_l_def of_int_add
  unfolding linear_poly_of_lpoly_def Let_def map_map o_def split valuate_sum_list valuate_lp_monom
  unfolding of_int_mult[symmetric] of_int_sum
  unfolding vars_l_list_def 
  by (subst sum_list_distinct_conv_sum_set, auto)

definition dleq_to_constraint :: "var dleq \<Rightarrow> constraint" where
  "dleq_to_constraint p = EQ (linear_poly_of_lpoly p) (of_int (- constant_l p))" 

lemma dleq_to_constraint: "satisfies_dleq \<alpha> e \<longleftrightarrow> satisfies_constraint (\<lambda> x. rat_of_int (\<alpha> x)) (dleq_to_constraint e)" 
proof -
  have "satisfies_dleq \<alpha> e \<longleftrightarrow> rat_of_int (eval_l \<alpha> e) = 0" 
    unfolding satisfies_dleq_def by blast
  also have "\<dots> \<longleftrightarrow> satisfies_constraint (\<lambda> x. rat_of_int (\<alpha> x)) (dleq_to_constraint e)" 
    unfolding linear_poly_of_lpoly[of \<alpha> e] dleq_to_constraint_def 
    by auto
  finally show ?thesis .
qed

definition dlineq_to_constraint :: "var dlineq \<Rightarrow> constraint" where
  "dlineq_to_constraint p = LEQ (linear_poly_of_lpoly p) (of_int (- constant_l p))" 

lemma dlineq_to_constraint: "satisfies_dlineq \<alpha> e \<longleftrightarrow> 
  satisfies_constraint (\<lambda> x. rat_of_int (\<alpha> x)) (dlineq_to_constraint e)" 
proof -
  have "satisfies_dlineq \<alpha> e \<longleftrightarrow> rat_of_int (eval_l \<alpha> e) \<le> 0" 
    unfolding satisfies_dlineq_def by simp
  also have "\<dots> \<longleftrightarrow> satisfies_constraint (\<lambda> x. rat_of_int (\<alpha> x)) (dlineq_to_constraint e)" 
    unfolding linear_poly_of_lpoly[of \<alpha> e] dlineq_to_constraint_def 
    by auto
  finally show ?thesis .
qed

definition eq_finder_int :: "var dlineq list \<Rightarrow> 
    (var dleq list \<times> var dlineq list) option" where
  [code del]: "eq_finder_int ineqs = (case 
      eq_finder_rat (map dlineq_to_constraint ineqs) of
         None \<Rightarrow> None
       | Some (idx_eq, _) \<Rightarrow> let I = set idx_eq;
            ics = zip [0..< length ineqs] ineqs
          in case List.partition (\<lambda> (i,c). i \<in> I) ics
            of (eqs2, ineqs2) \<Rightarrow> Some (map snd eqs2, map snd ineqs2))"

lemma classify_dlineq_to_constraint[simp]: 
  "\<not> is_strict (dlineq_to_constraint c)"
  "\<not> is_equality (dlineq_to_constraint c)" 
  "is_nstrict (dlineq_to_constraint c)" 
  by (auto simp: dlineq_to_constraint_def)

lemma init_constraints_ineqs: 
  "init_constraints (map dlineq_to_constraint ineqs) =
     (let idx = [0..<length ineqs];
     ics' = zip idx
        (map dlineq_to_constraint ineqs);
     ics = concat (map index_constraint ics')
     in (ics, idx, [], []))"
  unfolding init_constraints_def length_map Let_def
  apply (clarsimp simp flip: set_empty, intro conjI)   
  subgoal apply (subst filter_True)
    subgoal by (auto dest!: set_zip_rightD)
    subgoal by auto
    done
  by (auto dest!: set_zip_rightD)
  
lemmas eq_finder_int_code[code] = 
  eq_finder_int_def[unfolded eq_finder_rat_def init_eq_finder_rat_def, unfolded init_constraints_ineqs]

lemma eq_finder_int: assumes 
  res: "eq_finder_int ineqs = res"
  shows "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs)" 
    "res = Some (eqs, ineqs') \<Longrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs) \<longleftrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs')" 
    "res = Some (eqs, ineqs') \<Longrightarrow> \<exists> \<alpha>. \<alpha> \<Turnstile>\<^sub>c\<^sub>s (make_strict ` dlineq_to_constraint ` set ineqs')" 
    "res = Some (eqs, ineqs') \<Longrightarrow> length ineqs = length eqs + length ineqs'" 
proof (atomize(full), goal_cases)
  case 1
  define cs where "cs = map dlineq_to_constraint ineqs" 
  let ?sat = "\<lambda> \<alpha> eqs ineqs. Ball (set eqs) (satisfies_dleq \<alpha>) \<and>  Ball (set ineqs) (satisfies_dlineq \<alpha>)" 
  note defs = dlineq_to_constraint dleq_to_constraint
  note defs2 = satisfies_dlineq_def satisfies_dleq_def
  note defs3 = dlineq_to_constraint_def dleq_to_constraint_def
  note res = res[unfolded eq_finder_int_def, folded cs_def]
  show ?case
  proof (cases "eq_finder_rat cs")
    case None
    with res have res: "res = None" by auto
    from eq_finder_rat(1)[OF None, unfolded cs_def]
    have "\<nexists> \<alpha>. ?sat \<alpha> [] ineqs" unfolding defs by auto
    with res show ?thesis by auto
  next
    case (Some pair)  
    then obtain eq_idx sol where eq: "eq_finder_rat cs = Some (eq_idx, sol)" by (cases pair, auto)
    define ics where "ics = zip [0 ..< length ineqs] ineqs" 
    let ?I = "set eq_idx" 
    let ?part = "List.partition (\<lambda>(i, c). i \<in> ?I) ics" 
    obtain ineqs2 eqs2 where part: "?part = (eqs2, ineqs2)" by force
    let ?ineqs2 = "map snd ineqs2" 
    let ?eqs2 = "map snd eqs2" 
    have ics: "ics = map (\<lambda> i. (i, ineqs ! i)) [0 ..< length ineqs]" 
      unfolding ics_def by (intro nth_equalityI, auto)
    from part have eqs2: "?eqs2 = map ((!) ineqs) (filter (\<lambda> i. i \<in> ?I) [0 ..< length ineqs])" 
      unfolding ics by (auto simp: filter_map o_def)
    from part have ineqs2: "?ineqs2 = map ((!) ineqs) (filter (\<lambda> i. i \<notin> ?I) [0 ..< length ineqs])" 
      unfolding ics by (auto simp: filter_map o_def)
    note res = res[unfolded eq option.simps split Let_def, folded ics_def,
      unfolded part split]  
    from eq_finder_rat(2)[OF eq] 
    have eq_finder2: "{i. i < length cs \<and> is_equality (cs ! i)} \<subseteq> ?I"
       "?I \<subseteq> {0..<length cs}"
       "distinct eq_idx" by auto
    have len: "length ineqs = length cs" unfolding cs_def by auto
    from eq_finder2 have filter: "{x \<in> set [0..<length ineqs]. x \<in> ?I} = ?I" 
      unfolding len by force
    from eq_finder2 have filter': "set (filter (\<lambda>i. i \<notin> ?I) [0..<length ineqs]) = {0 ..< length cs} - ?I" 
      unfolding len by force
    have eqs2': "set (map dleq_to_constraint ?eqs2) = make_equality ` (!) cs ` ?I" 
      unfolding set_map eqs2 set_filter image_comp filter o_def using eq_finder2
      by (intro image_cong[OF refl])
        (auto simp: cs_def nth_append defs3)
    have ineqs2': "set (map dlineq_to_constraint ?ineqs2) = (!) cs ` ({0..<length cs} - ?I)" 
      unfolding set_map ineqs2 filter' image_comp o_def
      apply (intro image_cong[OF refl])
      subgoal for i using set_mp[OF eq_finder2(1), of i]
        unfolding defs2 by (auto simp: cs_def nth_append defs3)
      done

    from eq_finder_rat(3)[OF eq eqs2' ineqs2'] have
      equiv: "\<And> v. v \<Turnstile>\<^sub>c\<^sub>s set cs = v \<Turnstile>\<^sub>c\<^sub>s (dleq_to_constraint ` set ?eqs2 \<union> dlineq_to_constraint ` set ?ineqs2)" 
      and strict: "sol \<Turnstile>\<^sub>c\<^sub>s (set (map dleq_to_constraint ?eqs2) \<union> make_strict ` set (map dlineq_to_constraint ?ineqs2))" 
      unfolding set_map by metis+
    from strict have strict: "sol \<Turnstile>\<^sub>c\<^sub>s (make_strict ` dlineq_to_constraint ` set ?ineqs2)" by auto
    {
      let ?\<alpha> = "\<lambda> x :: var. rat_of_int (\<alpha> x)" 
      have "?sat \<alpha> [] ineqs \<longleftrightarrow> ?\<alpha> \<Turnstile>\<^sub>c\<^sub>s set cs" unfolding cs_def 
        by (auto simp: defs)
      also have "\<dots> \<longleftrightarrow> ?sat \<alpha> ?eqs2 ?ineqs2" unfolding equiv 
        using defs[of \<alpha>] by fastforce
      finally have "?sat \<alpha> [] ineqs \<longleftrightarrow> ?sat \<alpha> ?eqs2 ?ineqs2" .
    } note eq = this

    have "length ineqs = length ics" unfolding ics_def by auto
    also have "\<dots> = length eqs2 + length ineqs2" using part[simplified]
      by (smt (verit) comp_def filter_cong sum_length_filter_compl)
    finally show ?thesis using eq res strict by fastforce
  qed
qed
  
end