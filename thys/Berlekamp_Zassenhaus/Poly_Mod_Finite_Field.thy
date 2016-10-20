(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Polynomials in a Finite Field\<close>
text \<open>We connect polynomials in a prime field with integer polynomials modulo some prime.\<close>

theory Poly_Mod_Finite_Field
imports 
  Poly_Mod
  Finite_Field
  "../Polynomial_Interpolation/Ring_Hom_Poly"
begin

abbreviation of_int_poly :: "int poly \<Rightarrow> 'a :: ring_1 poly" where
  "of_int_poly \<equiv> map_poly of_int"

abbreviation to_int_poly :: "'a :: finite mod_ring poly \<Rightarrow> int poly" where
  "to_int_poly \<equiv> map_poly to_int_mod_ring"

interpretation ring_hom_of_int: ring_hom "of_int :: int \<Rightarrow> 'a :: comm_ring_1"
  by (unfold_locales, auto)

lemma irreducible_def_lt: "irreducible f = (degree f \<noteq> 0 \<and> 
  (\<forall> g h. degree g < degree f \<longrightarrow> degree h < degree f \<longrightarrow> f \<noteq> g * h))" 
proof (cases "degree f = 0")
  case True
  thus ?thesis unfolding irreducible_def by auto
next
  case False
  from False have f0: "f \<noteq> 0" by auto
  {
    fix g h
    assume f: "f = g * h" 
    with f0 have "g \<noteq> 0" "h \<noteq> 0" by auto
    from degree_mult_eq[OF this]
    have "degree (g * h) = degree g + degree h" by auto
  } note deg = this
  have "?thesis = ((\<forall> g h. degree g < degree f \<longrightarrow> degree h < degree f \<longrightarrow> f \<noteq> g * h)
    = (\<forall> g h. degree g \<noteq> 0 \<longrightarrow> degree g < degree f \<longrightarrow> f \<noteq> g * h))" 
    unfolding irreducible_def dvd_def using False by auto
  also have "\<dots> = True"
    by (auto simp: deg, force+)
  finally show ?thesis by simp
qed

lemma irreducible_def_0: "irreducible f = (degree f \<noteq> 0 \<and> 
  (\<forall> g h. degree g \<noteq> 0 \<longrightarrow> degree h \<noteq> 0 \<longrightarrow> f \<noteq> g * h))" 
proof (cases "degree f = 0")
  case True
  thus ?thesis unfolding irreducible_def by auto
next
  case False
  from False have f0: "f \<noteq> 0" by auto
  {
    fix g h
    assume f: "f = g * h" 
    with f0 have "g \<noteq> 0" "h \<noteq> 0" by auto
    from degree_mult_eq[OF this]
    have "degree (g * h) = degree g + degree h" by auto
  } note deg = this
  have "?thesis = ((\<forall> g h. degree g \<noteq> 0 \<longrightarrow> degree h \<noteq> 0 \<longrightarrow> f \<noteq> g * h)
    = (\<forall> g h. degree g \<noteq> 0 \<longrightarrow> degree g < degree f \<longrightarrow> f \<noteq> g * h))" 
    unfolding irreducible_def dvd_def using False by auto
  also have "\<dots> = True"
    by (auto simp: deg, force+)
  finally show ?thesis by simp
qed

context poly_mod 
begin

definition factorization_m :: "int poly \<Rightarrow> (int \<times> int poly multiset) \<Rightarrow> bool" where
  "factorization_m f cfs \<equiv> (case cfs of (c,fs) \<Rightarrow> f =m (smult c (prod_mset fs)) \<and> 
    (\<forall> f \<in> set_mset fs. irreducible_m f \<and> monic (Mp f)))"  

definition Mf :: "int \<times> int poly multiset \<Rightarrow> int \<times> int poly multiset" where
  "Mf cfs \<equiv> case cfs of (c,fs) \<Rightarrow> (M c, image_mset Mp fs)" 

lemma Mf_Mf[simp]: "Mf (Mf x) = Mf x" 
proof (cases x, auto simp: Mf_def, goal_cases)
  case (1 c fs)
  show ?case by (induct fs, auto)
qed

definition equivalent_fact_m :: "int \<times> int poly multiset \<Rightarrow> int \<times> int poly multiset \<Rightarrow> bool" where
  "equivalent_fact_m cfs dgs = (Mf cfs = Mf dgs)" 

definition unique_factorization_m :: "int poly \<Rightarrow> (int \<times> int poly multiset) \<Rightarrow> bool" where
  "unique_factorization_m f cfs = (Mf ` Collect (factorization_m f) = {Mf cfs})"

lemma Mp_irreducible_m[simp]: "irreducible_m (Mp f) = irreducible_m f" 
  unfolding irreducible_m_def by simp

lemma Mf_factorization_m[simp]: "factorization_m f (Mf cfs) = factorization_m f cfs" 
  unfolding factorization_m_def Mf_def
proof (cases cfs, simp, goal_cases)
  case (1 c fs)
  have "Mp (smult c (prod_mset fs)) = Mp (smult (M c) (Mp (prod_mset fs)))" by simp
  also have "\<dots> = Mp (smult (M c) (Mp (prod_mset (image_mset Mp fs))))"
    unfolding Mp_prod_mset by simp
  also have "\<dots> = Mp (smult (M c) (prod_mset (image_mset Mp fs)))" unfolding Mp_smult ..
  finally show ?case unfolding equivalent_def by auto
qed    

lemma unique_factorization_m_imp_factorization: assumes "unique_factorization_m f cfs" 
  shows "factorization_m f cfs" 
proof -
  from assms[unfolded unique_factorization_m_def] obtain dfs where
     fact: "factorization_m f dfs" and id: "Mf cfs = Mf dfs" by blast
  from fact have "factorization_m f (Mf dfs)" by simp
  from this[folded id] show ?thesis by simp
qed

lemma unique_factorization_m_alt_def: "unique_factorization_m f cfs = (factorization_m f cfs
  \<and> (\<forall> dgs. factorization_m f dgs \<longrightarrow> Mf dgs = Mf cfs))" 
  using unique_factorization_m_imp_factorization[of f cfs]
  unfolding unique_factorization_m_def by auto


end

locale poly_mod_type = poly_mod m for m :: int + 
  fixes ty :: "'a :: prime_card itself"  
  assumes m: "m = CARD('a)"
begin 
definition MP_Rel :: "int poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> bool" where 
  "MP_Rel f f' \<equiv> (Mp f = to_int_poly f')"

definition M_Rel :: "int \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where 
  "M_Rel x x' \<equiv> (M x = to_int_mod_ring x')"

definition "MF_Rel \<equiv> rel_prod M_Rel (rel_mset MP_Rel)" 
 
lemma to_int_mod_ring_plus: "to_int_mod_ring ((x :: 'a mod_ring) + y) = M (to_int_mod_ring x + to_int_mod_ring y)" 
  unfolding M_def using m by (transfer, auto)

lemma to_int_mod_ring_times: "to_int_mod_ring ((x :: 'a mod_ring) * y) = M (to_int_mod_ring x * to_int_mod_ring y)" 
  unfolding M_def using m by (transfer, auto)

lemma degree_MP_Rel [transfer_rule]: "(MP_Rel ===> op =) degree_m degree" 
  unfolding MP_Rel_def rel_fun_def degree_m_def
  by (auto intro!: degree_map_poly)

lemma eq_M_Rel[transfer_rule]: "(M_Rel ===> M_Rel ===> op =) (\<lambda> x y. M x = M y) (op =)"
  unfolding M_Rel_def rel_fun_def
  by (auto simp: inj_to_int_mod_ring_point)

lemma eq_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> op =) (op =m) (op =)"
  unfolding MP_Rel_def rel_fun_def equivalent_def
  by (auto, intro map_poly_inj[of to_int_mod_ring], auto simp: inj_to_int_mod_ring_point)

lemma eq_Mf_Rel[transfer_rule]: "(MF_Rel ===> MF_Rel ===> op =) (\<lambda> x y. Mf x = Mf y) (op =)"
proof (intro rel_funI, goal_cases)
  case (1 cfs Cfs dgs Dgs)
  have [transfer_rule]: "(MP_Rel ===> MP_Rel ===> op =) (\<lambda> x y. Mp x = Mp y) (op =)" 
    using eq_MP_Rel unfolding equivalent_def[abs_def] .    
  obtain c fs where cfs: "cfs = (c,fs)" by force
  obtain C Fs where Cfs: "Cfs = (C,Fs)" by force
  obtain d gs where dgs: "dgs = (d,gs)" by force
  obtain D Gs where Dgs: "Dgs = (D,Gs)" by force
  note pairs = cfs Cfs dgs Dgs
  from 1[unfolded pairs MF_Rel_def rel_prod.simps]
  have *[transfer_rule]: "M_Rel c C" "M_Rel d D" "rel_mset MP_Rel fs Fs" "rel_mset MP_Rel gs Gs" 
    by auto  
  have eq1: "(M c = M d) = (C = D)" by transfer_prover
  from *(3)[unfolded rel_mset_def] obtain fs' Fs' where fs_eq: "mset fs' = fs" "mset Fs' = Fs"
    and rel_f: "list_all2 MP_Rel fs' Fs'" by auto
  from *(4)[unfolded rel_mset_def] obtain gs' Gs' where gs_eq: "mset gs' = gs" "mset Gs' = Gs"
    and rel_g: "list_all2 MP_Rel gs' Gs'" by auto
  have eq2: "(image_mset Mp fs = image_mset Mp gs) = (Fs = Gs)" 
    using *(3-4)
  proof (induct fs arbitrary: Fs gs Gs)
    case (empty Fs gs Gs)
    from empty(1) have Fs: "Fs = {#}" unfolding rel_mset_def by auto
    with empty show ?case by (cases gs; cases Gs; auto simp: rel_mset_def)
  next
    case (add f fs Fs' gs' Gs')
    note [transfer_rule] = add(3)
    from msed_rel_invL[OF add(2)]
    obtain Fs F where Fs': "Fs' = Fs + {#F#}" and rel[transfer_rule]: 
      "MP_Rel f F" "rel_mset MP_Rel fs Fs" by auto      
    note IH = add(1)[OF rel(2)]
    {      
      from add(3)[unfolded rel_mset_def] obtain gs Gs where id: "mset gs = gs'" "mset Gs = Gs'" 
        and rel: "list_all2 MP_Rel gs Gs" by auto
      have "Mp f \<in># image_mset Mp gs' \<longleftrightarrow> F \<in># Gs'" 
      proof -
        have "?thesis = ((Mp f \<in> Mp ` set gs) = (F \<in> set Gs))" 
          unfolding id[symmetric] by simp
        also have \<dots> using rel
        proof (induct gs Gs rule: list_all2_induct)
          case (Cons g gs G Gs)
          note [transfer_rule] = Cons(1-2)
          have id: "(Mp g = Mp f) = (F = G)" by (transfer, auto)
          show ?case using id Cons(3) by auto
        qed auto
        finally show ?thesis by simp
      qed
    } note id = this
    show ?case
    proof (cases "Mp f \<in># image_mset Mp gs'")
      case False
      have "Mp f \<in># image_mset Mp (fs + {#f#})" by auto
      with False have F: "image_mset Mp (fs + {#f#}) \<noteq> image_mset Mp gs'" by metis
      with False[unfolded id] show ?thesis unfolding Fs' by auto
    next
      case True
      then obtain g where fg: "Mp f = Mp g" and g: "g \<in># gs'" by auto
      from g obtain gs where gs': "gs' = add_mset g gs" by (rule mset_add)
      from msed_rel_invL[OF add(3)[unfolded gs']]
      obtain Gs G where Gs': "Gs' = Gs + {# G #}" and gG[transfer_rule]: "MP_Rel g G" and 
        gsGs: "rel_mset MP_Rel gs Gs" by auto
      have FG: "F = G" by (transfer, simp add: fg)
      note IH = IH[OF gsGs]
      show ?thesis unfolding gs' Fs' Gs' by (simp add: fg IH FG)
    qed
  qed
  show "(Mf cfs = Mf dgs) = (Cfs = Dgs)" unfolding pairs Mf_def split
    by (simp add: eq1 eq2)
qed

lemmas coeff_map_poly_to_int_mod_ring = coeff_map_poly[of to_int_mod_ring, OF to_int_mod_ring_0]
lemmas coeff_map_poly_of_int = coeff_map_poly[of of_int, OF of_int_0]

lemma plus_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> MP_Rel) (op +) (op +)"
  unfolding MP_Rel_def 
proof (intro rel_funI, goal_cases)
  case (1 x f y g)
  have "Mp (x + y) = Mp (Mp x + Mp y)" by simp
  also have "\<dots> = Mp (map_poly to_int_mod_ring f + map_poly to_int_mod_ring g)" unfolding 1 ..
  also have "\<dots> = map_poly to_int_mod_ring (f + g)" unfolding poly_eq_iff Mp_coeff 
    coeff_add coeff_map_poly_to_int_mod_ring to_int_mod_ring_plus by auto
  finally show ?case .
qed

lemma times_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> MP_Rel) (op *) (op *)"
  unfolding MP_Rel_def
proof (intro rel_funI, goal_cases)
  case (1 x f y g)
  have "Mp (x * y) = Mp (Mp x * Mp y)" by simp
  also have "\<dots> = Mp (map_poly to_int_mod_ring f * map_poly to_int_mod_ring g)" unfolding 1 ..
  also have "\<dots> = map_poly to_int_mod_ring (f * g)" unfolding poly_eq_iff Mp_coeff 
    coeff_mult coeff_map_poly_to_int_mod_ring
  proof 
    fix n :: nat
    define A where "A = {.. n}" 
    have "finite A" unfolding A_def by auto
    thus "M (\<Sum>i\<le>n. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))) =
         to_int_mod_ring (\<Sum>i\<le>n. coeff f i * coeff g (n - i))"
      unfolding A_def[symmetric]
    proof (induct A)
      case (insert a A)
      have "?case = ?case" (is "(?l = ?r) = _") by simp
      have "?r = to_int_mod_ring (coeff f a * coeff g (n - a) + (\<Sum>i\<in> A. coeff f i * coeff g (n - i)))" 
        using insert(1-2) by auto
      note r = this[unfolded to_int_mod_ring_plus to_int_mod_ring_times]
      from insert(1-2) have "?l = M (to_int_mod_ring (coeff f a) * to_int_mod_ring (coeff g (n - a)) 
        + M (\<Sum>i\<in>A. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))))" 
        by simp
      also have "M (\<Sum>i\<in>A. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))) = to_int_mod_ring (\<Sum>i\<in>A. coeff f i * coeff g (n - i))"
        unfolding insert ..
      finally
      show ?case unfolding r by simp
    qed auto
  qed
  finally show ?case .
qed

lemma smult_MP_Rel[transfer_rule]: "(M_Rel ===> MP_Rel ===> MP_Rel) smult smult"
  unfolding MP_Rel_def M_Rel_def
proof (intro rel_funI, goal_cases)
  case (1 x x' f f')
  thus ?case unfolding poly_eq_iff coeff coeff_map_poly_to_int_mod_ring Mp_coeff
    coeff_smult M_def
  proof (intro allI, goal_cases)
    case (1 n)
    have "x * coeff f n mod m = (x mod m) * (coeff f n mod m) mod m" 
      by (simp add: zmod_simps)
    also have "\<dots> = to_int_mod_ring x' * (to_int_mod_ring (coeff f' n)) mod m" 
      using 1 by auto
    also have " \<dots> = to_int_mod_ring (x' * coeff f' n)" 
      unfolding to_int_mod_ring_times M_def by simp
    finally show ?case .
  qed
qed

lemma one_M_Rel[transfer_rule]: "M_Rel 1 1"
  unfolding M_Rel_def poly_eq_iff Mp_coeff M_def coeff_map_poly_to_int_mod_ring 
  unfolding m by auto

lemma one_MP_Rel[transfer_rule]: "MP_Rel 1 1"
  unfolding MP_Rel_def poly_eq_iff Mp_coeff M_def coeff_map_poly_to_int_mod_ring 
  unfolding m by auto

lemma zero_MP_Rel[transfer_rule]: "MP_Rel 0 0" 
  unfolding MP_Rel_def poly_eq_iff Mp_coeff M_def coeff_map_poly_to_int_mod_ring 
  unfolding m by auto

lemma listprod_MP_Rel[transfer_rule]: "(list_all2 MP_Rel ===> MP_Rel) prod_list prod_list"
proof (intro rel_funI, goal_cases)
  case (1 xs ys)
  thus ?case 
  proof (induct xs ys rule: list_all2_induct)
    case (Cons x xs y ys)
    note [transfer_rule] = this
    show ?case by simp transfer_prover
  qed (simp add: one_MP_Rel)
qed

lemma prod_mset_MP_Rel[transfer_rule]: "(rel_mset MP_Rel ===> MP_Rel) prod_mset prod_mset"
proof (intro rel_funI, goal_cases)
  case (1 xs ys)
  have "(MP_Rel ===> MP_Rel ===> MP_Rel) (op *) (op *)" "MP_Rel 1 1" by transfer_prover+
  from 1 this show ?case
  proof (induct xs ys rule: rel_mset_induct)
    case (add R x xs y ys)
    note [transfer_rule] = this
    show ?case by simp transfer_prover
  qed (simp add: one_MP_Rel)
qed

lemma right_unique_MP_Rel[transfer_rule]: "right_unique MP_Rel"
  unfolding right_unique_def MP_Rel_def
  by (auto intro!: map_poly_inj[of to_int_mod_ring] inj_to_int_mod_ring_point)

lemma M_to_int_mod_ring: "M (to_int_mod_ring (x :: 'a mod_ring)) = to_int_mod_ring x"
  unfolding M_def unfolding m by (transfer, auto)

lemma Mp_to_int_poly: "Mp (to_int_poly (f :: 'a mod_ring poly)) = to_int_poly f"
  unfolding poly_eq_iff Mp_coeff coeff_map_poly_to_int_mod_ring M_to_int_mod_ring
  by auto

lemma right_total_M_Rel[transfer_rule]: "right_total M_Rel"
  unfolding right_total_def M_Rel_def using M_to_int_mod_ring by blast

lemma left_total_M_Rel[transfer_rule]: "left_total M_Rel"
  unfolding left_total_def M_Rel_def[abs_def] 
proof
  fix x
  show "\<exists> x' :: 'a mod_ring. M x = to_int_mod_ring x'"  unfolding M_def unfolding m
    by (rule exI[of _ "of_int x"], transfer, simp)
qed

lemma bi_total_M_Rel[transfer_rule]: "bi_total M_Rel" 
  using right_total_M_Rel left_total_M_Rel by (metis bi_totalI)

lemma right_total_MP_Rel[transfer_rule]: "right_total MP_Rel"
  unfolding right_total_def MP_Rel_def
proof
  fix f :: "'a mod_ring poly"
  show "\<exists>x. Mp x = to_int_poly f"
    by (intro exI[of _ "to_int_poly f"], simp add: Mp_to_int_poly)
qed

lemma to_int_mod_ring_of_int_M: "to_int_mod_ring (of_int x :: 'a mod_ring) = M x" unfolding M_def
  unfolding m by transfer auto

lemma Mp_f_representative: "Mp f = to_int_poly (map_poly of_int f :: 'a mod_ring poly)"
  unfolding Mp_def poly_eq_iff coeff_map_poly_to_int_mod_ring
  by (subst coeff_map_poly[of M], force, subst coeff_map_poly, auto simp: to_int_mod_ring_of_int_M)

lemma left_total_MP_Rel[transfer_rule]: "left_total MP_Rel"
  unfolding left_total_def MP_Rel_def[abs_def] using Mp_f_representative by blast

lemma bi_total_MP_Rel[transfer_rule]: "bi_total MP_Rel"
  using right_total_MP_Rel left_total_MP_Rel by (metis bi_totalI)

lemma bi_total_MF_Rel[transfer_rule]: "bi_total MF_Rel"
  unfolding MF_Rel_def[abs_def] 
  by (intro prod.bi_total_rel multiset.bi_total_rel bi_total_MP_Rel bi_total_M_Rel)

lemma right_total_MF_Rel[transfer_rule]: "right_total MF_Rel"
  using bi_total_MF_Rel unfolding bi_total_alt_def by auto

lemma left_total_MF_Rel[transfer_rule]: "left_total MF_Rel"
  using bi_total_MF_Rel unfolding bi_total_alt_def by auto

lemma domain_RT_rel[transfer_domain_rule]: "Domainp MP_Rel = (\<lambda> f. True)"
proof
  fix f :: "int poly"
  show "Domainp MP_Rel f = True" unfolding MP_Rel_def[abs_def] Domainp.simps
    by (auto simp: Mp_f_representative)
qed

lemma dvd_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> op =) (op dvdm) (op dvd)"
  unfolding dvdm_def[abs_def] dvd_def[abs_def]
  by (transfer_prover_start, transfer_step+, auto)

lemma irreducible_MP_Rel [transfer_rule]: "(MP_Rel ===> op =) irreducible_m irreducible"
  unfolding irreducible_m_def[abs_def] irreducible_def_lt[abs_def]
  by (transfer_prover_start, transfer_step+, auto)

lemma UNIV_M_Rel[transfer_rule]: "rel_set M_Rel {0..<m} UNIV" 
  unfolding rel_set_def M_Rel_def[abs_def] M_def 
  by (auto simp: M_def m, goal_cases, metis to_int_mod_ring_of_int_mod_ring, (transfer, auto)+)

lemma coeff_MP_Rel [transfer_rule]: "(MP_Rel ===> op = ===> M_Rel) coeff coeff" 
  unfolding rel_fun_def M_Rel_def MP_Rel_def
  by (metis coeff_map_poly_to_int_mod_ring poly_mod.Mp_coeff)

lemma M_1_1[simp]: "M 1 = 1" unfolding M_def unfolding m by simp

lemma factorization_MP_Rel [transfer_rule]: "(MP_Rel ===> MF_Rel ===> op =)
  factorization_m (factorization Irr_Mon)"
  unfolding rel_fun_def
proof (intro allI impI, goal_cases)
  case (1 f F cfs Cfs)
  note [transfer_rule] = 1(1)
  obtain c fs where cfs: "cfs = (c,fs)" by force
  obtain C Fs where Cfs: "Cfs = (C,Fs)" by force
  from 1(2)[unfolded rel_prod.simps cfs Cfs MF_Rel_def] 
  have tr[transfer_rule]: "M_Rel c C" "rel_mset MP_Rel fs Fs" by auto
  have eq: "(f =m smult c (prod_mset fs) = (F = smult C (prod_mset Fs)))" 
    by transfer_prover
  have "set_mset Fs \<subseteq> Irr_Mon = (\<forall> x \<in># Fs. irreducible x \<and> monic x)" unfolding Irr_Mon_def by auto
  also have "\<dots> = (\<forall>f\<in>#fs. irreducible_m f \<and> monic (Mp f))"
  proof (rule sym, transfer_prover_start, transfer_step+)
    {
      fix f
      assume "f \<in># fs" 
      have "monic (Mp f) \<longleftrightarrow> M (coeff f (degree_m f)) = M 1"
        unfolding Mp_coeff[symmetric] degree_m_def by simp
    }
    thus "(\<forall>f\<in>#fs. irreducible_m f \<and> monic (Mp f)) = 
      (\<forall>x\<in>#fs. irreducible_m x \<and> M (coeff x (degree_m x)) = M 1)" by auto
  qed
  finally     
  show "factorization_m f cfs = factorization Irr_Mon F Cfs" unfolding cfs Cfs
    factorization_m_def factorization_def split eq by simp
qed

lemma unique_factorization_MP_Rel [transfer_rule]: "(MP_Rel ===> MF_Rel ===> op =)
  unique_factorization_m (unique_factorization Irr_Mon)"
  unfolding rel_fun_def
proof (intro allI impI, goal_cases)
  case (1 f F cfs Cfs)
  note [transfer_rule] = 1(1,2)
  let ?F = "factorization Irr_Mon F" 
  let ?f = "factorization_m f" 
  let ?R = "Collect ?F" 
  let ?L = "Mf ` Collect ?f"
  note X_to_x = right_total_MF_Rel[unfolded right_total_def, rule_format]
  {
    fix X
    assume "X \<in> ?R" 
    hence F: "?F X" by simp
    from X_to_x[of X] obtain x where rel[transfer_rule]: "MF_Rel x X" by blast
    from F[untransferred] have "Mf x \<in> ?L" by blast
    with rel have "\<exists> x. Mf x \<in> ?L \<and> MF_Rel x X" by blast
  } note R_to_L = this
  show "unique_factorization_m f cfs = unique_factorization Irr_Mon F Cfs" unfolding 
    unique_factorization_m_def unique_factorization_def  
  proof -
    have fF: "?F Cfs = ?f cfs" by transfer simp
    have "(?L = {Mf cfs}) = (?L \<subseteq> {Mf cfs} \<and> Mf cfs \<in> ?L)" by blast
    also have "?L \<subseteq> {Mf cfs} = (\<forall> dfs. ?f dfs \<longrightarrow> Mf dfs = Mf cfs)" by blast
    also have "\<dots> = (\<forall> y. ?F y \<longrightarrow> y = Cfs)" (is "?left = ?right")
    proof (rule; intro allI impI)
      fix Dfs
      assume *: ?left and F: "?F Dfs" 
      from X_to_x[of Dfs] obtain dfs where [transfer_rule]: "MF_Rel dfs Dfs" by auto
      from F[untransferred] have f: "?f dfs" .
      from *[rule_format, OF f] have eq: "Mf dfs = Mf cfs" by simp
      have "(Mf dfs = Mf cfs) = (Dfs = Cfs)" by (transfer_prover_start, transfer_step+, simp) 
      thus "Dfs = Cfs" using eq by simp
    next
      fix dfs
      assume *: ?right and f: "?f dfs" 
      from left_total_MF_Rel obtain Dfs where 
        rel[transfer_rule]: "MF_Rel dfs Dfs" unfolding left_total_def by blast
      have "?F Dfs" by (transfer, rule f)
      from *[rule_format, OF this] have eq: "Dfs = Cfs" .
      have "(Mf dfs = Mf cfs) = (Dfs = Cfs)" by (transfer_prover_start, transfer_step+, simp) 
      thus "Mf dfs = Mf cfs" using eq by simp
    qed    
    also have "Mf cfs \<in> ?L = (\<exists> dfs. ?f dfs \<and> Mf cfs = Mf dfs)" by auto
    also have "\<dots> = ?F Cfs"  unfolding fF
    proof
      assume "\<exists> dfs. ?f dfs \<and> Mf cfs  = Mf dfs" 
      then obtain dfs where f: "?f dfs" and id: "Mf dfs = Mf cfs" by auto
      from f have "?f (Mf dfs)" by simp
      from this[unfolded id] show "?f cfs" by simp
    qed blast
    finally show "(?L = {Mf cfs}) = (?R = {Cfs})" by auto
  qed
qed


lemma square_free_MP_Rel [transfer_rule]: "(MP_Rel ===> op =) square_free_m square_free"
  unfolding square_free_m_def[abs_def] square_free_def[abs_def]
  by (transfer_prover_start, transfer_step+, auto)

lemma coprime_MP_Rel [transfer_rule]: "(MP_Rel ===> MP_Rel ===> op =) coprime_m coprime"
  unfolding coprime_m_def[abs_def] coprime[abs_def]
  by (transfer_prover_start, transfer_step+, auto)
end
end
