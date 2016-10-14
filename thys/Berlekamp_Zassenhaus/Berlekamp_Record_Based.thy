(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Record Based Version\<close>
theory Berlekamp_Record_Based
imports
  Berlekamp_Type_Based
  Matrix_Record_Based
  Poly_Mod_Finite_Field_Record_Based
  "../Perron_Frobenius/Types_To_Sets/Types_To_Sets"
  "../Jordan_Normal_Form/Matrix_IArray_Impl"
  "../Jordan_Normal_Form/Gauss_Jordan_IArray_Impl"  
  "../Polynomial_Interpolation/Improved_Code_Equations"
  "../Polynomial_Factorization/Missing_List"
begin

text \<open>Whereas @{thm berlekamp_factorization} provides a result for a polynomials over GF(p),
  we now develop a theorem which speaks about integer polynomials modulo p.\<close>
context poly_mod_type
begin
lemma berlekamp_factorization_modulo_ring: assumes g: "(g :: 'a mod_ring poly) = of_int_poly f"
  and sf: "square_free_m f"
  and fact: "berlekamp_factorization g = (d,gs)"
  and c: "c = to_int_mod_ring d"
  and fs: "fs = map to_int_poly gs"
  shows "unique_factorization_m f (c, mset fs)"
proof -
  have [transfer_rule]: "MP_Rel f g" unfolding g MP_Rel_def by (simp add: Mp_f_representative)
  have sg: "square_free g" by (transfer, rule sf)
  have [transfer_rule]: "M_Rel c d" unfolding M_Rel_def c by (rule M_to_int_mod_ring)
  have fs_gs[transfer_rule]: "list_all2 MP_Rel fs gs"
    unfolding fs list_all2_map1 MP_Rel_def[abs_def] Mp_to_int_poly by (simp add: list.rel_refl)
  have [transfer_rule]: "rel_mset MP_Rel (mset fs) (mset gs)"
    using fs_gs using rel_mset_def by blast
  have [transfer_rule]: "MF_Rel (c,mset fs) (d,mset gs)" unfolding MF_Rel_def by transfer_prover
  from berlekamp_factorization[OF sg fact]
  have uf: "unique_factorization Irr_Mon g (d,mset gs)" by auto
  from uf[untransferred] show "unique_factorization_m f (c, mset fs)" .
qed
end

text \<open>We now have to implement @{const berlekamp_factorization}.\<close>  
context
  fixes p :: int
  and ff_ops :: "int arith_ops_record"  (* finite-fields *)
begin

fun power_poly_f_mod_i :: "(int list \<Rightarrow> int list) \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "power_poly_f_mod_i modulus a n = (if n = 0 then modulus (one_poly_i ff_ops)
    else let (d,r) = Divides.divmod_nat n 2; 
       rec = power_poly_f_mod_i modulus (modulus (times_poly_i ff_ops a a)) d in 
    if r = 0 then rec else modulus (times_poly_i ff_ops rec a))"

declare power_poly_f_mod_i.simps[simp del]

fun power_polys_i :: "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list list" where
  "power_polys_i mul_p u curr_p (Suc i) = curr_p # 
      power_polys_i mul_p u (mod_field_poly_i ff_ops (times_poly_i ff_ops curr_p mul_p) u) i"
| "power_polys_i mul_p u curr_p 0 = []"

lemma length_power_polys_i[simp]: "length (power_polys_i x y z n) = n" 
  by (induct n arbitrary: x y z, auto)

definition berlekamp_mat_i :: "int list \<Rightarrow> int mat" where
  "berlekamp_mat_i u = (let n = degree_i u;
    mul_p = power_poly_f_mod_i (\<lambda> v. mod_field_poly_i ff_ops v u) [0,1] (nat p);
    xks = power_polys_i mul_p u [1] n
   in mat_of_rows_list n (map (\<lambda> cs. cs @ replicate (n - length cs) 0) xks))"

definition berlekamp_resulting_mat_i :: "int list \<Rightarrow> int mat" where
"berlekamp_resulting_mat_i u = (let Q = berlekamp_mat_i u;
    n = dim\<^sub>r Q;
    QI = mat n n (\<lambda> (i,j). if i = j then minus_p p (Q $$ (i,j)) 1 else Q $$ (i,j))
    in (gauss_jordan_single_i ff_ops (mat_transpose QI)))"

definition berlekamp_basis_i :: "int list \<Rightarrow> int list list" where
  "berlekamp_basis_i u = (map (poly_of_list_i ff_ops o list_of_vec) 
    (find_base_vectors_i ff_ops (berlekamp_resulting_mat_i u)))"

primrec berlekamp_factorization_main_i :: "int list list \<Rightarrow> int list list \<Rightarrow> nat \<Rightarrow> int list list" where
  "berlekamp_factorization_main_i divs (v # vs) n = (
    if v = [1] then berlekamp_factorization_main_i divs vs n else
    if length divs = n then divs else
    let facts = [ w . u \<leftarrow> divs, s \<leftarrow> [0 ..< nat p], w \<leftarrow> [gcd_poly_i ff_ops u (minus_poly_i ff_ops v (if s = 0 then [] else [int s]))], w \<noteq> [1]];
      (lin,nonlin) = partition (\<lambda> q. degree_i q = 1) facts 
      in lin @ berlekamp_factorization_main_i nonlin vs (n - length lin))"
| "berlekamp_factorization_main_i divs [] n = divs"

definition berlekamp_factorization_i :: "int list \<Rightarrow> int \<times> int list list" where
  "berlekamp_factorization_i f = (if degree_i f = 0 then (lead_coeff_i ff_ops f,[]) else let
     a = lead_coeff_i ff_ops f;
     u = smult_i ff_ops (inverse_p p a) f;
     vs = berlekamp_basis_i u;
     n = length vs;
     fs = berlekamp_factorization_main_i [u] vs n
    in (a,fs))"         

end

context prime_field
begin

lemma power_polys_i: assumes i: "i < n" and [transfer_rule]: "ff.poly_rel f f'" "ff.poly_rel g g'" 
  and h: "ff.poly_rel h h'"
  shows "ff.poly_rel (power_polys_i ff_ops g f h n ! i) (power_polys g' f' h' n ! i)"
  using i h
proof (induct n arbitrary: h h' i)
  case (Suc n h h' i) note * = this
  note [transfer_rule] = *(3)
  show ?case 
  proof (cases i)
    case 0
    with Suc show ?thesis by auto
  next
    case (Suc j)
    with *(2-) have "j < n" by auto
    note IH = *(1)[OF this]
    show ?thesis unfolding Suc by (simp, rule IH, transfer_prover)
  qed
qed simp

lemma power_poly_f_mod_i: assumes m: "(ff.poly_rel ===> ff.poly_rel) m (\<lambda> x'. x' mod m')"
  shows "ff.poly_rel f f' \<Longrightarrow> ff.poly_rel (power_poly_f_mod_i ff_ops m f n) (power_poly_f_mod m' f' n)"
proof -
  from m have m: "\<And> x x'. ff.poly_rel x x' \<Longrightarrow> ff.poly_rel (m x) (x' mod m')" 
    unfolding rel_fun_def by auto
  show "ff.poly_rel f f' \<Longrightarrow> ff.poly_rel (power_poly_f_mod_i ff_ops m f n) (power_poly_f_mod m' f' n)"
  proof (induct n arbitrary: f f' rule: less_induct)
    case (less n f f')
    note f[transfer_rule] = less(2)
    show ?case
    proof (cases "n = 0")
      case True
      show ?thesis 
        by (simp add: True power_poly_f_mod_i.simps power_poly_f_mod_binary, 
          rule m[OF ff.poly_rel_one])
    next
      case False
      hence n: "(n = 0) = False" by simp
      obtain q r where div: "Divides.divmod_nat n 2 = (q,r)" by force
      from this[unfolded divmod_nat_div_mod] n have "q < n" by auto
      note IH = less(1)[OF this]
      have rec: "ff.poly_rel (power_poly_f_mod_i ff_ops m (m (times_poly_i ff_ops f f)) q) 
        (power_poly_f_mod m' (f' * f' mod m') q)" 
        by (rule IH, rule m, transfer_prover)
      have other: "ff.poly_rel 
        (m (times_poly_i ff_ops (power_poly_f_mod_i ff_ops m (m (times_poly_i ff_ops f f)) q) f))
        (power_poly_f_mod m' (f' * f' mod m') q * f' mod m')" 
        by (rule m, rule ff.poly_rel_times[unfolded rel_fun_def, rule_format, OF rec f])
      show ?thesis unfolding power_poly_f_mod_i.simps[of _ _ _ n] Let_def 
        power_poly_f_mod_binary[of _ _ n] div split n if_False using rec other by auto
    qed
  qed
qed
    
lemma berlekamp_mat_i[transfer_rule]: "(ff.poly_rel ===> mat_rel mod_ring_rel) 
  (berlekamp_mat_i p ff_ops) berlekamp_mat"
proof (intro rel_funI)
  fix f f' 
  assume f[transfer_rule]: "ff.poly_rel f f'"
  have deg: "degree_i f = degree f'" by transfer_prover
  {
    fix i j
    assume i: "i < degree f'" and j: "j < degree f'" 
    define cs where "cs = (\<lambda>cs :: int list. cs @ replicate (degree f' - length cs) 0)"
    define cs' where "cs' = (\<lambda>cs :: 'a mod_ring poly. coeffs cs @ replicate (degree f' - length (coeffs cs)) 0)"
    define poly where "poly = power_polys_i ff_ops
         (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [0, 1] (nat p)) f [1]
         (degree f')"
    define poly' where "poly' = (power_polys (power_poly_f_mod f' [:0, 1:] (nat p)) f' 1 (degree f'))"
    have *: "ff.poly_rel (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [0, 1] (nat p))
      (power_poly_f_mod f' [:0, 1:] (nat p))" 
      by (rule power_poly_f_mod_i, transfer_prover, simp add: ff.poly_rel_def mod_ring_0 mod_ring_1)
    have [transfer_rule]: "ff.poly_rel (poly ! i) (poly' ! i)" 
      unfolding poly_def poly'_def 
      by (rule power_polys_i[OF i f *], simp add: ff.poly_rel_def mod_ring_1)
    have *: "list_all2 mod_ring_rel (cs (poly ! i)) (cs' (poly' ! i))"
      unfolding cs_def cs'_def by transfer_prover
    from list_all2_nthD[OF *[unfolded ff.poly_rel_def], of j] j
    have "mod_ring_rel (cs (poly ! i) ! j) (cs' (poly' ! i) ! j)" unfolding cs_def by auto
    hence "mod_ring_rel
            (mat_of_rows_list (degree f')
              (map (\<lambda>cs. cs @ replicate (degree f' - length cs) 0)
                (power_polys_i ff_ops
                  (power_poly_f_mod_i ff_ops (\<lambda>v. mod_field_poly_i ff_ops v f) [0, 1] (nat p)) f [1]
                  (degree f'))) $$
             (i, j))
            (mat_of_rows_list (degree f')
              (map (\<lambda>cs. coeffs cs @ replicate (degree f' - length (coeffs cs)) 0)
                (power_polys (power_poly_f_mod f' [:0, 1:] (nat p)) f' 1 (degree f'))) $$
             (i, j))"           
        unfolding mat_of_rows_list_def length_map length_power_polys_i power_polys_works
          length_power_polys mat_index_mat[OF i j] split
        unfolding poly_def cs_def poly'_def cs'_def using i
        by auto
  } note main = this
  show "mat_rel mod_ring_rel (berlekamp_mat_i p ff_ops f) (berlekamp_mat f')"
    unfolding berlekamp_mat_i_def berlekamp_mat_def Let_def nat_p[symmetric] deg
    unfolding mat_rel_def
    by (intro conjI allI impI, insert main, auto)
qed

lemma berlekamp_resulting_mat_i[transfer_rule]: "(ff.poly_rel ===> mat_rel mod_ring_rel) 
  (berlekamp_resulting_mat_i p ff_ops) berlekamp_resulting_mat"
proof (intro rel_funI)
  fix f f'
  assume "ff.poly_rel f f'"
  from berlekamp_mat_i[unfolded rel_fun_def, rule_format, OF this]
  have bmi: "mat_rel mod_ring_rel (berlekamp_mat_i p ff_ops f) (berlekamp_mat f')" .
  show "mat_rel mod_ring_rel (berlekamp_resulting_mat_i p ff_ops f) (berlekamp_resulting_mat f')"
    unfolding berlekamp_resulting_mat_def Let_def berlekamp_resulting_mat_i_def
    by (rule field_ops.gauss_jordan_i[OF finite_field_ops, unfolded rel_fun_def, rule_format],
    insert bmi, auto simp: mat_rel_def mod_ring_1 intro!: mod_ring_minus[unfolded rel_fun_def, rule_format])
qed

lemma berlekamp_basis_i[transfer_rule]: "(ff.poly_rel ===> list_all2 ff.poly_rel) 
  (berlekamp_basis_i p ff_ops) berlekamp_basis"
  unfolding berlekamp_basis_i_def[abs_def] berlekamp_basis_code[abs_def] o_def
  by transfer_prover

lemma berlekamp_factorization_main_i[transfer_rule]: 
  "(list_all2 ff.poly_rel ===> list_all2 ff.poly_rel ===> op = ===> list_all2 ff.poly_rel) 
     (berlekamp_factorization_main_i p ff_ops) berlekamp_factorization_main" 
proof (intro rel_funI, clarify, goal_cases)
  case (1 xs xs' ys ys' _ n)
  from 1(2) 1(1) show ?case
  proof (induct ys ys' arbitrary: xs xs' n rule: list_all2_induct)   
    case (Cons y ys y' ys' xs xs' n)
    note trans[transfer_rule] = Cons(1,2,4)
    define facts where "facts = concat (map (\<lambda>u. concat
                        (map (\<lambda>s. if gcd_poly_i ff_ops u
                                      (minus_poly_i ff_ops y (if s = 0 then [] else [int s])) \<noteq>
                                     [1]
                                  then [gcd_poly_i ff_ops u
                                         (minus_poly_i ff_ops y (if s = 0 then [] else [int s]))]
                                  else [])
                          [0..<nat p])) xs)"
    define facts' where "facts' = concat
             (map (\<lambda>u. concat
                        (map (\<lambda>x. if gcd u (y' - [:of_nat x:]) \<noteq> 1
                                  then [gcd u (y' - [:of_int (int x):])] else [])
                          [0..<nat p]))
               xs')" 
    have id: "\<And> x. of_int (int x) = of_nat x" "[1] = one_poly_i ff_ops" 
      by (auto simp: one_poly_i_def finite_field_ops_def)
    have facts[transfer_rule]: "list_all2 ff.poly_rel facts facts'"
      unfolding facts_def facts'_def
    apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
    apply (rule list.map_transfer[unfolded rel_fun_def, rule_format, OF _ trans(3)])
    apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
    apply (rule list_all2_map_map)      
    proof (unfold id)
      fix f f' x
      assume [transfer_rule]: "ff.poly_rel f f'" and x: "x \<in> set [0..<nat p]"
      from x have [transfer_rule]: "ff.poly_rel (if x = 0 then [] else [int x]) [:of_nat x:]"
        unfolding ff.poly_rel_def by (simp add: cCons_def p mod_ring_rel_unsafe)
      show "list_all2 ff.poly_rel
          (if gcd_poly_i ff_ops f (minus_poly_i ff_ops y (if x = 0 then [] else [int x])) \<noteq> one_poly_i ff_ops
           then [gcd_poly_i ff_ops f (minus_poly_i ff_ops y (if x = 0 then [] else [int x]))]
           else [])
          (if gcd f' (y' - [:of_nat x:]) \<noteq> 1 then [gcd f' (y' - [:of_nat x:])] else [])"
        by transfer_prover
    qed
    have id1: "berlekamp_factorization_main_i p ff_ops xs (y # ys) n = (
      if y = [1] then berlekamp_factorization_main_i p ff_ops xs ys n else
      if length xs = n then xs else
      (let fac = facts;
          (lin, nonlin) = partition (\<lambda>q. degree_i q = 1) fac
             in lin @ berlekamp_factorization_main_i p ff_ops nonlin ys (n - length lin)))" 
      by (simp add: o_def facts_def)
    have id2: "berlekamp_factorization_main xs' (y' # ys') n = (
      if y' = 1 then berlekamp_factorization_main xs' ys' n
      else if length xs' = n then xs' else
      (let fac = facts';
          (lin, nonlin) = partition (\<lambda>q. degree q = 1) fac
              in lin @ berlekamp_factorization_main nonlin ys' (n - length lin)))"
      by (simp add: o_def facts'_def nat_p)
    have len: "length xs = length xs'" by transfer_prover
    have id3: "(y = [1]) = (y' = 1)" 
      by (transfer_prover_start, transfer_step+, simp add: one_poly_i_def finite_field_ops_def)
    show ?case
    proof (cases "y' = 1")
      case True
      hence id4: "(y' = 1) = True" by simp
      show ?thesis unfolding id1 id2 id3 id4 if_True
        by (rule Cons(3), transfer_prover)
    next
      case False
      hence id4: "(y' = 1) = False" by simp
      note id1 = id1[unfolded id3 id4 if_False]
      note id2 = id2[unfolded id4 if_False]
      show ?thesis
      proof (cases "length xs' = n")
        case True
        thus ?thesis unfolding id1 id2 Let_def len using trans by simp
      next
        case False
        hence id: "(length xs' = n) = False" by simp
        have id': "length [q\<leftarrow>facts . degree_i q = 1] = length [q\<leftarrow>facts'. degree q = 1]" 
          by transfer_prover   
        have [transfer_rule]: "list_all2 ff.poly_rel (berlekamp_factorization_main_i p ff_ops [x\<leftarrow>facts . degree_i x \<noteq> 1] ys
         (n - length [q\<leftarrow>facts . degree_i q = 1])) 
         (berlekamp_factorization_main [x\<leftarrow>facts' . degree x \<noteq> 1] ys'
         (n - length [q\<leftarrow>facts' . degree q = 1]))"
          unfolding id'
          by (rule Cons(3), transfer_prover)
        show ?thesis unfolding id1 id2 Let_def len id if_False
          unfolding partition_filter_conv o_def split by transfer_prover
      qed
    qed
  qed simp
qed
    
lemma berlekamp_factorization_i[transfer_rule]: 
  "(ff.poly_rel ===> rel_prod mod_ring_rel (list_all2 ff.poly_rel)) 
     (berlekamp_factorization_i p ff_ops) berlekamp_factorization" 
  unfolding berlekamp_factorization_i_def[abs_def] berlekamp_factorization_def[abs_def] Let_def
  by transfer_prover

text \<open>Since the implementation is sound, we can now combine it with the soundness result
  of Berlekamp.\<close>

lemma berlekamp_factorization_i_sound: 
  assumes f': "f' = coeffs (Mp f)" 
  and berl_i: "berlekamp_factorization_i p ff_ops f' = (c,fs')"
  and sq: "square_free_m f" 
  and fs: "fs = map poly_of_list fs'"
  shows "unique_factorization_m f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
proof -
  define f'' :: "'a mod_ring poly" where "f'' = of_int_poly (Mp f)"
  have rel_f[transfer_rule]: "ff.poly_rel f' f''" 
    by (rule poly_rel_coeffs_Mp_of_int_poly[OF f'], simp add: f''_def)
  interpret pff: idom_ops "poly_ops ff_ops" ff.poly_rel 
    by (rule ff.idom_ops_poly)
  obtain c' fs'' where berl: "berlekamp_factorization f'' = (c',fs'')" by force
  from rel_funD[OF berlekamp_factorization_i rel_f, unfolded rel_prod_conv assms(2) split berl]
  have rel[transfer_rule]: "mod_ring_rel c c'" "list_all2 ff.poly_rel fs' fs''" by auto  
  from rel(1) have c: "c \<in> {0 ..< p}" using fun_cong[OF Domainp_mod_ring_rel, of c] 
    unfolding Domainp_iff[abs_def] by auto
  {
    fix f
    assume "f \<in> set fs'" 
    with rel(2) obtain f' where "ff.poly_rel f f'"  unfolding list_all2_conv_all_nth set_conv_nth
      by auto
    hence "is_poly ff_ops f" using fun_cong[OF ff.Domainp_is_poly, of f]
      unfolding Domainp_iff[abs_def] by auto
  }
  hence fs': "Ball (set fs') (is_poly ff_ops)" by auto
  define mon :: "'a mod_ring poly \<Rightarrow> bool" where "mon = monic"
  have [transfer_rule]: "(ff.poly_rel ===> op =) (monic_i ff_ops) mon" unfolding mon_def 
    by (rule ff.poly_rel_monic)
  have cc': "c = to_int_mod_ring c'" using rel(1) unfolding mod_ring_rel_def .
  have len: "length fs' = length fs''" by transfer_prover
  have fs': "fs = map to_int_poly fs''" unfolding fs 
  proof (rule nth_map_conv[OF len], intro allI impI)
    fix i
    assume i: "i < length fs'" 
    obtain f g where id: "fs' ! i = f" "fs'' ! i = g" by auto
    from i rel(2)[unfolded ff.poly_rel_def list_all2_conv_all_nth[of _ fs' fs'']]
    have "list_all2 mod_ring_rel (fs' ! i) (coeffs (fs'' ! i))" by auto
    note rel[transfer_rule] = this[unfolded id]
    have id': "coeffs (map_poly to_int_mod_ring g) = map to_int_mod_ring (coeffs g)" 
      by (rule coeffs_map_poly, auto)
    have len: "length f = length (coeffs g)" by transfer_prover 
    have id'': "coeffs (poly_of_list f) = f"
    proof (rule ccontr) 
      assume "\<not> ?thesis" hence "strip_while (op = 0) f \<noteq> f" by auto
      then obtain f' where f: "f = f' @ [0]"
        by (metis (full_types) append_butlast_last_id strip_while_Nil strip_while_not_last)
      from len[unfolded this] have "coeffs g \<noteq> []" by auto 
      note * = append_butlast_last_id[OF this]
      then obtain g' z where g: "coeffs g = (g' @ [z])" by metis
      from rel[unfolded f g] have "mod_ring_rel 0 z" by auto
      from this[unfolded mod_ring_rel_def]
      have z: "0 = z" by auto
      with g have "coeffs g = g' @ [0]" by simp
      thus False
        by (metis * \<open>coeffs g \<noteq> []\<close> append1_eq_conv coeffs_eq_Nil last_coeffs_not_0)
    qed
    show "poly_of_list (fs' ! i) = map_poly to_int_mod_ring (fs'' ! i)" 
      unfolding id coeffs_eq_iff id' id'' using rel[unfolded mod_ring_rel_def[abs_def]]
      unfolding list_all2_conv_all_nth 
      by (intro nth_equalityI, auto)
  qed
  have f: "f'' = of_int_poly f" unfolding poly_eq_iff
    unfolding ring_hom_of_int.coeff_map_poly_hom
  proof
    fix n
    show "coeff f'' n = of_int (coeff f n)" using f' rel_f[unfolded ff.poly_rel_def] p
    by (metis Mp_Mp Mp_f_representative coeff_map_poly_to_int_mod_ring f''_def poly_mod.Mp_coeff to_int_mod_ring_inj to_int_mod_ring_of_int_M)
  qed
  have *: "unique_factorization_m f (c, mset fs)" 
    using berlekamp_factorization_modulo_ring[OF f sq berl cc' fs'] by auto
  have fs': "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})" unfolding fs' 
    using range_to_int_mod_ring[where 'a = 'a]
    by (auto simp: coeffs_to_int_poly p)
  with c fs *
  show ?thesis by blast
qed
end

lemma berlekamp_factorization_i: 
  assumes p: "prime p" 
  and f_ops: "f_ops = finite_field_ops p" 
  and berl_i: "berlekamp_factorization_i p f_ops (coeffs (poly_mod.Mp p f)) = (c,fs')"
  and sq: "poly_mod.square_free_m p f"
  and fs: "fs = map poly_of_list fs'"
  shows "poly_mod.unique_factorization_m p f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
proof -
  have ne: "{0..<p} \<noteq> {}" using prime_ge_2_int[OF p] by auto
  {
    assume "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< p :: int}"
    from prime_type_prime_card[OF p this]
    have "class.prime_card TYPE('b)" "p = int CARD('b)" by auto
    from prime_field.berlekamp_factorization_i_sound[unfolded prime_field_def mod_ring_locale_def,
      internalize_sort "?'a :: prime_card", OF this, folded f_ops, OF refl berl_i sq fs]
    have ?thesis .
  }
  from this[cancel_type_definition, OF ne]
  show ?thesis .
qed

definition berlekamp_factorization_int_main :: "int \<Rightarrow> int list \<Rightarrow> int \<times> int poly list" where
  "berlekamp_factorization_int_main p f' \<equiv> 
    let f_ops = finite_field_ops p; 
      (c,fs') = berlekamp_factorization_i p f_ops f'
      in (c, map poly_of_list fs')"

definition berlekamp_factorization_int :: "int \<Rightarrow> int poly \<Rightarrow> int \<times> int poly list" where
  "berlekamp_factorization_int p f = 
     berlekamp_factorization_int_main p (coeffs (poly_mod.Mp p f))"

lemma berlekamp_factorization_int_main: assumes p: "prime p" 
  and sq: "poly_mod.square_free_m p f" 
  and result: "berlekamp_factorization_int_main p (coeffs (poly_mod.Mp p f)) = (c,fs)"
  shows "poly_mod.unique_factorization_m p f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
proof -
  let ?f' = "coeffs (poly_mod.Mp p f)" 
  obtain d fs' where 
    res: "berlekamp_factorization_i p (finite_field_ops p) ?f' = (d,fs')" 
    by force
  from result[unfolded berlekamp_factorization_int_main_def Let_def res split]
  have id: "d = c" "fs = map poly_of_list fs'" by auto
  show ?thesis
    by (rule berlekamp_factorization_i[OF p refl res[unfolded id] sq], rule id)
qed
 
lemma berlekamp_factorization_int: assumes p: "prime p" 
  and sq: "poly_mod.square_free_m p f" 
  and result: "berlekamp_factorization_int p f = (c,fs)"
  shows "poly_mod.unique_factorization_m p f (c, mset fs)
    \<and> c \<in> {0 ..< p} 
    \<and> (\<forall> fi \<in> set fs. set (coeffs fi) \<subseteq> {0 ..< p})" 
  by (rule berlekamp_factorization_int_main[OF p sq 
    result[unfolded berlekamp_factorization_int_def]])
    
end
