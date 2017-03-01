(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Factoring Arbitrary Integer Polynomials\<close>

text \<open>We combine the factorization algorithm for square-free integer polynomials
  with a square-free factorization algorithm to
  a factorization algorithm for integer polynomials which does not make
  any assumptions.\<close>
theory Factorize_Int_Poly
imports 
  Berlekamp_Zassenhaus
  Square_Free_Factorization_Int
begin

(* main factorization algorithm of polynomials, without preprocessing and special cases *)
definition internal_int_poly_factorization :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat) list" where
  "internal_int_poly_factorization f = ( 
    let (a,gis) = square_free_factorization_int f;
        bzf = berlekamp_zassenhaus_factorization
     in (a, [ (h,i) . (g,i) \<leftarrow> gis, h \<leftarrow> bzf g ])
  )"

lemma internal_int_poly_factorization_code[code]: "internal_int_poly_factorization f = (    
    case square_free_factorization_int f of (a,gis) \<Rightarrow> 
   (a, concat (map (\<lambda> (g,i). (map (\<lambda> f. (f,i)) (berlekamp_zassenhaus_factorization g))) gis)))" 
  unfolding internal_int_poly_factorization_def by auto
  
definition reflect_factorization :: "int \<times> (int poly \<times> nat) list \<Rightarrow> int \<times> (int poly \<times> nat) list" where
  "reflect_factorization cfs = (case cfs of (c,fs) \<Rightarrow> (c,map (\<lambda> (f,i). (reflect_poly f,i)) fs))" 

definition factorize_int_last_nz_poly :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat) list" where
  "factorize_int_last_nz_poly f = (let df = degree f
    in if df = 0 then (coeff f 0, []) else if df = 1 then (1,[(f,0)]) else
    if abs (coeff f 0) < abs (coeff f df) (* take reverse polynomial, if f(0) < lc(f) *)
     then reflect_factorization (internal_int_poly_factorization (reflect_poly f))
     else internal_int_poly_factorization f)"   
  
definition factorize_int_poly :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat) list" where
  "factorize_int_poly f = (case x_split f of (n,g) (* extract x^n *)
    \<Rightarrow> if g = 0 then (0,[]) else case factorize_int_last_nz_poly g of (a,fs) 
    \<Rightarrow> if n = 0 then (a,fs) else (a, (monom 1 1, n - 1) # fs))" 


lemma factorize_int_poly_0[simp]: "factorize_int_poly 0 = (0,[])" 
  unfolding factorize_int_poly_def x_split_def by simp


lemma internal_int_poly_factorization: assumes res: "internal_int_poly_factorization f = (c,fs)"
shows "square_free_factorization f (c,fs)"
  "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"
proof -
  obtain a psi where a_psi: "square_free_factorization_int f = (a, psi)" 
    by force
  from square_free_factorization_int[OF this]
  have sff: "square_free_factorization f (a, psi)"  
    and cnt: "\<And> fi i. (fi, i) \<in> set psi \<Longrightarrow> content fi = 1" by blast+
  note res = res[unfolded internal_int_poly_factorization_def a_psi Let_def split]
  obtain fact where fact: "fact = (\<lambda> (q,i :: nat). (map (\<lambda> f. (f,i)) (berlekamp_zassenhaus_factorization q)))" by auto
  from res[unfolded split Let_def]
  have c: "c = a" and fs: "fs = concat (map fact psi)"
    unfolding fact by auto  
  note sff' = square_free_factorizationD[OF sff]
  {
    fix fi i
    assume "(fi,i) \<in> set fs" 
    from this[unfolded fs, simplified] obtain d j where psi: "(d,j) \<in> set psi" 
       and fi: "(fi, i) \<in> set (fact (d,j))" by auto
    obtain hs where d: "berlekamp_zassenhaus_factorization d = hs" by force   
    from fi[unfolded d split fact] have fi: "fi \<in> set hs" by auto
    from berlekamp_zassenhaus_factorization[OF d] fi sff'(2)[OF psi]
    have "irreducible fi" by auto 
  } note irr = this
  show "(fi, i) \<in> set fs \<Longrightarrow> irreducible fi" by fact
  show "square_free_factorization f (c,fs)" unfolding square_free_factorization_def split
  proof (intro conjI impI allI)
    show "f = 0 \<Longrightarrow> c = 0" "f = 0 \<Longrightarrow> fs = []" using sff'(4) unfolding c fs by auto
    {
      fix a i
      assume "(a,i) \<in> set fs"
      from irr[OF this] show "square_free a" "degree a \<noteq> 0" 
        using irreducible_square_free[of a] unfolding irreducible_def by auto
    }
    have eq: "f = smult c (\<Prod>(a, i)\<leftarrow>fs. a ^ Suc i)" unfolding 
      prod.distinct_set_conv_list[OF sff'(5)]
      sff'(1) c
    proof (rule arg_cong[where f = "smult a"], unfold fs, insert sff'(2), induct psi)
      case (Cons pi psi)
      obtain p i where pi: "pi = (p,i)" by force  
      obtain gs where gs: "berlekamp_zassenhaus_factorization p = gs" by auto
      from Cons(2)[of p i] have p: "square_free p" "degree p \<noteq> 0" unfolding pi by auto
      from berlekamp_zassenhaus_factorization[OF gs this] have pgs: "p = prod_list gs" by auto
      have fact: "fact (p,i) = map (\<lambda> g. (g,i)) gs" unfolding fact split gs by auto
      have cong: "\<And> x y X Y. x = X \<Longrightarrow> y = Y \<Longrightarrow> x * y = X * Y" by auto
      show ?case unfolding pi list.simps prod_list.Cons split fact concat.simps prod_list.append
        map_append
      proof (rule cong)
        show "p ^ Suc i = (\<Prod>(a, i)\<leftarrow>map (\<lambda>g. (g, i)) gs. a ^ Suc i)" unfolding pgs
          by (induct gs, auto simp: ac_simps power_mult_distrib)
        show "(\<Prod>(a, i)\<leftarrow>psi. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>concat (map fact psi). a ^ Suc i)" 
          by (rule Cons(1), insert Cons(2), auto)
      qed
    qed simp
    {
      fix i j l fi
      assume *: "j < length psi" "l < length (fact (psi ! j))" "fact (psi ! j) ! l = (fi, i)" 
      from * have psi: "psi ! j \<in> set psi" by auto
      obtain d k where "psi ! j = (d,k)" by force
      with * have psij: "psi ! j = (d,i)" unfolding fact split by auto
      from sff'(2)[OF psi[unfolded psij]] have d: "square_free d" "degree d \<noteq> 0" by auto
      from * psij fact
      have bz: "berlekamp_zassenhaus_factorization d = map fst (fact (psi ! j))" by (auto simp: o_def)
      from berlekamp_zassenhaus_factorization[OF bz d] 
      have dhs: "d = prod_list (map fst (fact (psi ! j)))" and 
        irr: "(\<forall>fi\<in>set (map fst (fact (psi ! j))). irreducible fi)" by auto
      from * have mem: "fi \<in> set (map fst (fact (psi ! j)))"
        by (metis fst_conv image_eqI nth_mem set_map)
      from mem dhs psij d have "\<exists> d. fi \<in> set (map fst (fact (psi ! j))) \<and>
        d = prod_list (map fst (fact (psi ! j))) \<and>
        psi ! j = (d, i) \<and>
        square_free d" by blast
    } note deconstruct = this
    {
      fix k K fi i Fi I
      assume k: "k < length fs" "K < length fs" and f: "fs ! k = (fi, i)" "fs ! K = (Fi, I)" 
      and diff: "k \<noteq> K" 
      from nth_concat_diff[OF k[unfolded fs] diff, folded fs, unfolded length_map]
        obtain j l J L where diff: "(j, l) \<noteq> (J, L)"
          and j: "j < length psi" "J < length psi" 
          and l: "l < length (map fact psi ! j)" "L < length (map fact psi ! J)"
          and fs: "fs ! k = map fact psi ! j ! l" "fs ! K = map fact psi ! J ! L" by blast+
      hence psij: "psi ! j \<in> set psi" by auto
      from j have id: "map fact psi ! j = fact (psi ! j)" "map fact psi ! J = fact (psi ! J)" by auto
      note l = l[unfolded id] note fs = fs[unfolded id]
      from j have psi: "psi ! j \<in> set psi" "psi ! J \<in> set psi" by auto
      from deconstruct[OF j(1) l(1) fs(1)[unfolded f, symmetric]]
      obtain d where mem: "fi \<in> set (map fst (fact (psi ! j)))" 
        and d: "d = prod_list (map fst (fact (psi ! j)))" "psi ! j = (d, i)" "square_free d" by blast
      from deconstruct[OF j(2) l(2) fs(2)[unfolded f, symmetric]]
      obtain D where Mem: "Fi \<in> set (map fst (fact (psi ! J)))"
        and D: "D = prod_list (map fst (fact (psi ! J)))" "psi ! J = (D, I)" "square_free D" by blast
      from cnt[OF psij[unfolded d(2)]] have cnt: "content d = 1" .
      have "coprime fi Fi" 
      proof (cases "J = j")
        case False
        from sff'(5) False j have "(d,i) \<noteq> (D,I)" 
          unfolding distinct_conv_nth d(2)[symmetric] D(2)[symmetric] by auto
        from sff'(3)[OF psi[unfolded d(2) D(2)] this]
        have cop: "coprime d D" by auto
        from prod_list_dvd[OF mem, folded d(1)] have fid: "fi dvd d" by auto
        from prod_list_dvd[OF Mem, folded D(1)] have FiD: "Fi dvd D" by auto
        from coprime_divisors[OF fid FiD cop] show ?thesis .
      next
        case True note id = this
        from id diff have diff: "l \<noteq> L" by auto
        obtain bz where bz: "bz = map fst (fact (psi ! j))" by auto
        from fs[unfolded f] l 
        have fi: "fi = bz ! l" "Fi = bz ! L"
          unfolding id bz by (metis fst_conv nth_map)+
        from d[folded bz] have sf: "square_free (prod_list bz)" by auto
        from d[folded bz] cnt have cnt: "content (prod_list bz) = 1" by auto
        from l have l: "l < length bz" "L < length bz" unfolding bz id by auto
        from l fi have "fi \<in> set bz" by auto
        from content_dvd_1[OF cnt prod_list_dvd[OF this]] have cnt: "content fi = 1" .
        obtain g where g: "g = gcd fi Fi" by auto
        have g': "g dvd fi" "g dvd Fi" unfolding g by auto
        define bef where "bef = take l bz" 
        define aft where "aft = drop (Suc l) bz" 
        from id_take_nth_drop[OF l(1)] l have bz: "bz = bef @ fi # aft" and bef: "length bef = l" 
          unfolding bef_def aft_def fi by auto
        with l diff have mem: "Fi \<in> set (bef @ aft)" unfolding fi(2) by (auto simp: nth_append)
        from split_list[OF this] obtain Bef Aft where ba: "bef @ aft = Bef @ Fi # Aft" by auto
        have "prod_list bz = fi * prod_list (bef @ aft)" unfolding bz by simp
        also have "prod_list (bef @ aft) = Fi * prod_list (Bef @ Aft)" unfolding ba by auto
        finally have "fi * Fi dvd prod_list bz" by auto
        with g' have "g * g dvd prod_list bz" by (meson dvd_trans mult_dvd_mono)
        with sf[unfolded square_free_def] have deg: "degree g = 0" by auto
        from content_dvd_1[OF cnt g'(1)] have cnt: "content g = 1" .
        from degree0_coeffs[OF deg] obtain c where gc: "g = [: c :]" by auto
        from cnt[unfolded gc content_def, simplified] have "abs c = 1" 
          by (cases "c = 0", auto)
        with g gc have "gcd fi Fi \<in> {1,-1}" by fastforce
        thus "coprime fi Fi" by (metis coprime_1_left gcd_neg1 gcd_right_idem insertE singletonD)
      qed
    } note cop = this
    
    show dist: "distinct fs" unfolding distinct_conv_nth
    proof (intro impI allI)
      fix k K
      assume k: "k < length fs" "K < length fs" and diff: "k \<noteq> K"
      obtain fi i Fi I where f: "fs ! k = (fi,i)" "fs ! K = (Fi,I)" by force+
      from cop[OF k f diff] have cop: "coprime fi Fi" .
      from k(1) f(1) have "(fi,i) \<in> set fs" unfolding set_conv_nth by force
      from irr[OF this] have "irreducible fi" by auto
      hence "degree fi \<noteq> 0" unfolding irreducible_def by auto
      hence "\<not> is_unit fi" by (simp add: poly_dvd_1)
      with cop coprime_id_is_unit[of fi] have "fi \<noteq> Fi" by auto
      thus "fs ! k \<noteq> fs ! K" unfolding f by auto
    qed
    show "f = smult c (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" unfolding eq
      prod.distinct_set_conv_list[OF dist] by simp
    fix fi i Fi I
    assume mem: "(fi, i) \<in> set fs" "(Fi,I) \<in> set fs" and diff: "(fi, i) \<noteq> (Fi, I)" 
    then obtain k K where k: "k < length fs" "K < length fs" 
      and f: "fs ! k = (fi, i)" "fs ! K = (Fi, I)" unfolding set_conv_nth by auto
    with diff have diff: "k \<noteq> K" by auto
    from cop[OF k f diff] show "coprime fi Fi" by auto
  qed
qed 

lemma irreducible_reflect_poly: assumes nz: "coeff f 0 \<noteq> 0" 
  shows "irreducible (reflect_poly f) = irreducible f" 
proof -  
  {
    fix f :: "'a poly" 
    assume nz: "coeff f 0 \<noteq> 0" 
    and irr: "\<forall>q. degree q \<noteq> 0 \<longrightarrow> degree q < degree f \<longrightarrow> \<not> q dvd reflect_poly f" 
    have "\<forall>q. degree q \<noteq> 0 \<longrightarrow> degree q < degree f \<longrightarrow> \<not> q dvd f" 
    proof (intro allI impI notI)
      fix g
      assume deg: "degree g \<noteq> 0" "degree g < degree f" and dvd: "g dvd f" 
      from dvd obtain h where fgh: "f = g * h" unfolding dvd_def by auto
      from arg_cong[OF this, of "\<lambda> f. coeff f 0"] nz 
      have nz': "coeff g 0 \<noteq> 0" by (auto simp: coeff_mult_0)
      from arg_cong[OF fgh, of reflect_poly, unfolded reflect_poly_mult]
      have dvd: "reflect_poly g dvd reflect_poly f" by auto
      from deg have "degree (reflect_poly g) \<noteq> 0" "degree (reflect_poly g) < degree f" 
        unfolding degree_reflect_poly_eq[OF nz'] by auto
      from irr[rule_format, OF this] dvd show False by auto
    qed
  } note main = this
  from nz have nz': "coeff (reflect_poly f) 0 \<noteq> 0" by auto
  have "(\<forall>q. degree q \<noteq> 0 \<longrightarrow> degree q < degree f \<longrightarrow> \<not> q dvd reflect_poly f)
    = (\<forall>q. degree q \<noteq> 0 \<longrightarrow> degree q < degree f \<longrightarrow> \<not> q dvd f)" 
    using main[OF nz] main[OF nz'] 
    unfolding degree_reflect_poly_eq[OF nz] reflect_poly_reflect_poly[OF nz] by blast
  thus ?thesis unfolding irreducible_def degree_reflect_poly_eq[OF nz] by auto
qed

lemma reflect_poly_dvd: "(f :: 'a :: idom poly) dvd g \<Longrightarrow> reflect_poly f dvd reflect_poly g" 
  unfolding dvd_def by (auto simp: reflect_poly_mult)

lemma gcd_reflect_poly: fixes f :: "'a :: factorial_ring_gcd poly" 
  assumes nz: "coeff f 0 \<noteq> 0" "coeff g 0 \<noteq> 0" 
  shows "gcd (reflect_poly f) (reflect_poly g) = normalize (reflect_poly (gcd f g))" 
proof (rule sym, rule gcdI)
  have "gcd f g dvd f" by auto
  from reflect_poly_dvd[OF this]  
  show "normalize (reflect_poly (gcd f g)) dvd reflect_poly f" by simp
  have "gcd f g dvd g" by auto
  from reflect_poly_dvd[OF this]  
  show "normalize (reflect_poly (gcd f g)) dvd reflect_poly g" by simp
  show "normalize (normalize (reflect_poly (gcd f g))) = normalize (reflect_poly (gcd f g))" by auto
  fix h
  assume hf: "h dvd reflect_poly f" and hg: "h dvd reflect_poly g" 
  from hf obtain k where "reflect_poly f = h * k" unfolding dvd_def by auto
  from arg_cong[OF this, of "\<lambda> f. coeff f 0", unfolded coeff_mult_0] nz(1) have h: "coeff h 0 \<noteq> 0" by auto
  from reflect_poly_dvd[OF hf] reflect_poly_dvd[OF hg]
  have "reflect_poly h dvd f" "reflect_poly h dvd g" using nz by auto
  hence "reflect_poly h dvd gcd f g" by auto
  from reflect_poly_dvd[OF this] h have "h dvd reflect_poly (gcd f g)" by auto
  thus "h dvd normalize (reflect_poly (gcd f g))" by auto
qed  

lemma factorize_int_last_nz_poly: assumes res: "factorize_int_last_nz_poly f = (c,fs)"
    and nz: "coeff f 0 \<noteq> 0" 
shows "square_free_factorization f (c,fs)"
  "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"
proof -
  from nz have lz: "lead_coeff f \<noteq> 0" by auto
  obtain rev where rev: "(\<bar>coeff f 0\<bar> < \<bar>coeff f (degree f)\<bar>) = rev" by auto
  note res = res[unfolded factorize_int_last_nz_poly_def Let_def rev]
  consider (0) "degree f = 0" 
    | (1) "degree f = 1" 
    | (complex_rev) "degree f > 1" "rev" 
    | (complex_norm) "degree f > 1" "\<not> rev" by linarith
  hence "square_free_factorization f (c,fs) \<and> ((fi,i) \<in> set fs \<longrightarrow> irreducible fi)" 
  proof cases
    case 0
    from degree0_coeffs[OF 0] obtain a where f: "f = [:a:]" by auto
    from res show ?thesis unfolding square_free_factorization_def f by auto
  next
    case 1   
    from linear_irreducible[OF 1] have irr: "irreducible f" by auto
    from irreducible_square_free[OF irr] have sf: "square_free f" .
    from 1 have f0: "f \<noteq> 0" by auto 
    from res irr sf f0 show ?thesis unfolding square_free_factorization_def by (auto simp: 1)
  next
    case complex_norm
    with res have "internal_int_poly_factorization f = (c,fs)" by auto
    from internal_int_poly_factorization[OF this] show ?thesis by auto
  next
    case complex_rev
    obtain d gs where fact: "internal_int_poly_factorization (reflect_poly f) = (d,gs)" by force
    with res complex_rev have refl: "reflect_factorization (d,gs) = (c,fs)" by auto
    from internal_int_poly_factorization[OF fact] 
    have sff: "square_free_factorization (reflect_poly f) (d, gs)" 
      and irr: "\<And> fi i. (fi, i) \<in> set gs \<Longrightarrow> irreducible fi" by auto
    from nz have nz': "coeff (reflect_poly f) 0 \<noteq> 0" by auto
    {
      fix gi i
      assume gi: "(gi,i) \<in> set gs"  
      from split_list[OF this] obtain xs zs where gs: "gs = xs @ (gi,i) # zs" by auto
      from square_free_factorization_prod_list[OF sff, unfolded gs, simplified] 
      obtain c d where fcd: "reflect_poly f = smult c (gi * d)" by (auto simp: ac_simps)
      from arg_cong[OF this, of "\<lambda> f. coeff f 0", simplified] lz
      have nzg: "coeff gi 0 \<noteq> 0" unfolding coeff_mult_0 by auto
      from irr[OF gi] have irr: "irreducible (reflect_poly gi)" using irreducible_reflect_poly[OF nzg]
        by auto
      note nzg irr
    } note nzg = this
    from refl[unfolded reflect_factorization_def] 
    have d: "c = d" and fs: "fs = map (\<lambda> (f,i). (reflect_poly f, i)) gs" by auto
    note sf = square_free_factorizationD[OF sff]
    {
      fix fi i
      assume "(fi,i) \<in> set fs" 
      then obtain gi where "(gi,i) \<in> set gs" and "fi = reflect_poly gi" 
        using fs by auto
      with nzg[OF this(1)] have "irreducible fi" by auto
    } note irr = this
    show ?thesis unfolding d
    proof (intro conjI allI impI)
      show "(fi, i) \<in> set fs \<Longrightarrow> irreducible fi" by fact
      show "square_free_factorization f (d, fs)"
        unfolding square_free_factorization_def split
      proof (intro allI conjI impI)
        show "f = 0 \<Longrightarrow> d = 0" "f = 0 \<Longrightarrow> fs = []" using sf(4) unfolding fs by auto
        {
          fix fi i
          assume "(fi, i) \<in> set fs"
          from irr[OF this] have "irreducible fi" .
          from irreducible_square_free[OF this] this show "square_free fi" "degree fi \<noteq> 0" 
            unfolding irreducible_def by auto
        }
        show dist: "distinct fs" unfolding fs distinct_map
          by (rule conjI[OF sf(5) inj_on_inverseI[of _ "\<lambda> (f, i). (reflect_poly f, i)"]],
            insert nzg, auto)
        have "f = reflect_poly (reflect_poly f)" using nz by simp
        also have "\<dots> = smult d (reflect_poly (\<Prod>(a, i)\<leftarrow>gs. a ^ Suc i))" 
          unfolding square_free_factorization_prod_list[OF sff] by (simp only: reflect_poly_simps)
        also have "reflect_poly (\<Prod>(a, i)\<leftarrow>gs. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>fs. a ^ Suc i)" 
          unfolding fs reflect_poly_prod_list map_map o_def
        proof (rule prod_list_cong[OF HOL.refl], goal_cases)
          case (1 gii)
          obtain gi i where gii: "gii = (gi,i)" by force
          show ?case unfolding gii split reflect_poly_power ..
        qed
        also have "\<dots> = (\<Prod>(a, i) \<in> set fs. a ^ Suc i)" 
          using dist by (simp add: prod.distinct_set_conv_list)
        finally show "f = smult d (\<Prod>(a, i) \<in> set fs. a ^ Suc i)" .
        fix fi i fj j
        assume mem: "(fi, i) \<in> set fs" "(fj, j) \<in> set fs" and diff: "(fi, i) \<noteq> (fj, j)" 
        from mem[unfolded fs] obtain gi gj where fi: "fi = reflect_poly gi" "fj = reflect_poly gj" 
            and gi: "(gi,i) \<in> set gs" "(gj,j) \<in> set gs" by auto
        from diff[unfolded fi] have "(gi,i) \<noteq> (gj,j)" by auto
        from sf(3)[OF gi this] have cop: "coprime gi gj" .
        have nz: "coeff gi 0 \<noteq> 0" "coeff gj 0 \<noteq> 0" using nzg(1)[OF gi(1)] nzg(1)[OF gi(2)] .
        show "coprime fi fj" unfolding fi gcd_reflect_poly[OF nz] cop by auto
      qed
    qed
  qed
  thus "square_free_factorization f (c,fs)"
    "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi" by auto
qed
 
lemma factorize_int_poly: assumes res: "factorize_int_poly f = (c,fs)"
shows "square_free_factorization f (c,fs)"
  "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"    
proof -
  obtain n g where xs: "x_split f = (n,g)" by force
  obtain d hs where fact: "factorize_int_last_nz_poly g = (d,hs)" by force
  from res[unfolded factorize_int_poly_def xs split fact]
  have res: "(if g = 0 then (0, []) else if n = 0 then (d, hs) else (d, (monom 1 1, n - 1) # hs)) = (c, fs)" .
  note xs = x_split[OF xs]
  have "square_free_factorization f (c,fs) \<and> ((fi,i) \<in> set fs \<longrightarrow> irreducible fi)" 
  proof (cases "g = 0")
    case True
    hence "f = 0" "c = 0" "fs = []" using res xs by auto
    thus ?thesis unfolding square_free_factorization_def by auto
  next
    case False
    with xs have "\<not> monom 1 1 dvd g" by auto
    hence "coeff g 0 \<noteq> 0" by (simp add: monom_1_dvd_iff')
    note fact = factorize_int_last_nz_poly[OF fact this]
    let ?x = "monom 1 1 :: int poly" 
    have x: "content ?x = 1 \<and> lead_coeff ?x = 1 \<and> degree ?x = 1"
      by (auto simp add: degree_monom_eq monom_Suc content_def)
    from res False have res: "(if n = 0 then (d, hs) else (d, (?x, n - 1) # hs)) = (c, fs)" by auto
    show ?thesis
    proof (cases n)
      case 0
      with res xs have id: "fs = hs" "c = d" "f = g" by auto
      from fact show ?thesis unfolding id by auto
    next
      case (Suc m)      
      with res have id: "c = d" "fs = (?x,m) # hs" by auto
      from Suc xs have fg: "f = monom 1 (Suc m) * g" and dvd: "\<not> ?x dvd g" by auto
      from x linear_irreducible[of ?x] have irr: "irreducible ?x" by auto
      from irreducible_square_free[OF this] have sfx: "square_free ?x" .
      from irr fact(2) have one: "(fi, i) \<in> set fs \<longrightarrow> irreducible fi" unfolding id by auto
      have fg: "f = ?x ^ n * g" unfolding fg Suc by (metis x_pow_n)
      from x have degx: "degree ?x = 1" by simp
      note sf = square_free_factorizationD[OF fact(1)]
      {
        fix a i
        assume ai: "(a,i) \<in> set hs" 
        with sf(4) have g0: "g \<noteq> 0" by auto
        from split_list[OF ai] obtain ys zs where hs: "hs = ys @ (a,i) # zs" by auto
        have "a dvd g" unfolding square_free_factorization_prod_list[OF fact(1)] hs
          by (rule dvd_smult, simp add: ac_simps)
        moreover have "\<not> ?x dvd g" using xs[unfolded Suc] by auto
        ultimately have dvd: "\<not> ?x dvd a" using dvd_trans by blast
        from sf(2)[OF ai] have "a \<noteq> 0" by auto
        have "1 = gcd ?x a"
        proof (rule gcdI)
          fix d
          assume d: "d dvd ?x" "d dvd a" 
          from dvd_content_dvd_rev[OF d(1)] x have cnt: "is_unit (content d)" by auto
          show "is_unit d"
          proof (cases "degree d = 1")
            case False
            with divides_degree[OF d(1), unfolded degx] have "degree d = 0" by auto
            from degree0_coeffs[OF this] obtain c where dc: "d = [:c:]" by auto
            from cnt[unfolded dc] have "is_unit c" by (auto simp: content_def, cases "c = 0", auto)
            hence "d * d = 1" unfolding dc by (auto simp: one_poly_def, cases "c = -1"; cases "c = 1", auto)
            thus "is_unit d" by (metis dvd_triv_right)
          next
            case True
            from d(1) obtain e where xde: "?x = d * e" unfolding dvd_def by auto
            from arg_cong[OF this, of degree] degx have "degree d + degree e = 1"
              by (metis True add.right_neutral degree_0 degree_mult_eq one_neq_zero)
            with True have "degree e = 0" by auto
            from degree0_coeffs[OF this] xde obtain e where xde: "?x = [:e:] * d" by auto
            from arg_cong[OF this, of content, unfolded gauss_lemma] x
            have "content [:e:] * content d = 1" by auto
            also have "content [:e :] = abs e" by (auto simp: content_def, cases "e = 0", auto)
            finally have "\<bar>e\<bar> * content d = 1" .
            from pos_zmult_eq_1_iff_lemma[OF this] have "e * e = 1" by (cases "e = 1"; cases "e = -1", auto)
            with arg_cong[OF xde, of "smult e"] have "d = ?x * [:e:]" by auto
            hence "?x dvd d" unfolding dvd_def by blast
            with d(2) have "?x dvd a" by (metis dvd_trans)
            with dvd show ?thesis by auto
          qed
        qed auto
        hence "coprime ?x a" by simp
        note this dvd
      } note hs_dvd_x = this
      from hs_dvd_x[of ?x m]
      have nmem: "(?x,m) \<notin> set hs" by auto
      hence eq: "?x ^ n * g = smult d (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" 
        unfolding sf(1) unfolding id Suc by simp
      have eq0: "?x ^ n * g = 0 \<longleftrightarrow> g = 0" by simp
      have "square_free_factorization f (d,fs)" unfolding fg id(1) square_free_factorization_def split eq0 unfolding eq
      proof (intro conjI allI impI, rule refl)
        fix a i 
        assume ai: "(a,i) \<in> set fs" 
        thus "square_free a" "degree a \<noteq> 0" using sf(2) sfx degx unfolding id by auto
        fix b j
        assume bj: "(b,j) \<in> set fs" and diff: "(a,i) \<noteq> (b,j)" 
        consider (hs_hs) "(a,i) \<in> set hs" "(b,j) \<in> set hs" 
          | (hs_x) "(a,i) \<in> set hs" "b = ?x" 
          | (x_hs) "(b,j) \<in> set hs" "a = ?x" 
          using ai bj diff unfolding id by auto
        thus "coprime a b"
        proof cases
          case hs_hs
          from sf(3)[OF this diff] show ?thesis .
        next
          case hs_x
          from hs_dvd_x(1)[OF hs_x(1)] show ?thesis unfolding hs_x(2) unfolding gcd.commute[of ?x] .
        next
          case x_hs
          from hs_dvd_x(1)[OF x_hs(1)] show ?thesis unfolding x_hs(2) .
        qed
      next
        show "g = 0 \<Longrightarrow> d = 0" using sf(4) by auto
        show "g = 0 \<Longrightarrow> fs = []" using sf(4) xs Suc by auto
        show "distinct fs" using sf(5) nmem unfolding id by auto
      qed
      thus ?thesis using one unfolding id by auto
    qed
  qed
  thus "square_free_factorization f (c,fs)"
    "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi" by auto
qed
    
end
