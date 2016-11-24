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

definition factorize_int_poly :: "int poly \<Rightarrow> int \<times> (int poly \<times> nat) list" where
  "factorize_int_poly f = ( 
    let (a,gis) = square_free_factorization_int f;
        bzf = berlekamp_zassenhaus_factorization
     in (a, [ (h,i) . (g,i) \<leftarrow> gis, h \<leftarrow> bzf g ])
  )"
  
lemma factorize_int_poly_code[code]: "factorize_int_poly f = (    
    case square_free_factorization_int f of (a,gis) \<Rightarrow> 
   (a, concat (map (\<lambda> (g,i). (map (\<lambda> f. (f,i)) (berlekamp_zassenhaus_factorization g))) gis)))" 
  unfolding factorize_int_poly_def by auto

thm factorize_int_poly_def  
lemma factorize_int_poly_0[simp]: "factorize_int_poly 0 = (0,[])" 
  unfolding factorize_int_poly_def square_free_factorization_int_def Let_def by auto
    
lemma factorize_int_poly: assumes res: "factorize_int_poly f = (c,fs)"
shows "square_free_factorization f (c,fs)"
  "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"
proof -
  obtain a psi where a_psi: "square_free_factorization_int f = (a, psi)" 
    by force
  from square_free_factorization_int[OF this]
  have sff: "square_free_factorization f (a, psi)" and dist: "distinct (map snd psi)" 
    and cnt: "\<And> fi i. (fi, i) \<in> set psi \<Longrightarrow> content fi = 1" by blast+
  note res = res[unfolded factorize_int_poly_def a_psi Let_def split]
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
        from cnt[unfolded gc content_def list_gcd_def, simplified] have "abs c = 1" 
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

end
