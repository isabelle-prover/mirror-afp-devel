(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Berlekamp-Hensel Factorization\<close>

text \<open>This theory contains the Berlekamp factorization algorithm in combination 
  with Hensel lifting. This yields a fast factorization algorithm for integer polynomials.
  There is no proof contained in this development, so it can only be used as an oracle
  to get a factorization. Validity can be checked trivially, and optimality has to be ensured
  by other means, e.g., by using the formalized Kronecker factorization.

  The algorithms contains several sanity checks, which are currently disabled.\<close>

theory Berlekamp_Hensel_Factorization
imports 
  "../Polynomial_Interpolation/Divmod_Int"
  "../Sqrt_Babylonian/Sqrt_Babylonian"
  "../Polynomial_Interpolation/Is_Rat_To_Rat"
  "../Jordan_Normal_Form/Gauss_Jordan_IArray_Impl"
  Gauss_Jordan_Field
  Polynomial_Field
  Square_Free_Factorization
  Prime_Factorization
  Gauss_Lemma
  Polynomial_Division
begin

hide_const (open) Module.smult
hide_const (open) Divisibility.prime

context
  fixes F :: "GFp ffield" (structure)
begin
fun power_polys where
  "power_polys mul_p u curr_p (Suc i) = curr_p # 
      power_polys mul_p u (mod_poly_f F (times_poly_f F curr_p mul_p) u) i"
| "power_polys mul_p u curr_p 0 = []"


definition berlekamp_mat :: "GFp poly_f \<Rightarrow> GFp mat" where
  "berlekamp_mat u = (let n = degree_poly_f u;
    mul_p = power_poly_f_mod F u [0f,1f] (nat (characteristic F));
    xks = power_polys mul_p u (one_poly_f F) n
   in 
    mat_of_rows_list n (map (\<lambda> cs. let k = n - length cs in cs @ replicate k 0f) xks))"

definition berlekamp_resulting_mat :: "GFp poly_f \<Rightarrow> GFp mat" where
  "berlekamp_resulting_mat u = (let Q = berlekamp_mat u;
    n = dim\<^sub>r Q;
    QI = mat n n (\<lambda> (i,j). if i = j then Q $$ (i,j) -f 1f else Q $$ (i,j))
    in gauss_jordan_f F (mat_transpose QI))"

definition berlekamp_basis :: "GFp poly_f \<Rightarrow> GFp poly_f list" where
  "berlekamp_basis u = (map (list_to_poly_f F o list_of_vec) (find_base_vectors_f F (berlekamp_resulting_mat u)))"

primrec berlekamp_factorization_main :: "GFp poly_f list \<Rightarrow> GFp poly_f list \<Rightarrow> nat \<Rightarrow> GFp poly_f list" where
  "berlekamp_factorization_main divs (v # vs) n = (
    let facts = [ w . u \<leftarrow> divs, s \<leftarrow> [0 .. (characteristic F - 1)], w \<leftarrow> [gcd_poly_f F u (plus_poly_f F v [of_int_f F s])], w \<noteq> one_poly_f F]
    in if length facts = n then facts else 
      let (lin,nonlin) = partition (\<lambda> q. degree_poly_f q = 1) facts 
      in lin @ berlekamp_factorization_main nonlin vs (n - length lin))"
| "berlekamp_factorization_main divs [] n = divs" (* should never happen *)

text \<open>berlekamp-factorization takes as input a square-free non-zero polynomial and delivers
  a fully factored polynomial\<close>
definition berlekamp_factorization :: "GFp poly_f \<Rightarrow> GFp \<times> GFp poly_f list" where
  "berlekamp_factorization f = (let a = leading_coeff_f F f;
    u = smult_poly_f F (inverse_f F a) f;
    vs = berlekamp_basis u;
    n = length vs;
    fs = berlekamp_factorization_main [u] vs n;
    sanity = True (* smult_poly_f F a (listprod_poly_f F fs) = f *)
    in if sanity then (a,fs) else 
    Code.abort (String.implode 
       (''error in berlekamp_factorization of '' @ show_poly_f F u @ '' modulo '' @ show (characteristic F))) (\<lambda> _. (a,fs)))"

definition finite_factorization :: "GFp poly_f \<Rightarrow> GFp \<times> (GFp poly_f \<times> int) list" where
  "finite_factorization pp = (let 
     (a,qs) = yun_factorization_f F pp; 
     (* yun-factorization_f will deliver monic polys, so we can ignore the constants that
        are returned by berlekamp, they will all be 1 *)
     fs = concat (map (\<lambda> (q,i). map (\<lambda> f. (f,i)) (snd (berlekamp_factorization q))) qs);
     sanity = True (* (pp = smult_poly_f F a (listprod_poly_f F (map (\<lambda> (p,i). power_poly_f F p i) fs))
       \<and> list_all (\<lambda> (f,i). irreducible_GFp_poly F f) fs) *)
     in if sanity then (a,fs) else 
       Code.abort (String.implode 
       (''error in finite_factorization of '' @ show_poly_f F pp @ '' modulo '' @ show (characteristic F))) 
       (\<lambda> _. (a,fs)))"
end

context
begin

text \<open>We exclude prime number 2 since some algorithms later on require odd primes.\<close>

private definition next_primes :: "nat \<Rightarrow> nat \<times> nat list" where
  "next_primes n = (if n = 0 then case next_candidates 0 of (m,ps) \<Rightarrow> (m,tl ps) else 
    let (m,ps) = next_candidates n in (m,filter prime ps))"

definition [code_unfold]: "leading_coeff_non_zero = last"

private partial_function (tailrec) prime_for_finite_factorization_main :: 
  "nat list \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> int" where
  [code]: "prime_for_finite_factorization_main ps np f = (case ps of [] \<Rightarrow> 
    let (np',ps') = next_primes np
      in prime_for_finite_factorization_main ps' np' f
    | (p # ps) \<Rightarrow> let F = GFp p; g = int_list_to_poly_f F f
      in if gcd_poly_f F g (pderiv_poly_f F g) = one_poly_f F \<and> (* square_free modulo p *)
        gcd (leading_coeff_non_zero f) (int p) = 1  (* leading coefficient will have an inverse modulo p^m *)
      then int p else prime_for_finite_factorization_main ps np f)"

definition prime_for_finite_factorization :: "int poly_f \<Rightarrow> int" where
  "prime_for_finite_factorization p = prime_for_finite_factorization_main [] 0 p"

definition mignotte_bounds :: "int poly_f \<Rightarrow> nat \<Rightarrow> int" where
  "mignotte_bounds p n = (let 
    f = nat (sqrt_int_floor (listsum (map (\<lambda> a. a * a) p)));
    am = nat (abs (leading_coeff_non_zero p)) in 
    int (max_list (map (\<lambda> j. ((n-1) choose j) * f + ((n-1) choose (j-1)) * am) [0 ..< Suc n] )))"

private partial_function (tailrec) hensel_prime_power_main :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  [code]: "hensel_prime_power_main p pm m bnd = (if pm > bnd then m
    else hensel_prime_power_main p (pm * p) (Suc m) bnd)"

definition hensel_prime_power :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "hensel_prime_power p bnd = hensel_prime_power_main p p 1 bnd"
end

partial_function (tailrec) extended_gcd_int_main :: 
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
   (int \<times> int \<times> int)" where
  [code]: "extended_gcd_int_main ri1 si1 ti1 ri si ti = 
    (if ri = 0 then (ri1,si1,ti1) else let q = ri1 div ri
     in extended_gcd_int_main ri si ti 
     (ri1 - q * ri)
     (si1 - q * si)
     (ti1 - q * ti))"

definition extended_gcd_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<times> int" where
  "extended_gcd_int a b = extended_gcd_int_main 
      a 1 0 
      b 0 1"

definition inverse_int_modulo :: "int \<Rightarrow> int \<Rightarrow> int" where
  "inverse_int_modulo x y = (let (g,a,b) = extended_gcd_int x y
     in a)"

text \<open>Pre-Hensel-Factorization assumes square free and content-free integer polynomial as input.
  It finds a suitable prime and exponent, factors the polynomial w.r.t. the prime and returns
  the factors, the prime, and the exponent.\<close>
definition pre_hensel_factorization :: "int poly_f \<Rightarrow> GFp poly_f list \<times> (int \<times> nat)" where
  "pre_hensel_factorization g = (let 
     p = prime_for_finite_factorization g;
     F = GFp p;
     dg = degree_poly_f g;
     M = mignotte_bounds g (dg div 2);
     a = leading_coeff_non_zero g;
     n = hensel_prime_power (nat p) (nat (2 * a * M));
     f = int_list_to_poly_f F g;
     (_,fs) = berlekamp_factorization F f
     in (fs,(p,n)))"

definition integer_ops :: "int ffield" where
  "integer_ops = \<lparr> 
    ffield.plus = op +,
    minus = op -,
    uminus = uminus,
    mult = op *,
    power = fast_power (op *) 1,
    inverse_f = (\<lambda> x. 0),
    divide = (\<lambda> x y. 0),
    zero = 0,
    one = 1,
    characteristic = 0,
    of_int_f = id,
    to_int_f = id\<rparr>"

definition rational_ops :: "rat ffield" where
  "rational_ops = \<lparr> 
    ffield.plus = op +,
    minus = op -,
    uminus = uminus,
    mult = op *,
    power = fast_power (op *) 1,
    inverse_f = inverse,
    divide = op /,
    zero = 0,
    one = 1,
    characteristic = 0,
    of_int_f = of_int,
    to_int_f = int_of_rat\<rparr>"

definition mod_int_poly :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "mod_int_poly n f = (let g = map (\<lambda> x. x mod n) f
    in foldr cCons g [])"

definition div_int_poly :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "div_int_poly n f = (let g = map (\<lambda> x. x div n) f
    in foldr cCons g [])"

text \<open>Algorithm according to Alfonso Miola and David Yun paper.
  We did not include refinement H2', since it resulted
  in worse runtime in our experiments. We further replaced the bound
 in H2 from $j > k$ to $j \geq k$.\<close>
context fixes
  Fp :: "GFp ffield"
  and p :: int
  and k :: nat
  and C :: "int poly_f"
  and S T D1 H1 :: "GFp poly_f"
begin

(* assumes leading coefficient of D1 is 1 *)
definition hensel_dupe_one :: "GFp poly_f 
   \<Rightarrow> GFp poly_f \<times> GFp poly_f" where
  "hensel_dupe_one U \<equiv> let 
       pp = plus_poly_f Fp;
       tt = times_poly_f Fp;  
       (Q,R) = divmod_poly_one_f Fp (tt T U) D1;
       A = pp (tt S U) (tt H1 Q);
       B = R
     in (A,B)"

partial_function (tailrec) linear_hensel_lifting_main :: "int \<Rightarrow> nat
  \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  [code]: "linear_hensel_lifting_main q j D H = (if j \<ge> k then (D,H) else
     let 
       Z = integer_ops;
       mm = minus_poly_f Z;
       pp = plus_poly_f Z;
       tt = times_poly_f Z;
       sm = smult_poly_f Z;
       I = map (to_int_f Fp);
       (* H2 *)
       U = div_int_poly q (mm C (tt D H))
     in if U = zero_poly_f then (D,H) else let (* opt. iii *)
       (* H3 *)
       U = int_list_to_poly_f Fp U;
       (A,B) = hensel_dupe_one U;
       (* H4 *)
       D = pp D (sm q (I B));
       H = pp H (sm q (I A));
       j = j + 1;
       q = q * p
     in linear_hensel_lifting_main q j D H)"
end

definition linear_hensel_lifting_binary :: "GFp ffield \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  "linear_hensel_lifting_binary Fp k C D1 H1 = (let
    p = characteristic Fp;
    G = int_list_to_poly_f Fp;
    D1' = G D1;
    H1' = G H1;
    (_,S,T) = extended_gcd_poly_f Fp D1' H1';
    j = 1;
    q = p;
    D = D1;
    H = H1
    in linear_hensel_lifting_main Fp p k C S T D1' H1' q j D H)"

text \<open>Algorithm according to Alfonso Miola and David Yun paper.\<close>
context fixes
    k :: nat
  and C :: "int poly_f"
begin

definition hensel_dupe :: "GFp ffield \<Rightarrow> int \<Rightarrow> GFp poly_f \<Rightarrow> GFp poly_f \<Rightarrow> GFp poly_f \<Rightarrow> GFp poly_f \<Rightarrow> GFp poly_f 
   \<Rightarrow> GFp poly_f \<times> GFp poly_f" where
  "hensel_dupe Fq q U D H S T \<equiv> let
       pp = plus_poly_f Fq;
       tt = times_poly_f Fq;
       lc = to_int_f Fq (leading_coeff_f Fq D);
       ilc = inverse_int_modulo lc q;
       Ilc = of_int_f Fq ilc;
       D' = smult_poly_f Fq Ilc D;
       (Q',R) = divmod_poly_one_f Fq (tt T U) D';
       Q = smult_poly_f Fq Ilc Q';
       A = pp (tt S U) (tt H Q);
       B = R
     in (A,B)"

partial_function (tailrec) quadratic_hensel_lifting_main :: "int \<Rightarrow> nat
  \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  [code]: "quadratic_hensel_lifting_main q j D H S T = (if j \<ge> k then (D,H) else
     let 
       Z = integer_ops;
       Fq = GFp q;
       mm = minus_poly_f Z;
       pp = plus_poly_f Z;
       tt = times_poly_f Z;
       sm = smult_poly_f Z;
       I' = int_list_to_poly_f Fq;
       I = map (to_int_f Fq);
       (* Z2 *)
       U = div_int_poly q (mm C (tt D H))
     in if U = zero_poly_f then (D,H) else let (* opt. iii *)
       (* Z3 *)
       IH = I' H;
       ID = I' D;
       IS = I' S;
       IT = I' T;
       U = int_list_to_poly_f Fq U;
       (A,B) = hensel_dupe Fq q U ID IH IS IT;
       (* Z4 *)
       D' = pp D (sm q (I B));
       H' = pp H (sm q (I A));
       (* Z5 *)
       U' = div_int_poly q (mm (pp (tt S D') (tt T H')) (one_poly_f Z));
       (* Z6 *)
       U' = int_list_to_poly_f Fq U';
       (A',B') = hensel_dupe Fq q U' ID IH IS IT;
       (* Z7 *)
       S = mm S (sm q (I A'));
       T = mm T (sm q (I B'));
       D = D';
       H = H';
       j = j * 2;
       q = q * q
     in quadratic_hensel_lifting_main q j D H S T)"
end

definition quadratic_hensel_lifting_binary :: "GFp ffield \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  "quadratic_hensel_lifting_binary Fp k C D1 H1 = (let
    p = characteristic Fp;
    G = int_list_to_poly_f Fp;
    I = map (to_int_f Fp);
    D1' = G D1;
    H1' = G H1;
    (_,S,T) = extended_gcd_poly_f Fp D1' H1';
    j = 1;
    q = p;
    D = D1;
    H = H1
    in quadratic_hensel_lifting_main k C q j D H (I S) (I T))"
    
fun hensel_lifting :: "GFp ffield \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> GFp poly_f list \<Rightarrow> int poly_f list" where
  "hensel_lifting F m u vs' = (let n = length vs' in if n \<le> 1 then if n = 1 then [u] else []
    else let 
      i = n div 2;
      vs_1 = take i vs';
      vs_2 = drop i vs';
      idxs = [0 ..< n];
      I = map (to_int_f F);
      v = I (listprod_poly_f F vs_1);
      w = I (listprod_poly_f F vs_2);
      (V,W) = quadratic_hensel_lifting_binary F m u v w
      in hensel_lifting F m V vs_1 @ hensel_lifting F m W vs_2)"

definition int_poly_bnd :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "int_poly_bnd b = map (\<lambda> x. if 2 * x \<le> b then x else x - b)"

text \<open>input to berlekamp-hensel-factorization-init: 
  content-free and square-free, non-zero integer polynomial $f$,
  delivers $(a,qs,m)$ such that $f$ = $a$ * $Prod$ $qs$ mod $m$, and $m$ is large enough
  to reconstruct real factors of $f$; moreover each $q_i$ in $qs$ should be monic modulo $m$.\<close>

definition berlekamp_hensel_factorization_init :: "int poly_f \<Rightarrow> int \<times> int poly_f list \<times> int" where 
  "berlekamp_hensel_factorization_init f = (let 
     a = last f;
     (ps',(p,m)) = pre_hensel_factorization f;
     F = GFp p;
     mm = p^m;
     i = inverse_int_modulo a mm;
     g = map (op * i) f;
     ps = map (map to_int_GFp) ps';
     qs = hensel_lifting F m g ps';
     sanity = True (* mod_int_poly mm (smult_poly_f integer_ops a (listprod_poly_f integer_ops qs)) =
       mod_int_poly mm f *)
     in if sanity then (a,qs,mm) else Code.abort (String.implode 
       (''error in berlekamp_hensel_factorization on input '' @ show f)) (\<lambda> _. (a,qs,mm)))"

fun sublists_i_n_main :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('b \<times> 'a list) list" where
  "sublists_i_n_main f b xs i n = (if i = 0 then [(b,[])] else if i = n then [(foldr f xs b, xs)]
    else case xs of 
      (y # ys) \<Rightarrow> map (\<lambda> (c,zs) \<Rightarrow> (c,y # zs)) (sublists_i_n_main f (f y b) ys (i - 1) (n - 1)) 
        @ sublists_i_n_main f b ys i (n - 1))"

definition sublists_length :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'a list) list" where
  "sublists_length f b i xs = (let n = length xs in if i > n then [] else sublists_i_n_main f b xs i n)"


definition normalize_content_f :: "int poly_f \<Rightarrow> int poly_f" where
  "normalize_content_f f = (let ct = list_gcd f in map (\<lambda> x. x div ct) f)" 

definition cCons_int :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "cCons_int x xs = (if xs = [] \<and> x = 0 then [] else x # xs)"

definition "smult_poly_int (a :: int) pp = (if a = 0 then [] else map (op * a) pp)"

definition coeff_poly_int :: "int poly_f \<Rightarrow> nat \<Rightarrow> int" where
  "coeff_poly_int = nth_default 0"

definition uminus_poly_int :: "int poly_f \<Rightarrow> int poly_f" where
  "uminus_poly_int = map (\<lambda> x. - x)"

fun minus_poly_int :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "minus_poly_int (x # xs) (y # ys) = cCons_int (x - y) (minus_poly_int xs ys)"
| "minus_poly_int xs [] = xs"
| "minus_poly_int [] ys = uminus_poly_int ys"

text \<open>The following division algorithm assumes that the second argument is a non-zero
  polynomial.\<close>
definition div_int_poly_ff :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f option" where
  "div_int_poly_ff pp q = (let n = degree_poly_f q; qn = coeff_poly_int q n in case (foldr (\<lambda> a sro.
    case sro of None \<Rightarrow> None | Some (s,r) \<Rightarrow>
      let
        ar = cCons_int a r;
        (b,m) = divmod_int (coeff_poly_int ar n) qn
      in if m = 0 then Some (cCons_int b s, minus_poly_int ar (smult_poly_int b q)) else None)
      pp (Some (zero_poly_f, zero_poly_f))) of None \<Rightarrow> None | Some (d,m) \<Rightarrow> if m = zero_poly_f then
        Some d else None)"

definition div_int_poly_f :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "div_int_poly_f p q = (case div_int_poly_ff p q of Some d \<Rightarrow> d | None \<Rightarrow> 
    Code.abort (STR ''integer poly division error'') (\<lambda> _. []))"

    
fun minus_poly_rev_int :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f" where
  "minus_poly_rev_int (x # xs) (y # ys) = (x - y) # (minus_poly_rev_int xs ys)"
| "minus_poly_rev_int xs [] = xs"
  
fun dvd_poly_int_main :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f 
  \<Rightarrow> nat \<Rightarrow> bool" where
  "dvd_poly_int_main lc r d n = (if n = 0 then list_all (op = 0) r else let
     a = hd r;
     (q,re) = divmod_int a lc
     in (re = 0 \<and> (let
     n1 = n - 1;
     rr = tl (if q = 0 then r else minus_poly_rev_int r (map (op * q) d))
     in dvd_poly_int_main lc rr d n1)))"

(* assumes q \<noteq> 0 *)     
definition dvd_int_poly_f :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> bool" where
  "dvd_int_poly_f q p = (let dp = degree_poly_f p; dq = degree_poly_f q
     in dvd_poly_int_main (last q) (rev p) (rev q) (1 + dp - dq))"
  
fun coeff_0_int_poly :: "int poly_f \<Rightarrow> int" where
  "coeff_0_int_poly (Cons x xs) = x"
| "coeff_0_int_poly Nil = 0"
  
context fixes
  m :: int
begin
  
private definition mul_const :: "int poly_f \<Rightarrow> int \<Rightarrow> int" where
  "mul_const p c = (coeff_0_int_poly p * c) mod m"

partial_function (tailrec) factorization_f_to_factorization_int :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> int poly_f list \<Rightarrow> int poly_f list \<Rightarrow> (int \<times> (int poly_f list)) list \<Rightarrow> int poly_f list" where
  [code]: "factorization_f_to_factorization_int u luu lu d r vs res cands = (case cands of Nil
    \<Rightarrow> let d' = d + 1
      in if 2 * d' > r then (u # res) else 
      factorization_f_to_factorization_int u luu lu d' r vs res (sublists_length mul_const lu d' vs)
   | (lv',ws) # cands' \<Rightarrow> let               
       lv = if 2 * lv' \<le> m then lv' else lv' - m (* lv is last coefficient of v below *)  
     in if lv dvd coeff_0_int_poly luu then let
       Z = integer_ops; 
       v = int_poly_bnd m (mod_int_poly m (smult_poly_f Z lu (listprod_poly_f Z ws)))
    in if dvd_int_poly_f v luu then 
      let vv = normalize_content_f v;
          u' = div_int_poly_f u vv;
          lu' = leading_coeff_non_zero u';
          luu' = smult_poly_f Z lu' u';
          vs' = foldr (\<lambda> vi vs. remove1 vi vs) ws vs;
          res' = vv # res;
          r' = r - length ws
        in if 2 * d > r' 
          then (u' # res') 
          else factorization_f_to_factorization_int u' luu' lu' d r' vs' res' (sublists_length mul_const lu' d vs')
     else factorization_f_to_factorization_int u luu lu d r vs res cands'
     else factorization_f_to_factorization_int u luu lu d r vs res cands')"
end


text \<open>input to berlekamp-hensel-factorization: content-free and square-free, 
  non-zero integer polynomial f,
  output: fully factored polynomial over the integers.\<close>

definition berlekamp_hensel_factorization :: "int poly_f \<Rightarrow> int poly_f list" where
  "berlekamp_hensel_factorization f = (let 
     (a,vs,m) = berlekamp_hensel_factorization_init f;
     af = smult_poly_f integer_ops a f     
     in (factorization_f_to_factorization_int m f af a 0 (length vs) vs [] []))"
       
end
