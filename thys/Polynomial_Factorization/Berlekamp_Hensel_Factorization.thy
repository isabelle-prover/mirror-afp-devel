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
  Gauss_Jordan_Field
  Polynomial_Field
  Square_Free_Factorization
  Prime_Factorization
  Gauss_Lemma
  Factorization_Oracle
  Polynomial_Division
begin

hide_const (open) Module.smult
hide_const (open) Divisibility.prime

context
  fixes F :: "GFp ffield" (structure)
begin
definition berlekamp_mat :: "GFp poly_f \<Rightarrow> GFp mat" where
  "berlekamp_mat u = (let n = degree_poly_f u;
    xks = map (\<lambda> k. power_poly_f_mod F u [0f,1f] (nat (characteristic F) * k)) [0..<n] in 
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

context
  fixes Z :: "int ffield"
  and   p :: int
  fixes a b :: "int poly_f"
begin
text \<open>Algorithm according to Exercise 22 (page 684-685 of Knuth's Art of Computer Programming,
  Volume 2.\<close>
definition hensel_lifting_binary_main :: "int \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  "hensel_lifting_binary_main m u v w = (let 
    q = fast_power (op *) 1 p (nat m);
    r = p;
    qr = q * r;
    f = map (\<lambda> x. x div q) (mod_int_poly qr (minus_poly_f Z u (times_poly_f Z v w)));
    bf = times_poly_f Z b f;  
    t = fst (divmod_gen_poly_f Z 1 bf v);
    vbar = minus_poly_f Z bf (times_poly_f Z t v);
    wbar = plus_poly_f Z (times_poly_f Z a f) (times_poly_f Z t w);
    V = mod_int_poly qr (plus_poly_f Z v (smult_poly_f Z q vbar));
    W = mod_int_poly qr (plus_poly_f Z w (smult_poly_f Z q wbar))
  in (V,W))"

function hensel_lifting_binary_rec :: "nat \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  "hensel_lifting_binary_rec i m f f1 f2 = (if i \<ge> m then (f1,f2) else
     case hensel_lifting_binary_main i f f1 f2 of
       (f1',f2') \<Rightarrow> hensel_lifting_binary_rec (i + 1) m f f1' f2')"
  by pat_completeness auto
termination by (relation "measure (\<lambda> (i,m,_). m - i)", auto)
end

definition hensel_lifting_binary :: "GFp ffield \<Rightarrow> nat \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<Rightarrow> int poly_f \<times> int poly_f" where
  "hensel_lifting_binary F m u v w = (let 
    p = characteristic F;
    G = int_list_to_poly_f F;
    v' = G v;
    w' = G w;
    I = map (to_int_f F);
    (_,a',b') = extended_gcd_poly_f F v' w';
    b = I b';
    a = I a'
    in hensel_lifting_binary_rec integer_ops p a b 1 m u v w)"

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
      (V,W) = hensel_lifting_binary F m u v w
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

fun sublists_i_n_main :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "sublists_i_n_main xs i n = (if i = 0 then [[]] else if i = n then [xs]
    else case xs of 
      (y # ys) \<Rightarrow> map (Cons y) (sublists_i_n_main ys (i - 1) (n - 1)) @ sublists_i_n_main ys i (n - 1))"

definition sublists_length :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "sublists_length i xs = (let n = length xs in if i > n then [] else sublists_i_n_main xs i n)"


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

definition dvd_int_poly_f :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> bool" where
  "dvd_int_poly_f p q = (case div_int_poly_ff q p of None \<Rightarrow> False | Some _ \<Rightarrow> True)"

fun coeff_0_int_poly :: "int poly_f \<Rightarrow> int" where
  "coeff_0_int_poly (Cons x xs) = x"
| "coeff_0_int_poly Nil = 0"
  
context fixes
  m :: int
begin
partial_function (tailrec) factorization_f_to_factorization_int :: "int poly_f \<Rightarrow> int poly_f \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> int poly_f list \<Rightarrow> int poly_f list \<Rightarrow> int poly_f list list \<Rightarrow> int poly_f list" where
  [code]: "factorization_f_to_factorization_int u luu lu d r vs res cands = (case cands of Nil
    \<Rightarrow> let d' = d + 1 in if 2 * d' > r then (u # res) else 
      factorization_f_to_factorization_int u luu lu d' r vs res (sublists_length d' vs)
   | ws # cands' \<Rightarrow> let 
       lv' = foldr (\<lambda> w p. (p * coeff_0_int_poly w) mod m) ws lu;       
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
          else factorization_f_to_factorization_int u' luu' lu' d r' vs' res' (sublists_length d vs')
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

(* TODO: isn't list_to_poly possible in a more convenient way? Just invoking @{const Poly}
  yields abstraction violation *)
primrec list_to_poly_main :: "'a::comm_monoid_add list \<Rightarrow> nat \<Rightarrow> 'a poly"
where
  "list_to_poly_main [] i = 0"
| "list_to_poly_main (a # as) i = monom a i + list_to_poly_main as (Suc i)"

definition list_to_poly :: "'a::comm_monoid_add list \<Rightarrow> 'a poly" where
  "list_to_poly xs = list_to_poly_main xs 0"

text \<open>Factorization oracle for rational polynomials.\<close>
definition berlekamp_hensel_factorization_rat :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "berlekamp_hensel_factorization_rat p = (let
     (a,psi) = yun_factorization gcd_rat_poly p;
     ber_hen = (\<lambda> (q,i). let (b,f) = rat_to_normalized_int_poly q;
       fs = berlekamp_hensel_factorization (coeffs f);
       gs = map (map of_int) fs;
       hsi = map (\<lambda> h. (list_to_poly h,Suc i)) gs
       in (b^Suc i, hsi));
     pre_result = map ber_hen psi;
     factors = concat (map snd pre_result);
     b = a * listprod (map fst pre_result);     
     sanity = True (* (p = smult b (listprod (map (\<lambda> (q,i). q^i) factors))) *)
   in if sanity then (b,factors) else Code.abort (String.implode
       (''error in berlekamp_hensel_factorization_rat on input '' @ show (coeffs p))) (\<lambda> _. (b,factors)))"

       
overloading factorization_oracle \<equiv> factorization_oracle
begin

definition factorization_oracle[code]: "factorization_oracle x \<equiv> berlekamp_hensel_factorization_rat x"

end

end
