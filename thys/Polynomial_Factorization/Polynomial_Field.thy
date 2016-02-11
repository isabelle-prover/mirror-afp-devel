(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Polynomials over Finite Fields\<close>

text \<open>The theory contains copies of algorithms for univariate polynomials which
  have been adapted to finite fields (which are not in the type-class field).\<close>

theory Polynomial_Field
imports 
  Prime_Field
  "../Show/Show_Poly"
  "../Partial_Function_MR/Partial_Function_MR"
begin

type_synonym 'a poly_f = "'a list"

context
  fixes F :: "'a ffield" (structure)
begin

definition cCons_f :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" 
where
  "cCons_f x xs = (if xs = [] \<and> x = 0f then [] else x # xs)"

fun plus_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  "plus_poly_f (x # xs) (y # ys) = cCons_f (x +f y) (plus_poly_f xs ys)"
| "plus_poly_f xs [] = xs"
| "plus_poly_f [] ys = ys"

definition uminus_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f" where
  "uminus_poly_f = map (\<lambda> x. -f x)"

fun minus_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  "minus_poly_f (x # xs) (y # ys) = cCons_f (x -f y) (minus_poly_f xs ys)"
| "minus_poly_f xs [] = xs"
| "minus_poly_f [] ys = uminus_poly_f ys"

definition "smult_poly_f a pp = (if a = 0f then [] else map (op *f a) pp)"

definition zero_poly_f :: "'a poly_f" where
  [code_unfold]: "zero_poly_f = []"

definition one_poly_f :: "'a poly_f" where
  [code_unfold]: "one_poly_f = [1f]"

definition "times_poly_f pp qq \<equiv> foldr 
  (\<lambda> a pa. plus_poly_f (smult_poly_f a qq) (cCons_f 0f pa)) pp zero_poly_f"

fun listprod_poly_f :: "'a poly_f list \<Rightarrow> 'a poly_f" where
  "listprod_poly_f (x # xs) = times_poly_f x (listprod_poly_f xs)"
| "listprod_poly_f [] = one_poly_f"

definition power_poly_f :: "'a poly_f \<Rightarrow> nat \<Rightarrow> 'a poly_f" where
  "power_poly_f = fast_power times_poly_f one_poly_f"

definition coeff_poly_f :: "'a poly_f \<Rightarrow> nat \<Rightarrow> 'a" where
  "coeff_poly_f = nth_default 0f"

definition degree_poly_f :: "'a poly_f \<Rightarrow> nat" where
  "degree_poly_f pp \<equiv> length pp - 1"

definition leading_coeff_f :: "'a poly_f \<Rightarrow> 'a" where
  "leading_coeff_f pp = (if pp = zero_poly_f then 0f else last pp)"

fun minus_poly_rev_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  "minus_poly_rev_f (x # xs) (y # ys) = (x -f y) # (minus_poly_rev_f xs ys)"
| "minus_poly_rev_f xs [] = xs"

(* div mod where divisor has leading coefficient 1 *)
fun divmod_poly_one_main_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f 
  \<Rightarrow> nat \<Rightarrow> 'a poly_f \<times> 'a poly_f" where
  "divmod_poly_one_main_f q r d n = (if n = 0 then (q,r) else let
     a = hd r;
     n1 = n - 1;
     qqq = cCons_f a q;
     rr = tl (if a = 0f then r else minus_poly_rev_f r (map (op *f a) d))
     in divmod_poly_one_main_f qqq rr d n1)"

(* div mod where divisor has leading coefficient 1 *)
definition divmod_poly_one_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f \<times> 'a poly_f" where
  "divmod_poly_one_f p q = (let dp = degree_poly_f p; dq = degree_poly_f q;
     (qu,re) = divmod_poly_one_main_f zero_poly_f (rev p) (rev q) (1 + dp - dq)
     in (qu,rev (dropWhile (op = 0f) re)))"

definition divmod_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f \<times> 'a poly_f" where
  "divmod_poly_f pp q = (if q = zero_poly_f then (zero_poly_f,pp)
    else let 
      lc = leading_coeff_f q; 
      ilc = inverse_f F lc;
      q' = smult_poly_f ilc q;
      (qu,re) = divmod_poly_one_f pp q'
    in (smult_poly_f ilc qu, re))"

definition "div_poly_f pp qq = fst (divmod_poly_f pp qq)"
definition "mod_poly_f pp qq = snd (divmod_poly_f pp qq)"

definition power_poly_f_mod :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> nat \<Rightarrow> 'a poly_f" where
  "power_poly_f_mod modulus = fast_power 
     (\<lambda> a b. mod_poly_f (times_poly_f a b) modulus) one_poly_f"

partial_function (tailrec) gcd_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  [code]: "gcd_poly_f x y = (if y = zero_poly_f then smult_poly_f (inverse_f F (leading_coeff_f x)) x
    else gcd_poly_f y (mod_poly_f x y))"
    
fun pderiv_poly_f_main :: "'a \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  "pderiv_poly_f_main i (x # xs) = cCons_f (i *f x) (pderiv_poly_f_main (i +f 1f) xs)"
| "pderiv_poly_f_main i [] = []"

definition pderiv_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f" where
  "pderiv_poly_f pp = pderiv_poly_f_main 1f (tl pp)"

partial_function (tailrec) extended_gcd_poly_f_main :: 
  "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 
   'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 
   ('a poly_f \<times> 'a poly_f \<times> 'a poly_f)" where
  [code]: "extended_gcd_poly_f_main ri1 si1 ti1 ri si ti = 
    (if ri = zero_poly_f then (ri1,si1,ti1) else let q = div_poly_f ri1 ri
     in extended_gcd_poly_f_main ri si ti 
     (minus_poly_f ri1 (times_poly_f q ri))
     (minus_poly_f si1 (times_poly_f q si)) 
     (minus_poly_f ti1 (times_poly_f q ti)))"

definition extended_gcd_poly_f :: "'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> 
  ('a poly_f \<times> 'a poly_f \<times> 'a poly_f)" where
  "extended_gcd_poly_f a b = (let 
    (g,c,d) = extended_gcd_poly_f_main 
      a one_poly_f zero_poly_f 
      b zero_poly_f one_poly_f;
      l = leading_coeff_f g;
      i = inverse_f F l;
      scale = smult_poly_f i
    in if l = 0f then (g,c,d) else (scale g, scale c,scale d))"

fun poly_char_root_main :: "int \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f" where
  "poly_char_root_main n (x # xs) = (if n = 0 then x # poly_char_root_main (characteristic F -1) xs 
    else poly_char_root_main (n - 1) xs)"
| "poly_char_root_main n [] = []"

definition poly_char_root :: "'a poly_f \<Rightarrow> 'a poly_f" where
  "poly_char_root pp = poly_char_root_main 0 pp"

end 

(* we leave the locale only since partial_function_mr does not work within contexts *)
partial_function_mr (tailrec) yun_factorization_main_f :: "'a ffield \<Rightarrow> nat \<Rightarrow> 'a poly_f \<Rightarrow> ('a poly_f \<times> nat) list \<Rightarrow> ('a poly_f \<times> nat) list" 
  and yun_factorization_loop_f :: "'a ffield \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly_f \<Rightarrow> 'a poly_f \<Rightarrow> ('a poly_f \<times> nat) list \<Rightarrow> ('a poly_f \<times> nat) list" where
  "yun_factorization_main_f F m f res = (let g = pderiv_poly_f F f in
    if g = zero_poly_f then yun_factorization_main_f F (m * nat (characteristic F)) (poly_char_root F f) res
    else let c = gcd_poly_f F f g; w = div_poly_f F f c 
    in yun_factorization_loop_f F m 1 c w res)"
| "yun_factorization_loop_f F m i c w res = (if w = one_poly_f F then
      if c = one_poly_f F then res else yun_factorization_main_f F (m * nat (characteristic F)) (poly_char_root F c) res
      else let y = gcd_poly_f F w c; z = div_poly_f F w y
      in yun_factorization_loop_f F m (Suc i) (div_poly_f F c y) y 
        (if z = one_poly_f F then res else (z,m * i) # res))"      

context 
  fixes F :: "'a ffield" (structure)
begin
definition yun_factorization_f :: "'a poly_f \<Rightarrow> ('a \<times> ('a poly_f \<times> nat)list)" where
  "yun_factorization_f pp = (if pp = zero_poly_f then (0f,[])
    else let 
      a = leading_coeff_f F pp;
      q = smult_poly_f F (inverse_f F a) pp
      in (a, filter (\<lambda> (p,i). p \<noteq> one_poly_f F) (yun_factorization_main_f F 1 q [])))"

fun list_to_poly_f :: "'a list \<Rightarrow> 'a poly_f" where
  "list_to_poly_f (x # xs) = cCons_f F x (list_to_poly_f xs)"
| "list_to_poly_f [] = []"

definition int_list_to_poly_f :: "int list \<Rightarrow> 'a poly_f" where
  "int_list_to_poly_f xs = list_to_poly_f (map (of_int_f F) xs)"

definition show_poly_f :: "'a poly_f \<Rightarrow> string" where
  "show_poly_f p = show_poly_main 0 (map (to_int_f F) p)"
end

context
  fixes F :: "GFp ffield"
  and f :: "GFp poly_f"
begin
text \<open>Algorithm for irreducibility taken from Appendix A (Alg. A.1 on page 258) in 
   Guide to Elliptic Curve Cryptography.\<close>

fun irreducible_GFp_poly_main :: "GFp poly_f \<Rightarrow> GFp poly_f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "irreducible_GFp_poly_main u z p (Suc i) = 
    (let uu = power_poly_f_mod F f u p; d = gcd_poly_f F f (minus_poly_f F uu z) in 
      if d = one_poly_f F then irreducible_GFp_poly_main uu z p i else False)"
| "irreducible_GFp_poly_main u z p 0 = True"

definition irreducible_GFp_poly :: bool where
  "irreducible_GFp_poly = (let n = degree_poly_f f;
    p = characteristic F; z = int_list_to_poly_f F [0,1] 
    in irreducible_GFp_poly_main z z (nat p) (n div 2))"
end

end