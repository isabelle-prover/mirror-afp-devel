(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Prime Fields GF(p)\<close>

text \<open>This theory contains definitions related to prime fields, i.e.,
  finite fields $[0..<p]$ for some prime $p$ where addition and multiplication
  are just defined modulo $p$.\<close>

theory Prime_Field
imports 
  "../Show/Show_Instances"
begin

declare divmod_nat_div_mod[termination_simp]

fun fast_power :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "\<And> mult one. fast_power mult one x n = (if n = 0 then one else
    let (d,r) = Divides.divmod_nat n 2; 
       rec = fast_power mult one (mult x x) d in 
    if r = 1 then mult x rec else rec)"

record 'a ffield = 
  plus    :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+f\<index>" 65)
  minus   :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-f\<index>" 65)
  uminus  :: "'a \<Rightarrow> 'a" ("-f\<index> _" [81] 80)
  mult    :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*f\<index>" 70)
  power   :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "^f\<index>" 80)
  inverse_f :: "'a \<Rightarrow> 'a" 
  divide  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/f\<index>" 70)
  zero    :: 'a ("0f\<index>")
  one     :: 'a ("1f\<index>")
  characteristic :: int
  of_int_f :: "int \<Rightarrow> 'a"
  to_int_f :: "'a \<Rightarrow> int"

hide_const (open) plus minus uminus mult power divide zero one

text \<open>We make a copy of the integers to separate the set of all integers from
  the intended numbers: 0 to $p-1$ for some fixed prime $p$.\<close>

typedef GFp = "UNIV :: int set" by auto

setup_lifting type_definition_GFp

instantiation GFp :: equal
begin
lift_definition equal_GFp :: "GFp \<Rightarrow> GFp \<Rightarrow> bool" is "op =" .
instance
  by (intro_classes, transfer, simp)
end

context fixes
  p :: int
begin
lift_definition to_int_GFp :: "GFp \<Rightarrow> int" is "\<lambda> x. x" .

lift_definition plus_GFp :: "GFp \<Rightarrow> GFp \<Rightarrow> GFp" is
  "\<lambda> x y. let z = x + y in if z \<ge> p then z - p else z" .

lift_definition uminus_GFp :: "GFp \<Rightarrow> GFp" is
  "\<lambda> x. if x = 0 then 0 else p - x" .

lift_definition minus_GFp :: "GFp \<Rightarrow> GFp \<Rightarrow> GFp " is
  "\<lambda> x y. let z = x - y in if z < 0 then z + p else z" .

lift_definition of_int_GFp :: "int \<Rightarrow> GFp" is
  "\<lambda> x. x mod p" . (* mod with p is always positive *)

(* only invoke if you're sure that the integer is in range [0..<p] *)
lift_definition of_int_GFp_unsafe :: "int \<Rightarrow> GFp" is "\<lambda> x. x" .

lift_definition mult_GFp :: "GFp \<Rightarrow> GFp \<Rightarrow> GFp" is
  "\<lambda> x y. (x * y) mod p" .

lift_definition zero_GFp :: GFp is 0 .
lift_definition one_GFp :: GFp is 1 .

definition power_GFp :: "GFp \<Rightarrow> nat \<Rightarrow> GFp" where
  "power_GFp = fast_power mult_GFp one_GFp"

private partial_function (tailrec) inverse_main :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  [code]: "inverse_main t r newt newr = (if newr = 0 then
    t else let q = r div newr in 
     inverse_main newt newr (t - q * newt) (r - q * newr))"

definition inverse_GFp_large :: "GFp \<Rightarrow> GFp" where 
  "inverse_GFp_large X = (let x = to_int_GFp X;
    res' = inverse_main 0 p 1 x;
    res = if res' < 0 then res' + p else res'
    in of_int_GFp_unsafe res)"

definition inverse_GFp :: "GFp \<Rightarrow> GFp" where
  "inverse_GFp x = (if x = zero_GFp then zero_GFp else power_GFp x (nat (p - 2)))"

text \<open>The extended Euclidean algorithm @{const inverse_GFp_large} to compute
   inverses is more efficient 
   if the prime is large, whereas on small primes, exponentiation @{const inverse_GFp}
   performs better.\<close>

definition divide_GFp :: "GFp \<Rightarrow> GFp \<Rightarrow> GFp"  where
  "divide_GFp x y = mult_GFp x (inverse_GFp y)" 

definition GFp :: "GFp ffield" where
  "GFp = \<lparr> 
    ffield.plus = plus_GFp,
    minus = minus_GFp,
    uminus = uminus_GFp,
    mult = mult_GFp,
    power = power_GFp,
    inverse_f = inverse_GFp,
    divide = divide_GFp,
    zero = zero_GFp,
    one = one_GFp,
    characteristic = p,
    of_int_f = of_int_GFp,
    to_int_f = to_int_GFp\<rparr>"
end

definition showsp_GFp :: "GFp showsp"
where
  "showsp_GFp p x y = (show (to_int_GFp x) @ y)"

lemma show_law_GFp [show_law_intros]:
  "show_law showsp_GFp r"
  by (rule show_lawI) (simp add: showsp_GFp_def show_law_simps)

lemma showsp_GFp_append [show_law_simps]:
  "showsp_GFp p r (x @ y) = showsp_GFp p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup {*
  Show_Generator.register_foreign_showsp @{typ GFp} @{term "showsp_GFp"} @{thm show_law_GFp}
*}

derive "show" GFp

end
