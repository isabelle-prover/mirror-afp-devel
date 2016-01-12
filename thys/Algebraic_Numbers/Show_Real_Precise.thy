(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Show for Real (Algebraic) Numbers -- Unique Representation\<close>

text \<open>We implement the show-function for real (algebraic) numbers by printing them
  uniquely via their monic irreducible polynomial. This is currently a costly operation
  since it involves Kronecker-factorization.\<close>

theory Show_Real_Precise
imports
  Show_Real_Alg
  "../Show/Show_Instances"
begin

fun info_radt :: "real_alg_dt \<Rightarrow> rat poly \<times> nat" where
  "info_radt (Rational r) = info_rai (of_rat_rai r)"
| "info_radt (Irrational rai) = info_rai (normalize_rai Irreducible rai)"

lemma info_radt:
  assumes x: "radt_cond x"
  shows  "\<exists> rai. real_of_radt x = real_of_rai rai \<and> 
    info_radt x = info_rai (normalize_rai Irreducible rai)"
proof (cases x)
  case (Rational r)
  thus ?thesis by (intro exI[of _ "of_rat_rai r"], auto simp: of_rat_rai normalize_rai_of_rat_rai)
next
  case (Irrational rai)
  thus ?thesis using x by auto
qed


lemma info_radt_fun: assumes x: "radt_cond x" and y: "radt_cond y"
  and eq: "real_of_radt x = real_of_radt y"
  shows "info_radt x = info_radt y"
proof -
  from info_radt[OF x] obtain rai1 where x: "real_of_radt x = real_of_rai rai1" and
    ix: "info_radt x = (info_rai (normalize_rai Irreducible rai1))" by auto
  from info_radt[OF y] obtain rai2 where y: "real_of_radt y = real_of_rai rai2" and
    iy: "info_radt y = info_rai (normalize_rai Irreducible rai2)" by auto   
  from info_rai_fun[OF eq[unfolded x y]] ix iy eq x y
  show ?thesis by auto
qed

lift_definition info_radtc :: "real_alg_dtc \<Rightarrow> rat poly \<times> nat" is info_radt .  

lemma info_radtc_fun: "real_of_radtc x = real_of_radtc y \<Longrightarrow> info_radtc x = info_radtc y"
  by (transfer, intro info_radt_fun, auto)

lift_definition real_alg_info :: "real_alg \<Rightarrow> rat poly \<times> nat" is info_radtc
  by (metis info_radtc_fun)

fun show_rai_info :: "int \<Rightarrow> rat poly \<times> nat \<Rightarrow> string" where
  "show_rai_info fl (p,n) = (if degree p = 1 then show (- coeff p 0) else     
    if degree p = 2 then (let p2 = coeff p 1 / 2; q = coeff p 0;
      sqrt = ''sqrt('' @ show (p2 * p2 - q) @ '')'' in
      if p2 = 0 
        then (if n = 1 then '' -'' else []) @ sqrt 
        else (''('' @ show (-p2) @ (if n = 1 then ''-'' else ''+'') @ sqrt @ '')''))
    else ''(num in ('' @ show fl @ '','' @ show (fl + 1) @ ''), root #'' @ show n @ '' of '' @ show p @ '')'')" 

overloading show_real_alg \<equiv> show_real_alg
begin
  definition show_real_alg[code]:
    "show_real_alg x \<equiv> show_rai_info (floor x) (real_alg_info x)"
end

end
