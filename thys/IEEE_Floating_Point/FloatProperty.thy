(*==========================================================================*)
(* Proofs of Properties about Floating Point Arithmetic.                    *) 
(*==========================================================================*) 

(* Author: Lei Yu, University of Cambridge *)

theory FloatProperty imports IEEE begin

section{* Proofs of Properties about Floating Point Arithmetic *}

lemmas float_defs = Finite_def Infinity_def Iszero_def Isnan_def Val_def Sign_def
                    Isnormal_def Isdenormal_def Fraction_def Exponent_def

subsection{*Theorems derived from definitions*}                                                           

lemma sign: "\<And>a. sign a = fst a"
by auto

lemma exponent: "\<And>a. exponent a = fst (snd a)"
by auto

lemma fraction: "\<And>a. fraction a = snd (snd a)"
by auto

lemma is_valid: "\<And>x a. is_valid x a = ((sign a < (2::nat)) \<and> (exponent a < 2^(expwidth x))
                        \<and> (fraction a < 2^(fracwidth x)))"
by (auto simp: is_valid_def emax_def)

lemma is_valid_defloat: " is_valid float_format (Rep_float a)"
  by (cases a) (simp add: Abs_float_inverse)


lemma float_cases: "Isnan a \<or> Infinity a \<or> Isnormal a \<or> Isdenormal a \<or> Iszero a"
  by (cases a) (auto simp: Abs_float_inverse emax_def is_nan_def float_defs
                  is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)

lemma float_cases_finite: "Isnan a \<or> Infinity a \<or> Finite a"
by (cases a) (auto simp: Abs_float_inverse emax_def is_nan_def float_defs
                is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)

lemma float_zero1: "Iszero Plus_zero"
  by (auto simp: Iszero_def Abs_float_inverse is_zero_def is_valid_def)

lemma float_zero2: "Iszero Minus_zero"
  by (auto simp: Iszero_def Abs_float_inverse Minus_zero_def is_zero_def is_valid_def)

lemma is_valid_special: "is_valid x (minus_infinity x)"
                        "is_valid x (plus_infinity x)"
                        "is_valid x (topfloat x)"
                        "is_valid x (bottomfloat x)"
                        "is_valid x (plus_zero x)"
                        "is_valid x (minus_zero x)"
  by (auto simp: emax_def is_valid_def minus_infinity_def plus_infinity_def topfloat_def bottomfloat_def)

lemma sign_0_1: "is_valid x a \<Longrightarrow> (sign a = 0) \<or> (sign a = 1)"
  by (auto simp: is_valid_def)

(*The types of floating-point numbers are mutually distinct*)
lemma float_distinct: "\<not>(Isnan a \<and> Infinity a)"
                      "\<not>(Isnan a \<and> Isnormal a)"
                      "\<not>(Isnan a \<and> Isdenormal a)"
                      "\<not>(Isnan a \<and> Iszero a)"
                      "\<not>(Infinity a \<and> Isnormal a)"
                      "\<not>(Infinity a \<and> Isdenormal a)"
                      "\<not>(Infinity a \<and> Iszero a)"
                      "\<not>(Isnormal a \<and> Isdenormal a)"
                      "\<not>(Isdenormal a \<and> Iszero a)"
by (auto simp: emax_def float_defs is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma float_distinct_finite: "\<not>(Isnan a \<and> Finite a)" "\<not>(Infinity a \<and> Finite a)"
  by (auto simp: emax_def float_defs is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma finite_infinity: "Finite a \<Longrightarrow> \<not> (Infinity a)"
  by (auto simp: emax_def float_defs is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma finite_nan: "Finite a \<Longrightarrow> \<not> (Isnan a)"
by (auto simp: emax_def float_defs is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)

(* For every real number, the floating-point numbers closest to it always exist. *)
lemma is_closest_exists: 
  fixes v::"representation \<Rightarrow> real" and s::"representation set" and x::real and a::representation
  assumes finite:"finite s" 
  assumes non_empty: "\<not>(s = {})" 
  shows  "\<exists> a. is_closest v s x a"
using finite non_empty
proof (induct s rule: finite_induct)
  case empty thus ?case by simp
next
  case (insert z s)
  have "s = {} \<Longrightarrow> ?case"
    proof -
      assume "s = {}"
      then have "is_closest v (insert z s) x z" by (auto simp: is_closest_def)
      then show ?thesis by metis
    qed
  moreover have "s \<noteq> {} \<Longrightarrow> ?case"
    proof -
      assume "s \<noteq> {}"
      obtain a where "is_closest v s x a" using insert.hyps by (metis `s \<noteq> {}`)
      have "abs((v a) - x ) \<le> abs ((v z) - x) \<Longrightarrow> ?case"
        proof -
          assume "abs((v a) - x ) \<le> abs ((v z) - x)"
          then have "is_closest v (insert z s) x a" 
            by (metis (hide_lams, no_types) `is_closest v s x a` insert_iff is_closest_def)
          then show ?thesis by metis
        qed
      moreover have "abs((v z) - x ) \<le> abs ((v a) - x) \<Longrightarrow> ?case"
        proof -
           assume z: "abs((v z) - x ) \<le> abs ((v a) - x)"
           have "\<forall>b. b \<in> s \<longrightarrow> abs((v a) - x ) \<le> abs ((v b) - x)"
             by (metis `is_closest v s x a` is_closest_def)
           then have "\<forall>b. b \<in> (insert z s) \<longrightarrow> abs((v z) - x ) \<le> abs ((v b) - x)"
             by (metis (full_types) insert_iff order_refl order_trans z)
           then have "is_closest v (insert z s) x z" using is_closest_def `is_closest v s x a`
             by (metis (mono_tags) insertI1)
           then show ?thesis by metis
         qed
      ultimately show ?thesis by (metis linear)
    qed
  ultimately show ?case by metis
qed

lemma closest_is_everything:
  fixes v::"representation \<Rightarrow> real" and s::"representation set" and x::real and a::representation
  assumes finite: "finite s"
  assumes non_empty: "\<not>(s = {})"
  shows "is_closest v s x (closest v p s x) \<and> 
         ((\<exists> b. is_closest v s x b \<and> p b) \<longrightarrow> p (closest v p s x))"
unfolding closest_def
by (rule someI_ex) (metis assms is_closest_exists [of s v x]) 

lemma closest_in_set:
  fixes v::"representation \<Rightarrow> real" 
  assumes "finite s"  "\<not>(s = {})"
  shows "(closest v p s x) \<in> s"
  by (metis assms closest_is_everything is_closest_def)

lemma closest_is_closest: 
  fixes v::"representation \<Rightarrow> real"
  assumes finite: "finite s"
  assumes non_empty: "\<not>(s = {})"
  shows "is_closest v s x (closest v p s x)"
by (metis closest_is_everything finite non_empty)

lemma float_first_cross: 
  "{a::representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p} =
   image (\<lambda> ((x::nat), (y, z)). (x, y, z)) ({x. x < m} \<times> {y. y < n} \<times> {z. z < p})"
  by auto

lemma finite_r3: "finite {a :: representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p}"
  by (auto simp: float_first_cross)

lemma is_valid_finite: "finite {a. is_valid x a}"
  by (auto simp: finite_r3 sign exponent fraction is_valid_def)

lemma is_finite_subset: "{a :: representation. is_finite x a} \<subseteq> {a. is_valid x a} "
  by (auto simp: is_finite_def)

lemma match_float_finite:
  assumes "({a :: representation. is_finite x a} \<subseteq> {a. is_valid x a})"
  shows "finite {a. is_finite x a}"
proof -
  have "finite {a. is_valid x a}" using is_valid_finite by metis
  thus ?thesis using assms by (metis finite_subset)
qed

lemma is_finite_finite: "finite {a :: representation. is_finite x a}"
by (metis is_finite_subset match_float_finite)

lemma is_valid_nonempty: "\<not>({a::representation. is_valid x a} = {})"
proof -
  have "(0::nat, 0, 0) \<in> {a. is_valid x a}" by (auto simp: is_valid_def)
  thus ?thesis by (metis empty_iff)
qed

lemma is_finite_nonempty: "\<not>({a::representation. is_finite x a} = {})"
proof -
  have "(0, 0, 0) \<in> {a. is_finite x a}" 
    by (auto simp: is_zero_def is_valid_def is_finite_def)
  thus ?thesis by (metis empty_iff)
qed

lemma is_finite_closest: 
  fixes v::"representation \<Rightarrow> real"
  shows "is_finite f (closest v p {a. is_finite f a} x)"
proof -
  have "closest v p {a. is_finite f a} x \<in> {a. is_finite f a}" using closest_in_set 
    by (metis is_finite_finite is_finite_nonempty)
  then show ?thesis by auto
qed

lemma is_valid_closest: 
  fixes v::"representation \<Rightarrow> real" 
  shows "is_valid f (closest v p {a. is_finite f a} x)"
by (metis is_finite_closest is_finite_def)

lemma is_valid_round: "is_valid f (round f To_nearest x)"
proof -
  have "round f To_nearest x = (if x \<le> -(threshold f) 
    then minus_infinity f 
    else if x \<ge> threshold f
    then plus_infinity f 
    else (closest (valof f) (\<lambda>a. even (fraction a)) {a. is_finite f a} x) )"
    by (metis round.simps(1))
  moreover have "is_valid f (minus_infinity f)" using is_valid_special by metis
  moreover have "is_valid f (plus_infinity f)" using is_valid_special by metis
  moreover have "is_valid f (closest (valof f) (\<lambda>a. even (fraction a)) {a. is_finite f a} x)"
    using is_valid_closest by auto
  ultimately have "is_valid f (if x \<le> -(threshold f) 
    then minus_infinity f 
    else if x \<ge> threshold f
    then plus_infinity f 
    else (closest (valof f) (\<lambda>a. even (fraction a)) {a. is_finite f a} x) )"
   by auto
  then have "is_valid f (round f To_nearest x)" by auto
  thus ?thesis by auto
qed

lemma defloat_float_round: "Rep_float (Abs_float (round float_format To_nearest x)) = 
                            round (float_format) To_nearest x"
  by (metis mem_Collect_eq Abs_float_inverse is_valid_round) 

lemma zerosign_valid: 
  assumes  sign: "s = 0 \<or> s = 1" and valid: "is_valid x a"
  shows "is_valid x (zerosign x s a)"
proof -
  have "exponent a < 2^expwidth x \<and> fraction a < 2^fracwidth x" using valid 
    by (auto simp: is_valid_def)
  moreover have "s < 2" using sign by auto
  ultimately have "is_valid x (s, exponent a, fraction a)" by (auto simp: is_valid_def)
  thus ?thesis using assms is_valid_special by (metis zerosign_def)
qed

lemma defloat_float_zerosign_round: 
  assumes "b = 0 \<or> b = 1"
  shows "Rep_float(Abs_float (zerosign float_format b (round float_format To_nearest x))) =
         zerosign float_format b (round float_format To_nearest x)"
by (metis assms is_valid_round mem_Collect_eq zerosign_valid Abs_float_inverse)


subsection{*Properties about ordering and bounding*}


(*Lifting of non-exceptional comparisons*)
lemma float_lt [simp]: 
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a < b \<longleftrightarrow> Val a < Val b)"
proof 
  assume "Val a  <  Val b"
  have "\<not> (Isnan a \<or> Isnan b)" using assms float_distinct_finite by metis
  moreover have "\<not> Infinity a" using A1 float_distinct_finite by metis
  moreover have "\<not> Infinity b" using A2 float_distinct_finite by auto
  ultimately have "fcompare float_format (Rep_float a) (Rep_float b) = Lt"  
    using  `Val a < Val b` by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  then show "a < b" by (auto simp: less_float_def) 
next
  assume "a < b"
  then have lt: "fcompare float_format (Rep_float a) (Rep_float b) = Lt"
    by (simp add: less_float_def)
  have nonNan: "\<not> (Isnan a \<or> Isnan b)" using assms float_distinct_finite by metis
  have "\<not> Infinity a" using A1 float_distinct_finite by metis
  then have nonInfinity_a: "\<not> (Infinity a)" by auto
  have "\<not> Infinity b" using A2 float_distinct_finite by auto
  then have nonInfinity_b: "\<not> (Infinity b)" by auto
  have "((Infinity a) \<and> ((Sign a) = 1)) \<Longrightarrow>
        \<not>((Infinity b) \<and> ((Sign b) = 1)) \<Longrightarrow> 
        fcompare float_format (Rep_float a) (Rep_float b) = Lt" 
    using nonNan nonInfinity_a by auto
  moreover have "(Infinity b) \<and> ((Sign b) = 0) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) = Lt" 
    using nonNan nonInfinity_a 
    nonInfinity_b by auto
  moreover have "Val a < Val b \<Longrightarrow> fcompare float_format (Rep_float a) (Rep_float b) = Lt" 
    using nonNan nonInfinity_a nonInfinity_b  
    by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  moreover have "\<not>(((Infinity a) \<and> ((Sign a) = 1)) \<and>
         \<not>((Infinity b) \<and> ((Sign b) = 1))) \<and>
         \<not>((Infinity b) \<and> ((Sign b) = 0)) \<and>
         \<not>(Val a < Val b) \<Longrightarrow>
         fcompare float_format (Rep_float a) (Rep_float b) \<noteq> Lt" 
    using fcompare_def nonNan nonInfinity_a 
    by (auto simp add: Infinity_def Val_def Sign_def fcompare_def)
  ultimately have "(((Infinity a) \<and> ((Sign a) = 1)) \<and>
                   \<not>((Infinity b) \<and> ((Sign b) = 1))) \<or>
                   ((Infinity b) \<and> ((Sign b) = 0)) \<or>
                   (Val a < Val b)" 
    using lt by force
  then show "Val a < Val b" 
    using fcompare_def lt nonInfinity_a nonInfinity_b nonNan assms Isnan_def 
    by auto
qed  

lemma float_eq [simp]:
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a \<doteq> b) \<longleftrightarrow> (Val a = Val b)"
proof 
  assume "Val a = Val b"
  have "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  moreover have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  moreover have "\<not> Infinity b" using A2 float_distinct_finite by auto
  ultimately have "fcompare float_format (Rep_float a) (Rep_float b) = Eq" 
    using `Val a = Val b` by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  then show "a \<doteq> b" by (auto simp: float_eq_def)
next
  assume "a \<doteq> b"
  then have eq: "fcompare float_format (Rep_float a) (Rep_float b) = Eq" by (simp add: float_eq_def)
   have nonNan: "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  then have  nonInfinity_a: "\<not> (Infinity a)" by auto
  have "\<not> Infinity b" using A2 float_distinct_finite by auto
  then have nonInfinity_b: "\<not> (Infinity b)" by auto
  have "((Infinity a) \<and> ((Sign a) = 1)) \<and>
    ((Infinity b) \<and> ((Sign b) = 1)) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" using nonNan nonInfinity_a by auto
  moreover have "((Infinity a) \<and> 
    ((Sign a) = 0)) \<and> (Infinity b) \<and> ((Sign b) = 0)
    \<Longrightarrow> fcompare float_format (Rep_float a) (Rep_float b) = Eq"
    using nonNan nonInfinity_a by auto
  moreover have "(Val a) = (Val b) \<Longrightarrow>
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" 
    using nonNan nonInfinity_a nonInfinity_b 
    by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  moreover have "\<not>(((Infinity a) \<and> ((Sign a) = 1)) \<and>
    ((Infinity b) \<and> ((Sign b) = 1))) \<and> 
    \<not>(((Infinity a) \<and> 
    ((Sign a) = 0)) \<and> (Infinity b) \<and> ((Sign b) = 0))
    \<and> \<not>((Val a) = (Val b)) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) \<noteq> Eq"  
    using nonNan nonInfinity_a by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def)
  ultimately have "((Infinity a) \<and> ((Sign a) = 1)) \<and>
    ((Infinity b) \<and> ((Sign b) = 1)) 
    \<or>
    ((Infinity a) \<and> 
    ((Sign a) = 0)) \<and> (Infinity b) \<and> ((Sign b) = 0)
    \<or> 
    (Val a) = (Val b)" using eq by force  
  then have "(Val a) = (Val b)" using A1 A2
    using fcompare_def eq nonInfinity_a nonInfinity_b nonNan assms Isnan_def 
    by auto
  then show "Val a = Val b" by simp
qed 

lemma float_le [simp]:
  assumes "Finite a" "Finite b"
  shows "(a \<le> b) \<longleftrightarrow> (Val a \<le> Val b)"
proof -
  have "(a \<le> b) \<equiv> fcompare float_format (Rep_float a) (Rep_float b) = Lt \<or>
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" using less_eq_float_def by auto
  then  have "(a \<le> b) \<equiv> flt float_format (Rep_float a) (Rep_float b) \<or> 
    feq float_format (Rep_float a) (Rep_float b)" by auto
  then have "(a \<le> b) \<equiv> a < b \<or> a \<doteq> b" using less_float_def float_eq_def by auto
  then show ?thesis using assms by auto
qed

(*Reflexivity of equality for non-NaNs*)
lemma float_eq_refl [simp]: "(a \<doteq> a) \<longleftrightarrow> \<not>(Isnan a)"
  by (auto simp add: Infinity_def Isnan_def Val_def fcompare_def float_eq_def)

(*Properties about Ordering*)
lemma float_lt_trans [simp]: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite c \<Longrightarrow> a < b \<and> b < c \<longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_trans [simp]: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite c \<Longrightarrow> a \<le> b \<and> b < c \<longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_neg [simp]: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> \<not>(a < b) \<longleftrightarrow> b \<le> a"
  by auto

(*Properties about bounding*)
lemma float_le_infinity [simp]: "\<not> Isnan a \<Longrightarrow> a \<le> Plus_infinity"
proof -
  assume "\<not> Isnan a"
  then have "(fcompare float_format (Rep_float a) (plus_infinity float_format) = Eq) \<or>
             (fcompare float_format (Rep_float a) (plus_infinity float_format) = Lt)"
             by (auto simp add: Isnan_def fcompare_def is_nan_def is_infinity_def plus_infinity_def)
  then show ?thesis 
    by (auto simp: Plus_infinity_def less_eq_float_def plus_infinity_def
                   Abs_float_inverse emax_def is_valid_def)
qed

lemma [simp]: "Plus_zero \<le> Abs_float (topfloat float_format)"
  by (auto simp: fcompare_def is_nan_def less_eq_float_def topfloat_def 
       Abs_float_inverse emax_def is_infinity_def is_zero_def is_valid_def)

lemma valof_topfloat: "valof float_format (topfloat float_format) = largest float_format"
  by (simp add: emax_def topfloat_def largest_def)

lemma float_frac_le: "Finite a \<Longrightarrow> (Fraction a) \<le> 2^52 - 1"
  by (cases a) (auto simp: Abs_float_inverse float_defs is_valid_def)

lemma float_exp_le: "Finite a \<Longrightarrow> (Exponent a) \<le> 2046"
  by (cases a) (auto simp: emax_def float_defs is_normal_def is_denormal_def is_zero_def)

lemma float_sign_le: "(-1::real)^(Sign a) = 1 \<or> (-1::real)^(Sign a) = -1"
by (metis neg_one_even_power neg_one_odd_power)

lemma exp_less: "(a::nat) \<le> b \<Longrightarrow> (2::real)^a \<le> 2^b"
  by auto

lemma div_less: "(a::'a::linordered_field_inverse_zero) \<le> b \<and> c > 0 \<Longrightarrow> a/c \<le> b/c"
  by (metis divide_le_cancel less_asym)

lemma finite_topfloat: "Finite Topfloat"
by (auto simp: float_defs Topfloat_def topfloat_def Abs_float_inverse emax_def is_normal_def is_valid_def)

lemma float_le_topfloat: "Finite a \<Longrightarrow>  a \<le> Topfloat"
proof -
  assume A: "Finite a"
  then have B: "(Fraction a) \<le> 2^52 - 1" by (rule float_frac_le)
  have C: "(Exponent a) \<le> 2046" using A by (rule float_exp_le)
  then have "(Fraction a)/2^(fracwidth float_format) \<le> ((2^52 - 1)/2^(fracwidth float_format))" 
    using B by auto 
  then have D: "(2 / (2^bias float_format)) *
    ((Fraction a)/2^(fracwidth float_format)) \<le>  
    (2 / (2^bias float_format)) * (( 2^52 - 1)/2^(fracwidth float_format))" 
    by (auto simp: bias_def)  
  have H: "0<(1 + (Fraction a)/2^fracwidth float_format) \<and>
    (1 + (Fraction a)/2^fracwidth float_format)
    \<le> (1 + (2^52 - 1)/2^fracwidth float_format)"  using D by (auto simp: bias_def) 
  have J: "(2::real)^(Exponent a) \<le> 2^2046" using C by (metis exp_less)
  then have K: "0<((2::real)^(Exponent a)) / (2^bias float_format)\<and>
    ((2::real)^(Exponent a)) / (2^bias float_format) \<le> (2^2046) / (2^bias float_format)"
    using div_less by (metis zero_less_divide_iff zero_less_numeral zero_less_power)  
  then have L: "0 < (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<and>
    (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<le>
    ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" 
    by (metis H divide_zero_left pos_divide_less_eq mult_mono' less_eq_real_def)
  then have M: "1 * (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<le> 
    (-1)^0 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by auto
  have "(-1) * (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<le> 
    (-1)^0 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using L by auto
  then have N: "(-1)^(Sign a) * (((2::real)^(Exponent a)) /
    (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<le>  (-1)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " using M A float_sign_le by metis
  have P: "(-1) * (2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<le> (-1)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)"  using A B by (auto simp: bias_def)
  have Q: "1 * (2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<le> (-1)^0 * ((2^2046) /
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using A B by (auto simp: bias_def)
  then have "(-1)^(Sign a) *(2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<le> (-1)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " 
    using P Q float_sign_le by (metis A)
  then have R: "
    (if (exponent(Rep_float a) = 0) 
    then (-1)^(Sign a) *(2 / (2^bias float_format)) * 
         ((Fraction a)/2^(fracwidth float_format)) 
    else (-1)^(Sign a) * (((2::real)^(Exponent a))/
         (2^bias float_format)) *
         (1 + (Fraction a)/2^fracwidth float_format)) \<le> 
         (-1)^0 * ((2^2046) / (2^bias float_format)) *
         (1 + (2^52 - 1)/2^fracwidth float_format)" using N by simp
  have "valof (float_format) (Rep_float a) =  
    (if (exponent(Rep_float a) = 0) 
    then (-1)^(Sign a) *(2 / (2^bias float_format)) * 
         ((Fraction a)/2^(fracwidth float_format)) 
    else (-1)^(Sign a) * (((2::real)^(Exponent a)) / 
         (2^bias float_format)) * (1 + (Fraction a)/2^fracwidth float_format))" 
    by (cases a) (auto simp: Sign_def float_defs Abs_float_inverse) 
  moreover have "valof (float_format) (topfloat float_format) =
        (-1)^0 * ((2^2046) / (2^bias float_format)) *(1 + (2^52 - 1)/2^fracwidth float_format)" 
    by (auto simp: emax_def topfloat_def) 
  ultimately have "valof (float_format) (Rep_float a) 
    \<le> valof (float_format) (topfloat float_format)" using R by auto
    then have "Val a \<le> Val Topfloat" 
      by (simp add: Abs_float_inverse Topfloat_def is_valid_special Val_def)
  thus ?thesis 
    using A finite_topfloat by (simp add: emax_def)
qed
     
lemma float_val_le_largest: 
  assumes "Finite a"
  shows "Val a \<le> largest float_format"
proof -
  have "Val Topfloat = valof float_format (topfloat float_format)" 
      by (simp add: Abs_float_inverse Topfloat_def is_valid_special Val_def)
  also have "... = largest float_format" by (simp add: emax_def largest_def topfloat_def)
  finally have "Val Topfloat = largest float_format" .
  thus ?thesis using float_le_topfloat by (metis assms finite_topfloat float_le)
qed

lemma float_val_lt_threshold:
  assumes "Finite a"
  shows "Val a < threshold float_format"
proof -
  have "Val a \<le> largest float_format" using float_val_le_largest assms by simp
  also have "... < threshold float_format" by (auto simp: largest_def threshold_def bias_def)
  finally show ?thesis .
qed

lemma float_val_ge_bottomfloat:  "Finite a \<Longrightarrow> Val a \<ge> Val Bottomfloat"
proof -
  assume A: "Finite a"
  then have B: "(Fraction a) \<le> 2^52 - 1" by (rule float_frac_le)
  have C: "(Exponent a) \<le> 2046" using A by (rule float_exp_le)
  then have "((Fraction a)/2^(fracwidth float_format)) \<le> 
    (( 2^52 - 1)/2^(fracwidth float_format))" using B  by auto 
  then have D: "(2 / (2^bias float_format)) * ((Fraction a)/2^(fracwidth float_format))
    \<le> (2 / (2^bias float_format)) * (( 2^52 - 1)/2^(fracwidth float_format))" 
    by (auto simp: bias_def) 
  have H: "0<(1 + (Fraction a)/2^fracwidth float_format) \<and>
    (1 + (Fraction a)/2^fracwidth float_format) \<le>
    (1 + (2^52 - 1)/2^fracwidth float_format)" 
    using D by (auto simp: bias_def)
  have J: "(2::real)^(Exponent a) \<le> 2^2046" using C by (metis exp_less)
  then have K: "0<((2::real)^(Exponent a)) / (2^bias float_format) \<and>
    ((2::real)^(Exponent a)) / (2^bias float_format) \<le> (2^2046) / (2^bias float_format)"
    using div_less by (metis zero_less_divide_iff zero_less_numeral zero_less_power)
  then have L: "0 < (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<and>
    (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<le> ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)"  
    by (metis H divide_zero_left pos_divide_less_eq mult_mono' less_eq_real_def)
  then have M: "1 * (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<ge> 
    (-1)^1 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by (auto simp: bias_def)
  have "(-1) * (((2::real)^(Exponent a)) / (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<ge> 
    (-1)^1 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using L by (auto simp: bias_def)
  then have N: "(-1)^(Sign a) * (((2::real)^(Exponent a)) / 
    (2^bias float_format)) *
    (1 + (Fraction a)/2^fracwidth float_format) \<ge>  (-1)^1 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " using M A float_sign_le by metis
  have P: "(-1) * (2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<ge> (-1)^1 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)"  using A B by (auto simp: bias_def)
  have Q: "1 * (2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<ge> (-1)^1 * ((2^2046) /
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using A B by (auto simp: bias_def)
  then have "(-1)^(Sign a) *(2 / (2^bias float_format)) * 
    ((Fraction a)/2^(fracwidth float_format)) \<ge> (-1)^1 * ((2^2046) / 
    (2^bias float_format)) * (1 + (2^52 - 1)/2^fracwidth float_format) " 
    using P Q float_sign_le by (metis A)
  then have R: "
    (if  (exponent(Rep_float a) = 0) 
    then (-1)^(Sign a) *(2 / (2^bias float_format)) * 
         ((Fraction a)/2^(fracwidth float_format)) 
    else (-1)^(Sign a) * (((2::real)^(Exponent a)) / 
         (2^bias float_format)) *
         (1 + (Fraction a)/2^fracwidth float_format)) \<ge> (-1)^1 * ((2^2046) / 
         (2^bias float_format)) *
         (1 + (2^52 - 1)/2^fracwidth float_format)" using N by auto
  have "valof (float_format) (Rep_float a) = 
    (if (exponent(Rep_float a) = 0) 
    then (-1)^(Sign a) *(2 / (2^bias float_format)) * 
         ((Fraction a)/2^(fracwidth float_format)) 
    else (-1)^(Sign a) * (((2::real)^(Exponent a)) / 
         (2^bias float_format)) * (1 + (Fraction a)/2^fracwidth float_format))" 
    by (cases a) (auto simp: float_defs Abs_float_inverse) 
  moreover have "valof (float_format) (bottomfloat float_format) =
      (-1)^1 * ((2^2046) / (2^bias float_format)) * (1 + (2^52 - 1)/2^fracwidth float_format)" 
    by (auto simp: emax_def bottomfloat_def)
  ultimately have "valof (float_format) (Rep_float a) \<ge> valof (float_format) (bottomfloat float_format)" 
    using R by auto
  then have "Val a \<ge> Val Bottomfloat" using Abs_float_inverse Bottomfloat_def is_valid_special
    by (metis Val_def mem_Collect_eq)
  thus ?thesis by auto
qed

lemma float_val_ge_largest: 
  assumes "Finite a"
  shows "Val a \<ge> -largest float_format"
proof -
  have "Val Bottomfloat = valof float_format (bottomfloat float_format)" 
    using Bottomfloat_def Abs_float_inverse is_valid_special
    by (metis (full_types) Val_def mem_Collect_eq)
  also have "... = -largest float_format" 
    by (auto simp: emax_def bias_def bottomfloat_def largest_def)
  finally have "Val Bottomfloat = -largest float_format" .
  thus ?thesis 
    using float_val_ge_bottomfloat by (metis assms)
qed

lemma float_val_gt_threshold:
  assumes "Finite a"
  shows "Val a > - threshold float_format"
proof -
  have largest: "Val a \<ge> -largest float_format" using float_val_ge_bottomfloat assms
    by (metis float_val_ge_largest)
  then have "-largest float_format > -(threshold float_format)"
    by (auto simp: bias_def threshold_def largest_def)
  then show ?thesis 
    by (metis largest less_le_trans)
qed


subsection{*Algebraic properties about basic arithmetic*}


(*Commutativity of addition*)
lemma float_plus_comm: 
  assumes "Finite a" "Finite b" "Finite (a + b)" shows "(a + b) \<doteq> (b + a)"
proof -
  have B: "\<not>(Isnan a)"  "\<not>(Isnan b)"
    using assms
      by (auto simp: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have D: "\<not>(Infinity a)" "\<not>(Infinity b)"
    using assms
    by (auto simp: finite_infinity emax_def is_infinity_def is_normal_def is_denormal_def
      is_zero_def)
  then have F: "(a + b) =  
    Abs_float (zerosign float_format (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then Sign a else 0)
                   (round float_format To_nearest ((Val a) + (Val b))))" 
    using B D 
    by (auto simp: float_defs fadd_def plus_float_def) 
  have G: "(b + a) = 
    Abs_float (zerosign float_format (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then Sign a else 0)
                  (round float_format To_nearest ((Val b) + (Val a))))" 
    using B D 
    by (auto simp: float_defs fadd_def plus_float_def Abs_float_inverse is_nan_def is_infinity_def)
  have "round float_format To_nearest ((Val b) + (Val a)) = round float_format To_nearest ((Val a) + (Val b))"
    by (simp add: add_commute)
  then have "(a + b) = (b + a)" using F G by arith
  then show ?thesis using assms 
    by (auto simp: fcompare_def emax_def float_defs is_nan_def is_normal_def is_denormal_def is_zero_def)
qed
  
(*Commutativity of multiplication*)
lemma float_mul_comm_eq:
  assumes "Finite a" "Finite b" shows "(a * b) = (b * a)"
proof -
  have B: "\<not>(Isnan a)"  
          "\<not>(Isnan b)"
    using assms
      by (auto simp: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have D: "\<not>(Infinity a)" 
          "\<not>(Infinity b)"
    using assms
    by (auto simp: finite_infinity emax_def is_infinity_def is_normal_def is_denormal_def
      is_zero_def)
  then have F: "(a * b) = 
                  Abs_float (zerosign float_format 
                             (of_bool (Sign a \<noteq> Sign b))
                             (round float_format To_nearest ((Val a) *  (Val b))))" 
               "(b * a) =
                   Abs_float (zerosign float_format 
                         (of_bool (Sign a \<noteq> Sign b))
                         (round float_format To_nearest ((Val b) * (Val a))))"
    using B D 
    by (auto simp: Sign_def fmul_def times_float_def Abs_float_inverse is_nan_def is_infinity_def Infinity_def Isnan_def Val_def) 
  have "round float_format To_nearest ((Val b) * (Val a)) =  
        round float_format To_nearest ((Val a) * (Val b))"
    by (metis mult_commute)
  then show ?thesis using F by arith
qed

lemma float_mul_comm: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite (a * b) \<Longrightarrow> (a * b) \<doteq> (b * a)"
by (metis float_distinct_finite float_eq_refl float_mul_comm_eq)

(*Showing --(-- a) = a*)
lemma sign_double_neg [simp]: assumes "is_valid x a" shows "(1 - (1 - sign a)) = sign a"
proof -
  have "sign a < 2" using assms 
    by (auto simp: is_valid_def)
  then show "(1 - (1 - sign a)) = sign a" by auto
qed
   
lemma float_double_neg_eq [simp]: 
  assumes "\<not>Isnan a" shows "float_neg (float_neg a) = a"
proof -
  have C: "float_neg a = Abs_float (1 - (Sign a), (Exponent a), (Fraction a))"
    by (simp add: float_defs float_neg_def fneg_def)
  then have D: "float_neg (float_neg a) = 
    Abs_float (fneg float_format To_nearest (Rep_float (Abs_float (1 - (Sign a), (Exponent a), (Fraction a)))))"
    by (simp add: float_neg_def)
  have E: "is_valid float_format ((1 - (Sign a), (Exponent a), (Fraction a)))"
    by (cases a)  (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have "Abs_float (fneg float_format To_nearest (Rep_float (Abs_float (
    1 - (Sign a), (Exponent a), (Fraction a))))) = 
    Abs_float (fneg float_format To_nearest (1 - (Sign a), (Exponent a), (Fraction a)))"
    by (simp add: Abs_float_inverse)
  then have "float_neg (float_neg a) = 
             Abs_float (fneg float_format To_nearest (1 - (Sign a), (Exponent a), (Fraction a)))" 
    using D by simp
  then have "float_neg (float_neg a) = 
    Abs_float (1 - (1 - (Sign a)), (Exponent a), (Fraction a))" 
    by (auto simp: fneg_def)
  also have "... = Abs_float ((Sign a), (Exponent a), (Fraction a))"
    by (metis Sign_def is_valid_defloat sign_double_neg)
  finally have "float_neg (float_neg a) = a"
    by (simp add: float_defs) (metis Rep_float_inverse exponent.elims fraction.simps sign.simps) 
  then show ?thesis using assms by auto
qed

lemma float_double_neg [simp]: "\<not>Isnan a \<Longrightarrow> float_neg (float_neg a) \<doteq> a"
  by auto

(* The floating-point number a falls into the same category as the negation of a *)
lemma neg_zero: "is_zero x a \<longleftrightarrow> is_zero x (fneg x m a)"
  by (auto simp: fneg_def is_zero_def)

lemma float_neg_zero: "Iszero a \<longleftrightarrow> Iszero (float_neg a)"
proof -
  have B: "Iszero (float_neg a) = 
           is_zero float_format 
             (Rep_float (Abs_float (fneg float_format To_nearest (Rep_float a))))"
    by (auto simp: Iszero_def float_neg_def)
  have "is_valid float_format ((1 - (Sign a), (Exponent a), (Fraction a)))"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have C: "(Iszero (Abs_float (fneg float_format To_nearest (Rep_float a)))) = 
                is_zero float_format (fneg float_format To_nearest (Rep_float a))" 
    by (auto simp: float_defs Abs_float_inverse fneg_def)
  then have "... = (Iszero a)" by (metis Iszero_def neg_zero)
  then show ?thesis
    by (metis C float_neg_def) 
qed
   
lemma neg_infinity: "is_infinity x a \<longleftrightarrow> is_infinity x (fneg x m a)"
  by (auto simp: fneg_def is_infinity_def)

lemma neg_normal: "is_normal x a \<longleftrightarrow> is_normal x (fneg x m a)"
  by (auto simp: fneg_def is_normal_def)

lemma float_neg_normal: "Isnormal a \<longleftrightarrow> Isnormal (float_neg a)"
proof -
  have "is_valid float_format ((1 - (Sign a), (Exponent a), (Fraction a)))"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have C: "is_normal float_format (Rep_float (Abs_float (fneg float_format To_nearest 
    (Rep_float a)))) = 
    is_normal float_format (fneg float_format To_nearest (Rep_float a))" 
     by (auto simp: Abs_float_inverse float_defs fneg_def)
  then have "... = is_normal float_format (Rep_float a)" by (metis neg_normal)
  then show ?thesis using C by (simp add: float_defs float_neg_def)
qed

lemma neg_denormal: "is_denormal x a \<longleftrightarrow> is_denormal x (fneg x m a)"
  by (auto simp: fneg_def is_denormal_def)

lemma float_neg_denormal: "Isdenormal a \<longleftrightarrow> Isdenormal (float_neg a)"
proof -
  have "is_valid float_format ((1 - (Sign a), (Exponent a), (Fraction a)))"
    by (cases a) (auto simp: float_defs Abs_float_inverse is_valid_def)
  then have "Isdenormal (Abs_float (fneg float_format To_nearest (Rep_float a))) = 
             is_denormal float_format (fneg float_format To_nearest (Rep_float a))" 
    by (auto simp: float_defs Abs_float_inverse fneg_def)
  also have "... = Isdenormal a" by (metis Isdenormal_def neg_denormal)
  finally show ?thesis 
    by (simp add: float_neg_def)
qed


lemma neg_valid: "is_valid x a \<Longrightarrow> is_valid x (fneg x m a)"
  by (auto simp: fneg_def is_valid_def)

lemma neg_finite: "is_finite x a \<Longrightarrow> is_finite x (fneg x m a) "
  by (metis is_finite_def neg_denormal neg_normal neg_valid neg_zero)

lemma float_neg_finite: "Finite a \<Longrightarrow> Finite (float_neg a)"
  by (metis Finite_def float_neg_denormal float_neg_normal float_neg_zero)

(* The sign of a and the sign of a's negation is different *)
lemma float_neg_sign: "(Sign a) \<noteq> (Sign (float_neg a))"
proof -
  have "(Sign a) = 0 \<or> (Sign a) = 1" 
    by (metis Sign_def is_valid_defloat sign_0_1)
  moreover have "(Sign a) = 0 \<Longrightarrow> (Sign (float_neg a)) = 1" 
    by (cases a) (auto simp: Sign_def fneg_def float_neg_def Abs_float_inverse is_valid_def)
  moreover have "(Sign a) = 1 \<Longrightarrow> (Sign (float_neg a)) = 0"
    by (cases a) (auto simp: Sign_def fneg_def float_neg_def Abs_float_inverse is_valid_def)
  ultimately show ?thesis  by (metis zero_neq_one)
qed

lemma float_neg_sign1: "((Sign a) = (Sign (float_neg b))) \<longleftrightarrow> ((Sign a) \<noteq> (Sign  b))"
by (metis Sign_def float_neg_sign is_valid_defloat sign_0_1)

lemma neg_val: 
  assumes "is_finite float_format a"
  shows "- valof float_format a = valof float_format (fneg float_format m a)" (is "?R = ?L")
proof -
  have A: "?L = valof float_format (sign (fneg float_format m a), 
    exponent (fneg float_format m a), fraction (fneg float_format m a))"
    by (metis exponent.simps fneg_def fraction.simps sign.simps)
  then have B: "... = valof float_format (1 - sign a, exponent a, fraction a)"
    by (metis fneg_def)
  have C: "sign a = 0 \<longleftrightarrow> 1 - (sign a) = 1" by auto
  have D: "sign a = 1 \<longleftrightarrow> 1 - (sign a) = 0" using sign_0_1 assms 
    by (auto simp: is_valid_def is_finite_def)
  then have "valof float_format (0, exponent a, fraction a) = 
    -valof float_format (1, exponent a, fraction a)"
    by auto
  then show "?thesis" using A B C D
    by (metis (no_types) assms exponent.simps 
        fneg_def fraction.simps is_finite_def minus_minus prod.exhaust sign.simps sign_0_1)
qed

lemma float_neg_val: 
  assumes "Finite b"
    shows "(Val (float_neg b)) = - (Val b)"
proof -
  have "Val (float_neg b) = 
    valof float_format ((Sign (float_neg b)),(Exponent (float_neg b)), (Fraction (float_neg b)))"
    unfolding float_defs
    by (metis PairE exponent.simps fraction.simps sign.simps)
  have B: "... = valof float_format ((1 - (Sign b), (Exponent b), (Fraction b)))"
    using float_neg_def fneg_def Abs_float_inverse 
    by (cases b) (auto simp: float_defs is_valid_def) 
  have C: "(Val b) = valof float_format (((Sign b), (Exponent b), (Fraction b)))" 
    unfolding float_defs
    by (metis exponent.simps fraction.simps prod.exhaust sign.simps)
  have D: "(Sign b) = 0 \<longleftrightarrow> 1 - (Sign b) = 1" by arith
  have E: "(Sign b) = 1 \<longleftrightarrow> 1 - (Sign b) = 0" 
    using is_valid_defloat sign_0_1 by (metis Sign_def D diff_self_eq_0) 
  then have "valof float_format (0, (Exponent b), (Fraction b)) = 
    - valof float_format (1, (Exponent b),
    (Fraction b)) " by auto
  thus ?thesis using assms B C D  
    unfolding float_defs
    by (metis  comm_monoid_diff_class.diff_cancel exponent.simps 
          fraction.simps is_valid_defloat minus_minus prod.exhaust sign.simps sign_0_1) 
qed

(* Showing  a + (-b) = a - b *)
lemma float_neg_add:
   "Finite a \<Longrightarrow> Finite b \<Longrightarrow> Finite (a - b) \<Longrightarrow> 
        (Val a) + 
                    (Val (float_neg b)) =
        (Val a) - (Val b)"
by (metis comm_ring_1_class.normalizing_ring_rules(2) float_neg_val)

lemma float_plus_minus:
  assumes "Finite a" "Finite b" "Finite (a - b)" shows "(a + float_neg b) \<doteq> (a - b)"
proof -
  have B: "\<not>(Isnan a)" using assms
    by (metis finite_nan)
  have C: "\<not>(Isnan (float_neg b))" using assms 
    by (metis finite_nan float_neg_finite)
  have D: "\<not>(Infinity a)" using assms
    by (metis finite_infinity)
  have E: "\<not>(Infinity (float_neg  b))" using assms 
    by (metis finite_infinity float_neg_finite) 
  then have F: "(a + float_neg b) =  
       Abs_float (zerosign float_format 
          (if Iszero a \<and> Iszero (float_neg b) \<and> Sign a = Sign (float_neg b) 
           then Sign a else 0)
        (round float_format To_nearest ((Val a) + (Val (float_neg b)))))" 
    using B C D E 
    by (auto simp: float_defs fadd_def plus_float_def) 
  then have G: "... = Abs_float (zerosign float_format 
    (if (Iszero a) \<and> 
        (Iszero  b) \<and>
        ((Sign a) \<noteq> (Sign b)) 
     then (Sign a) else 0)
        (round float_format To_nearest ((Val a) + 
         (Val (float_neg b)))))"
     using float_neg_sign1 float_neg_zero
     by auto
  then have H: "... = Abs_float (zerosign float_format 
    (if (Iszero a) \<and> (Iszero b) \<and> ((Sign a) \<noteq> (Sign b)) 
     then (Sign a) else 0)
        (round float_format To_nearest ((Val a) - 
        (Val b))))" 
    using assms float_neg_add by metis
  have "(a - b) = 
        Abs_float (zerosign float_format 
            (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b
             then (Sign a) else of_bool (To_nearest = To_ninfinity))
           (round float_format To_nearest (Val a - Val b)))" 
        using assms finite_infinity finite_nan
        by (simp only: of_bool_def fsub_def minus_float_def float_defs [symmetric] simp_thms if_False)
  then have "(a - b) = Abs_float (zerosign float_format 
    (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b
     then (Sign a) else 0)
          (round float_format To_nearest ((Val a) - (Val b))))"  
    by auto
  thus ?thesis using assms F H by (metis G float_eq)
qed

(* Showing abs (-a) = abs (a) *)
lemma float_abs: "\<not>Isnan a \<Longrightarrow> float_abs (float_neg a) = float_abs a"
  by (cases a) (auto simp: float_abs_def float_neg_def fneg_def Abs_float_inverse is_valid_def)

lemma neg_zerosign: "fneg x m (zerosign x s a) = zerosign x (1-s) (fneg x m a)"
  by (auto simp: fneg_def zerosign_def is_zero_def is_valid_def)

lemma finite_valid: "is_finite x a \<Longrightarrow> is_valid x a"
  by (cases a) (metis is_finite_def)

end
