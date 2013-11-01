(*==========================================================================*)
(* Proofs of Properties about Floating Point Arithmetic.                    *) 
(*==========================================================================*) 

(* Author: Lei Yu, University of Cambridge *)

theory FloatProperty imports IEEE begin

section{* Proofs of Properties about Floating Point Arithmetic *}

subsection{*Theorems derived from definitions*}                                                           


lemma sign: "\<forall>a. sign a = fst a"
by auto

lemma exponent: "\<forall> a. exponent a = fst (snd a)"
by auto

lemma fraction: "\<forall> a. fraction a = snd (snd a)"
by auto

lemma is_valid: "\<forall> x a. is_valid x a = ((sign a < (2::nat)) \<and> (exponent a < 2^(expwidth x))
                        \<and> (fraction a < 2^(fracwidth x)))"
by (auto simp add: is_valid_def emax_def)


lemma is_valid_defloat: " is_valid float_format (Rep_float a)"
apply (cases a)
apply (simp  add: Abs_float_inverse)
done


lemma float_cases: "Isnan a \<or> Infinity a \<or> Isnormal a \<or> Isdenormal a \<or> Iszero a"
apply (cases a)
apply (auto simp add: Abs_float_inverse emax_def is_nan_def 
      is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)
done

lemma float_cases_finite: "Isnan a \<or> Infinity a \<or> Finite a"
apply (cases a)
apply (auto simp add: Abs_float_inverse emax_def is_nan_def 
      is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)
done

lemma float_zero1: "Iszero Plus_zero"
apply (auto simp add: Abs_float_inverse is_zero_def is_valid_def)
done

lemma float_zero2: "Iszero Minus_zero"
apply (auto simp add: Abs_float_inverse Minus_zero_def is_zero_def is_valid_def)
done

lemma is_valid_special: "\<forall> x. is_valid x (minus_infinity x) \<and>
                              is_valid x (plus_infinity x) \<and>
                              is_valid x (topfloat x) \<and>
                              is_valid x (bottomfloat x) \<and>
                              is_valid x (plus_zero x) \<and>
                              is_valid x (minus_zero x)"
apply (auto simp add: emax_def is_valid_def)
done

lemma sign_0_1: "is_valid x a \<Longrightarrow> (sign a = 0) \<or> (sign a = 1)"
apply (auto simp add: is_valid_def)
done

(*The types of floating-point numbers are mutually distinct*)
lemma float_distinct: "\<not>(Isnan a \<and> Infinity a) \<and>
                       \<not>(Isnan a \<and> Isnormal a) \<and>
                       \<not>(Isnan a \<and> Isdenormal a) \<and>
                       \<not>(Isnan a \<and> Iszero a) \<and>
                       \<not>(Infinity a \<and> Isnormal a) \<and>
                       \<not>(Infinity a \<and> Isdenormal a) \<and>
                       \<not>(Infinity a \<and> Iszero a) \<and>
                       \<not>(Isnormal a \<and> Isdenormal a) \<and>
                       \<not>(Isdenormal a \<and> Iszero a)"
by (auto simp add: emax_def is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)

lemma float_distinct_finite: "\<not>(Isnan a \<and> Infinity a) \<and>
                              \<not>(Isnan a \<and> Finite a) \<and>
                              \<not>(Infinity a \<and> Finite a)"
apply (auto simp add: emax_def is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)
done

lemma finite_infinity: "Finite a \<Longrightarrow> \<not> is_infinity float_format (Rep_float a)"
apply (auto simp add: emax_def is_infinity_def is_normal_def is_denormal_def is_zero_def)
done

lemma finite_nan: "Finite a \<Longrightarrow> \<not> is_nan float_format (Rep_float a)"
apply (auto simp add: emax_def is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)
done

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
      then have "is_closest v (insert z s) x z" by (auto simp add: is_closest_def)
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
apply (unfold closest_def)
apply (rule someI_ex)
apply (insert is_closest_exists [of s v x]) using assms
apply auto
by metis

lemma closest_in_set:
  fixes v::"representation \<Rightarrow> real" and s::"representation set" and x::real and a::representation
  assumes finite: "finite s"
  assumes non_empty: "\<not>(s = {})"
  shows "(closest v p s x) \<in> s"
proof -
  show ?thesis using assms closest_is_everything is_closest_def
    by (metis (hide_lams, no_types))
qed

lemma closest_is_closest: 
  fixes v::"representation \<Rightarrow> real" and s::"representation set" and x::real and a::representation
  assumes finite: "finite s"
  assumes non_empty: "\<not>(s = {})"
  shows "is_closest v s x (closest v p s x)"
by (metis closest_is_everything finite non_empty)

lemma float_first_cross: 
  "{a::representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p} =
   image (\<lambda> ((x::nat), (y, z)). (x, y, z)) ({x. x < m} \<times> {y. y < n} \<times> {z. z < p})"
apply auto
done

lemma finite_r3: "finite {a :: representation. fst a < m \<and> fst (snd a) < n \<and> snd (snd a) < p}"
apply (auto simp add: float_first_cross)
done

lemma is_valid_finite: "finite {a. is_valid x a}"
apply (auto simp add: finite_r3 sign exponent fraction is_valid_def)
done

lemma is_finite_subset: "{a :: representation. is_finite x a} \<subseteq> {a. is_valid x a} "
apply (auto simp add: is_finite_def)
done

lemma match_float_finite:
  fixes a x
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
  have "(0::nat, 0, 0) \<in> {a. is_valid x a}" by (auto simp add: is_valid_def)
  thus ?thesis by (metis empty_iff)
qed

lemma is_finite_nonempty: "\<not>({a::representation. is_finite x a} = {})"
proof -
  have "(0::nat, 0, 0) \<in> {a. is_finite x a}" by (auto simp add: is_zero_def 
    is_valid_def is_finite_def)
  thus ?thesis by (metis empty_iff)
qed

lemma is_finite_closest: 
  fixes v::"representation \<Rightarrow> real" and s::"representation set" and x::real
  shows "is_finite f (closest v p {a. is_finite f a} x)"
proof -
  have "closest v p {a. is_finite f a} x \<in> {a. is_finite f a}" using closest_in_set 
    by (metis is_finite_finite is_finite_nonempty)
  then show ?thesis by auto
qed

lemma is_valid_closest: 
  fixes f and  v::"representation \<Rightarrow> real" and p::"representation \<Rightarrow> bool" and x::real
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
proof -
  show ?thesis using Abs_float_inverse is_valid_round 
    by (metis mem_Collect_eq) 
qed

lemma zerosign_valid: 
  fixes s::nat and x
  assumes  sign:"s = 0 \<or> s = 1"
  assumes  valid: "is_valid x a"
  shows "is_valid x (zerosign x s a)"
proof -
  have "exponent a < 2^expwidth x \<and> fraction a < 2^fracwidth x" using valid 
    by (auto simp add: is_valid_def)
  moreover have "s < 2" using sign by auto
  ultimately have "is_valid x (s, exponent a, fraction a)" by (auto simp add: is_valid_def)
  thus ?thesis using assms by (metis (full_types) is_valid_special zerosign_def)
qed

lemma defloat_float_zerosign_round: 
  fixes b::nat and x
  assumes "b = 0 \<or> b = 1"
  shows "Rep_float(Abs_float (zerosign float_format b (round float_format To_nearest x))) =
         zerosign float_format b (round float_format To_nearest x)"
by (metis assms is_valid_round mem_Collect_eq 
    zerosign_valid Abs_float_inverse)


subsection{*Properties about ordering and bounding*}


(*Lifting of non-exceptional comparisons*)
lemma float_lt [simp]: 
  fixes a b
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a < b \<longleftrightarrow> Val a < Val b)"
proof 
  assume "Val a  <  Val b"
  have "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  moreover have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  moreover have "\<not> Infinity b" using A2 float_distinct_finite by auto
  ultimately have "fcompare float_format (Rep_float a) (Rep_float b) = Lt"  
    using  `Val a < Val b` fcompare_def by auto
  then show "a < b" by (auto simp add: less_float_def) 
next
  assume "a < b"
  then have lt: "fcompare float_format (Rep_float a) (Rep_float b) = Lt"
    by (simp add: less_float_def)
  have nonNan: "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  then have  nonInfinity_a: "\<not> is_infinity float_format (Rep_float a)" by auto
  have "\<not> Infinity b" using A2 float_distinct_finite by auto
  then have nonInfinity_b: "\<not> is_infinity float_format (Rep_float b)" by auto

  have "(is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    \<not>(is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1)) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) = Lt" using nonNan nonInfinity_a by auto
  moreover have "is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) = Lt" using nonNan nonInfinity_a 
    nonInfinity_b by auto
  moreover have "valof float_format (Rep_float a) < valof float_format (Rep_float b) \<Longrightarrow>
    fcompare float_format (Rep_float a) (Rep_float b) = Lt" 
    using nonNan nonInfinity_a nonInfinity_b 
    fcompare_def by auto
  moreover have "\<not>((is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    \<not>(is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1))) \<and>
   \<not>(is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0)) \<and>
   \<not>(valof float_format (Rep_float a) < valof float_format (Rep_float b)) \<Longrightarrow>
   fcompare float_format (Rep_float a) (Rep_float b) \<noteq> Lt" 
    using fcompare_def nonNan nonInfinity_a by auto
  ultimately have "((is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    \<not>(is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1))) \<or>
   (is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0)) \<or>
   (valof float_format (Rep_float a) < valof float_format (Rep_float b))" using lt by force
  then have "valof float_format (Rep_float a) < valof float_format (Rep_float b)" 
    using fcompare_def lt nonInfinity_a nonInfinity_b nonNan assms Isnan_def 
    by auto
  then show "Val a < Val b" by simp 
qed  
       
lemma float_gt [simp]:
  fixes a b
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "a > b \<longleftrightarrow> Val a > Val b"
proof -
  show ?thesis using A1 A2  by auto
qed


lemma float_eq [simp]:
  fixes a b
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a \<doteq> b) \<longleftrightarrow> (Val a = Val b)"
proof 
  assume "Val a = Val b"
  have "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  moreover have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  moreover have "\<not> Infinity b" using A2 float_distinct_finite by auto
  ultimately have "fcompare float_format (Rep_float a) (Rep_float b) = Eq" 
    using fcompare_def `Val a = Val b` by auto
  then show "a \<doteq> b" by (auto simp add: float_eq_def)
next
  assume "a \<doteq> b"
  then have eq: "fcompare float_format (Rep_float a) (Rep_float b) = Eq" by (simp add: float_eq_def)
   have nonNan: "\<not> (Isnan a \<or> Isnan b)" using assms by (metis float_distinct_finite)
  have "\<not> Infinity a" using A1 by (metis float_distinct_finite)
  then have  nonInfinity_a: "\<not> is_infinity float_format (Rep_float a)" by auto
  have "\<not> Infinity b" using A2 float_distinct_finite by auto
  then have nonInfinity_b: "\<not> is_infinity float_format (Rep_float b)" by auto

  have "(is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    (is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1)) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" using nonNan nonInfinity_a by auto
  moreover have "(is_infinity float_format (Rep_float a) \<and> 
    (sign (Rep_float a) = 0)) \<and> is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0)
    \<Longrightarrow> fcompare float_format (Rep_float a) (Rep_float b) = Eq"
    using nonNan nonInfinity_a by auto
  moreover have "valof float_format (Rep_float a) = valof float_format (Rep_float b) \<Longrightarrow>
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" 
    using nonNan nonInfinity_a nonInfinity_b 
    fcompare_def by auto
  moreover have "\<not>((is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    (is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1))) \<and> 
    \<not>((is_infinity float_format (Rep_float a) \<and> 
    (sign (Rep_float a) = 0)) \<and> is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0))
    \<and> \<not>(valof float_format (Rep_float a) = valof float_format (Rep_float b)) \<Longrightarrow> 
    fcompare float_format (Rep_float a) (Rep_float b) \<noteq> Eq"  
    using fcompare_def nonNan nonInfinity_a by auto
  ultimately have "(is_infinity float_format (Rep_float a) \<and> (sign (Rep_float a) = 1)) \<and>
    (is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 1)) 
    \<or>
    (is_infinity float_format (Rep_float a) \<and> 
    (sign (Rep_float a) = 0)) \<and> is_infinity float_format (Rep_float b) \<and> (sign (Rep_float b) = 0)
    \<or> 
    valof float_format (Rep_float a) = valof float_format (Rep_float b)" using eq by force  
  then have "valof float_format (Rep_float a) = valof float_format (Rep_float b)" using A1 A2
    using fcompare_def eq nonInfinity_a nonInfinity_b nonNan assms Isnan_def 
    by auto
  then show "Val a = Val b" by simp
qed 

lemma float_le [simp]:
  fixes a b
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a \<le> b) \<longleftrightarrow> (Val a \<le> Val b)"
proof -
  have "(a \<le> b) \<equiv> fcompare float_format (Rep_float a) (Rep_float b) = Lt \<or>
    fcompare float_format (Rep_float a) (Rep_float b) = Eq" using less_eq_float_def by auto
  then  have "(a \<le> b) \<equiv> flt float_format (Rep_float a) (Rep_float b) \<or> 
    feq float_format (Rep_float a) (Rep_float b)" by auto
  then have "(a \<le> b) \<equiv> a < b \<or> a \<doteq> b" using less_float_def float_eq_def by auto
  then show ?thesis using assms by auto
qed

lemma float_ge [simp]:
  fixes a b
  assumes A1: "Finite a"
  assumes A2: "Finite b"
  shows "(a \<ge> b) \<longleftrightarrow> (Val a \<ge> Val b)"
proof -
  show ?thesis using A1 A2  by auto
qed

(*Reflexivity of equality for non-NaNs*)
lemma float_eq_refl [simp]: "(a \<doteq> a) \<longleftrightarrow> \<not>(Isnan a)"
apply (auto simp add: fcompare_def float_eq_def)
done

(*Properties about Ordering*)
lemma float_lt_trans [simp]: "Finite a \<and> Finite b \<and> Finite c \<Longrightarrow> a < b \<and> b < c \<longrightarrow> a < c"
apply (auto simp add: le_trans)
done

lemma float_le_trans [simp]: "Finite a \<and> Finite b \<and> Finite c \<Longrightarrow> a \<le> b \<and> b < c \<longrightarrow> a < c"
apply (auto simp add: le_trans)
done

lemma float_le_neg [simp]: "Finite a \<and> Finite b \<Longrightarrow> \<not>(a < b) \<longleftrightarrow> b \<le> a"
apply (auto)
done

(*Properties about bounding*)
lemma float_le_infinity [simp]: "\<not> Isnan a \<Longrightarrow> a \<le> Plus_infinity"
proof -
  assume "\<not> Isnan a"
  then have "(fcompare float_format  (Rep_float a) (plus_infinity float_format) = Eq) \<or>
             (fcompare float_format  (Rep_float a) (plus_infinity float_format) = Lt) " 
    by (auto simp add: fcompare_def is_nan_def is_infinity_def)
  then show ?thesis by (auto simp add: Plus_infinity_def less_eq_float_def
    Abs_float_inverse emax_def is_valid_def)
qed

lemma [simp]: "Plus_zero \<le> Abs_float (topfloat float_format)"
apply (auto simp add: fcompare_def is_nan_def less_eq_float_def 
  Abs_float_inverse emax_def is_infinity_def is_zero_def is_valid_def)
done

lemma "valof float_format (topfloat float_format) = largest float_format"
apply (auto simp add: emax_def is_nan_def)
done

lemma float_frac_le: "Finite a \<Longrightarrow> fraction (Rep_float a) \<le> 2^52 - 1"
apply (cases a)
apply (auto simp add: Abs_float_inverse is_valid_def)
done

lemma float_exp_le: "Finite a \<Longrightarrow> exponent (Rep_float a) \<le> 2046"
apply (cases a)
apply (auto simp add: emax_def is_normal_def is_denormal_def is_zero_def)
done

lemma float_sign_le: "Finite a \<Longrightarrow> (-1::real)^sign (Rep_float a) = 1
                       \<or> (-1::real)^sign (Rep_float a) = -1"
proof -
  assume "Finite a"
  then have "sign (Rep_float a) = 0 \<or> sign (Rep_float a) = 1" 
    by (metis is_valid_defloat sign_0_1)
  thus ?thesis by auto
qed

lemma "(2::real)^((a::nat) + b) = (2^a) * (2^b)"
apply (induction a)
apply auto
done

lemma exp_less: "(a::nat) \<le> b \<Longrightarrow> (2::real)^a \<le> 2^b"
apply auto
done

lemma div_less: "(a::real) \<le> b \<and> c > 0 \<Longrightarrow> a/c \<le> b/c"
apply (auto)
by (metis divide_le_cancel not_less_iff_gr_or_eq)

lemma mul_less: "0 < (a::real) \<and> a \<le> b \<and> 0 < c \<and> c \<le> d \<Longrightarrow> a * c \<le> b * d"
apply (auto)
by (metis less_eq_real_def mult_mono')

lemma finite_topfloat: "Finite Topfloat"
apply (auto simp add: Topfloat_def Abs_float_inverse emax_def is_normal_def is_valid_def)
done

lemma float_le_topfloat: "Finite a \<Longrightarrow>  a \<le> Topfloat"
proof -
  assume A: "Finite a"
  then have B: "fraction (Rep_float a) \<le> 2^52 - 1" by (rule float_frac_le)
  have C: "exponent (Rep_float a) \<le> 2046" using A by (rule float_exp_le)
  then have "(fraction (Rep_float a)/2^(fracwidth float_format)) 
    \<le> (( 2^52 - 1)/2^(fracwidth float_format))" 
 
    using B  by auto 
  then have D: "(2 / (2^bias float_format)) *
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<le>  
    (2 / (2^bias float_format)) * (( 2^52 - 1)/2^(fracwidth float_format))" 
    by (auto simp add: bias_def)  
  have H: "0<(1 + fraction (Rep_float a)/2^fracwidth float_format) \<and>
    (1 + fraction (Rep_float a)/2^fracwidth float_format)
    \<le> (1 + (2^52 - 1)/2^fracwidth float_format)"  using D by (auto simp add: bias_def) 
  have J: "(2::real)^exponent (Rep_float a) \<le> 2^2046" using C by (metis exp_less)
  then have K: "0<((2::real)^exponent (Rep_float a)) / (2^bias float_format)\<and>
    ((2::real)^exponent (Rep_float a)) / (2^bias float_format) \<le> (2^2046) / (2^bias float_format)"
    using div_less by (metis zero_less_divide_iff zero_less_numeral zero_less_power)  
  then have L: "0 < (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<and>
    (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le>
    ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using H mul_less 
    by (metis divide_zero_left pos_divide_less_eq)
  then have M: "1 * (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le> 
    (-1::real)^0 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by auto
  have "(-1) * (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le> 
    (-1::real)^0 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using L by auto
  then have N: "(-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a)) /
    (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le>  (-1::real)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " using M A float_sign_le by metis
  have P: "(-1) * (2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<le> (-1::real)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)"  using A B by (auto simp add: bias_def)
  have Q: "1 * (2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<le> (-1::real)^0 * ((2^2046) /
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using A B by (auto simp add: bias_def)
  then have "(-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<le> (-1::real)^0 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " 
    using P Q float_sign_le by (metis A)
  then have R: "
    (if (exponent(Rep_float a) = 0) 
    then (-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
         (fraction (Rep_float a)/2^(fracwidth float_format)) 
    else (-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a))/
         (2^bias float_format)) *
         (1 + fraction (Rep_float a)/2^fracwidth float_format)) \<le> 
         (-1::real)^0 * ((2^2046) / (2^bias float_format)) *
         (1 + (2^52 - 1)/2^fracwidth float_format)" using N by auto
  have "valof (float_format) (Rep_float a) =  
    (if (exponent(Rep_float a) = 0) 
    then (-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
         (fraction (Rep_float a)/2^(fracwidth float_format)) 
    else (-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a)) / 
         (2^bias float_format)) * (1 + fraction (Rep_float a)/2^fracwidth float_format))" 
    by (cases a) (auto simp add: Abs_float_inverse) 
  moreover have "valof (float_format) (topfloat float_format) =
    (-1::real)^0 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by (auto simp add: emax_def) 
  ultimately have "valof (float_format) (Rep_float a) 
    \<le> valof (float_format) (topfloat float_format)" using R by auto
    then have "Val a \<le> Val Topfloat" using Abs_float_inverse Abs_float_inverse Topfloat_def 
    by (metis Val_def is_valid_special mem_Collect_eq)
  thus ?thesis using A finite_topfloat by (auto simp add: emax_def)
qed
     
lemma float_val_le_largest: 
  fixes a
  assumes "Finite a"
  shows "Val a \<le> largest float_format"
proof -
  have "Val Topfloat = valof float_format (topfloat float_format)" 
    using Topfloat_def Abs_float_inverse
    by (metis (full_types) Val_def is_valid_special mem_Collect_eq)
  also have "... = largest float_format" by (auto simp add: emax_def)
  finally have "Val Topfloat = largest float_format" .
  thus ?thesis using float_le_topfloat by (metis assms finite_topfloat float_le)
qed

lemma float_val_lt_threshold:
  fixes a
  assumes "Finite a"
  shows "Val a < threshold float_format"
proof -
  have "Val a \<le> largest float_format" using float_val_le_largest assms by simp
  moreover have "... < threshold float_format" by (auto simp add: bias_def)
  finally show ?thesis .
qed

lemma float_val_ge_bottomfloat:  "Finite a \<Longrightarrow> Val a \<ge> Val Bottomfloat"
proof -
  assume A: "Finite a"
  then have B: "fraction (Rep_float a) \<le> 2^52 - 1" by (rule float_frac_le)
  have C: "exponent (Rep_float a) \<le> 2046" using A by (rule float_exp_le)
  then have "(fraction (Rep_float a)/2^(fracwidth float_format)) \<le> 
    (( 2^52 - 1)/2^(fracwidth float_format))" using B  by auto 
  then have D: "(2 / (2^bias float_format)) * (fraction (Rep_float a)/2^(fracwidth float_format))
    \<le> (2 / (2^bias float_format)) * (( 2^52 - 1)/2^(fracwidth float_format))" 
    by (auto simp add: bias_def) 
  have H: "0<(1 + fraction (Rep_float a)/2^fracwidth float_format) \<and>
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le>
    (1 + (2^52 - 1)/2^fracwidth float_format)" 
    using D by (auto simp add: bias_def)
  have J: "(2::real)^exponent (Rep_float a) \<le> 2^2046" using C by (metis exp_less)
  then have K: "0<((2::real)^exponent (Rep_float a)) / (2^bias float_format) \<and>
    ((2::real)^exponent (Rep_float a)) / (2^bias float_format) \<le> (2^2046) / (2^bias float_format)"
    using div_less by (metis zero_less_divide_iff zero_less_numeral zero_less_power)
  then have L: "0 < (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<and>
    (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<le> ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using H mul_less 
    by (metis divide_zero_left pos_divide_less_eq)
  then have M: "1 * (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<ge> 
    (-1::real)^1 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by (auto simp add: bias_def)
  have "(-1) * (((2::real)^exponent (Rep_float a)) / (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<ge> 
    (-1::real)^1 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using L by (auto simp add: bias_def)
  then have N: "(-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a)) / 
    (2^bias float_format)) *
    (1 + fraction (Rep_float a)/2^fracwidth float_format) \<ge>  (-1::real)^1 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " using M A float_sign_le by metis
  have P: "(-1) * (2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<ge> (-1::real)^1 * ((2^2046) / 
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)"  using A B by (auto simp add: bias_def)
  have Q: "1 * (2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<ge> (-1::real)^1 * ((2^2046) /
    (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format)" using A B by (auto simp add: bias_def)
  then have "(-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
    (fraction (Rep_float a)/2^(fracwidth float_format)) \<ge> (-1::real)^1 * ((2^2046) / 
    (2^bias float_format)) * (1 + (2^52 - 1)/2^fracwidth float_format) " 
    using P Q float_sign_le by (metis A)
  then have R: "
    (if  (exponent(Rep_float a) = 0) 
    then (-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
         (fraction (Rep_float a)/2^(fracwidth float_format)) 
    else (-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a)) / 
         (2^bias float_format)) *
         (1 + fraction (Rep_float a)/2^fracwidth float_format)) \<ge> (-1::real)^1 * ((2^2046) / 
         (2^bias float_format)) *
         (1 + (2^52 - 1)/2^fracwidth float_format)" using N by auto
  have "valof (float_format) (Rep_float a) = 
    (if (exponent(Rep_float a) = 0) 
    then (-1::real)^sign (Rep_float a) *(2 / (2^bias float_format)) * 
         (fraction (Rep_float a)/2^(fracwidth float_format)) 
    else (-1::real)^sign (Rep_float a) * (((2::real)^exponent (Rep_float a)) / 
         (2^bias float_format)) * (1 + fraction (Rep_float a)/2^fracwidth float_format))" 
    by (cases a) (auto simp add: Abs_float_inverse) 
  moreover have "valof (float_format) (bottomfloat float_format) =
    (-1::real)^1 * ((2^2046) / (2^bias float_format)) *
    (1 + (2^52 - 1)/2^fracwidth float_format) " by (auto simp add: emax_def)
  ultimately have "valof (float_format) (Rep_float a) \<ge> 
    valof (float_format) (bottomfloat float_format)" 
    using R by auto
  then have "Val a \<ge> Val Bottomfloat" using Abs_float_inverse Abs_float_inverse Bottomfloat_def 
    by (metis Val_def is_valid_special mem_Collect_eq)
  thus ?thesis by auto
qed

lemma float_val_ge_largest: 
  fixes a
  assumes "Finite a"
  shows "Val a \<ge> -largest float_format"
proof -
  have "Val Bottomfloat = valof float_format (bottomfloat float_format)" 
    using Bottomfloat_def Abs_float_inverse
    by (metis (full_types) Val_def is_valid_special mem_Collect_eq)
  also have "... = -largest float_format" by (auto simp add: emax_def bias_def)
  finally have "Val Bottomfloat = -largest float_format" .
  thus ?thesis using float_val_ge_bottomfloat by (metis assms)
qed

lemma float_val_gt_threshold:
  fixes a
  assumes "Finite a"
  shows "Val a > - threshold float_format"
proof -
  have largest: "Val a \<ge> -largest float_format" using float_val_ge_bottomfloat assms
    by (metis float_val_ge_largest)
  then have "-largest float_format > -(threshold float_format)" by (auto simp add: bias_def)
  then show ?thesis by (metis largest less_le_trans)
qed


subsection{*Algebraic properties about basic arithmetic*}


(*Commutativity of addition*)
lemma float_plus_comm: "Finite a \<and> Finite b \<and> Finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
proof -
  assume A: "Finite a \<and> Finite b \<and> Finite (a + b)"
  then have B: "\<not>is_nan float_format (Rep_float a)" 
    by (auto simp add: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have C: "\<not>is_nan float_format (Rep_float b)" using A 
    by (auto simp add: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have D: "\<not>is_infinity float_format (Rep_float a)" using A 
    by (auto simp add: finite_infinity emax_def is_infinity_def is_normal_def is_denormal_def
      is_zero_def)
  have E: "\<not>is_infinity float_format (Rep_float b)" using A 
    by (auto simp add: finite_infinity emax_def is_infinity_def is_normal_def is_denormal_def
      is_zero_def)
  then have F: "(a + b) =  Abs_float (zerosign float_format (if is_zero float_format (Rep_float a)
    \<and> is_zero float_format (Rep_float b) \<and>
    (sign (Rep_float a) = sign (Rep_float b)) then sign (Rep_float a) else 0)
    (round float_format To_nearest (valof float_format (Rep_float a) + 
    valof float_format (Rep_float b))))" using B C D E 
    by (auto simp add: fadd_def plus_float_def)
  have G: "(b + a) =  Abs_float (zerosign float_format (if is_zero float_format (Rep_float a) \<and>
    is_zero float_format (Rep_float b) \<and>
    (sign (Rep_float a) = sign (Rep_float b)) then sign (Rep_float a) else 0)
    (round float_format To_nearest (valof float_format (Rep_float b) + 
    valof float_format (Rep_float a))))" using B C D E 
    by (auto simp add: fadd_def plus_float_def Abs_float_inverse is_nan_def is_infinity_def)
  have "valof float_format (Rep_float b) + valof float_format (Rep_float a) = 
    valof float_format (Rep_float a) + valof float_format (Rep_float b)" 
    by (simp add: add_commute)
  then have "round float_format To_nearest (valof float_format (Rep_float b) +
    valof float_format (Rep_float a)) = 
    round float_format To_nearest (valof float_format (Rep_float a) + 
    valof float_format (Rep_float b)) "
    by arith
  then have "(a + b) = (b + a)" using F G by arith
  then show ?thesis using A by (auto simp add: fcompare_def emax_def 
    is_nan_def is_normal_def is_denormal_def is_zero_def)
qed
  
(*Commutativity of multiplication*)
lemma float_mul_comm_eq: "Finite a \<and> Finite b \<and> Finite (a * b) \<Longrightarrow> (a * b) = (b * a)"
proof -
  assume A: "Finite a \<and> Finite b \<and> Finite (a * b)"
  then have B: "\<not>is_nan float_format (Rep_float a)" 
    by (auto simp add: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have C: "\<not>is_nan float_format (Rep_float b)" using A 
    by (auto simp add: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have D: "\<not>is_infinity float_format (Rep_float a)" using A
    by (auto simp add: finite_infinity emax_def is_infinity_def is_normal_def 
      is_denormal_def is_zero_def)
  have E: "\<not>is_infinity float_format (Rep_float b)" using A
    by (auto simp add: finite_infinity emax_def is_infinity_def is_normal_def 
      is_denormal_def is_zero_def)
  then have F: "(a * b) =  Abs_float (zerosign float_format 
    (if sign (Rep_float a) = sign (Rep_float b) then 0 else 1)
    (round float_format To_nearest (valof float_format (Rep_float a) * 
    valof float_format (Rep_float b))))" using B C D E 
    by (auto simp add: fmul_def times_float_def Abs_float_inverse is_nan_def is_infinity_def) 
  then have G: "(b * a) =  Abs_float (zerosign float_format 
    (if sign (Rep_float a) = sign (Rep_float b) then 0 else 1)
    (round float_format To_nearest (valof float_format (Rep_float b) * 
    valof float_format (Rep_float a))))" using B C D E 
    by (auto simp add: fmul_def times_float_def Abs_float_inverse is_nan_def is_infinity_def) 
  have "valof float_format (Rep_float b) * valof float_format (Rep_float a) =
    valof float_format (Rep_float a) * valof float_format (Rep_float b)" 
    by simp
  then have  "round float_format To_nearest (valof float_format (Rep_float b) *
    valof float_format (Rep_float a)) =  
    round float_format To_nearest (valof float_format (Rep_float a) *
    valof float_format (Rep_float b))"
    by metis
  then have "(a * b) = (b * a)"  using F G by arith
  then show ?thesis using A by auto
qed

lemma float_mul_comm: "Finite a \<and> Finite b \<and> Finite (a * b) \<Longrightarrow> (a * b) \<doteq> (b * a)"
by (metis float_distinct_finite float_eq_refl float_mul_comm_eq)

(*Showing --(-- a) = a*)
lemma sign_double_neg [simp]: "is_valid x a \<Longrightarrow> (1 - (1 - sign a)) = sign a"
proof -
  assume A: "is_valid x a"
  then have "sign a < 2"  by (auto simp add: is_valid_def)
  then have "sign a = 0 \<or> sign a = 1" by auto
  then show "(1 - (1 - sign a)) = sign a" by auto
qed
   
lemma float_double_neg_eq [simp]: "\<not>Isnan a \<Longrightarrow> float_neg (float_neg a) = a"
proof -
  assume A: "\<not>Isnan a"
  have B: "float_neg a = Abs_float (fneg (float_format) To_nearest (Rep_float a))"
    by (simp add: float_neg_def) 
  then have C: "... = 
    Abs_float (1 - sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a))"
    by (simp add: fneg_def)
  then have D: "float_neg (float_neg a) = 
    Abs_float (fneg float_format To_nearest (Rep_float (Abs_float (
    1 - sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a)))))"
    by (simp add: float_neg_def)
  have E: "is_valid float_format ((1 - sign (Rep_float a), exponent (Rep_float a), 
    fraction (Rep_float a)))"
    by (cases a)  (auto simp add:  Abs_float_inverse is_valid_def)
  then have "Abs_float (fneg float_format To_nearest (Rep_float (Abs_float (
    1 - sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a))))) = 
    Abs_float (fneg float_format To_nearest  (
    1 - sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a)))"
    by (simp add: Abs_float_inverse)
  then have "float_neg (float_neg a) = 
    Abs_float (fneg float_format To_nearest (
    1 - sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a)))" using D by simp
  then have "float_neg (float_neg a) = 
    Abs_float (1 - (1 - sign (Rep_float a)), exponent (Rep_float a), fraction (Rep_float a))" 
    by (auto simp add: fneg_def)
  then have "... = Abs_float (sign (Rep_float a), exponent (Rep_float a), fraction (Rep_float a))"
    by (metis is_valid_defloat sign_double_neg)
  then have "float_neg (float_neg a) = a" 
    by (metis Rep_float_inverse `float_neg (float_neg a) = 
    Abs_float (1 - (1 - sign (Rep_float a)), exponent (Rep_float a), fraction (Rep_float a))
    ` exponent.simps fraction.cases fraction.simps sign.simps)
  then show ?thesis using A by auto
qed

lemma float_double_neg [simp]: "\<not>Isnan a \<Longrightarrow> float_neg (float_neg a) \<doteq> a"
apply auto
done

(* The floating-point number a falls into the same category as the negation of a *)
lemma neg_zero: "is_zero x a \<longleftrightarrow> is_zero x (fneg x m a)"
apply (auto simp add: fneg_def is_zero_def)
done

lemma float_neg_zero: "Iszero a \<longleftrightarrow> Iszero (float_neg a)"
proof -
  have A:  "Iszero a = is_zero float_format (Rep_float a)" by simp
  have B: "Iszero (float_neg a) = is_zero float_format 
    (Rep_float (Abs_float (fneg float_format To_nearest (Rep_float a))))"
    by (auto simp add: float_neg_def)
  have "is_valid float_format ((1 - sign (Rep_float a), exponent (Rep_float a), 
    fraction (Rep_float a)))"
    by (cases a) (auto simp add: Abs_float_inverse is_valid_def)
  then have C: "is_zero float_format (Rep_float (Abs_float (fneg float_format To_nearest 
    (Rep_float a)))) = is_zero float_format (fneg float_format To_nearest (Rep_float a))" 
    by (auto simp add: Abs_float_inverse fneg_def)
  then have "... = is_zero float_format (Rep_float a)" by (metis neg_zero)
  then show ?thesis using A B C by auto 
qed
   
lemma float_neg_zero1: "is_zero float_format (Rep_float a) = 
                        is_zero float_format (Rep_float (float_neg a))"
by (metis Iszero_def float_neg_zero)

   
lemma neg_infinity: "is_infinity x a \<longleftrightarrow> is_infinity x (fneg x m a)"
apply (auto simp add: fneg_def is_infinity_def)
done

lemma neg_normal: "is_normal x a \<longleftrightarrow> is_normal x (fneg x m a)"
apply (auto simp add: fneg_def is_normal_def )
done

lemma float_neg_normal: "Isnormal a \<longleftrightarrow> Isnormal (float_neg a)"
proof -
  have A:  "Isnormal a = is_normal float_format (Rep_float a)" by simp
  have B: "Isnormal (float_neg a) = is_normal float_format (Rep_float (Abs_float 
    (fneg float_format To_nearest (Rep_float a))))"
    by (auto simp add: float_neg_def)
  have "is_valid float_format ((1 - sign (Rep_float a), exponent (Rep_float a), 
    fraction (Rep_float a)))"
    by (cases a) (auto simp add: Abs_float_inverse is_valid_def)
  then have C: "is_normal float_format (Rep_float (Abs_float (fneg float_format To_nearest 
    (Rep_float a)))) = is_normal float_format (fneg float_format To_nearest (Rep_float a))" 
     by (auto simp add: Abs_float_inverse fneg_def)
  then have "... = is_normal float_format (Rep_float a)" by (metis neg_normal)
  then show ?thesis using A B C by auto 
qed

lemma neg_denormal: "is_denormal x a \<longleftrightarrow> is_denormal x (fneg x m a)"
apply (auto simp add: fneg_def is_denormal_def)
done

lemma float_neg_denormal: "Isdenormal a \<longleftrightarrow> Isdenormal (float_neg a)"
proof -
  have A: "Isdenormal a = is_denormal float_format (Rep_float a)" by simp
  have B: "Isdenormal (float_neg a) = is_denormal float_format (Rep_float (Abs_float 
    (fneg float_format To_nearest (Rep_float a))))"
    by (auto simp add: float_neg_def)
  have "is_valid float_format ((1 - sign (Rep_float a), exponent (Rep_float a), 
    fraction (Rep_float a)))"
    by (cases a) (auto simp add: Abs_float_inverse is_valid_def)
  then have C: "is_denormal float_format (Rep_float (Abs_float (fneg float_format To_nearest 
    (Rep_float a)))) = is_denormal float_format (fneg float_format To_nearest (Rep_float a))" 
    by (auto simp add: Abs_float_inverse fneg_def)
  then have "... = is_denormal float_format (Rep_float a)" by (metis neg_denormal)
  then show ?thesis using A B C by auto 
qed


lemma neg_valid: "is_valid x a \<Longrightarrow> is_valid x (fneg x m a)"
apply (auto simp add: fneg_def is_valid_def)
done

lemma neg_finite: "is_finite x a \<Longrightarrow> is_finite x (fneg x m a) "
by (metis is_finite_def neg_denormal neg_normal neg_valid neg_zero)

lemma float_neg_finite: "Finite a \<Longrightarrow> Finite (float_neg a)"
by (metis Finite_def float_neg_denormal float_neg_normal float_neg_zero)

(* The sign of a and the sign of a's negation is different *)
lemma float_neg_sign: "sign (Rep_float a) \<noteq> sign (Rep_float (float_neg a))"
proof -
  have "sign (Rep_float a) = 0 \<or> sign (Rep_float a) = 1" by (metis is_valid_defloat sign_0_1)
  moreover have "sign (Rep_float a) = 0 \<Longrightarrow> sign (Rep_float (float_neg a)) = 1" 
    by (cases a) (auto simp add: fneg_def float_neg_def Abs_float_inverse is_valid_def)
  moreover have "sign (Rep_float a) = 1 \<Longrightarrow> sign (Rep_float (float_neg a)) = 0"
    by (cases a) (auto simp add: fneg_def float_neg_def Abs_float_inverse is_valid_def)
  ultimately show ?thesis  by (metis zero_neq_one)
qed

lemma float_neg_sign1: "(sign (Rep_float a) = sign (Rep_float (float_neg b))) \<longleftrightarrow>
                        (sign (Rep_float a) \<noteq> sign (Rep_float  b))"
by (metis float_neg_sign is_valid_defloat sign_0_1)

lemma neg_val: 
  fixes  m a
  assumes "is_finite float_format a"
  shows " - valof float_format a = valof float_format (fneg float_format m a)" (is "?R = ?L")
proof -
  have A: "?L = valof float_format (sign (fneg float_format m a), 
    exponent (fneg float_format m a), fraction (fneg float_format m a))"
    by (metis exponent.simps fneg_def fraction.simps sign.simps)
  then have B: "... = valof float_format (1 - sign a, exponent a, fraction a)"
    by (metis fneg_def)
  have C: "sign a = 0 \<longleftrightarrow> 1 - (sign a) = 1" by auto
  have D: "sign a = 1 \<longleftrightarrow> 1 - (sign a) = 0" using sign_0_1 assms 
    by (auto simp add: is_valid_def is_finite_def)
  then have "valof float_format (0, exponent a, fraction a) = 
    -valof float_format (1, exponent a, fraction a)"
    by auto
  then show "?thesis" using A B C D
    by (metis (hide_lams, no_types) assms exponent.simps 
    fneg_def fraction.simps is_finite_def minus_minus prod.exhaust sign.simps sign_0_1)
qed

lemma float_neg_val: "Finite b \<Longrightarrow> valof float_format (Rep_float (float_neg b))
                    = - valof float_format (Rep_float b)"
proof -
  assume A: "Finite b"
  then have "valof float_format (Rep_float (float_neg b)) = 
    valof float_format (sign (Rep_float (float_neg b)),
    exponent (Rep_float (float_neg b)), fraction (Rep_float (float_neg b))) "
    by (metis PairE exponent.simps fraction.simps sign.simps)
  also have B:"... = valof float_format ((1 - sign (Rep_float b),
    exponent (Rep_float b), fraction (Rep_float b)))"
    using float_neg_def fneg_def Abs_float_inverse by (cases b) (auto simp add: is_valid_def) 
  have C: "valof float_format (Rep_float b) = 
    valof float_format ((sign (Rep_float b), exponent (Rep_float b), fraction (Rep_float b)))" 
    by (metis exponent.simps fraction.simps prod.exhaust sign.simps)
  have D: "sign (Rep_float b) = 0 \<longleftrightarrow> 1 - sign (Rep_float b) = 1" by arith
  have E: "sign (Rep_float b) = 1 \<longleftrightarrow> 1 - sign (Rep_float b) = 0" 
    using is_valid_defloat sign_0_1 by (metis D diff_self_eq_0) 
  then have "valof float_format (0, exponent (Rep_float b), fraction (Rep_float b)) = 
    - valof float_format (1, exponent (Rep_float b),
    fraction (Rep_float b)) " by auto
  thus ?thesis using A B C D  
    by (metis comm_monoid_diff_class.diff_cancel exponent.simps 
    fraction.simps is_valid_defloat minus_minus prod.exhaust sign.simps sign_0_1) 
qed

(* Showing  a + (-b) = a - b *)
lemma float_neg_add: "Finite a \<and> Finite b \<and> Finite (a - b) \<Longrightarrow> 
                    valof float_format (Rep_float a) + 
                    valof float_format (Rep_float (float_neg b)) =
                    valof float_format (Rep_float a) - 
                    valof float_format (Rep_float b)"
by (metis comm_ring_1_class.normalizing_ring_rules(2) float_neg_val)

lemma float_plus_minus: "Finite a \<and> Finite b \<and> Finite (a - b) \<Longrightarrow> (a + float_neg b) \<doteq> (a - b)"
proof -
  assume A: "Finite a \<and> Finite b \<and> Finite (a - b)"
  then have B: "\<not>is_nan float_format (Rep_float a)" 
    by (auto simp add: finite_nan emax_def is_nan_def is_normal_def is_denormal_def is_zero_def)
  have C: "\<not>is_nan float_format (Rep_float (float_neg b))" using A 
    by (metis finite_nan float_neg_finite)
  have D: "\<not>is_infinity float_format (Rep_float a)" using A 
    by (auto simp add: finite_infinity emax_def is_infinity_def 
      is_normal_def is_denormal_def is_zero_def)
  have E: "\<not>is_infinity float_format (Rep_float (float_neg  b))" using A 
    by (metis finite_infinity float_neg_finite) 
  then have F: "(a + float_neg b) =  Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float (float_neg b)) \<and>
        (sign (Rep_float a) = sign (Rep_float (float_neg b))) 
    then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
         valof float_format (Rep_float (float_neg b)))))" using B C D E 
    by (auto simp add: fadd_def plus_float_def ) 
  then have G: "... = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float  b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) + 
         valof float_format (Rep_float (float_neg b))))) " using float_neg_sign1 float_neg_zero1
     by auto
  then have H: "... = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float  b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))" 
    using A float_neg_add by metis
  have "(a - b) = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float  b) \<and>
        \<not>(sign (Rep_float a) = sign (Rep_float b)) 
     then sign (Rep_float a) else if (To_nearest = To_ninfinity) then 1 else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))" using A B C D E fsub_def minus_float_def
     by (metis finite_infinity finite_nan) 
  then have "(a - b) = Abs_float (zerosign float_format 
    (if is_zero float_format (Rep_float a) \<and> 
        is_zero float_format (Rep_float  b) \<and>
        (sign (Rep_float a) \<noteq> sign (Rep_float b)) 
     then sign (Rep_float a) else 0)
        (round float_format To_nearest (valof float_format (Rep_float a) - 
        valof float_format (Rep_float b))))"  by auto
  thus ?thesis using F H by (metis A G float_eq)
qed

(* Showing abs (-a) = abs (a) *)
lemma float_abs: "\<not>Isnan a \<Longrightarrow> float_abs (float_neg a) = float_abs a"
apply (cases a)
apply (auto simp add: float_abs_def float_neg_def  fneg_def Abs_float_inverse is_valid_def)
done

lemma neg_zerosign: "fneg x m (zerosign x s a) = zerosign x (1-s) (fneg x m a)"
apply (auto simp add: fneg_def zerosign_def is_zero_def is_valid_def)
done

lemma "a \<in> {m. is_finite float_format m} \<Longrightarrow> is_finite float_format a"
apply auto
done

lemma float_finite_valid: "Finite a \<Longrightarrow> is_valid float_format (Rep_float a)"
apply (cases a)
apply (auto simp add: Abs_float_inverse)
done

lemma finite_valid: "is_finite x a \<Longrightarrow> is_valid x a"
apply (cases a)
by (metis is_finite_def)

end
