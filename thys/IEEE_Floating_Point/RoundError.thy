(*=========================================================================*)
(* Properties about Rounding Errors.                                       *)
(*=========================================================================*)

(* Author: Lei Yu, University of Cambridge *)

theory RoundError imports IEEE FloatProperty begin

subsection {*Properties about Rounding Errors *}

definition error :: "real \<Rightarrow> real" where
"error x = Val(Abs_float(round float_format To_nearest x)) - x" 

lemma bound_at_worst_lemma: 
  assumes threshold: "\<bar>x\<bar> < threshold float_format"
  assumes finite: "is_finite float_format a"
  shows "abs (valof float_format (round float_format To_nearest x) - x) \<le>
         \<bar>valof float_format a - x\<bar>"
proof -
  have "round float_format To_nearest x = 
        closest (valof float_format)  (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x"
    using threshold by (metis abs_less_iff le_minus_iff not_less round.simps(1))
  then have "is_closest (valof float_format) {a. is_finite float_format a} x 
            (round float_format To_nearest x)" using closest_is_closest 
    by (metis is_finite_finite is_finite_nonempty)
  then show ?thesis 
    using finite is_closest_def by (metis mem_Collect_eq)
qed

lemma defloat_float_round: "Rep_float (Abs_float (round float_format To_nearest x)) = 
                            round (float_format) To_nearest x"
  by (metis mem_Collect_eq Abs_float_inverse is_valid_round) 

lemma error_at_worst_lemma:
  assumes "\<bar>x\<bar> < threshold float_format"  "Finite a"
  shows "\<bar>error x\<bar> \<le> \<bar>Val a - x\<bar> "
proof -
  have "Finite a = is_finite float_format (Rep_float a)" using is_valid_defloat 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  then have "\<bar>Val(Abs_float(round float_format To_nearest x)) - x\<bar> \<le> \<bar>Val a - x\<bar>" 
    using bound_at_worst_lemma assms
    by (metis Val_def defloat_float_round)
  then show ?thesis by (metis error_def)
qed

lemma error_is_zero [simp]:
  assumes "Finite a" 
  shows "error (Val a) = 0"
proof -
  have "\<bar>Val a\<bar> < threshold float_format" 
    by (metis abs_less_iff minus_less_iff float_val_gt_threshold float_val_lt_threshold assms)
  then show ?thesis 
    by (metis abs_le_zero_iff abs_zero diff_self error_at_worst_lemma assms)
qed

lemma valof_scale_up:
  assumes "e \<noteq> 0"
  shows "valof float_format (s::nat, e + k, f) = 2^k * valof float_format (s, e, f)"
using assms
by auto (metis add.commute power_add)

lemma is_finite_zerosign:
  assumes "is_finite float_format a"
  shows "is_finite float_format (zerosign float_format s a)"
using assms
by (metis (full_types) exponent.simps fraction.simps is_finite_def is_zero_def 
    minus_zero_def plus_zero_def zerosign_def zerosign_valid)

lemma defloat_float_zerosign_round_finite:
  assumes threshold: "\<bar>x\<bar> < threshold float_format"
  shows "is_finite float_format
         (zerosign float_format s (round float_format To_nearest x))"
proof -
  have "round float_format To_nearest x = 
        (closest (valof float_format) (\<lambda>a. even (fraction a)) {a. is_finite float_format a} x)"
    using threshold by (metis (full_types) abs_less_iff leD le_minus_iff round.simps(1))
  then have "is_finite float_format (round float_format To_nearest x) "
    by (metis is_finite_closest)
  then show ?thesis
    using is_finite_zerosign by auto
qed

lemma signzero_zero: "is_zero float_format a \<Longrightarrow> 
      valof float_format (zerosign float_format s a) = 0"
  by (auto simp add: zerosign_def)

lemma val_zero: "is_zero float_format a \<Longrightarrow> 
      valof float_format a = 0"
  by (cases a) (auto simp add: is_zero_def)

lemma float_add:
  assumes "Finite a" "Finite b" 
  assumes threshold: "\<bar>Val a + Val b\<bar> < threshold float_format"
  shows finite_float_add: "Finite (a + b)"
    and error_float_add:  "Val (a + b) = Val a + Val b + error (Val a + Val b)"
proof -
  have "\<not>(Isnan a)"  "\<not>(Isnan b)"  "\<not>(Infinity a)" "\<not>(Infinity b)"
    using assms float_distinct_finite by auto
  then have ab: "(a + b) = Abs_float (zerosign float_format 
                          (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then (Sign a) else 0)
                          (round float_format To_nearest (Val a + Val b)))" 
    using assms
    by (auto simp add: float_defs fadd_def plus_float_def)
  then have "is_finite float_format (Rep_float(a + b))" 
    by (metis threshold defloat_float_zerosign_round defloat_float_zerosign_round_finite)
  then show "Finite (a + b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a + b) = 
        valof float_format (zerosign float_format 
              (if Iszero a \<and> Iszero b \<and> Sign a = Sign b then (Sign a) else 0)
              (round float_format To_nearest (Val a + Val b)))" 
    using defloat_float_zerosign_round 
    by (auto simp: ab Infinity_def Isnan_def Val_def)
  show "(Val (a + b) = Val a + Val b + error (Val a + Val b))"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a + Val b))")
    case True 
    have "Val a + Val b + error (Val a + Val b) = 
          valof float_format (round float_format To_nearest (Val a + Val b))" 
      unfolding error_def Val_def  
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis 
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed
       
lemma float_sub:
  assumes "Finite a" "Finite b" 
  assumes threshold: "\<bar>Val a - Val b\<bar> < threshold float_format"
  shows finite_float_sub: "Finite (a - b)"
    and error_float_sub:  "Val (a - b) = Val a - Val b + error (Val a - Val b)"
proof -
  have "\<not>(Isnan a)"  "\<not>(Isnan b)"  "\<not>(Infinity a)" "\<not>(Infinity b)"
    using assms by (auto simp: finite_nan finite_infinity)
  then have ab: "(a - b) = Abs_float (zerosign float_format 
                    (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b then (Sign a) else 0)
                        (round float_format To_nearest (Val a - Val b)))" 
    using assms
    by (auto simp add: float_defs fsub_def minus_float_def)
  then have "is_finite float_format (Rep_float(a - b))"  
   by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round) 
  then show "Finite (a - b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a - b) = 
                valof float_format (zerosign float_format 
                (if Iszero a \<and> Iszero b \<and> Sign a \<noteq> Sign b then (Sign a) else 0)
                    (round float_format To_nearest (Val a - Val b)))" 
    using defloat_float_zerosign_round 
    by (auto simp: ab Infinity_def Isnan_def Val_def)
  show "(Val (a - b) = Val a - Val b + error (Val a - Val b))"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a - Val b))")
    case True 
    have "Val a - Val b + error (Val a - Val b) = 
          valof float_format (round float_format To_nearest (Val a - Val b))" 
      unfolding error_def Val_def  
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis 
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed      

lemma float_mul:
  assumes "Finite a" "Finite b" 
  assumes threshold: "\<bar>Val a * Val b\<bar> < threshold float_format"
  shows finite_float_mul: "Finite (a * b)"
    and error_float_mul:  "Val (a * b) = Val a * Val b + error (Val a * Val b)"
proof -
  have non: "\<not> Isnan a" "\<not> Isnan b"  "\<not> Infinity a"  "\<not> Infinity b" 
    using assms float_distinct_finite by auto
  then have ab: "(a * b) = Abs_float (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
                     (round float_format To_nearest (Val a * Val b)))"  
    using assms
    by (auto simp: float_defs fmul_def times_float_def)
  then have "is_finite float_format (Rep_float(a * b))" 
    by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round)
  then show "Finite (a * b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a * b) = 
                   valof float_format (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
                         (round float_format To_nearest (Val a * Val b)))" 
    using defloat_float_zerosign_round
    by (auto simp: ab float_defs of_bool_def)
  show "(Val (a * b) = Val a * Val b + error (Val a * Val b))"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a * Val b))")
    case True
    have "Val a * Val b + error (Val a * Val b) = 
          valof float_format (round float_format To_nearest (Val a * Val b))" 
      unfolding error_def Val_def  
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis 
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed


lemma float_div:
  assumes "Finite a" "Finite b" 
  assumes not_zero: "\<not>Iszero b"
  assumes threshold: "\<bar>Val a / Val b\<bar> < threshold float_format"
  shows finite_float_div: "Finite (a / b)"
    and error_float_div:  "Val (a / b) = Val a / Val b + error (Val a / Val b)"
proof -
  have ab: "a / b = Abs_float (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
                               (round float_format To_nearest (Val a / Val b)))"  
     using assms
     by (simp add: divide_float_def fdiv_def finite_infinity finite_nan not_zero float_defs [symmetric])
  then have "is_finite float_format (Rep_float(a / b))" 
    by (metis threshold defloat_float_zerosign_round_finite defloat_float_zerosign_round) 
  then show "Finite (a / b)" 
    by (metis Finite_def Isdenormal_def Isnormal_def Iszero_def is_finite_def)
  have val_ab: "Val (a / b) = 
                valof float_format (zerosign float_format (of_bool (Sign a \<noteq> Sign b))
                                     (round float_format To_nearest (Val a / Val b)))"
    using defloat_float_zerosign_round  
    by (auto simp: ab float_defs of_bool_def)
  show "(Val (a / b) = Val a / Val b + error (Val a / Val b))"
  proof (cases "is_zero float_format (round float_format To_nearest (Val a / Val b))")
    case True 
    have "Val a / Val b + error (Val a / Val b) = 
          valof float_format (round float_format To_nearest (Val a / Val b))" 
      unfolding error_def Val_def  
      by (metis add_diff_cancel_left add_0_right defloat_float_round diff_add_cancel)
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis 
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

end
