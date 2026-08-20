(*  Title:  HyperArchimedean.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>The floor and ceiling functions extended to hypernumbers\<close>

theory HyperArchimedean
imports HyperInt
begin

subsection\<open>The nonstandard floor function\<close>

definition
  hfloor :: "'a::floor_ceiling star \<Rightarrow> hypint"  (\<open>(\<open>open_block notation=\<open>mixfix floor\<close>\<close>\<lfloor>_\<rfloor>)\<close>) where
  [transfer_unfold]: "hfloor x = (*f* floor) x"

lemma hfloor:
  "hfloor (star_n X) = star_n (\<lambda>n. floor (X n))"
  by (simp add: hfloor_def starfun_star_n)

lemma hfloor_correct: "\<And>x. of_hypint (hfloor x) \<le> x \<and> x < of_hypint (hfloor x + 1)"
by transfer (rule floor_correct)

lemma hfloor_unique: "\<And>x z. \<lbrakk> of_hypint z \<le> x; x < of_hypint z + 1 \<rbrakk> \<Longrightarrow> hfloor x = z"
by transfer (blast intro: floor_unique)

lemma hfloor_eq_zero [simp]: "\<lbrakk> 0 \<le> x; x < 1\<rbrakk> \<Longrightarrow> hfloor x = 0"
  by (simp add: hfloor_unique)

lemma of_hypint_floor_le: "of_hypint (hfloor x) \<le> x"
using hfloor_correct ..

lemma le_hfloor_iff: "\<And>x z. z \<le> hfloor x \<longleftrightarrow> of_hypint z \<le> x"
by transfer (rule le_floor_iff)

lemma hfloor_less_iff: "\<And>x z. hfloor x < z \<longleftrightarrow> x < of_hypint z"
by transfer (rule floor_less_iff)

lemma less_hfloor_iff: "\<And>x z. z < hfloor x \<longleftrightarrow> of_hypint z + 1 \<le> x"
by transfer (rule less_floor_iff)

lemma hfloor_le_iff: "\<And>x z. hfloor x \<le> z \<longleftrightarrow> x < of_hypint z + 1"
by transfer (rule floor_le_iff)

lemma hfloor_mono: "\<And>x y. x \<le> y \<Longrightarrow> hfloor x \<le> hfloor y"
by transfer (rule floor_mono)

lemma hfloor_less_cancel: "\<And>x y. hfloor x < hfloor y \<Longrightarrow> x < y"
by transfer (rule floor_less_cancel)

lemma hfloor_of_hypint [simp]: "\<And>z. hfloor (of_hypint z) = z"
by transfer (rule floor_of_int)

lemma hfloor_of_int [simp]: "hfloor (of_int z) = hypint_of_int z"
by (rule hfloor_unique) auto
  
lemma hfloor_of_hypnat [simp]: "\<And>n. hfloor (of_hypnat n) = of_hypnat n"
by transfer (rule floor_of_nat)

lemma hfloor_of_nat [simp]: "hfloor (of_nat n) = of_nat n"
using hfloor_of_hypint [of "of_nat n"] by simp


text\<open>Floor with numerals\<close>

lemma hfloor_zero [simp]: "hfloor 0 = 0"
  using hfloor_of_int [of 0] by simp

lemma hfloor_one [simp]: "hfloor 1 = 1"
  using hfloor_of_int [of 1] by simp

lemma hfloor_star_of [simp]: "hfloor (star_of x) = star_of x"
by transfer simp

lemma star_of_hfloor [simp]: "star_of(floor x) = hfloor (star_of x)"
by (metis hfloor_def starfun_star_of)

lemma hfloor_number_of [simp]: "hfloor (numeral v :: hypreal) = (numeral v :: hypint)"
by (metis hfloor_of_int of_int_numeral star_numeral_def)

lemma zero_le_hfloor [simp]: "0 \<le> hfloor x \<longleftrightarrow> 0 \<le> x"
  by (simp add: le_hfloor_iff)

lemma one_le_hfloor [simp]: "1 \<le> hfloor x \<longleftrightarrow> 1 \<le> x"
  by (simp add: le_hfloor_iff)

lemma numeral_le_hfloor [simp]: "\<And>x. numeral v \<le> hfloor x \<longleftrightarrow> numeral v \<le> x"
by transfer simp

lemma zero_less_hfloor [simp]: "0 < hfloor x \<longleftrightarrow> 1 \<le> x"
  by (simp add: less_hfloor_iff)

lemma one_less_hfloor [simp]: "1 < hfloor x \<longleftrightarrow> 2 \<le> x"
  by (simp add: less_hfloor_iff)

lemma numeral_less_hfloor [simp]:
  "\<And>x. numeral v < hfloor x \<longleftrightarrow> numeral v + 1  \<le> x"
by transfer simp

lemma hfloor_le_zero [simp]: "hfloor x \<le> 0 \<longleftrightarrow> x < 1"
  by (simp add: hfloor_le_iff)

lemma hfloor_le_one [simp]: "hfloor x \<le> 1 \<longleftrightarrow> x < 2"
  by (simp add: hfloor_le_iff)

lemma hfloor_le_numeral [simp]:
  "\<And>x. hfloor x  \<le> numeral v \<longleftrightarrow> x < numeral v + 1"
by transfer simp

lemma hfloor_less_zero [simp]: "hfloor x < 0 \<longleftrightarrow> x < 0"
  by (simp add: hfloor_less_iff)

lemma hfloor_less_one [simp]: "hfloor x < 1 \<longleftrightarrow> x < 1"
  by (simp add: hfloor_less_iff)

lemma hfloor_less_numeral [simp]:
  "\<And>x. hfloor x < numeral v \<longleftrightarrow> x < numeral v"
by transfer simp

lemma hfloor_add_of_hypint [simp]: "hfloor (x + of_hypint z) = hfloor x + z"
  using hfloor_correct [of x] by (simp add: hfloor_unique)

lemma hfloor_add_of_int [simp]: "\<And>x. hfloor (x + of_int z) = hfloor x + of_int z"
by transfer simp

lemma hfloor_add_numeral [simp]:
    "hfloor (x + numeral v) = hfloor x + numeral v"
  using hfloor_add_of_int [of x "numeral v"] by simp

lemma hfloor_add_one [simp]: "hfloor (x + 1) = hfloor x + 1"
  using hfloor_add_of_int [of x 1] by simp

lemma hfloor_diff_of_hypint [simp]: "hfloor (x - of_hypint z) = hfloor x - z"
  using hfloor_add_of_hypint [of x "- z"] by (simp add: algebra_simps)

lemma hfloor_diff_of_int [simp]: "hfloor (x - of_int z) = hfloor x - of_int z"
  using hfloor_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma hfloor_diff_numeral [simp]:
  "hfloor (x - numeral v) = hfloor x - numeral v"
  using hfloor_diff_of_int [of x "numeral v"] by simp

lemma hfloor_diff_one [simp]: "hfloor (x - 1) = hfloor x - 1"
  using hfloor_diff_of_int [of x 1] by simp

lemma hfloor_add_one_gt_zero:
  "\<And>y. 0 < y \<Longrightarrow> 0 < hfloor y + 1"
by (metis hypint_le_add1_eq_le le_less zero_le_hfloor)

subsection\<open>The nonstandard ceiling function\<close>

definition
  hceiling :: "'a::floor_ceiling star => hypint" (\<open>(\<open>open_block notation=\<open>mixfix ceiling\<close>\<close>\<lceil>_\<rceil>)\<close>) where
  [transfer_unfold]: "hceiling x = - hfloor (- x)"

lemma hceiling_correct: "of_hypint (hceiling x) - 1 < x \<and> x \<le> of_hypint (hceiling x)"
  unfolding hceiling_def using hfloor_correct [of "- x"] by simp

lemma hceiling_unique: "\<lbrakk>of_hypint z - 1 < x; x \<le> of_hypint z\<rbrakk> \<Longrightarrow> hceiling x = z"
  unfolding hceiling_def using hfloor_unique [of "- z" "- x"] by simp

lemma le_of_int_hceiling: "x \<le> of_hypint (hceiling x)"
  using hceiling_correct ..

lemma hceiling_le_iff: "hceiling x \<le> z \<longleftrightarrow> x \<le> of_hypint z"
  unfolding hceiling_def using le_hfloor_iff [of "- z" "- x"] by auto

lemma less_hceiling_iff: "z < hceiling x \<longleftrightarrow> of_hypint z < x"
  by (simp add: not_le [symmetric] hceiling_le_iff)

lemma hceiling_less_iff: "hceiling x < z \<longleftrightarrow> x \<le> of_hypint z - 1"
  using hceiling_le_iff [of x "z - 1"] by simp

lemma le_hceiling_iff: "z \<le> hceiling x \<longleftrightarrow> of_hypint z - 1 < x"
  by (simp add: not_less [symmetric] hceiling_less_iff)

lemma hceiling_mono: "x \<ge> y \<Longrightarrow> hceiling x \<ge> hceiling y"
  unfolding hceiling_def by (simp add: hfloor_mono)

lemma hceiling_less_cancel: "hceiling x < hceiling y \<Longrightarrow> x < y"
  by (auto simp add: not_le [symmetric] hceiling_mono)

lemma hceiling_of_hypint [simp]: "hceiling (of_hypint z) = z"
  by (rule hceiling_unique) simp_all

lemma hceiling_of_int [simp]: "hceiling (of_int z) = of_int z"
  by (rule hceiling_unique) simp_all

lemma hceiling_of_hypnat [simp]: "hceiling (of_hypnat n) = of_hypnat n"
  using hceiling_of_hypint [of "of_hypnat n"] by simp

lemma hceiling_of_nat [simp]: "hceiling (of_nat n) = of_nat n"
  using hceiling_of_int [of "of_nat n"] by simp

text\<open>Ceiling with numerals\<close>

lemma hceiling_zero [simp]: "hceiling 0 = 0"
  using hceiling_of_int [of 0] by simp

lemma hceiling_one [simp]: "hceiling 1 = 1"
  using hceiling_of_int [of 1] by simp

lemma hceiling_numeral [simp]: "hceiling (numeral v) = numeral v"
  using hceiling_of_int [of "numeral v"] by simp

lemma hceiling_le_zero [simp]: "hceiling x \<le> 0 \<longleftrightarrow> x \<le> 0"
  by (simp add: hceiling_le_iff)

lemma hceiling_le_one [simp]: "hceiling x \<le> 1 \<longleftrightarrow> x \<le> 1"
  by (simp add: hceiling_le_iff)

lemma hceiling_le_numeral [simp]:
  "\<And>x. hceiling x \<le> numeral v \<longleftrightarrow> x \<le> numeral v"
by transfer (simp add: floor_minus) 

lemma hceiling_less_zero [simp]: "hceiling x < 0 \<longleftrightarrow> x \<le> -1"
  by (simp add: hceiling_less_iff)

lemma hceiling_less_one [simp]: "hceiling x < 1 \<longleftrightarrow> x \<le> 0"
  by (simp add: hceiling_less_iff)

lemma hceiling_less_numeral [simp]:
  "\<And>x. hceiling x < numeral v \<longleftrightarrow> x \<le> numeral v - 1"
by transfer(metis ceiling_def ceiling_less_numeral)

lemma zero_le_hceiling [simp]: "0 \<le> hceiling x \<longleftrightarrow> -1 < x"
  by (simp add: le_hceiling_iff)

lemma one_le_hceiling [simp]: "1 \<le> hceiling x \<longleftrightarrow> 0 < x"
  by (simp add: le_hceiling_iff)

lemma numeral_le_hceiling [simp]:
  "\<And>x. numeral v \<le> hceiling x\<longleftrightarrow> numeral v - 1 < x"
by (meson hceiling_less_numeral leD not_le_imp_less)

lemma zero_less_hceiling [simp]: "0 < hceiling x \<longleftrightarrow> 0 < x"
  by (simp add: less_hceiling_iff)

lemma one_less_hceiling [simp]: "1 < hceiling x \<longleftrightarrow> 1 < x"
  by (simp add: less_hceiling_iff)

lemma numeral_less_hceiling [simp]:
  "\<And>x. numeral v < hceiling x \<longleftrightarrow> numeral v < x"
by (metis hceiling_le_numeral not_less)

lemma hceiling_add_of_hypint [simp]: "hceiling (x + of_hypint z) = hceiling x + z"
  using hceiling_correct [of x] by (simp add: hceiling_unique)

lemma hceiling_add_of_int [simp]: "hceiling (x + of_int z) = hceiling x + of_int z"
  using hceiling_correct [of x] by (simp add: hceiling_unique)

lemma hceiling_add_numeral [simp]:
    "hceiling (x + numeral v) = hceiling x + numeral v"
  using hceiling_add_of_int [of x "numeral v"] by simp

lemma hceiling_add_one [simp]: "hceiling (x + 1) = hceiling x + 1"
  using hceiling_add_of_int [of x 1] by simp

lemma hceiling_diff_of_hypint [simp]: "hceiling (x - of_hypint z) = hceiling x - z"
  using hceiling_add_of_hypint [of x "- z"] by (simp add: algebra_simps)

lemma hceiling_diff_of_int [simp]: "hceiling (x - of_int z) = hceiling x - of_int z"
  using hceiling_add_of_int [of x "- z"] by (simp add: algebra_simps)

lemma hceiling_diff_numeral [simp]:
  "hceiling (x - numeral v) = hceiling x - numeral v"
  using hceiling_diff_of_int [of x "numeral v"] by simp


lemma hceiling_diff_one [simp]: "hceiling (x - 1) = hceiling x - 1"
  using hceiling_diff_of_int [of x 1] by simp


lemma hfloor_minus: "hfloor (- x) = - hceiling x"
  unfolding hceiling_def by simp

lemma hceiling_minus: "hceiling (- x) = - hfloor x"
  unfolding hceiling_def by simp

subsection\<open>The nonstandard fractional part\<close>

definition
  hpart :: "'a::floor_ceiling star => 'a star" where
  [transfer_unfold]: "hpart x = x - of_hypint (hfloor x)"

notation 
  hpart  ("\<lbrace>_\<rbrace>")

notation (HTML output)
  hpart  ("\<lbrace>_\<rbrace>")

lemma hpart_zero [simp]: "hpart(0) = 0"
by (simp add: hpart_def)

lemma hpart_ge_zero [simp]: "0 \<le> hpart x"
using hfloor_correct [of x] by (simp add: hpart_def)

lemma hpart_less_one [simp]: "hpart x < 1"
using hfloor_correct [of x] by (simp add: hpart_def)

lemma hpart_le_one [simp]: "hpart x \<le> 1"
by (simp add: less_imp_le)

lemma hypreal_eq_hfloor_hpart_add:
      "x = of_hypint (hfloor x) + hpart x"
by (simp add: hpart_def)

lemma hfloor_eq_self_diff_hpart: "of_hypint (hfloor x) = x - hpart x"
by (simp add: hpart_def)

lemma HFinite_hpart [simp]: "\<And>x. hpart (x::hypreal) \<in> HFinite"
  using HFinite_1 HFinite_bounded hpart_ge_zero hpart_le_one by blast

lemma hpart_not_less_one [simp]: "\<not> 1 < \<lbrace>x\<rbrace>"
by (simp add: not_less)

lemma hpart_mult_less_cancel [simp]: "(x * \<lbrace>y\<rbrace> < x) = (0 < x)"
by (auto simp add: mult_less_cancel_left2)

lemma hfloor_of_hypint_divide [simp]: 
  "\<And>x y. hfloor ((of_hypint x :: hypreal)/ of_hypint y) = (x div y)"
by transfer (simp add: floor_divide_of_int_eq)

lemma hfloor_of_hypint_of_hypnat_divide [simp]: 
  "\<And>x y. hfloor ((of_hypint x :: hypreal)/ of_hypnat y) = (x div (of_hypnat y))"
by (metis hfloor_of_hypint_divide of_hypint_of_hypnat)

lemma floor_real_of_nat_real_of_int_divide [simp]: 
  "floor (real x / real y) = int x div y"
by (metis floor_divide_of_int_eq of_int_of_nat_eq)

lemma hfloor_of_hypnat_of_hypint_divide [simp]: 
  "\<And>x y. hfloor ((of_hypnat x:: hypreal) / of_hypint y) = (of_hypnat x) div y"
by (metis hfloor_of_hypint_divide of_hypint_of_hypnat)

lemma of_hypnat_hypnat_of_hypint [simp]:
  "0 \<le> x \<Longrightarrow> of_hypnat(hypnat(hfloor x)) = of_hypint (hfloor x)"
  by simp

subsection\<open>Miscellaneous properties\<close>

lemma HFinite_hypnat_hfloor_Nat:
  assumes "(y::hypreal) \<in> HFinite"
  shows "hypnat (hfloor y) \<in> \<nat>"
proof -
  have ybounds: "hypreal_of_hypint (hfloor y) \<le> y" "y < hypreal_of_hypint (hfloor y + 1)"
    using hfloor_correct by blast+
  then show ?thesis
  proof (cases "y > 0")
    case True
    assume y0: "y > 0" 
    show ?thesis 
    proof (rule ccontr)
      assume "hypnat (hfloor y) \<notin> \<nat>"
      then have "hypnat (hfloor y) \<in> HNatInfinite"
        using HNatInfinite_not_Nats_iff by blast 
      moreover have "hypreal_of_hypnat (hypnat (hfloor y)) \<le> y"
        by (metis hypint_hypnat_eq less_imp_le of_hypint_of_hypnat y0 ybounds(1) zero_le_hfloor)
      ultimately show False
        using HInfinite_HFinite_iff HInfinite_ge_HNatInfinite assms by blast
    qed
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma HFinite_between_Nats: 
  assumes "(x::hypreal) \<in> HFinite" 
  and "x > 0"
  shows "\<exists>n\<in>\<nat>. n \<le> x \<and> x < n + 1" 
proof -
  have x1: "hypreal_of_hypint (hfloor x) \<le> x" and x2: "x < hypreal_of_hypint (hfloor x + 1)"
    using hfloor_correct by auto
  moreover obtain m where "hfloor x = hypint_of_hypnat m"
    using assms(2) nonneg_eq_hypint zero_le_hfloor less_imp_le by metis
  moreover have "m \<in> \<nat>"
    using HFinite_hypnat_hfloor_Nat assms(1) calculation(3) by force 
  ultimately show ?thesis 
    by (auto simp add: Nats_def)
qed

lemma hfloor_eq_self_diff_hpart2: 
      "\<And>x. 0 \<le> x \<Longrightarrow> of_hypnat (hypnat (hfloor x)) = x - hpart x"
  by (metis hfloor_eq_self_diff_hpart hypint_hypnat_eq of_hypint_of_hypnat zero_le_hfloor)

lemma hypreal_HInfinite_hfloor:
  "(x::hypreal) \<in> HInfinite \<Longrightarrow> hypreal_of_hypint (hfloor x) \<in> HInfinite"
  by (metis HFinite_hpart HInfinite_HFinite_add_cancel diff_add_cancel hfloor_eq_self_diff_hpart)

lemma hypreal_HInfinite_hfloor_cancel:
  "hypreal_of_hypint (hfloor x) \<in> HInfinite \<Longrightarrow> (x::hypreal) \<in> HInfinite"
by (metis HFinite_hpart HInfinite_HFinite_add diff_add_cancel hfloor_eq_self_diff_hpart)

lemma hypreal_HNatInfinite_hfloor:
  "\<lbrakk> (x::hypreal) \<in> HInfinite; x > 0 \<rbrakk> \<Longrightarrow> hypnat (hfloor x) \<in> HNatInfinite"
by (metis HInfinite_gt_zero_gt_one hypreal_HInfinite_hfloor 
    HInfinite_of_hypint_HNatInfinite_hypnat less_imp_le zero_less_hfloor)

lemma hypreal_HNatInfinite_hfloor_cancel:
  "hypnat (hfloor x) \<in> HNatInfinite \<Longrightarrow> (x::hypreal) \<in> HInfinite"
by (metis hypreal_HInfinite_hfloor_cancel HNatInfinite_hypnat_HInfinite_of_hypint)

lemma hypreal_HNatInfinite_hfloor_inverse_Infinitesimal:
   "\<lbrakk> (e::hypreal) \<in> Infinitesimal; e > 0 \<rbrakk> \<Longrightarrow> hypnat (hfloor (1 / e)) \<in> HNatInfinite"
by  (auto intro!: hypreal_HNatInfinite_hfloor Infinitesimal_inverse_HInfinite 
        simp add: divide_inverse)

lemma hypreal_Infinitesimal_HNatInfinite_hfloor_inverse_iff:
      assumes pos: "e > 0"
      shows "((e::hypreal) \<in> Infinitesimal) = (hypnat (hfloor (1 / e)) \<in> HNatInfinite)" (is "?L = ?R")
proof 
  assume ?L 
  then show ?R using pos hypreal_HNatInfinite_hfloor_inverse_Infinitesimal by blast 
next 
  assume ?R then have "1/e \<in> HInfinite" using hypreal_HNatInfinite_hfloor_cancel by blast
  then show ?L using HInfinite_inverse_Infinitesimal by fastforce
qed

lemma hypreal_Infinitesimal_hfloor_inverse_HNatInfinite:
   "hypnat (hfloor (1 / e)) \<in> HNatInfinite \<Longrightarrow> (e::hypreal) \<in> Infinitesimal"
  using HInfinite_inverse_Infinitesimal hypreal_HNatInfinite_hfloor_cancel by force

lemma inverse_hfloor_inverse_approx:
  "e \<in> Infinitesimal \<Longrightarrow> inverse (hypreal_of_hypint(hfloor(1 / e))) \<approx> e"
proof -
  assume a1: "e \<in> Infinitesimal"
  then have f2: "e = 0 \<or> 1 / e \<in> HInfinite"
    by (metis (no_types) Infinitesimal_inverse_HInfinite inverse_eq_divide)
  then have "1 / hypreal_of_hypint (hfloor (1 / e)) \<approx> e"
    by (metis HInfinite_inverse_Infinitesimal Infinitesimal_approx a1 div_by_0 hfloor_zero 
        hypreal_HInfinite_hfloor inverse_eq_divide of_hypint_0)
  then show ?thesis
    by (simp add: inverse_eq_divide)
qed


lemma Infinitesimal_hfloor_divide_mult: 
      assumes infmal_x: "x \<in> Infinitesimal"
      and not_zero_x: " x \<noteq> (0::hypreal)" 
      shows "x * of_hypint(hfloor (z/x)) \<approx> z"
proof - 
  have infmal_hpart_mult: "x * hpart (z/ x) \<approx> 0" 
    using infmal_x
    by (simp add: Infinitesimal_HFinite_mult Infinitesimal_approx )
  have "x * of_hypint(hfloor (z/x)) = x * (z/x - hpart (z/x))"
    using hfloor_eq_self_diff_hpart 
    by auto
  also have "\<dots> = z - x * hpart (z/x)"
    by (simp add: not_zero_x right_diff_distrib)
  finally show ?thesis 
    using approx_diff infmal_hpart_mult 
    by force       
qed

lemma Infinitesimal_hfloor_inverse_mult_self: 
      assumes infmal_x: "x \<in> Infinitesimal"
      and not_zero_x: " x \<noteq> (0::hypreal)" 
      shows "x * of_hypint(hfloor (inverse x)) \<approx> 1"
by (simp add: Infinitesimal_hfloor_divide_mult infmal_x inverse_eq_divide not_zero_x)

lemma Infinitesimal_hfloor_inverse_mult_self_pos:
  "\<lbrakk> e \<in> Infinitesimal;  e > (0::hypreal) \<rbrakk> \<Longrightarrow> e * of_hypint(hfloor(1/e)) \<approx> 1"
  by (auto dest: Infinitesimal_hfloor_inverse_mult_self simp add: inverse_eq_divide)

end