(*  Title:  HyperInt.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Hyperinteger numbers\<close>

theory HyperInt
  imports AuxiliaryNSA "HOL-Nonstandard_Analysis.NSA"
begin

type_synonym hypint = "int star"

abbreviation
  hypint_of_int :: "int \<Rightarrow> int star" where
  "hypint_of_int \<equiv> star_of"

abbreviation
  hypint_of_hypnat :: "hypnat \<Rightarrow> hypint" where
  "hypint_of_hypnat \<equiv> of_hypnat"

subsection\<open>Properties of Hyperintegers\<close>

text\<open>Many properties hold by transfer from the integers\<close>

lemma hypint_nat_mult_less_mono2_lemma:
     "(i::hypint)<j \<Longrightarrow> 0<k \<Longrightarrow> of_nat k * i < of_nat k * j"
by (metis mult_less_cancel_left_disj of_nat_0_less_iff)

lemma hypint_mult_less_mono2_lemma:
     "\<And>i j k. (i::hypint)<j \<Longrightarrow> 0<k \<Longrightarrow> of_hypnat k * i < of_hypnat k * j"
by transfer (rule zmult_zless_mono2_lemma)

lemma zero_le_imp_eq_hypint: "\<And>k. (0::hypint) \<le> k \<Longrightarrow> \<exists>n. k = of_hypnat n"
by transfer (rule zero_le_imp_eq_int)

lemma zero_less_imp_eq_hypint: "\<And>k. (0::hypint) < k \<Longrightarrow> \<exists>n>0. k = of_hypnat n"
by transfer (rule zero_less_imp_eq_int)

lemma hypint_less_mono2: "\<And>i j k. \<lbrakk> i<j;  (0::hypint) < k \<rbrakk> \<Longrightarrow> k*i < k*j"
by transfer (rule zmult_zless_mono2)

lemma hypint_less_imp_add1_le: "\<And>w z. w < z \<Longrightarrow> w + (1::hypint) \<le> z"
by transfer (rule zless_imp_add1_zle)

lemma hypint_less_iff_hSuc_add:
  "\<And>w z. (w :: hypint) < z \<longleftrightarrow> (\<exists>n. z = w + of_hypnat (hSuc n))"
by transfer (rule zless_iff_Suc_zadd)

lemma hypint_le_iff_add:
  "\<And>w z. (w :: hypint) \<le> z \<longleftrightarrow> (\<exists>n. z = w + of_hypnat n)"
by transfer (simp add: zle_iff_zadd)

lemma hypint_le_iff_diff:
  "\<And>w z. (w :: hypint) \<le> z \<longleftrightarrow> (\<exists>n. w = z - of_hypnat n)"
using hypint_le_iff_add by auto

lemma hypint_less_zero_eq_minus_of_hypnat: "x < (0::hypint) \<Longrightarrow> \<exists>n. x = - hypint_of_hypnat (n)"
by (metis minus_minus neg_0_less_iff_less zero_less_imp_eq_hypint)

lemma hypint_less_add1_eq: "\<And>w z. (w < z + (1::hypint)) = (w<z | w=z)"
by transfer (rule zless_add1_eq)

lemma add1_hypint_le_eq: "\<And>w z. (w + (1::hypint)\<le> z) = (w<z)"
by transfer (rule add1_zle_eq)

lemma hypint_le_diff1_eq [simp]: "\<And>w z. (w \<le> z - (1::hypint)) = (w<z)"
by transfer (rule zle_diff1_eq)

lemma hypint_le_add1_eq_le [simp]: "\<And>w z. (w < z + (1::hypint)) = (w \<le> z)"
by transfer (rule zle_add1_eq_le)

lemma hypint_one_le_iff_zero_less: "\<And>z. ((1::hypint) \<le> z) = (0 < z)"
by transfer (rule int_one_le_iff_zero_less)


subsection\<open>Embedding of the hyperintegers into other types\<close> 

definition
  of_hypint :: "hypint => 'a::linordered_idom star" where
  of_hypint_def [transfer_unfold]: "of_hypint = *f* of_int"

lemma of_hypint_of_int [simp]: "of_hypint (of_int z) = of_int z"
by transfer simp

lemma of_hypint_hypint_of_int [simp]: "of_hypint (hypint_of_int z) = of_int z"
by transfer simp

lemma of_hypint_of_hypnat [simp]: "\<And>z. of_hypint (of_hypnat z) = of_hypnat z"
by transfer simp

lemma of_hypint_of_nat [simp]: "of_hypint (of_nat z) = of_nat z"
by transfer simp

lemma of_hypint_0 [simp]: "of_hypint 0 = 0"
by transfer (rule of_int_0)

lemma of_hypint_1 [simp]: "of_hypint 1 = 1"
by transfer (rule of_int_1)

lemma of_hypint_add [simp]: "\<And>w z. of_hypint (w+z) = of_hypint w + of_hypint z"
by transfer (rule of_int_add)

lemma of_hypint_minus [simp]: "\<And>z. of_hypint (-z) = - (of_hypint z)"
by transfer (rule of_int_minus)

lemma of_hypint_diff [simp]: "\<And>w z. of_hypint (w - z) = of_hypint w - of_hypint z"
by transfer (rule of_int_diff)

lemma of_hypint_mult [simp]: "\<And>w z. of_hypint (w*z) = of_hypint w * of_hypint z"
by transfer (rule of_int_mult)

lemma of_hypint_of_nat_eq [simp]: "of_hypint (of_nat n) = of_nat n"
by (induct n) auto

lemma of_hypint_nat_power: "of_hypint (z ^ n) = of_hypint z ^ n"
  by (induct n) simp_all

lemma of_hypint_eq_iff [simp]:
   "\<And>w z. of_hypint w = of_hypint z \<longleftrightarrow> w = z"
by transfer (rule of_int_eq_iff)

lemma of_hypint_eq_0_iff [simp]:
  "\<And>z. of_hypint z = 0 \<longleftrightarrow> z = 0"
by transfer (rule of_int_eq_0_iff)

lemma of_hypint_0_eq_iff [simp]:
  "\<And>z. 0 = of_hypint z \<longleftrightarrow> z = 0"
by transfer (rule of_int_0_eq_iff)

lemma of_hypint_le_iff [simp]:
  "\<And> w z. of_hypint w \<le> of_hypint z \<longleftrightarrow> w \<le> z"
by transfer (rule of_int_le_iff)

lemma of_hypint_less_iff [simp]:
  "\<And>w z. of_hypint w < of_hypint z \<longleftrightarrow> w < z"
by transfer (rule of_int_less_iff)  

lemma of_hypint_0_le_iff [simp]:
  "\<And>z. 0 \<le> of_hypint z \<longleftrightarrow> 0 \<le> z"
by transfer (rule of_int_0_le_iff)

lemma of_hypint_le_0_iff [simp]:
  "\<And>z. of_hypint z \<le> 0 \<longleftrightarrow> z  \<le> 0"
by transfer (rule of_int_le_0_iff)

lemma of_hypint_0_less_iff [simp]:
  "\<And>z. 0 < of_hypint z \<longleftrightarrow> 0 < z"
by transfer (rule of_int_0_less_iff)

lemma of_hypint_less_0_iff [simp]:
  "\<And>z. of_hypint z < 0 \<longleftrightarrow> z < 0"
by transfer (rule of_int_less_0_iff)  

lemma of_hypint_abs: "\<And>z. of_hypint (abs z) = abs(of_hypint z)"
by transfer (simp add: abs_if)

lemma of_hypint_add_one: "of_hypint z + (1 :: real star) = of_hypint (z + 1)"
by (metis of_hypint_1 of_hypint_add)

subsection\<open>Embedding the naturals into the hyperintegers\<close>

abbreviation
  hypint_of_nat :: "nat => hypint" where
  "hypint_of_nat == of_nat"

lemma HypintNat_eq: "Nats = {z. \<exists>N. z = hypint_of_nat N}"
by (simp add: Nats_def image_def)

lemma hypint_of_nat:
     "hypint_of_nat m = star_n (%n. int m)"
by (fold star_of_def) simp

lemma HypintNat_ge_zero: "n \<in> \<nat> \<Longrightarrow> 0 \<le> (n :: hypint)"
by (auto simp add: Nats_def)

lemma hypint_of_hypnat_hypint_of_nat_eq [simp]:
     "\<And>n. hypint_of_hypnat (hypnat_of_nat n) = hypint_of_nat n"
by (simp add: of_hypnat_def)

lemma abs_hypint_of_hypnat [simp]: "\<bar>hypint_of_hypnat n\<bar> = hypint_of_hypnat n"
  by (auto simp add: abs_if)

lemma hypint_abs_less_one_iff [simp]: "\<And>z. (\<bar>z\<bar> < 1) = (z = (0::hypint))"
by transfer simp

lemma abs_hypint_mult_eq_1:
    "\<And>m n. \<bar>m * n\<bar> = 1 \<Longrightarrow> \<bar>m\<bar> = (1::hypint)"
by transfer (rule abs_zmult_eq_1)
 
lemma pos_hypint_mult_eq_1_iff_lemma: 
    "\<And>m n. (m * n = 1) ==> m = (1::hypint) | m = -1"
by transfer (rule pos_zmult_eq_1_iff_lemma)

lemma pos_hypint_mult_eq_1_iff:
   "\<And>m n. 0 < (m::hypint) \<Longrightarrow> (m * n = 1) = (m = 1 \<and> n = 1)"
by transfer (rule pos_zmult_eq_1_iff)

lemma hypint_mult_eq_1_iff: 
   "\<And>m n. (m*n = (1::hypint)) = ((m = 1 \<and> n = 1) \<or> (m = -1 \<and> n = -1))"
by transfer (rule zmult_eq_1_iff)

subsection\<open>Magnitude of a hyperinteger\<close> 

definition
  hypnat :: "hypint => hypnat"
where
  [transfer_unfold]: "hypnat \<equiv> *f* nat"

lemma hypnat_hypint [simp]: "\<And>n. hypnat (of_hypnat n) = n"
by transfer simp

lemma hypnat_zero [simp]: "hypnat 0 = 0"
by transfer simp

lemma hypnat_one [simp]: "hypnat 1 = 1"
by (metis hypnat_hypint of_hypnat_1)

lemma hypint_hypnat_eq [simp]: "\<And>z. of_hypnat (hypnat z) = (if 0 \<le> z then z else 0)"
by transfer simp

corollary hypnat_0_le: "0 \<le> z \<Longrightarrow> of_hypnat (hypnat z) = z"
by simp

lemma hypnat_le_0 [simp]: "\<And>z. z \<le> 0 \<Longrightarrow> hypnat z = 0"
by transfer simp

lemma hypnat_le_eq_zle: "\<And>w z. 0 < w \<or> 0 \<le> z \<Longrightarrow> (hypnat w  \<le> hypnat z) = (w \<le> z)"
by transfer (rule nat_le_eq_zle)

corollary hypnat_mono_iff: "0 < z \<Longrightarrow> (hypnat w < hypnat z) = (w < z)"
by (simp add: hypnat_le_eq_zle linorder_not_le [symmetric])

corollary hypnat_less_eq_less: "0 \<le> w \<Longrightarrow> (hypnat w < hypnat z) = (w<z)"
by (simp add: hypnat_le_eq_zle linorder_not_le [symmetric])  

lemma less_hypnat_conj [simp]: "\<And>w z. (hypnat w < hypnat z) = (0 < z \<and> w < z)"
by transfer (rule zless_nat_conj)

lemma nonneg_eq_hypint:
  fixes z :: hypint
  assumes "0 \<le> z" and "\<And>m. z = of_hypnat m \<Longrightarrow> P"
  shows P
  using assms by (blast dest: hypnat_0_le sym)

lemma hypnat_eq_iff: 
  "\<And> m w. (hypnat w = m) = (if 0 \<le> w then w = of_hypnat m else m=0)"
by transfer (rule nat_eq_iff)

corollary hypnat_eq_iff2: "(m = hypnat w) = (if 0 \<le> w then w = of_hypnat m else m=0)"
by (simp only: eq_commute [of m] hypnat_eq_iff)

lemma hypnat_less_iff: "\<And>m w. 0 \<le> w \<Longrightarrow> (hypnat w < m) = (w < of_hypnat m)"
by transfer (rule nat_less_iff)

lemma hypnat_0_iff[simp]: "\<And>i. hypnat i = 0 \<longleftrightarrow> i\<le>0"
by transfer simp

lemma hypint_eq_iff: "(of_hypnat m = z) = (m = hypnat z \<and> 0 \<le> z)"
by (auto simp add: hypnat_eq_iff2)

lemma zero_less_hypnat_eq [simp]: "(0 < hypnat z) = (0 < z)"
by (insert less_hypnat_conj [of 0], auto)

lemma hypnat_add_distrib:
     "\<And>z z'. \<lbrakk> (0::hypint) \<le> z;  0 \<le> z' \<rbrakk> \<Longrightarrow> hypnat (z+z') = hypnat z + hypnat z'"
by transfer (rule nat_add_distrib)

lemma hypnat_diff_distrib:
     "\<And>z z'. \<lbrakk> (0::hypint) \<le> z';  z' \<le> z \<rbrakk> \<Longrightarrow> hypnat (z-z') = hypnat z - hypnat z'"
by transfer (rule nat_diff_distrib)

lemma hypnat_minus_hypint [simp]: "\<And>n. hypnat (- (of_hypnat n)) = 0"
by transfer simp

lemma less_hypnat_eq_hypint_less: "\<And>m z. (m < hypnat z) = (of_hypnat m < z)"
  by transfer (rule zless_nat_eq_int_zless)

lemma hypnat_add_one: "0 \<le> z \<Longrightarrow> hypnat z + (1 :: nat star) = hypnat (z + 1)"
by (metis hypint_eq_iff hypnat_add_distrib of_hypnat_1)

subsection\<open>The divides relation\<close>

lemma hypint_dvd_antisym_nonneg:
    "\<And>m n. 0 <= m \<Longrightarrow> 0 <= n \<Longrightarrow> m dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = (n::hypint)"
by transfer (rule zdvd_antisym_nonneg)
  
lemma  hypint_dvd_antisym_abs:
    "\<And>a b. \<lbrakk> (a::hypint) dvd b; b dvd a \<rbrakk> \<Longrightarrow> \<bar>a\<bar> = \<bar>b\<bar>"
by transfer (rule zdvd_antisym_abs)

lemma hyperint_dvd_diffD: "\<And>k m n. k dvd m - n \<Longrightarrow> k dvd n \<Longrightarrow> k dvd (m::hypint)"
by transfer (rule zdvd_zdiffD)

lemma hypint_dvd_reduce: "\<And>k m n. (k dvd n + k * m) = (k dvd (n::hypint))"
by transfer (rule zdvd_reduce)

lemma hypint_dvd_imp_le_hypint:
    "\<And>d i. \<lbrakk> i \<noteq> 0; d dvd (i::hypint) \<rbrakk> \<Longrightarrow> \<bar>d\<bar> \<le> \<bar>i\<bar>"
by transfer (rule dvd_imp_le_int)

lemma hypint_dvd_not_less:
    "\<And>m n. \<lbrakk> 0 < m; m < (n::hypint) \<rbrakk> \<Longrightarrow> \<not> n dvd m"
by transfer (rule zdvd_not_zless)

lemma hypint_dvd_mult_cancel: 
    "\<And>k m n. \<lbrakk> k * m dvd k * n; k \<noteq> (0::hypint) \<rbrakk> \<Longrightarrow> m dvd n"
by transfer (rule zdvd_mult_cancel)

theorem dvd_hypint_of_hypnat: 
  "\<And>x y. ((x::hypnat) dvd y) = ((hypint_of_hypnat x) dvd  (hypint_of_hypnat y))"
  by transfer simp

lemma hypint_dvd1_eq[simp]: "\<And>x. (x::hypint) dvd 1 = ( \<bar>x\<bar> = 1)"
by transfer (rule zdvd1_eq)

lemma hypint_dvd_mult_cancel1: 
  "\<And>m n. m \<noteq> (0::hypint) \<Longrightarrow> (m * n dvd m) = (\<bar>n\<bar> = 1)"
by transfer (rule zdvd_mult_cancel1)

lemma hypint_of_hypnat_dvd_iff: 
  "\<And>m z. ((of_hypnat m) dvd z) = (m dvd hypnat (abs z))"
  using dvd_hypint_of_hypnat by auto

lemma dvd_hypint_iff: "\<And>m z. (z dvd of_hypnat m) = (hypnat (abs z) dvd m)"
  using nat_abs_dvd_iff by transfer blast

lemma hypnat_dvd_iff: "(hypnat z dvd m) = (if 0 \<le> z then (z dvd of_hypnat m) else m = 0)"
  by (auto simp add: dvd_hypint_iff)

lemma eq_hypnat_hypnat_iff:
  "0 \<le> z \<Longrightarrow> 0 \<le> z' \<Longrightarrow> hypnat z = hypnat z' \<longleftrightarrow> z = z'"
  by (auto elim!: nonneg_eq_hypint)

lemma hypnat_power_eq:
  "\<And>z. 0 \<le> z \<Longrightarrow> hypnat (z ^ n) = hypnat z ^ n"
by transfer (rule nat_power_eq)

lemma hypint_dvd_imp_le: 
  "\<And>n z. \<lbrakk> z dvd n; 0 < n \<rbrakk> \<Longrightarrow> z \<le> (n::hypint)"
by transfer (rule zdvd_imp_le)

lemma hypint_period: 
  "\<And>a c d t x. (a::hypint) dvd d \<Longrightarrow> a dvd (x + t) \<longleftrightarrow> a dvd ((x + c * d) + t)"
by transfer (rule zdvd_period)

subsection\<open>Division on @{typ hypint}\<close> 

lemma hypint_of_nat_div: "hypint_of_nat(m div n) = hypint_of_nat m div (hypint_of_nat n)"
by transfer (simp add: zdiv_int)

lemma hypint_of_hypnat_div: "\<And>m n. hypint_of_hypnat(m div n) = hypint_of_hypnat m div (hypint_of_hypnat n)"
by transfer (simp add: zdiv_int)

lemma HypintNats_div: "\<lbrakk>(n::hypint) \<in> \<nat>; m \<in> \<nat> \<rbrakk> \<Longrightarrow> n div m \<in> \<nat>"
  by (metis Nats_cases hypint_of_nat_div of_nat_in_Nats)

lemma hypint_div_mono1: "\<And>a a' b. \<lbrakk> a \<le> a';  0 < (b::hypint) \<rbrakk> \<Longrightarrow> a div b  \<le> a' div b"
by transfer (rule zdiv_mono1)

lemma hypint_div_neg_pos_less0: "\<And>a b. \<lbrakk> a < (0::hypint);  0 < b \<rbrakk> \<Longrightarrow>  a div b < 0"
by transfer (rule div_neg_pos_less0)

lemma hypint_div_nonneg_neg_le0: "\<And>a b. \<lbrakk> (0::hypint) \<le> a; b < 0 \<rbrakk> \<Longrightarrow> a div b \<le> 0"
by transfer (rule div_nonneg_neg_le0)

lemma hypint_div_nonpos_pos_le0: "\<And>a b. \<lbrakk> (a::hypint) \<le> 0; b > 0 \<rbrakk> \<Longrightarrow> a div b  \<le> 0"
by transfer (rule div_nonpos_pos_le0)

lemma hypint_pos_imp_div_nonneg_iff: "\<And>a b. (0::hypint) < b \<Longrightarrow> (0 \<le> a div b) = (0 \<le> a)"
by transfer (rule pos_imp_zdiv_nonneg_iff)

lemma hypint_neg_imp_div_nonneg_iff:
  "\<And>a b. b < (0::hypint) \<Longrightarrow> (0  \<le> a div b) = (a \<le> (0::hypint))"
by transfer (rule neg_imp_zdiv_nonneg_iff)

lemma hypint_pos_imp_div_neg_iff: "\<And>a b. (0::hypint) < b \<Longrightarrow> (a div b < 0) = (a < 0)"
by transfer (rule pos_imp_zdiv_neg_iff)

lemma hypint_neg_imp_div_neg_iff: "\<And>a b. b < (0::hypint) \<Longrightarrow> (a div b < 0) = (0 < a)"
by transfer (rule neg_imp_zdiv_neg_iff)

lemma hypint_nonneg1_imp_div_pos_iff:
  "\<And>a b. (0::hypint) \<le> a \<Longrightarrow> (a div b > 0) = (a \<ge> b \<and> b > 0)"
by transfer (rule nonneg1_imp_zdiv_pos_iff)

subsection\<open>Properties of the set of embedded integers\<close>

lemma of_int_eq_star_of [simp]: "of_int = star_of"
proof
  fix z :: int
  show "of_int z = star_of z" by transfer simp
qed

lemma Ints_eq_Standard: "(\<int> :: int star set) = Standard"
by (auto simp add: Ints_def Standard_def)

lemma hypint_of_int_mem_Ints [simp]: "hypint_of_int z \<in> \<int>"
by (simp add: Ints_eq_Standard)

lemma hypint_of_nat_Suc [simp]:
     "hypint_of_nat (Suc n) = hypint_of_nat n + (1::hypint)"
by transfer simp

lemma of_int_eq_add [rule_format]:
     "\<forall>d::hypint. of_int m = of_int n + d \<longrightarrow> d \<in> range of_int"
  by (metis add_diff_cancel_left' of_int_diff rangeI)

subsection\<open>Infinite hyperintegers\<close>

definition
  (* the set of infinite hyperintegers *)
  HIntInfinite :: "hypint set" where
  "HIntInfinite = {z. z \<notin> \<int>}"

lemma Ints_not_HIntInfinite_iff: "(x \<in> Ints) = (x \<notin> HIntInfinite)"
by (simp add: HIntInfinite_def)

lemma HIntInfinite_not_Ints_iff: "(x \<in> HIntInfinite) = (x \<notin> Ints)"
by (simp add: HIntInfinite_def)

lemma star_of_neq_HIntInfinite: "Z \<in> HIntInfinite ==> star_of n \<noteq> Z"
by (metis HIntInfinite_not_Ints_iff Ints_of_int of_hypint_hypint_of_int 
     of_hypint_of_int of_int_eq_iff star_of_int_def)

lemma HIntInfinite_minus_iff [simp]: 
  "(- Z \<in> HIntInfinite) =  (Z \<in> HIntInfinite)"
by (metis Ints_minus Ints_not_HIntInfinite_iff minus_minus)


lemma star_of_less_pos_HIntInfinite:
  assumes "0 < Z" and "Z \<in> HIntInfinite"
  shows "star_of z < Z"
proof (cases "z \<ge> 0")
  case True
  then obtain n where z: "z = int n"
    using zero_le_imp_eq_int by blast
  have "hypint_of_int (int n) < Z"
  proof (induct n)
    case 0
    then show ?case
      by (simp add: assms(1)) 
  next
    case (Suc n)
    then show ?case
      by (metis assms(2) hypint_less_imp_add1_le hypint_of_nat_Suc 
          less_le star_of_neq_HIntInfinite star_of_of_nat) 
  qed
  then show ?thesis 
    using z by simp
next
  case False
  then obtain n where "z = - int (Suc n)"
    by (metis int_cases of_nat_0_le_iff)
  then show ?thesis
    by (metis False assms(1) le_less less_le_trans not_less star_of_less_0) 
qed

lemma star_of_gt_neg_HIntInfinite:
  assumes "Z < 0"
and  "Z \<in> HIntInfinite"
shows "Z < star_of z"
proof -
  have  "0 < - Z"
    by (simp add: assms(1))
  then show ?thesis using star_of_less_pos_HIntInfinite [of _ "-z"]
    using assms(2) by fastforce
qed

lemma zero_not_HIntInfinite [simp]: "0 \<notin> HIntInfinite"
by (metis HIntInfinite_not_Ints_iff Ints_0)

lemma star_of_less_abs_HIntInfinite:
  "Z \<in> HIntInfinite \<Longrightarrow> star_of z < abs Z"
by (auto intro: star_of_less_pos_HIntInfinite simp add: abs_if not_less le_less)

lemma hypint_of_nat_less_abs_HIntInfinite:
  "y \<in> HIntInfinite \<Longrightarrow> hypint_of_nat n < \<bar>y\<bar>"
by (metis star_of_less_abs_HIntInfinite star_of_nat_def)

lemma Ints_less_pos_HIntInfinite: "\<lbrakk> 0 < y; x \<in> \<int>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x < y"
by (auto simp add: Ints_def star_of_less_pos_HIntInfinite)

lemma Ints_gt_neg_HIntInfinite: "\<lbrakk> y < 0; x \<in> \<int>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> y < x"
by (auto simp add: Ints_def star_of_gt_neg_HIntInfinite)

lemma Ints_less_abs_HIntInfinite: "\<lbrakk> x \<in> \<int>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x < abs y"
by (auto simp add: Ints_def star_of_less_abs_HIntInfinite)

lemma Ints_le_abs_HIntInfinite: "\<lbrakk> x \<in> \<int>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x \<le> abs y"
by (metis Ints_less_abs_HIntInfinite less_imp_le)

lemma Nats_less_abs_HIntInfinite: "\<lbrakk> x \<in> \<nat>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x < abs y"
by (metis Nats_cases hypint_of_nat_less_abs_HIntInfinite)

lemma Nats_le_abs_HIntInfinite: "\<lbrakk> x \<in> \<nat>; y \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x < abs y"
by (metis Nats_less_abs_HIntInfinite)

lemma Ints_pos_downward_closed:
  "\<lbrakk> 0 \<le> y; x \<in> Ints; (y::hypint) \<le> x \<rbrakk> \<Longrightarrow> y \<in> \<int>"
  using HIntInfinite_not_Ints_iff Ints_le_abs_HIntInfinite by fastforce

lemma Ints_neg_upward_closed:
  "\<lbrakk> y \<le> 0; x \<in> Ints; x \<le> (y::hypint) \<rbrakk> \<Longrightarrow> y \<in> \<int>"
  by (metis HIntInfinite_not_Ints_iff Ints_0 Ints_gt_neg_HIntInfinite linorder_not_less order_le_less)

lemma HIntInfinite_pos_upward_closed:
  "\<lbrakk> 0 \<le> x; x \<in> HIntInfinite; x \<le> y \<rbrakk> \<Longrightarrow> y \<in> HIntInfinite"
by (auto intro: Ints_pos_downward_closed simp only: HIntInfinite_not_Ints_iff)

lemma HIntInfinite_neg_downward_closed:
  "\<lbrakk> x \<le> 0; x \<in> HIntInfinite; y \<le> x \<rbrakk> \<Longrightarrow> y \<in> HIntInfinite"
by (auto intro: Ints_neg_upward_closed simp only: HIntInfinite_not_Ints_iff)

lemma HIntInfinite_pos_add: 
  "\<lbrakk> 0 \<le> x; 0 \<le> y; x \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x + y \<in> HIntInfinite"
by (metis HIntInfinite_pos_upward_closed add_increasing2 order_refl)

lemma HIntInfinite_neg_add: 
  "\<lbrakk> x \<le> 0; y \<le> 0; x \<in> HIntInfinite \<rbrakk> \<Longrightarrow> x + y \<in> HIntInfinite"
by (metis HIntInfinite_neg_downward_closed add_0_iff add_le_cancel_left)

lemma HIntInfinite_add_Ints: 
  "\<lbrakk> x \<in> HIntInfinite; y \<in> Ints \<rbrakk> \<Longrightarrow> x + y \<in> HIntInfinite"
  by (metis HIntInfinite_not_Ints_iff Ints_diff add.commute add_diff_cancel_left')

lemma HIntInfinite_diff: 
  "\<lbrakk> x \<in> HIntInfinite; y \<in> Ints \<rbrakk> \<Longrightarrow> x - y \<in> HIntInfinite"
by (metis HIntInfinite_not_Ints_iff Ints_add diff_add_cancel)

lemma Ints_def2: "\<int> = {z. \<exists>Z. z = hypint_of_int Z}"
by (auto simp add: Ints_def)

lemma HIntInfinite_hypint_of_hypnat_iff:
  "(hypint_of_hypnat n \<in> HIntInfinite) = (n \<in> HNatInfinite)"
proof 
  assume "hypint_of_hypnat n \<in> HIntInfinite" 
  then show "n \<in> HNatInfinite"
    using HNatInfinite_not_Nats_iff SHNat_eq hypint_of_nat_less_abs_HIntInfinite by force
next
  assume "n \<in> HNatInfinite"
  then have "\<forall>N. n \<noteq> hypnat_of_nat N"
    using star_of_neq_HNatInfinite by blast
  then show "hypint_of_hypnat n \<in> HIntInfinite"
    by (metis Ifun_star_of Ints_cases Ints_not_HIntInfinite_iff hypnat_def 
        hypnat_hypint of_int_eq_star_of starfun_def)
qed

lemma two_hyperpow_ge_one [simp]: "(1::hypint)  \<le> 2 pow n"
  by (simp add: hyperpow_gt_zero hypint_one_le_iff_zero_less)

subsection\<open>Embedding of hypertintegers in hyperreals\<close>

abbreviation
  hypreal_of_hypint :: "hypint \<Rightarrow> hypreal" where
  "hypreal_of_hypint \<equiv> of_hypint"

lemma of_hypint_numeral [simp]: "of_hypint (numeral v) = numeral v"
by transfer simp

lemma real_of_int_le_real_of_nat_iff: "(real_of_int a \<le> real_of_nat b) = (a \<le> int b)"
proof 
  assume "real_of_int a \<le> real b" then show "a \<le> int b"
    by auto 
next
  assume "a \<le> int b" then show "real_of_int a \<le> real b"
    by linarith 
qed

lemma minus_real_of_int_le_real_of_nat_iff: "(- real_of_int a \<le> real_of_nat b) = (- a \<le> int b)"
  by linarith

lemma hypreal_of_hypint_le_hypreal_of_hypnat_iff:
      "\<And>a b.(hypreal_of_hypint a \<le> of_hypnat b) = (a \<le> of_hypnat b)"
by transfer (auto simp add: real_of_int_le_real_of_nat_iff)

lemma minus_hypreal_of_hypint_le_hypreal_of_hypnat_iff:
      "\<And>a b.(- hypreal_of_hypint a \<le> hypreal_of_hypnat b) = (- a \<le> of_hypnat b)"
by transfer (auto simp add: minus_real_of_int_le_real_of_nat_iff)

lemma hnorm_of_hypint [simp]:  
   "\<And>z. hnorm (of_hypint z::'a::{real_normed_algebra_1, linordered_idom} star) = abs(of_hypint z)"
  by transfer simp

lemma of_hypnat_hypnat [simp]: "\<And>z. 0 \<le> z \<Longrightarrow> of_hypnat(hypnat z) = of_hypint z"
  by transfer simp

(* Move to NSA.thy if HyperInt is moved before NSA.thy *)
lemma HInfinite_def3: "HInfinite = {x. \<forall>z \<in> Ints. hypreal_of_hypint z < hnorm x}"
proof (auto simp add: HInfinite_def2)
  fix x::"'a :: real_normed_vector star" and z::"int star"
  assume less_hnorm: "\<forall>n\<in>\<nat>. hypreal_of_hypnat n < hnorm x" and z: "z \<in> \<int>"
  then obtain z' where "z = of_int z'"
    using Ints_cases by blast
  moreover have  "\<forall>n. hypreal_of_nat n < hnorm x"
    using less_hnorm of_nat_in_Nats by fastforce
  moreover have "of_int z' < hnorm x" using less_hnorm
    by (metis calculation(2) hnorm_ge_zero less_le_trans nonneg_int_cases not_le 
        of_int_less_0_iff of_int_of_nat_eq)
  ultimately show "hypreal_of_hypint z < hnorm x"
    by simp
next
  fix x::"'a :: real_normed_vector star" and n::"nat star"
  assume less_hnorm: "\<forall>z\<in>\<int>. hypreal_of_hypint z < hnorm x" and n: "n \<in> \<nat>"
  then have "hypint_of_hypnat n \<in> \<int>"
    by (metis Nats_cases hypint_of_hypnat_hypint_of_nat_eq hypint_of_int_mem_Ints star_of_nat_def)
  then have "hypreal_of_hypint (hypint_of_hypnat n) < hnorm x"
    using  less_hnorm by blast
  then show "hypreal_of_hypnat n < hnorm x"
    by simp
qed

lemma HInfinite_of_hypint_HNatInfinite_hypnat:
  "\<lbrakk> (of_hypint x :: 'a::{real_normed_algebra_1,linordered_idom} star) \<in> HInfinite; x > 0 \<rbrakk> 
       \<Longrightarrow> hypnat x \<in> HNatInfinite"
by (rule nonneg_eq_hypint [of x], auto simp add: HNatInfinite_of_hypnat_HInfinite_iff)

lemma HNatInfinite_hypnat_HInfinite_of_hypint:
  "hypnat x \<in> HNatInfinite 
      \<Longrightarrow> (of_hypint x :: 'a::{real_normed_algebra_1,linordered_idom} star) \<in> HInfinite"
  by (metis HNatInfinite_of_hypnat_HInfinite_iff hypnat_eq_iff2 of_hypint_of_hypnat 
      zero_not_mem_HNatInfinite)

end