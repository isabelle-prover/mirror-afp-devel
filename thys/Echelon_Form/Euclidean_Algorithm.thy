(* Author: Manuel Eberl *)

(* Slightly modified by Jose Divasón*)

(*This is the file developed by Manuel Eberl presented in the Isabelle repository version 
  (http://isabelle.in.tum.de/repos/isabelle/file/62826b36ac5e/src/HOL/Number_Theory/Euclidean_Algorithm.thy)
  but slightly modified by Jose Divasón.

  Most of theorems proved over the euclidean_semiring_gcd and euclidean_ring_gcd classes have now 
  been proven over the euclidean_semiring and euclidean_ring ones. Then, lemmas are now stated using 
  gcd_eucl, lcm_eucl, Gcd_eucl, Lcm_eucl instead of gcd, lcm, Gcd and Lcm.

  The final aim is to prove the following instances:

  instantiation nat :: euclidean_semiring_gcd
  instantiation int :: euclidean_ring_gcd
  instantiation poly :: (field) euclidean_ring
  instantiation poly :: (field) euclidean_ring_gcd

  In order to do that, I have moved some results presented in the euclidean_semiring_gcd class 
  to the euclidean_semiring class. Since it is proved that nat and int are euclidean_semiring, then 
  it will be possible to use such lemmas while proving that nat and int are euclidean_semiring_gcd.

  For instance, the following lemma was proven in the euclidean_semiring_gcd class:
  
  context euclidean_semiring_gcd
  begin
  
  lemma gcd_red:
     "gcd x y = gcd y (x mod y)"
    by (metis gcd_eucl.simps mod_0 mod_by_0 gcd_gcd_eucl)
  
  end
  
  Now, I have moved it to the euclidean_semiring class (obviously, I have had to replace 
    gcd with gcd_eucl).
  
  context euclidean_semiring
  begin
  
  lemma gcd_eucl_red:
     "gcd_eucl x y = gcd_eucl y (x mod y)"
    by (metis gcd_eucl.simps mod_0 mod_by_0)
  
  end
  
  Finally, in order to preserve the previous theorem:
  
  context euclidean_semiring_gcd
  begin
  
  lemmas gcd_red = gcd_eucl_red[unfolded gcd_gcd_eucl[symmetric]]
  
  end
  
  This process has been applied to 140 lemmas approximately.
  In the file Euclidean_Algorithm_Extension are proven the instances we aimed.

*)

section {* Abstract euclidean algorithm *}

theory Euclidean_Algorithm
imports Complex_Main
begin

lemma finite_int_set_iff_bounded_le:
  "finite (N::int set) = (\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m)"
proof
  assume "finite (N::int set)"
  hence "finite (nat ` abs ` N)" by (intro finite_imageI)
  hence "\<exists>m. \<forall>n\<in>nat`abs`N. n \<le> m" by (simp add: finite_nat_set_iff_bounded_le)
  then obtain m :: nat where "\<forall>n\<in>N. nat (abs n) \<le> nat (int m)" by auto
  then show "\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m" by (intro exI[of _ "int m"]) (auto simp: nat_le_eq_zle)
next
  assume "\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m"
  then obtain m where "m \<ge> 0" and "\<forall>n\<in>N. abs n \<le> m" by blast
  hence "\<forall>n\<in>N. nat (abs n) \<le> nat m" by (auto simp: nat_le_eq_zle)
  hence "\<forall>n\<in>nat`abs`N. n \<le> nat m" by (auto simp: nat_le_eq_zle)
  hence A: "finite ((nat \<circ> abs)`N)" unfolding o_def 
      by (subst finite_nat_set_iff_bounded_le) blast
  {
    assume "\<not>finite N"
    from pigeonhole_infinite[OF this A] obtain x 
       where "x \<in> N" and B: "~finite {a\<in>N. nat (abs a) = nat (abs x)}" 
       unfolding o_def by blast
    have "{a\<in>N. nat (abs a) = nat (abs x)} \<subseteq> {x, -x}" by auto
    hence "finite {a\<in>N. nat (abs a) = nat (abs x)}" by (rule finite_subset) simp
    with B have False by contradiction
  }
  then show "finite N" by blast
qed

context semiring_div
begin

lemmas dvd_setprod = dvd_setprodI

lemma dvd_mult_cancel_left:
  assumes "a \<noteq> 0" and "a * b dvd a * c"
  shows "b dvd c"
proof-
  from assms(2) obtain k where "a * c = a * b * k" unfolding dvd_def by blast
  hence "c * a = b * k * a" by (simp add: ac_simps)
  hence "c * (a div a) = b * k * (a div a)" by auto
  also from `a \<noteq> 0` have "a div a = 1" by simp
  finally show ?thesis by simp
qed

lemma dvd_mult_cancel_right:
  "a \<noteq> 0 \<Longrightarrow> b * a dvd c * a \<Longrightarrow> b dvd c"
  by (subst (asm) (1 2) ac_simps, rule dvd_mult_cancel_left)

lemma nonzero_pow_nonzero:
  "a \<noteq> 0 \<Longrightarrow> a ^ n \<noteq> 0"
  by (fact power_not_zero)

lemma zero_pow_zero: "n \<noteq> 0 \<Longrightarrow> 0 ^ n = 0"
  by (cases n, simp_all)

lemma pow_zero_iff:
  "n \<noteq> 0 \<Longrightarrow> a ^ n = 0 \<longleftrightarrow> a = 0"
  by simp

end

context semiring_div
begin 

definition ring_inv :: "'a \<Rightarrow> 'a"
where
  "ring_inv x = 1 div x"

definition is_unit :: "'a \<Rightarrow> bool"
where
  "is_unit x \<longleftrightarrow> x dvd 1"

definition associated :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "associated x y \<longleftrightarrow> x dvd y \<and> y dvd x"

lemma unit_prod [intro]:
  "is_unit x \<Longrightarrow> is_unit y \<Longrightarrow> is_unit (x * y)"
  unfolding is_unit_def by (subst mult_1_left [of 1, symmetric], rule mult_dvd_mono) 

lemma unit_ring_inv:
  "is_unit y \<Longrightarrow> x div y = x * ring_inv y"
  by (simp add: div_mult_swap ring_inv_def is_unit_def)

lemma unit_ring_inv_ring_inv [simp]:
  "is_unit x \<Longrightarrow> ring_inv (ring_inv x) = x"
  unfolding is_unit_def ring_inv_def
  by (metis div_mult_mult1_if div_mult_self1_is_id dvd_mult_div_cancel mult_1_right)

lemma inv_imp_eq_ring_inv:
  "a * b = 1 \<Longrightarrow> ring_inv a = b"
  by (metis dvd_mult_div_cancel dvd_mult_right mult_1_right mult.left_commute one_dvd ring_inv_def)

lemma ring_inv_is_inv1 [simp]:
  "is_unit a \<Longrightarrow> a * ring_inv a = 1"
  unfolding is_unit_def ring_inv_def by simp

lemma ring_inv_is_inv2 [simp]:
  "is_unit a \<Longrightarrow> ring_inv a * a = 1"
  by (simp add: ac_simps)

lemma unit_ring_inv_unit [simp, intro]:
  assumes "is_unit x"
  shows "is_unit (ring_inv x)"
proof -
  from assms have "1 = ring_inv x * x" by simp
  then show "is_unit (ring_inv x)" unfolding is_unit_def by (rule dvdI)
qed

lemma mult_unit_dvd_iff:
  "is_unit y \<Longrightarrow> x * y dvd z \<longleftrightarrow> x dvd z"
proof
  assume "is_unit y" "x * y dvd z"
  then show "x dvd z" by (simp add: dvd_mult_left)
next
  assume "is_unit y" "x dvd z"
  then obtain k where "z = x * k" unfolding dvd_def by blast
  with `is_unit y` have "z = (x * y) * (ring_inv y * k)" 
      by (simp add: mult_ac)
  then show "x * y dvd z" by (rule dvdI)
qed

lemma div_unit_dvd_iff:
  "is_unit y \<Longrightarrow> x div y dvd z \<longleftrightarrow> x dvd z"
  by (subst unit_ring_inv) (assumption, simp add: mult_unit_dvd_iff)

lemma dvd_mult_unit_iff:
  "is_unit y \<Longrightarrow> x dvd z * y \<longleftrightarrow> x dvd z"
proof
  assume "is_unit y" and "x dvd z * y"
  have "z * y dvd z * (y * ring_inv y)" by (subst mult_assoc [symmetric]) simp
  also from `is_unit y` have "y * ring_inv y = 1" by simp
  finally have "z * y dvd z" by simp
  with `x dvd z * y` show "x dvd z" by (rule dvd_trans)
next
  assume "x dvd z"
  then show "x dvd z * y" by simp
qed

lemma dvd_div_unit_iff:
  "is_unit y \<Longrightarrow> x dvd z div y \<longleftrightarrow> x dvd z"
  by (subst unit_ring_inv) (assumption, simp add: dvd_mult_unit_iff)

lemmas unit_dvd_iff = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff dvd_div_unit_iff

lemma unit_div [intro]:
  "is_unit x \<Longrightarrow> is_unit y \<Longrightarrow> is_unit (x div y)"
  by (subst unit_ring_inv) (assumption, rule unit_prod, simp_all)

lemma unit_div_mult_swap:
  "is_unit z \<Longrightarrow> x * (y div z) = x * y div z"
  by (simp only: unit_ring_inv [of _ y] unit_ring_inv [of _ "x*y"] ac_simps)

lemma unit_div_commute:
  "is_unit y \<Longrightarrow> x div y * z = x * z div y"
  by (simp only: unit_ring_inv [of _ x] unit_ring_inv [of _ "x*z"] ac_simps)

lemma unit_imp_dvd [dest]:
  "is_unit y \<Longrightarrow> y dvd x"
  by (rule dvd_trans [of _ 1]) (simp_all add: is_unit_def)

lemma dvd_unit_imp_unit:
  "is_unit y \<Longrightarrow> x dvd y \<Longrightarrow> is_unit x"
  by (unfold is_unit_def) (rule dvd_trans)

lemma ring_inv_0 [simp]:
  "ring_inv 0 = 0"
  unfolding ring_inv_def by simp

lemma unit_ring_inv'1:
  assumes "is_unit y"
  shows "x div (y * z) = x * ring_inv y div z" 
proof -
  from assms have "x div (y * z) = x * (ring_inv y * y) div (y * z)"
    by simp
  also have "... = y * (x * ring_inv y) div (y * z)"
    by (simp only: mult_ac)
  also have "... = x * ring_inv y div z"
    by (cases "y = 0", simp, rule div_mult_mult1)
  finally show ?thesis .
qed

lemma associated_comm:
  "associated x y \<Longrightarrow> associated y x"
  by (simp add: associated_def)

lemma associated_0 [simp]:
  "associated 0 b \<longleftrightarrow> b = 0"
  "associated a 0 \<longleftrightarrow> a = 0"
  unfolding associated_def by simp_all

lemma associated_unit:
  "is_unit x \<Longrightarrow> associated x y \<Longrightarrow> is_unit y"
  unfolding associated_def by (auto dest: dvd_unit_imp_unit)

lemma is_unit_1 [simp]:
  "is_unit 1"
  unfolding is_unit_def by simp

lemma not_is_unit_0 [simp]:
  "\<not> is_unit 0"
  unfolding is_unit_def by auto

lemma unit_mult_left_cancel:
  assumes "is_unit x"
  shows "(x * y) = (x * z) \<longleftrightarrow> y = z"
proof -
  from assms have "x \<noteq> 0" by auto
  then show ?thesis by (metis div_mult_self1_is_id)
qed

lemma unit_mult_right_cancel:
  "is_unit x \<Longrightarrow> (y * x) = (z * x) \<longleftrightarrow> y = z"
  by auto

lemma unit_div_cancel:
  "is_unit x \<Longrightarrow> (y div x) = (z div x) \<longleftrightarrow> y = z"
  apply (subst unit_ring_inv[of _ y], assumption)
  apply (subst unit_ring_inv[of _ z], assumption)
  apply (rule unit_mult_right_cancel, erule unit_ring_inv_unit)
  done

lemma unit_eq_div1:
  "is_unit y \<Longrightarrow> x div y = z \<longleftrightarrow> x = z * y"
  apply (subst unit_ring_inv, assumption)
  apply (subst unit_mult_right_cancel[symmetric], assumption)
  apply (subst mult_assoc, subst ring_inv_is_inv2, assumption, simp)
  done

lemma unit_eq_div2:
  "is_unit y \<Longrightarrow> x = z div y \<longleftrightarrow> x * y = z"
  by (subst (1 2) eq_commute, simp add: unit_eq_div1, subst eq_commute, rule refl)

lemma associated_iff_div_unit:
  "associated x y \<longleftrightarrow> (\<exists>z. is_unit z \<and> x = z * y)"
proof
  assume "associated x y"
  show "\<exists>z. is_unit z \<and> x = z * y"
  proof (cases "x = 0")
    assume "x = 0"
    then show "\<exists>z. is_unit z \<and> x = z * y" using `associated x y`
        by (intro exI[of _ 1], simp add: associated_def)
  next
    assume [simp]: "x \<noteq> 0"
    hence [simp]: "x dvd y" "y dvd x" using `associated x y`
        unfolding associated_def by simp_all
    hence "1 = x div y * (y div x)"
      by (simp add: div_mult_swap)
    hence "is_unit (x div y)" unfolding is_unit_def by (rule dvdI)
    moreover have "x = (x div y) * y" by simp
    ultimately show ?thesis by blast
  qed
next
  assume "\<exists>z. is_unit z \<and> x = z * y"
  then obtain z where "is_unit z" and "x = z * y" by blast
  hence "y = x * ring_inv z" by (simp add: algebra_simps)
  hence "x dvd y" by simp
  moreover from `x = z * y` have "y dvd x" by simp
  ultimately show "associated x y" unfolding associated_def by simp
qed

lemmas unit_simps = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff 
  dvd_div_unit_iff unit_div_mult_swap unit_div_commute
  unit_mult_left_cancel unit_mult_right_cancel unit_div_cancel 
  unit_eq_div1 unit_eq_div2

end

context ring_div
begin

lemma is_unit_neg [simp]:
  "is_unit (- x) \<Longrightarrow> is_unit x"
  unfolding is_unit_def by simp

lemma is_unit_neg_1 [simp]:
  "is_unit (-1)"
  unfolding is_unit_def by simp

end

lemma is_unit_nat [simp]:
  "is_unit (x::nat) \<longleftrightarrow> x = 1"
  unfolding is_unit_def by simp

lemma is_unit_int:
  "is_unit (x::int) \<longleftrightarrow> x = 1 \<or> x = -1"
  unfolding is_unit_def by auto

text {*
  A Euclidean semiring is a semiring upon which the Euclidean algorithm can be
  implemented. It must provide:
  \begin{itemize}
  \item division with remainder
  \item a size function such that @{term "size (a mod b) < size b"} 
        for any @{term "b \<noteq> 0"}
  \item a normalisation factor such that two associated numbers are equal iff 
        they are the same when divided by their normalisation factors.
  \end{itemize}
  The existence of these functions makes it possible to derive gcd and lcm functions 
  for any Euclidean semiring.
*} 

class euclidean_semiring = semiring_div + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  fixes normalisation_factor :: "'a \<Rightarrow> 'a"
  assumes mod_size_less [simp]: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a * b) \<ge> euclidean_size a"
  assumes normalisation_factor_is_unit [intro,simp]: 
    "a \<noteq> 0 \<Longrightarrow> is_unit (normalisation_factor a)"
  assumes normalisation_factor_mult: "normalisation_factor (a * b) = 
    normalisation_factor a * normalisation_factor b"
  assumes normalisation_factor_unit: "is_unit x \<Longrightarrow> normalisation_factor x = x"
  assumes normalisation_factor_0 [simp]: "normalisation_factor 0 = 0"
begin

lemma normalisation_factor_dvd [simp]:
  "a \<noteq> 0 \<Longrightarrow> normalisation_factor a dvd b"
  by (rule unit_imp_dvd, simp)
    
lemma normalisation_factor_1 [simp]:
  "normalisation_factor 1 = 1"
  by (simp add: normalisation_factor_unit)

lemma normalisation_factor_0_iff [simp]:
  "normalisation_factor x = 0 \<longleftrightarrow> x = 0"
proof
  assume "normalisation_factor x = 0"
  hence "\<not> is_unit (normalisation_factor x)"
    by (metis not_is_unit_0)
  then show "x = 0" by force
next
  assume "x = 0"
  then show "normalisation_factor x = 0" by simp
qed

lemma normalisation_factor_pow:
  "normalisation_factor (x ^ n) = normalisation_factor x ^ n"
  by (induct n) (simp_all add: normalisation_factor_mult power_Suc2)

lemma normalisation_correct [simp]:
  "normalisation_factor (x div normalisation_factor x) = (if x = 0 then 0 else 1)"
proof (cases "x = 0", simp)
  assume "x \<noteq> 0"
  let ?nf = "normalisation_factor"
  from normalisation_factor_is_unit[OF `x \<noteq> 0`] have "?nf x \<noteq> 0"
    by (metis not_is_unit_0) 
  have "?nf (x div ?nf x) * ?nf (?nf x) = ?nf (x div ?nf x * ?nf x)" 
    by (simp add: normalisation_factor_mult)
  also have "x div ?nf x * ?nf x = x" using `x \<noteq> 0`
    by simp
  also have "?nf (?nf x) = ?nf x" using `x \<noteq> 0` 
    normalisation_factor_is_unit normalisation_factor_unit by simp
  finally show ?thesis using `x \<noteq> 0` and `?nf x \<noteq> 0` 
    by (metis div_mult_self2_is_id div_self)
qed

lemma normalisation_0_iff [simp]:
  "x div normalisation_factor x = 0 \<longleftrightarrow> x = 0"
  by (cases "x = 0", simp, subst unit_eq_div1, blast, simp)

lemma associated_iff_normed_eq:
  "associated a b \<longleftrightarrow> a div normalisation_factor a = b div normalisation_factor b"
proof (cases "b = 0", simp, cases "a = 0", metis associated_0(1) normalisation_0_iff, rule iffI)
  let ?nf = normalisation_factor
  assume "a \<noteq> 0" "b \<noteq> 0" "a div ?nf a = b div ?nf b"
  hence "a = b * (?nf a div ?nf b)"
    apply (subst (asm) unit_eq_div1, blast, subst (asm) unit_div_commute, blast)
    apply (subst div_mult_swap, simp, simp)
    done
  with `a \<noteq> 0` `b \<noteq> 0` have "\<exists>z. is_unit z \<and> a = z * b"
    by (intro exI[of _ "?nf a div ?nf b"], force simp: mult_ac)
  with associated_iff_div_unit show "associated a b" by simp
next
  let ?nf = normalisation_factor
  assume "a \<noteq> 0" "b \<noteq> 0" "associated a b"
  with associated_iff_div_unit obtain z where "is_unit z" and "a = z * b" by blast
  then show "a div ?nf a = b div ?nf b"
    apply (simp only: `a = z * b` normalisation_factor_mult normalisation_factor_unit)
    apply (rule div_mult_mult1, force)
    done
  qed

lemma normed_associated_imp_eq:
  "associated a b \<Longrightarrow> normalisation_factor a \<in> {0, 1} \<Longrightarrow> normalisation_factor b \<in> {0, 1} \<Longrightarrow> a = b"
  by (simp add: associated_iff_normed_eq, elim disjE, simp_all)
    
lemmas normalisation_factor_dvd_iff [simp] =
  unit_dvd_iff [OF normalisation_factor_is_unit]

lemma euclidean_division:
  fixes a :: 'a and b :: 'a
  assumes "b \<noteq> 0"
  obtains s and t where "a = s * b + t" 
    and "euclidean_size t < euclidean_size b"
proof -
  from div_mod_equality[of a b 0] 
     have "a = a div b * b + a mod b" by simp
  with that and assms show ?thesis by force
qed

lemma dvd_euclidean_size_eq_imp_dvd:
  assumes "a \<noteq> 0" and b_dvd_a: "b dvd a" and size_eq: "euclidean_size a = euclidean_size b"
  shows "a dvd b"
proof (subst dvd_eq_mod_eq_0, rule ccontr)
  assume "b mod a \<noteq> 0"
  from b_dvd_a have b_dvd_mod: "b dvd b mod a" by (simp add: dvd_mod_iff)
  from b_dvd_mod obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with `b mod a \<noteq> 0` have "c \<noteq> 0" by auto
  with `b mod a = b * c` have "euclidean_size (b mod a) \<ge> euclidean_size b"
      using size_mult_mono by force
  moreover from `a \<noteq> 0` have "euclidean_size (b mod a) < euclidean_size a"
      using mod_size_less by blast
  ultimately show False using size_eq by simp
qed

function gcd_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "gcd_eucl a b = (if b = 0 then a div normalisation_factor a else gcd_eucl b (a mod b))"
  by (pat_completeness, simp)
termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

declare gcd_eucl.simps [simp del]

lemma gcd_induct: "\<lbrakk>\<And>b. P b 0; \<And>a b. 0 \<noteq> b \<Longrightarrow> P b (a mod b) \<Longrightarrow> P a b\<rbrakk> \<Longrightarrow> P a b"
proof (induct a b rule: gcd_eucl.induct)
  case ("1" m n)
    then show ?case by (cases "n = 0") auto
qed

definition lcm_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "lcm_eucl a b = a * b div (gcd_eucl a b * normalisation_factor (a * b))"

  (* Somewhat complicated definition of Lcm that has the advantage of working
     for infinite sets as well *)

definition Lcm_eucl :: "'a set \<Rightarrow> 'a"
where
  "Lcm_eucl A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) then
     let l = SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l =
       (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n)
       in l div normalisation_factor l
      else 0)"

definition Gcd_eucl :: "'a set \<Rightarrow> 'a"
where
  "Gcd_eucl A = Lcm_eucl {d. \<forall>a\<in>A. d dvd a}"

end

class euclidean_semiring_gcd = euclidean_semiring + gcd + Gcd +
  assumes gcd_gcd_eucl: "gcd = gcd_eucl" and lcm_lcm_eucl: "lcm = lcm_eucl"
  assumes Gcd_Gcd_eucl: "Gcd = Gcd_eucl" and Lcm_Lcm_eucl: "Lcm = Lcm_eucl"
begin
end

(* The following lemmas  were proven in the euclidean_semiring_gcd class, 
   Now they have been proven in the euclidean_semiring one*)

context euclidean_semiring
begin

lemma gcd_eucl_red:
   "gcd_eucl x y = gcd_eucl y (x mod y)"
  by (metis gcd_eucl.simps mod_0 mod_by_0)

lemma gcd_eucl_non_0:
  "y \<noteq> 0 \<Longrightarrow> gcd_eucl x y = gcd_eucl y (x mod y)"
  by (rule gcd_eucl_red)

lemma gcd_eucl_0_left:
  "gcd_eucl 0 x = x div normalisation_factor x"
  by (subst gcd_eucl.simps, subst gcd_eucl.simps, simp add: Let_def)

lemma gcd_eucl_0:
  "gcd_eucl x 0 = x div normalisation_factor x"
   by (subst gcd_eucl.simps, subst gcd_eucl.simps, simp add: Let_def)

lemma gcd_eucl_dvd1 [iff]: "gcd_eucl x y dvd x"
  and gcd_eucl_dvd2 [iff]: "gcd_eucl x y dvd y"
proof (induct x y rule: gcd_eucl.induct)
  fix x y :: 'a
  assume IH1: "y \<noteq> 0 \<Longrightarrow> gcd_eucl y (x mod y) dvd y"
  assume IH2: "y \<noteq> 0 \<Longrightarrow> gcd_eucl y (x mod y) dvd (x mod y)"
  
  have "gcd_eucl x y dvd x \<and> gcd_eucl x y dvd y"
  proof (cases "y = 0")
    case True
      then show ?thesis by (cases "x = 0", simp_all add: gcd_eucl_0)
  next
    case False
      with IH1 and IH2 show ?thesis by (simp add: gcd_eucl_non_0 dvd_mod_iff)
  qed
  then show "gcd_eucl x y dvd x" "gcd_eucl x y dvd y" by simp_all
qed

lemma dvd_gcd_eucl_D1: "k dvd gcd_eucl m n \<Longrightarrow> k dvd m"
  by (rule dvd_trans, assumption, rule gcd_eucl_dvd1)

lemma dvd_gcd_eucl_D2: "k dvd gcd_eucl m n \<Longrightarrow> k dvd n"
  by (rule dvd_trans, assumption, rule gcd_eucl_dvd2)

lemma gcd_eucl_greatest:
  fixes k x y :: 'a
  shows "k dvd x \<Longrightarrow> k dvd y \<Longrightarrow> k dvd gcd_eucl x y"
proof (induct x y rule: gcd_eucl.induct)
  case (1 x y)
  show ?case
    proof (cases "y = 0")
      assume "y = 0"
      with 1 show ?thesis by (cases "x = 0", simp_all add: gcd_eucl_0)
    next
      assume "y \<noteq> 0"
      with 1 show ?thesis by (simp add: gcd_eucl_non_0 dvd_mod_iff) 
    qed
qed

lemma dvd_gcd_eucl_iff:
  "k dvd gcd_eucl x y \<longleftrightarrow> k dvd x \<and> k dvd y"
  by (blast intro!: gcd_eucl_greatest intro: dvd_trans)

lemmas gcd_eucl_greatest_iff = dvd_gcd_eucl_iff

lemma gcd_eucl_zero [simp]:
  "gcd_eucl x y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (metis dvd_0_left dvd_refl gcd_eucl_dvd1 gcd_eucl_dvd2 gcd_eucl_greatest)+

lemma normalisation_factor_gcd_eucl [simp]:
  "normalisation_factor (gcd_eucl x y) = (if x = 0 \<and> y = 0 then 0 else 1)" (is "?f x y = ?g x y")
proof (induct x y rule: gcd_eucl.induct)
  fix x y :: 'a
  assume IH: "y \<noteq> 0 \<Longrightarrow> ?f y (x mod y) = ?g y (x mod y)"
  then show "?f x y = ?g x y" by (cases "y = 0", auto simp: gcd_eucl_non_0 gcd_eucl_0)
qed

lemma gcd_euclI:
  "k dvd x \<Longrightarrow> k dvd y \<Longrightarrow> (\<And>l. l dvd x \<Longrightarrow> l dvd y \<Longrightarrow> l dvd k)
    \<Longrightarrow> normalisation_factor k = (if k = 0 then 0 else 1) \<Longrightarrow> k = gcd_eucl x y"
  by (intro normed_associated_imp_eq) (auto simp: associated_def intro: gcd_eucl_greatest)

sublocale gcd: abel_semigroup gcd_eucl
proof
  fix x y z 
  show "gcd_eucl (gcd_eucl x y) z = gcd_eucl x (gcd_eucl y z)"
  proof (rule gcd_euclI)
    have "gcd_eucl (gcd_eucl x y) z dvd gcd_eucl x y" "gcd_eucl x y dvd x" by simp_all
    then show "gcd_eucl (gcd_eucl x y) z dvd x" by (rule dvd_trans)
    have "gcd_eucl (gcd_eucl x y) z dvd gcd_eucl x y" "gcd_eucl x y dvd y" by simp_all
    hence "gcd_eucl (gcd_eucl x y) z dvd y" by (rule dvd_trans)
    moreover have "gcd_eucl (gcd_eucl x y) z dvd z" by simp
    ultimately show "gcd_eucl (gcd_eucl x y) z dvd gcd_eucl y z"
      by (rule gcd_eucl_greatest)
    show "normalisation_factor (gcd_eucl (gcd_eucl x y) z) =  (if gcd_eucl (gcd_eucl x y) z = 0 then 0 else 1)"
      by auto
    fix l assume "l dvd x" and "l dvd gcd_eucl y z"
    with dvd_trans[OF _ gcd_eucl_dvd1] and dvd_trans[OF _ gcd_eucl_dvd2]
      have "l dvd y" and "l dvd z" by blast+
    with `l dvd x` show "l dvd gcd_eucl (gcd_eucl x y) z"
      by (intro gcd_eucl_greatest)
  qed
next
  fix x y
  show "gcd_eucl x y = gcd_eucl y x"
    by (rule gcd_euclI) (simp_all add: gcd_eucl_greatest)
qed

lemma gcd_eucl_unique: "d dvd a \<and> d dvd b \<and> 
    normalisation_factor d = (if d = 0 then 0 else 1) \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd_eucl a b"
  by (rule, auto intro: gcd_euclI simp: gcd_eucl_greatest)

lemma gcd_eucl_dvd_prod: "gcd_eucl a b dvd k * b"
  using mult_dvd_mono [of 1] by auto

lemma gcd_eucl_1_left [simp]: "gcd_eucl 1 x = 1"
  by (rule sym, rule gcd_euclI, simp_all)

lemma gcd_eucl_1 [simp]: "gcd_eucl x 1 = 1"
  by (rule sym, rule gcd_euclI, simp_all)

lemma gcd_eucl_proj2_if_dvd: 
  "y dvd x \<Longrightarrow> gcd_eucl x y = y div normalisation_factor y"
  by (cases "y = 0", simp_all add: dvd_eq_mod_eq_0 gcd_eucl_non_0 gcd_eucl_0)

lemma gcd_eucl_proj1_if_dvd: 
  "x dvd y \<Longrightarrow> gcd_eucl x y = x div normalisation_factor x"
  by (subst gcd.commute, simp add: gcd_eucl_proj2_if_dvd)

lemma gcd_eucl_proj1_iff: "gcd_eucl m n = m div normalisation_factor m \<longleftrightarrow> m dvd n"
proof
  assume A: "gcd_eucl m n = m div normalisation_factor m"
  show "m dvd n"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = gcd_eucl m n * normalisation_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp add: mult_unit_dvd_iff)
  qed (insert A, simp)
next
  assume "m dvd n"
  then show "gcd_eucl m n = m div normalisation_factor m" by (rule gcd_eucl_proj1_if_dvd)
qed
  
lemma gcd_eucl_proj2_iff: "gcd_eucl m n = n div normalisation_factor n \<longleftrightarrow> n dvd m"
  by (subst gcd.commute, simp add: gcd_eucl_proj1_iff)

lemma gcd_eucl_mod1 [simp]:
  "gcd_eucl (x mod y) y = gcd_eucl x y"
  by (rule gcd_euclI, metis dvd_mod_iff gcd_eucl_dvd1 gcd_eucl_dvd2, simp_all add: gcd_eucl_greatest dvd_mod_iff)

lemma gcd_eucl_mod2 [simp]:
  "gcd_eucl x (y mod x) = gcd_eucl x y"
  by (rule gcd_euclI, simp, metis dvd_mod_iff gcd_eucl_dvd1 gcd_eucl_dvd2, simp_all add: gcd_eucl_greatest dvd_mod_iff)
         
lemma normalisation_factor_dvd' [simp]:
  "normalisation_factor x dvd x"
  by (cases "x = 0", simp_all)

lemma gcd_eucl_mult_distrib': 
  "k div normalisation_factor k * gcd_eucl x y = gcd_eucl (k*x) (k*y)"
proof (induct x y rule: gcd_eucl.induct)
  case (1 x y)
  show ?case
  proof (cases "y = 0")
    case True
    then show ?thesis by (simp add: normalisation_factor_mult gcd_eucl_0 algebra_simps div_mult_div_if_dvd)
  next
    case False
    hence "k div normalisation_factor k * gcd_eucl x y =  gcd_eucl (k * y) (k * (x mod y))" 
      using 1 by (subst gcd_eucl_red, simp)
    also have "... = gcd_eucl (k * x) (k * y)"
      by (simp add: mult_mod_right gcd.commute)
    finally show ?thesis .
  qed
qed

lemma gcd_eucl_mult_distrib:
  "k * gcd_eucl x y = gcd_eucl (k*x) (k*y) * normalisation_factor k"
proof-
  let ?nf = "normalisation_factor"
  from gcd_eucl_mult_distrib' 
    have "gcd_eucl (k*x) (k*y) = k div ?nf k * gcd_eucl x y" ..
  also have "... = k * gcd_eucl x y div ?nf k"
    by (metis dvd_div_mult dvd_eq_mod_eq_0 mod_0 normalisation_factor_dvd)
  finally show ?thesis
    by (simp add: ac_simps)
qed

lemma euclidean_size_gcd_eucl_le1 [simp]:
  assumes "a \<noteq> 0"
  shows "euclidean_size (gcd_eucl a b) \<le> euclidean_size a"
proof -
   have "gcd_eucl a b dvd a" by (rule gcd_eucl_dvd1)
   then obtain c where A: "a = gcd_eucl a b * c" unfolding dvd_def by blast
   with `a \<noteq> 0` show ?thesis by (subst (2) A, intro size_mult_mono) auto
qed

lemma euclidean_size_gcd_eucl_le2 [simp]:
  "b \<noteq> 0 \<Longrightarrow> euclidean_size (gcd_eucl a b) \<le> euclidean_size b"
  by (subst gcd.commute, rule euclidean_size_gcd_eucl_le1)

lemma euclidean_size_gcd_eucl_less1:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size (gcd_eucl a b) < euclidean_size a"
proof (rule ccontr)
  assume "\<not>euclidean_size (gcd_eucl a b) < euclidean_size a"
  with `a \<noteq> 0` have "euclidean_size (gcd_eucl a b) = euclidean_size a"
    by (intro le_antisym, simp_all)
  with assms have "a dvd gcd_eucl a b" by (auto intro: dvd_euclidean_size_eq_imp_dvd)
  hence "a dvd b" using dvd_gcd_eucl_D2 by blast
  with `\<not>a dvd b` show False by contradiction
qed

lemma euclidean_size_gcd_eucl_less2:
  assumes "b \<noteq> 0" and "\<not>b dvd a"
  shows "euclidean_size (gcd_eucl a b) < euclidean_size b"
  using assms by (subst gcd.commute, rule euclidean_size_gcd_eucl_less1)

lemma gcd_eucl_mult_unit1: "is_unit a \<Longrightarrow> gcd_eucl (x*a) y = gcd_eucl x y"
  apply (rule gcd_euclI)
  apply (rule dvd_trans, rule gcd_eucl_dvd1, simp add: unit_simps)
  apply (rule gcd_eucl_dvd2)
  apply (rule gcd_eucl_greatest, simp add: unit_simps, assumption)
  apply (subst normalisation_factor_gcd_eucl, simp add: gcd_eucl_0)
  done

lemma gcd_eucl_mult_unit2: "is_unit a \<Longrightarrow> gcd_eucl x (y*a) = gcd_eucl x y"
  by (subst gcd.commute, subst gcd_eucl_mult_unit1, assumption, rule gcd.commute)

lemma gcd_eucl_div_unit1: "is_unit a \<Longrightarrow> gcd_eucl (x div a) y = gcd_eucl x y"
  by (simp add: unit_ring_inv gcd_eucl_mult_unit1)

lemma gcd_eucl_div_unit2: "is_unit a \<Longrightarrow> gcd_eucl x (y div a) = gcd_eucl x y"
  by (simp add: unit_ring_inv gcd_eucl_mult_unit2)

lemma gcd_eucl_idem: "gcd_eucl x x = x div normalisation_factor x"
  by (cases "x = 0") (simp add: gcd_eucl_0_left, rule sym, rule gcd_euclI, simp_all)

lemma gcd_eucl_right_idem: "gcd_eucl (gcd_eucl p q) q = gcd_eucl p q"
  apply (rule gcd_euclI)
  apply (simp add: ac_simps)
  apply (rule gcd_eucl_dvd2)
  apply (rule gcd_eucl_greatest, erule (1) gcd_eucl_greatest, assumption)
  apply (simp)
  done

lemma gcd_eucl_left_idem: "gcd_eucl p (gcd_eucl p q) = gcd_eucl p q"
  apply (rule gcd_euclI)
  apply simp
  apply (rule dvd_trans, rule gcd_eucl_dvd2, rule gcd_eucl_dvd2)
  apply (rule gcd_eucl_greatest, assumption, erule gcd_eucl_greatest, assumption)
  apply (simp)
  done

lemma comp_fun_idem_gcd_eucl: "comp_fun_idem gcd_eucl"
proof
  fix a b show "gcd_eucl a \<circ> gcd_eucl b = gcd_eucl b \<circ> gcd_eucl a"
    by (simp add: fun_eq_iff ac_simps)
next
  fix a show "gcd_eucl a \<circ> gcd_eucl a = gcd_eucl a"
    by (simp add: fun_eq_iff gcd_eucl_left_idem)
qed

lemma coprime_dvd_mult:
  assumes "gcd_eucl k n = 1" and "k dvd m * n"
  shows "k dvd m"
proof -
  let ?nf = "normalisation_factor"
  from assms gcd_eucl_mult_distrib [of m k n] 
    have A: "m = gcd_eucl (m * k) (m * n) * ?nf m" by simp
  from `k dvd m * n` show ?thesis by (subst A, simp_all add: gcd_eucl_greatest)
qed

lemma coprime_dvd_mult_iff:
  "gcd_eucl k n = 1 \<Longrightarrow> (k dvd m * n) = (k dvd m)"
  by (rule, rule coprime_dvd_mult, simp_all)

lemma gcd_eucl_dvd_antisym:
  "gcd_eucl a b dvd gcd_eucl c d \<Longrightarrow> gcd_eucl c d dvd gcd_eucl a b \<Longrightarrow> gcd_eucl a b = gcd_eucl c d"
proof (rule gcd_euclI)
  assume A: "gcd_eucl a b dvd gcd_eucl c d" and B: "gcd_eucl c d dvd gcd_eucl a b"
  have "gcd_eucl c d dvd c" by simp
  with A show "gcd_eucl a b dvd c" by (rule dvd_trans)
  have "gcd_eucl c d dvd d" by simp
  with A show "gcd_eucl a b dvd d" by (rule dvd_trans)
  show "normalisation_factor (gcd_eucl a b) = (if gcd_eucl a b = 0 then 0 else 1)"
    by simp
  fix l assume "l dvd c" and "l dvd d"
  hence "l dvd gcd_eucl c d" by (rule gcd_eucl_greatest)
  from this and B show "l dvd gcd_eucl a b" by (rule dvd_trans)
qed

lemma gcd_eucl_mult_cancel:
  assumes "gcd_eucl k n = 1"
  shows "gcd_eucl (k * m) n = gcd_eucl m n"
proof (rule gcd_eucl_dvd_antisym)
  have "gcd_eucl (gcd_eucl (k * m) n) k = gcd_eucl (gcd_eucl k n) (k * m)" by (simp add: ac_simps)
  also note `gcd_eucl k n = 1`
  finally have "gcd_eucl (gcd_eucl (k * m) n) k = 1" by simp
  hence "gcd_eucl (k * m) n dvd m" by (rule coprime_dvd_mult, simp add: ac_simps)
  moreover have "gcd_eucl (k * m) n dvd n" by simp
  ultimately show "gcd_eucl (k * m) n dvd gcd_eucl m n" by (rule gcd_eucl_greatest)
  have "gcd_eucl m n dvd (k * m)" and "gcd_eucl m n dvd n" by simp_all
  then show "gcd_eucl m n dvd gcd_eucl (k * m) n" by (rule gcd_eucl_greatest)
qed

lemma coprime_crossproduct:
  assumes [simp]: "gcd_eucl a d = 1" "gcd_eucl b c = 1"
  shows "associated (a * c) (b * d) \<longleftrightarrow> associated a b \<and> associated c d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs then show ?lhs unfolding associated_def by (fast intro: mult_dvd_mono)
next
  assume ?lhs
  from `?lhs` have "a dvd b * d" unfolding associated_def by (metis dvd_mult_left) 
  hence "a dvd b" by (simp add: coprime_dvd_mult_iff)
  moreover from `?lhs` have "b dvd a * c" unfolding associated_def by (metis dvd_mult_left) 
  hence "b dvd a" by (simp add: coprime_dvd_mult_iff)
  moreover from `?lhs` have "c dvd d * b" 
    unfolding associated_def by (metis dvd_mult_right mult_commute)
  hence "c dvd d" by (simp add: coprime_dvd_mult_iff gcd.commute)
  moreover from `?lhs` have "d dvd c * a"
    unfolding associated_def by (metis dvd_mult_right mult_commute)
  hence "d dvd c" by (simp add: coprime_dvd_mult_iff gcd.commute)
  ultimately show ?rhs unfolding associated_def by simp
qed

lemma gcd_eucl_add1 [simp]:
  "gcd_eucl (m + n) n = gcd_eucl m n"
  by (cases "n = 0", simp_all add: gcd_eucl_non_0)

lemma gcd_eucl_add2 [simp]:
  "gcd_eucl m (m + n) = gcd_eucl m n"
  using gcd_eucl_add1 [of n m] by (simp add: ac_simps)

lemma gcd_eucl_add_mult: "gcd_eucl m (k * m + n) = gcd_eucl m n"
  by (subst gcd.commute, subst gcd_eucl_red, simp)

lemma coprimeI: "(\<And>l. \<lbrakk>l dvd x; l dvd y\<rbrakk> \<Longrightarrow> l dvd 1) \<Longrightarrow> gcd_eucl x y = 1"
  by (rule sym, rule gcd_euclI, simp_all)

lemma coprime: "gcd_eucl a b = 1 \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> is_unit d)"
  by (auto simp: is_unit_def intro: coprimeI gcd_eucl_greatest dvd_gcd_eucl_D1 dvd_gcd_eucl_D2)

lemma div_gcd_eucl_coprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  defines [simp]: "d \<equiv> gcd_eucl a b"
  defines [simp]: "a' \<equiv> a div d" and [simp]: "b' \<equiv> b div d"
  shows "gcd_eucl a' b' = 1"
proof (rule coprimeI)
  fix l assume "l dvd a'" "l dvd b'"
  then obtain s t where "a' = l * s" "b' = l * t" unfolding dvd_def by blast
  moreover have "a = a' * d" "b = b' * d" by (simp_all add: dvd_div_mult_self)
  ultimately have "a = (l * d) * s" "b = (l * d) * t"
    by (metis ac_simps)+
  hence "l*d dvd a" and "l*d dvd b" by (simp_all only: dvd_triv_left)
  hence "l*d dvd d" by (simp add: gcd_eucl_greatest)
  then obtain u where "u * l * d = d" unfolding dvd_def
    by (metis mult.left_commute mult_commute)
  moreover from nz have "d \<noteq> 0" by simp
  ultimately have "u * l = 1"
    by (metis div_mult_self1_is_id div_self ac_simps)
  then show "l dvd 1" by force
qed

lemma coprime_mult: 
  assumes da: "gcd_eucl d a = 1" and db: "gcd_eucl d b = 1"
  shows "gcd_eucl d (a * b) = 1"
  apply (subst gcd.commute)
  using da apply (subst gcd_eucl_mult_cancel)
  apply (subst gcd.commute, assumption)
  apply (subst gcd.commute, rule db)
  done

lemma coprime_lmult:
  assumes dab: "gcd_eucl d (a * b) = 1" 
  shows "gcd_eucl d a = 1"
proof (rule coprimeI)
  fix l assume "l dvd d" and "l dvd a"
  hence "l dvd a * b" by simp
  with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_eucl_greatest)
qed

lemma coprime_rmult:
  assumes dab: "gcd_eucl d (a * b) = 1"
  shows "gcd_eucl d b = 1"
proof (rule coprimeI)
  fix l assume "l dvd d" and "l dvd b"
  hence "l dvd a * b" by simp
  with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_eucl_greatest)
qed

lemma coprime_mul_eq: "gcd_eucl d (a * b) = 1 \<longleftrightarrow> gcd_eucl d a = 1 \<and> gcd_eucl d b = 1"
  using coprime_rmult[of d a b] coprime_lmult[of d a b] coprime_mult[of d a b] by blast

lemma gcd_eucl_coprime:
  assumes z: "gcd_eucl a b \<noteq> 0" and a: "a = a' * gcd_eucl a b" and b: "b = b' * gcd_eucl a b"
  shows "gcd_eucl a' b' = 1"
proof -
  from z have "a \<noteq> 0 \<or> b \<noteq> 0" by simp
  with div_gcd_eucl_coprime have "gcd_eucl (a div gcd_eucl a b) (b div gcd_eucl a b) = 1" .
  also from assms have "a div gcd_eucl a b = a'" by (metis div_mult_self2_is_id)+
  also from assms have "b div gcd_eucl a b = b'" by (metis div_mult_self2_is_id)+
  finally show ?thesis .
qed

lemma coprime_power:
  assumes "0 < n"
  shows "gcd_eucl a (b ^ n) = 1 \<longleftrightarrow> gcd_eucl a b = 1"
using assms proof (induct n)
  case (Suc n) then show ?case
    by (cases n) (simp_all add: coprime_mul_eq)
qed simp

lemma gcd_eucl_coprime_exists:
  assumes nz: "gcd_eucl a b \<noteq> 0"
  shows "\<exists>a' b'. a = a' * gcd_eucl a b \<and> b = b' * gcd_eucl a b \<and> gcd_eucl a' b' = 1"
  apply (rule_tac x = "a div gcd_eucl a b" in exI)
  apply (rule_tac x = "b div gcd_eucl a b" in exI)
  apply (insert nz, auto simp add: dvd_div_mult gcd_eucl_0_left intro: div_gcd_eucl_coprime)
  done


lemma coprime_exp:
  "gcd_eucl d a = 1 \<Longrightarrow> gcd_eucl d (a^n) = 1"
  by (induct n, simp_all add: coprime_mult)

lemma coprime_exp2 [intro]:
  "gcd_eucl a b = 1 \<Longrightarrow> gcd_eucl (a^n) (b^m) = 1"
  apply (rule coprime_exp)
  apply (subst gcd.commute)
  apply (rule coprime_exp)
  apply (subst gcd.commute)
  apply assumption
  done

lemma gcd_eucl_exp:
  "gcd_eucl (a^n) (b^n) = (gcd_eucl a b) ^ n"
proof (cases "a = 0 \<and> b = 0")
  assume "a = 0 \<and> b = 0"
  then show ?thesis by (cases n, simp_all add: gcd_eucl_0_left)
next
  assume A: "\<not>(a = 0 \<and> b = 0)"
  hence "1 = gcd_eucl ((a div gcd_eucl a b)^n) ((b div gcd_eucl a b)^n)"
    using div_gcd_eucl_coprime by (subst sym, auto simp: div_gcd_eucl_coprime)
  hence "(gcd_eucl a b) ^ n = (gcd_eucl a b) ^ n * ..." by simp
  also note gcd_eucl_mult_distrib
  also have "normalisation_factor ((gcd_eucl a b)^n) = 1"
    by (simp add: normalisation_factor_pow A)
  also have "(gcd_eucl a b)^n * (a div gcd_eucl a b)^n = a^n"
    by (subst ac_simps, subst div_power, simp, rule dvd_div_mult_self, rule dvd_power_same, simp)
  also have "(gcd_eucl a b)^n * (b div gcd_eucl a b)^n = b^n"
    by (subst ac_simps, subst div_power, simp, rule dvd_div_mult_self, rule dvd_power_same, simp)
  finally show ?thesis by simp
qed

lemma coprime_common_divisor: 
  "gcd_eucl a b = 1 \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> is_unit x"
  apply (subgoal_tac "x dvd gcd_eucl a b")
  apply (simp add: is_unit_def)
  apply (erule (1) gcd_eucl_greatest)
  done

lemma division_decomp: 
  assumes dc: "a dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof (cases "gcd_eucl a b = 0")
  assume "gcd_eucl a b = 0"
  hence "a = 0 \<and> b = 0" by simp
  hence "a = 0 * c \<and> 0 dvd b \<and> c dvd c" by simp
  then show ?thesis by blast
next
  let ?d = "gcd_eucl a b"
  assume "?d \<noteq> 0"
  from gcd_eucl_coprime_exists[OF this]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd_eucl a' b' = 1"
    by blast
  from ab'(1) have "a' dvd a" unfolding dvd_def by blast
  with dc have "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
  from dc ab'(1,2) have "a'*?d dvd (b'*?d) * c" by simp
  hence "?d * a' dvd ?d * (b' * c)" by (simp add: mult_ac)
  with `?d \<noteq> 0` have "a' dvd b' * c" by (rule dvd_mult_cancel_left)
  with coprime_dvd_mult[OF ab'(3)] 
    have "a' dvd c" by (subst (asm) ac_simps, blast)
  with ab'(1) have "a = ?d * a' \<and> ?d dvd b \<and> a' dvd c" by (simp add: mult_ac)
  then show ?thesis by blast
qed


lemma pow_divides_pow:
  assumes ab: "a ^ n dvd b ^ n" and n: "n \<noteq> 0"
  shows "a dvd b"
proof (cases "gcd_eucl a b = 0")
  assume "gcd_eucl a b = 0"
  then show ?thesis by simp
next
  let ?d = "gcd_eucl a b"
  assume "?d \<noteq> 0"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  from `?d \<noteq> 0` have zn: "?d ^ n \<noteq> 0" by (rule nonzero_pow_nonzero)
  from gcd_eucl_coprime_exists[OF `?d \<noteq> 0`]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd_eucl a' b' = 1"
    by blast
  from ab have "(a' * ?d) ^ n dvd (b' * ?d) ^ n"
    by (simp add: ab'(1,2)[symmetric])
  hence "?d^n * a'^n dvd ?d^n * b'^n"
    by (simp only: power_mult_distrib ac_simps)
  with zn have "a'^n dvd b'^n" by (rule dvd_mult_cancel_left)
  hence "a' dvd b'^n" using dvd_trans[of a' "a'^n" "b'^n"] by (simp add: m)
  hence "a' dvd b'^m * b'" by (simp add: m ac_simps)
  with coprime_dvd_mult[OF coprime_exp[OF ab'(3), of m]]
    have "a' dvd b'" by (subst (asm) ac_simps, blast)
  hence "a'*?d dvd b'*?d" by (rule mult_dvd_mono, simp)
  with ab'(1,2) show ?thesis by simp
qed

lemma pow_divides_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> a ^ n dvd b ^ n \<longleftrightarrow> a dvd b"
  by (auto intro: pow_divides_pow dvd_power_same)

lemma divides_mult:
  assumes mr: "m dvd r" and nr: "n dvd r" and mn: "gcd_eucl m n = 1"
  shows "m * n dvd r"
proof -
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: ac_simps)
  hence "m dvd n'" using coprime_dvd_mult_iff[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  with n' have "r = m * n * k" by (simp add: mult_ac)
  then show ?thesis unfolding dvd_def by blast
qed

lemma coprime_plus_one [simp]: "gcd_eucl (n + 1) n = 1"
  by (subst add_commute, simp)

lemma setprod_coprime [rule_format]:
  "(\<forall>i\<in>A. gcd_eucl (f i) x = 1) \<longrightarrow> gcd_eucl (\<Prod>i\<in>A. f i) x = 1"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto simp add: gcd_eucl_mult_cancel)
  done

lemma coprime_divisors: 
  assumes "d dvd a" "e dvd b" "gcd_eucl a b = 1"
  shows "gcd_eucl d e = 1" 
proof -
  from assms obtain k l where "a = d * k" "b = e * l"
    unfolding dvd_def by blast
  with assms have "gcd_eucl (d * k) (e * l) = 1" by simp
  hence "gcd_eucl (d * k) e = 1" by (rule coprime_lmult)
  also have "gcd_eucl (d * k) e = gcd_eucl e (d * k)" by (simp add: ac_simps)
  finally have "gcd_eucl e d = 1" by (rule coprime_lmult)
  then show ?thesis by (simp add: ac_simps)
qed

lemma invertible_coprime:
  "x * y mod m = 1 \<Longrightarrow> gcd_eucl x m = 1"
  by (metis coprime_lmult gcd_eucl_1 ac_simps gcd_eucl_red)

lemma lcm_eucl_gcd_eucl:
  "lcm_eucl a b = a * b div (gcd_eucl a b * normalisation_factor (a*b))"
  by (rule lcm_eucl_def)

lemma lcm_eucl_gcd_eucl_prod:
  "lcm_eucl a b * gcd_eucl a b = a * b div normalisation_factor (a*b)"
proof (cases "a * b = 0")
  let ?nf = normalisation_factor
  assume "a * b \<noteq> 0"
  hence "gcd_eucl a b \<noteq> 0" by auto
  from lcm_eucl_gcd_eucl have "lcm_eucl a b * gcd_eucl a b = gcd_eucl a b * (a * b div (?nf (a*b) * gcd_eucl a b))" 
    by (simp add: mult_ac)
  also from `a * b \<noteq> 0` have "... = a * b div ?nf (a*b)" 
    by (simp_all add: unit_ring_inv'1 unit_ring_inv)
  finally show ?thesis .
qed (auto simp add: lcm_eucl_gcd_eucl)

lemma lcm_eucl_dvd1 [iff]:
  "x dvd lcm_eucl x y"
proof (cases "x*y = 0")
  assume "x * y \<noteq> 0"
  hence "gcd_eucl x y \<noteq> 0" by (auto simp: gcd_eucl_zero)
  let ?c = "ring_inv (normalisation_factor (x*y))"
  from `x * y \<noteq> 0` have [simp]: "is_unit (normalisation_factor (x*y))" by simp
  from lcm_eucl_gcd_eucl_prod[of x y] have "lcm_eucl x y * gcd_eucl x y = x * ?c * y"
    by (simp add: mult_ac unit_ring_inv)
  hence "lcm_eucl x y * gcd_eucl x y div gcd_eucl x y = x * ?c * y div gcd_eucl x y" by simp
  with `gcd_eucl x y \<noteq> 0` have "lcm_eucl x y = x * ?c * y div gcd_eucl x y"
    by (subst (asm) div_mult_self2_is_id, simp_all)
  also have "... = x * (?c * y div gcd_eucl x y)"
    by (metis div_mult_swap gcd_eucl_dvd2 mult_assoc)
  finally show ?thesis by (rule dvdI)
qed (auto simp add: lcm_eucl_gcd_eucl)

lemma lcm_eucl_least:
  "\<lbrakk>a dvd k; b dvd k\<rbrakk> \<Longrightarrow> lcm_eucl a b dvd k"
proof (cases "k = 0")
  let ?nf = normalisation_factor
  assume "k \<noteq> 0"
  hence "is_unit (?nf k)" by simp
  hence "?nf k \<noteq> 0" by (metis not_is_unit_0)
  assume A: "a dvd k" "b dvd k"
  hence "gcd_eucl a b \<noteq> 0" using `k \<noteq> 0` by (auto simp add: gcd_eucl_zero)
  from A obtain r s where ar: "k = a * r" and bs: "k = b * s" 
    unfolding dvd_def by blast
  with `k \<noteq> 0` have "r * s \<noteq> 0"
    using divisors_zero mult_zero_right by fastforce 
  hence "is_unit (?nf (r * s))" by simp
  let ?c = "?nf k div ?nf (r*s)"
  from `is_unit (?nf k)` and `is_unit (?nf (r * s))` have "is_unit ?c" by (rule unit_div)
  hence "?c \<noteq> 0" using not_is_unit_0 by fast 
  from ar bs have "k * k * gcd_eucl s r = ?nf k * k * gcd_eucl (k * s) (k * r)"
    by (subst mult_assoc, subst gcd_eucl_mult_distrib[of k s r], simp only: ac_simps mult_assoc)
  also have "... = ?nf k * k * gcd_eucl ((r*s) * a) ((r*s) * b)"
    by (subst (3) `k = a * r`, subst (3) `k = b * s`, simp add: algebra_simps)
  also have "... = ?c * r*s * k * gcd_eucl a b" using `r * s \<noteq> 0`
    by (subst gcd_eucl_mult_distrib'[symmetric], simp add: algebra_simps unit_simps)
  finally have "(a*r) * (b*s) * gcd_eucl s r = ?c * k * r * s * gcd_eucl a b"
    by (subst ar[symmetric], subst bs[symmetric], simp add: mult_ac)
  hence "a * b * gcd_eucl s r * (r * s) = ?c * k * gcd_eucl a b * (r * s)"
    by (simp add: algebra_simps)
  hence "?c * k * gcd_eucl a b = a * b * gcd_eucl s r" using `r * s \<noteq> 0`
    by (metis div_mult_self2_is_id)
  also have "... = lcm_eucl a b * gcd_eucl a b * gcd_eucl s r * ?nf (a*b)"
    by (subst lcm_eucl_gcd_eucl_prod[of a b], metis gcd_eucl_mult_distrib gcd_eucl_mult_distrib') 
  also have "... = lcm_eucl a b * gcd_eucl s r * ?nf (a*b) * gcd_eucl a b"
    by (simp add: algebra_simps)
  finally have "k * ?c = lcm_eucl a b * gcd_eucl s r * ?nf (a*b)" using `gcd_eucl a b \<noteq> 0`
    by (metis mult.commute div_mult_self2_is_id)
  hence "k = lcm_eucl a b * (gcd_eucl s r * ?nf (a*b)) div ?c" using `?c \<noteq> 0`
    by (metis div_mult_self2_is_id mult_assoc) 
  also have "... = lcm_eucl a b * (gcd_eucl s r * ?nf (a*b) div ?c)" using `is_unit ?c`
    by (simp add: unit_simps)
  finally show ?thesis by (rule dvdI)
qed simp

lemma lcm_eucl_zero:
  "lcm_eucl a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
proof -
  let ?nf = normalisation_factor
  {
    assume "a \<noteq> 0" "b \<noteq> 0"
    hence "a * b div ?nf (a * b) \<noteq> 0" by (simp add: no_zero_divisors)
    moreover from `a \<noteq> 0` and `b \<noteq> 0` have "gcd_eucl a b \<noteq> 0" by (simp add: gcd_eucl_zero)
    ultimately have "lcm_eucl a b \<noteq> 0" using lcm_eucl_gcd_eucl_prod[of a b] by (intro notI, simp)
  } moreover {
    assume "a = 0 \<or> b = 0"
    hence "lcm_eucl a b = 0" by (elim disjE, simp_all add: lcm_eucl_gcd_eucl)
  }
  ultimately show ?thesis by blast
qed

lemmas lcm_eucl_0_iff = lcm_eucl_zero

lemma gcd_eucl_lcm_eucl: 
  assumes "lcm_eucl a b \<noteq> 0"
  shows "gcd_eucl a b = a * b div (lcm_eucl a b * normalisation_factor (a * b))"
proof-
  from assms have "gcd_eucl a b \<noteq> 0" by (simp add: gcd_eucl_zero lcm_eucl_zero)
  let ?c = "normalisation_factor (a*b)"
  from `lcm_eucl a b \<noteq> 0` have "?c \<noteq> 0" by (intro notI, simp add: lcm_eucl_zero no_zero_divisors)
  hence "is_unit ?c" by simp
  from lcm_eucl_gcd_eucl_prod [of a b] have "gcd_eucl a b = a * b div ?c div lcm_eucl a b"
    by (subst (2) div_mult_self2_is_id[OF `lcm_eucl a b \<noteq> 0`, symmetric], simp add: mult_ac)
  also from `is_unit ?c` have "... = a * b div (?c * lcm_eucl a b)"
    by (simp only: unit_ring_inv'1 unit_ring_inv)
  finally show ?thesis by (simp only: ac_simps)
qed

lemma normalisation_factor_lcm_eucl [simp]:
  "normalisation_factor (lcm_eucl a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis
    by (simp add: lcm_eucl_gcd_eucl) (metis div_0 ac_simps mult_zero_left normalisation_factor_0)
next
  case False
  let ?nf = normalisation_factor
  from lcm_eucl_gcd_eucl_prod[of a b] 
    have "?nf (lcm_eucl a b) * ?nf (gcd_eucl a b) = ?nf (a*b) div ?nf (a*b)"
    by (metis div_by_0 div_self normalisation_correct normalisation_factor_0 normalisation_factor_mult)
  also have "... = (if a*b = 0 then 0 else 1)"
    by auto
  finally show ?thesis using False by (simp add: no_zero_divisors)
qed

lemma lcm_eucl_dvd2 [iff]: "y dvd lcm_eucl x y"
  using lcm_eucl_dvd1 [of y x] by (simp add: lcm_eucl_gcd_eucl ac_simps)

lemma lcm_euclI:
  "\<lbrakk>x dvd k; y dvd k; \<And>l. x dvd l \<Longrightarrow> y dvd l \<Longrightarrow> k dvd l;
    normalisation_factor k = (if k = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> k = lcm_eucl x y"
  by (intro normed_associated_imp_eq) (auto simp: associated_def intro: lcm_eucl_least)

sublocale lcm: abel_semigroup lcm_eucl
proof
  fix x y z
  show "lcm_eucl (lcm_eucl x y) z = lcm_eucl x (lcm_eucl y z)"
  proof (rule lcm_euclI)
    have "x dvd lcm_eucl x y" and "lcm_eucl x y dvd lcm_eucl (lcm_eucl x y) z" by simp_all
    then show "x dvd lcm_eucl (lcm_eucl x y) z" by (rule dvd_trans)
    
    have "y dvd lcm_eucl x y" and "lcm_eucl x y dvd lcm_eucl (lcm_eucl x y) z" by simp_all
    hence "y dvd lcm_eucl (lcm_eucl x y) z" by (rule dvd_trans)
    moreover have "z dvd lcm_eucl (lcm_eucl x y) z" by simp
    ultimately show "lcm_eucl y z dvd lcm_eucl (lcm_eucl x y) z" by (rule lcm_eucl_least)

    fix l assume "x dvd l" and "lcm_eucl y z dvd l"
    have "y dvd lcm_eucl y z" by simp
    from this and `lcm_eucl y z dvd l` have "y dvd l" by (rule dvd_trans)
    have "z dvd lcm_eucl y z" by simp
    from this and `lcm_eucl y z dvd l` have "z dvd l" by (rule dvd_trans)
    from `x dvd l` and `y dvd l` have "lcm_eucl x y dvd l" by (rule lcm_eucl_least)
    from this and `z dvd l` show "lcm_eucl (lcm_eucl x y) z dvd l" by (rule lcm_eucl_least)
  qed (simp add: lcm_eucl_zero)
next
  fix x y
  show "lcm_eucl x y = lcm_eucl y x"
    by (simp add: lcm_eucl_gcd_eucl ac_simps)
qed

lemma dvd_lcm_eucl_D1:
  "lcm_eucl m n dvd k \<Longrightarrow> m dvd k"
  by (rule dvd_trans, rule lcm_eucl_dvd1, assumption)

lemma dvd_lcm_eucl_D2:
  "lcm_eucl m n dvd k \<Longrightarrow> n dvd k"
  by (rule dvd_trans, rule lcm_eucl_dvd2, assumption)

lemma gcd_eucl_dvd_lcm_eucl [simp]:
  "gcd_eucl a b dvd lcm_eucl a b"
  by (metis dvd_trans gcd_eucl_dvd2 lcm_eucl_dvd2)

lemma lcm_eucl_1_iff:
  "lcm_eucl a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
proof
  assume "lcm_eucl a b = 1"
  then show "is_unit a \<and> is_unit b" unfolding is_unit_def by auto
next
  assume "is_unit a \<and> is_unit b"
  hence "a dvd 1" and "b dvd 1" unfolding is_unit_def by simp_all
  hence "is_unit (lcm_eucl a b)" unfolding is_unit_def by (rule lcm_eucl_least)
  hence "lcm_eucl a b = normalisation_factor (lcm_eucl a b)"
    by (subst normalisation_factor_unit, simp_all)
  also have "\<dots> = 1" using `is_unit a \<and> is_unit b` by (auto simp add: is_unit_def)
  finally show "lcm_eucl a b = 1" .
qed

lemma lcm_eucl_0_left [simp]:
  "lcm_eucl 0 x = 0"
  by (rule sym, rule lcm_euclI, simp_all)

lemma lcm_eucl_0 [simp]:
  "lcm_eucl x 0 = 0"
  by (rule sym, rule lcm_euclI, simp_all)

lemma lcm_eucl_unique:
  "a dvd d \<and> b dvd d \<and> 
  normalisation_factor d = (if d = 0 then 0 else 1) \<and>
  (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm_eucl a b"
  by (rule, auto intro: lcm_euclI simp: lcm_eucl_least lcm_eucl_zero)

lemma dvd_lcm_eucl_I1 [simp]:
  "k dvd m \<Longrightarrow> k dvd lcm_eucl m n"
  by (metis lcm_eucl_dvd1 dvd_trans)

lemma dvd_lcm_eucl_I2 [simp]:
  "k dvd n \<Longrightarrow> k dvd lcm_eucl m n"
  by (metis lcm_eucl_dvd2 dvd_trans)

lemma lcm_eucl_1_left [simp]:
  "lcm_eucl 1 x = x div normalisation_factor x"
  by (cases "x = 0") (simp, rule sym, rule lcm_euclI, simp_all)

lemma lcm_eucl_1_right [simp]:
  "lcm_eucl x 1 = x div normalisation_factor x"
  by (simp add: ac_simps)

lemma lcm_eucl_coprime:
  "gcd_eucl a b = 1 \<Longrightarrow> lcm_eucl a b = a * b div normalisation_factor (a*b)"
  by (subst lcm_eucl_gcd_eucl) simp

lemma lcm_eucl_proj1_if_dvd: 
  "y dvd x \<Longrightarrow> lcm_eucl x y = x div normalisation_factor x"
  by (cases "x = 0") (simp, rule sym, rule lcm_euclI, simp_all)

lemma lcm_eucl_proj2_if_dvd: 
  "x dvd y \<Longrightarrow> lcm_eucl x y = y div normalisation_factor y"
  using lcm_eucl_proj1_if_dvd [of x y] by (simp add: ac_simps)

lemma lcm_eucl_proj1_iff:
  "lcm_eucl m n = m div normalisation_factor m \<longleftrightarrow> n dvd m"
proof
  assume A: "lcm_eucl m n = m div normalisation_factor m"
  show "n dvd m"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = lcm_eucl m n * normalisation_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp)
  qed simp
next
  assume "n dvd m"
  then show "lcm_eucl m n = m div normalisation_factor m" by (rule lcm_eucl_proj1_if_dvd)
qed

lemma lcm_eucl_proj2_iff:
  "lcm_eucl m n = n div normalisation_factor n \<longleftrightarrow> m dvd n"
  using lcm_eucl_proj1_iff [of n m] by (simp add: ac_simps)

lemma euclidean_size_lcm_eucl_le1: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "euclidean_size a \<le> euclidean_size (lcm_eucl a b)"
proof -
  have "a dvd lcm_eucl a b" by (rule lcm_eucl_dvd1)
  then obtain c where A: "lcm_eucl a b = a * c" unfolding dvd_def by blast
  with `a \<noteq> 0` and `b \<noteq> 0` have "c \<noteq> 0" by (auto simp: lcm_eucl_zero)
  then show ?thesis by (subst A, intro size_mult_mono)
qed

lemma euclidean_size_lcm_eucl_le2:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> euclidean_size b \<le> euclidean_size (lcm_eucl a b)"
  using euclidean_size_lcm_eucl_le1 [of b a] by (simp add: ac_simps)

lemma euclidean_size_lcm_eucl_less1:
  assumes "b \<noteq> 0" and "\<not>b dvd a"
  shows "euclidean_size a < euclidean_size (lcm_eucl a b)"
proof (rule ccontr)
  from assms have "a \<noteq> 0" by auto
  assume "\<not>euclidean_size a < euclidean_size (lcm_eucl a b)"
  with `a \<noteq> 0` and `b \<noteq> 0` have "euclidean_size (lcm_eucl a b) = euclidean_size a"
    by (intro le_antisym, simp, intro euclidean_size_lcm_eucl_le1)
  with assms have "lcm_eucl a b dvd a" 
    by (rule_tac dvd_euclidean_size_eq_imp_dvd) (auto simp: lcm_eucl_zero)
  hence "b dvd a" by (rule dvd_lcm_eucl_D2)
  with `\<not>b dvd a` show False by contradiction
qed

lemma euclidean_size_lcm_eucl_less2:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size b < euclidean_size (lcm_eucl a b)"
  using assms euclidean_size_lcm_eucl_less1 [of a b] by (simp add: ac_simps)

lemma lcm_eucl_mult_unit1:
  "is_unit a \<Longrightarrow> lcm_eucl (x*a) y = lcm_eucl x y"
  apply (rule lcm_euclI)
  apply (rule dvd_trans[of _ "x*a"], simp, rule lcm_eucl_dvd1)
  apply (rule lcm_eucl_dvd2)
  apply (rule lcm_eucl_least, simp add: unit_simps, assumption)
  apply (subst normalisation_factor_lcm_eucl, simp add: lcm_eucl_zero)
  done

lemma lcm_eucl_mult_unit2:
  "is_unit a \<Longrightarrow> lcm_eucl x (y*a) = lcm_eucl x y"
  using lcm_eucl_mult_unit1 [of a y x] by (simp add: ac_simps)

lemma lcm_eucl_div_unit1:
  "is_unit a \<Longrightarrow> lcm_eucl (x div a) y = lcm_eucl x y"
  by (simp add: unit_ring_inv lcm_eucl_mult_unit1)

lemma lcm_eucl_div_unit2:
  "is_unit a \<Longrightarrow> lcm_eucl x (y div a) = lcm_eucl x y"
  by (simp add: unit_ring_inv lcm_eucl_mult_unit2)

lemma lcm_eucl_left_idem:
  "lcm_eucl p (lcm_eucl p q) = lcm_eucl p q"
  apply (rule lcm_euclI)
  apply simp
  apply (subst lcm.assoc [symmetric], rule lcm_eucl_dvd2)
  apply (rule lcm_eucl_least, assumption)
  apply (erule (1) lcm_eucl_least)
  apply (auto simp: lcm_eucl_zero)
  done

lemma lcm_eucl_right_idem:
  "lcm_eucl (lcm_eucl p q) q = lcm_eucl p q"
  apply (rule lcm_euclI)
  apply (subst lcm.assoc, rule lcm_eucl_dvd1)
  apply (rule lcm_eucl_dvd2)
  apply (rule lcm_eucl_least, erule (1) lcm_eucl_least, assumption)
  apply (auto simp: lcm_eucl_zero)
  done

lemma comp_fun_idem_lcm_eucl: "comp_fun_idem lcm_eucl"
proof
  fix a b show "lcm_eucl a \<circ> lcm_eucl b = lcm_eucl b \<circ> lcm_eucl a"
    by (simp add: fun_eq_iff ac_simps)
next
  fix a show "lcm_eucl a \<circ> lcm_eucl a = lcm_eucl a" unfolding o_def
    by (intro ext, simp add: lcm_eucl_left_idem)
qed

lemma dvd_Lcm_eucl [simp]: "x \<in> A \<Longrightarrow> x dvd Lcm_eucl A"
  and Lcm_eucl_dvd [simp]: "(\<forall>x\<in>A. x dvd l') \<Longrightarrow> Lcm_eucl A dvd l'"
  and normalisation_factor_Lcm_eucl [simp]: 
          "normalisation_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)"
proof -
  have "(\<forall>x\<in>A. x dvd Lcm_eucl A) \<and> (\<forall>l'. (\<forall>x\<in>A. x dvd l') \<longrightarrow> Lcm_eucl A dvd l') \<and>
    normalisation_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)" (is ?thesis)
  proof (cases "\<exists>l. l \<noteq>  0 \<and> (\<forall>x\<in>A. x dvd l)")
    case False
    hence "Lcm_eucl A = 0" by (auto simp: Lcm_Lcm_eucl Lcm_eucl_def)
    with False show ?thesis by auto
  next
    case True
    then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l\<^sub>0)" by blast
    def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
    def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
    have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      apply (subst n_def)
      apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
      apply (rule exI[of _ l\<^sub>0])
      apply (simp add: l\<^sub>0_props)
      done
    from someI_ex[OF this] have "l \<noteq> 0" and "\<forall>x\<in>A. x dvd l" and "euclidean_size l = n" 
      unfolding l_def by simp_all
    {
      fix l' assume "\<forall>x\<in>A. x dvd l'"
      with `\<forall>x\<in>A. x dvd l` have "\<forall>x\<in>A. x dvd gcd_eucl l l'" by (auto intro: gcd_eucl_greatest)
      moreover from `l \<noteq> 0` have "gcd_eucl l l' \<noteq> 0" by simp
      ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd b) \<and> euclidean_size b = euclidean_size (gcd_eucl l l')"
        by (intro exI[of _ "gcd_eucl l l'"], auto)
      hence "euclidean_size (gcd_eucl l l') \<ge> n" by (subst n_def) (rule Least_le)
      moreover have "euclidean_size (gcd_eucl l l') \<le> n"
      proof -
        have "gcd_eucl l l' dvd l" by simp
        then obtain a where "l = gcd_eucl l l' * a" unfolding dvd_def by blast
        with `l \<noteq> 0` have "a \<noteq> 0" by auto
        hence "euclidean_size (gcd_eucl l l') \<le> euclidean_size (gcd_eucl l l' * a)"
          by (rule size_mult_mono)
        also have "gcd_eucl l l' * a = l" using `l = gcd_eucl l l' * a` ..
        also note `euclidean_size l = n`
        finally show "euclidean_size (gcd_eucl l l') \<le> n" .
      qed
      ultimately have "euclidean_size l = euclidean_size (gcd_eucl l l')" 
        by (intro le_antisym, simp_all add: `euclidean_size l = n`)
      with `l \<noteq> 0` have "l dvd gcd_eucl l l'" by (blast intro: dvd_euclidean_size_eq_imp_dvd)
      hence "l dvd l'" by (blast dest: dvd_gcd_eucl_D2)
    }

    with `(\<forall>x\<in>A. x dvd l)` and normalisation_factor_is_unit[OF `l \<noteq> 0`] and `l \<noteq> 0`
      have "(\<forall>x\<in>A. x dvd l div normalisation_factor l) \<and> 
        (\<forall>l'. (\<forall>x\<in>A. x dvd l') \<longrightarrow> l div normalisation_factor l dvd l') \<and>
        normalisation_factor (l div normalisation_factor l) = 
        (if l div normalisation_factor l = 0 then 0 else 1)"
      by (auto simp: unit_simps)
    also from True have "l div normalisation_factor l = Lcm_eucl A"
      by (simp add: Lcm_Lcm_eucl Lcm_eucl_def Let_def n_def l_def)
    finally show ?thesis .
  qed
  note A = this

  {fix x assume "x \<in> A" then show "x dvd Lcm_eucl A" using A by blast}
  {fix l' assume "\<forall>x\<in>A. x dvd l'" then show "Lcm_eucl A dvd l'" using A by blast}
  from A show "normalisation_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)" by blast
qed
    
lemma Lcm_euclI:
  "(\<And>x. x\<in>A \<Longrightarrow> x dvd l) \<Longrightarrow> (\<And>l'. (\<forall>x\<in>A. x dvd l') \<Longrightarrow> l dvd l') \<Longrightarrow>
      normalisation_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Lcm_eucl A"
  by (intro normed_associated_imp_eq)
    (auto intro: Lcm_eucl_dvd dvd_Lcm_eucl simp: associated_def)

lemma Lcm_eucl_subset:
  "A \<subseteq> B \<Longrightarrow> Lcm_eucl A dvd Lcm_eucl B"
  by (blast intro: Lcm_eucl_dvd dvd_Lcm_eucl)

lemma Lcm_eucl_Un:
  "Lcm_eucl (A \<union> B) = lcm_eucl (Lcm_eucl A) (Lcm_eucl B)"
  apply (rule lcm_euclI)
  apply (blast intro: Lcm_eucl_subset)
  apply (blast intro: Lcm_eucl_subset)
  apply (intro Lcm_eucl_dvd ballI, elim UnE)
  apply (rule dvd_trans, erule dvd_Lcm_eucl, assumption)
  apply (rule dvd_trans, erule dvd_Lcm_eucl, assumption)
  apply simp
  done

lemma Lcm_eucl_1_iff:
  "Lcm_eucl A = 1 \<longleftrightarrow> (\<forall>x\<in>A. is_unit x)"
proof
  assume "Lcm_eucl A = 1"
  then show "\<forall>x\<in>A. is_unit x" unfolding is_unit_def by auto
qed (rule Lcm_euclI [symmetric], auto)

lemma Lcm_eucl_no_units:
  "Lcm_eucl A = Lcm_eucl (A - {x. is_unit x})"
proof -
  have "(A - {x. is_unit x}) \<union> {x\<in>A. is_unit x} = A" by blast
  hence "Lcm_eucl A = lcm_eucl (Lcm_eucl (A - {x. is_unit x})) (Lcm_eucl {x\<in>A. is_unit x})"
    by (simp add: Lcm_eucl_Un[symmetric])
  also have "Lcm_eucl {x\<in>A. is_unit x} = 1" by (simp add: Lcm_eucl_1_iff)
  finally show ?thesis by simp
qed

lemma Lcm_eucl_empty [simp]:
  "Lcm_eucl {} = 1"
  by (simp add: Lcm_eucl_1_iff)

lemma Lcm_eucl_eq_0 [simp]:
  "0 \<in> A \<Longrightarrow> Lcm_eucl A = 0"
  by (drule dvd_Lcm_eucl) simp

lemma Lcm_eucl0_iff':
   "Lcm_eucl A = 0 \<longleftrightarrow> \<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))"
proof
  assume "Lcm_eucl A = 0"
  show "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))"
  proof
    assume ex: "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l)"
    then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l\<^sub>0)" by blast
    def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
    def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
    have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      apply (subst n_def)
      apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
      apply (rule exI[of _ l\<^sub>0])
      apply (simp add: l\<^sub>0_props)
      done
    from someI_ex[OF this] have "l \<noteq> 0" unfolding l_def by simp_all
    hence "l div normalisation_factor l \<noteq> 0" by simp
    also from ex have "l div normalisation_factor l = Lcm_eucl A"
       by (simp only: Lcm_Lcm_eucl Lcm_eucl_def n_def l_def if_True Let_def)
    finally show False using `Lcm_eucl A = 0` by contradiction
  qed
qed (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)

lemma Lcm_eucl0_iff [simp]:
  "finite A \<Longrightarrow> Lcm_eucl A = 0 \<longleftrightarrow> 0 \<in> A"
proof -
  assume "finite A"
  have "0 \<in> A \<Longrightarrow> Lcm_eucl A = 0"  by (intro dvd_0_left dvd_Lcm_eucl)
  moreover {
    assume "0 \<notin> A"
    hence "\<Prod>A \<noteq> 0" 
      apply (induct rule: finite_induct[OF `finite A`]) 
      apply simp
      apply (subst setprod.insert, assumption, assumption)
      apply (rule no_zero_divisors)
      apply blast+
      done
    moreover from `finite A` have "\<forall>x\<in>A. x dvd \<Prod>A"  by auto
    ultimately have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l)" by blast
    with Lcm_eucl0_iff' have "Lcm_eucl A \<noteq> 0" by simp
  }
  ultimately show "Lcm_eucl A = 0 \<longleftrightarrow> 0 \<in> A" by blast
qed

lemma Lcm_eucl_no_multiple:
  "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>x\<in>A. \<not>x dvd m)) \<Longrightarrow> Lcm_eucl A = 0"
proof -
  assume "\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>x\<in>A. \<not>x dvd m)"
  hence "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))" by blast
  then show "Lcm_eucl A = 0" by (simp only: Lcm_eucl_def if_False)
qed

lemma Lcm_eucl_insert [simp]:
  "Lcm_eucl (insert a A) = lcm_eucl a (Lcm_eucl A)"
proof (rule lcm_euclI)
  fix l assume "a dvd l" and "Lcm_eucl A dvd l"
  hence "\<forall>x\<in>A. x dvd l" by (blast intro: dvd_trans dvd_Lcm_eucl)
  with `a dvd l` show "Lcm_eucl (insert a A) dvd l" by (force intro: Lcm_eucl_dvd)
qed (auto intro: Lcm_eucl_dvd dvd_Lcm_eucl)
 
lemma Lcm_eucl_finite:
  assumes "finite A"
  shows "Lcm_eucl A = Finite_Set.fold lcm_eucl 1 A"
  by (induct rule: finite.induct[OF `finite A`])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm_eucl])

lemma Lcm_eucl_set [code, code_unfold]:
  "Lcm_eucl (set xs) = fold lcm_eucl xs 1"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm_eucl] Lcm_eucl_finite by (simp add: ac_simps)

lemma Lcm_eucl_singleton [simp]:
  "Lcm_eucl {a} = a div normalisation_factor a"
  by simp

lemma Lcm_eucl_2 [simp]:
  "Lcm_eucl {a,b} = lcm_eucl a b"
  by (simp only: Lcm_eucl_insert Lcm_eucl_empty lcm_eucl_1_right)
    (cases "b = 0", simp, rule lcm_eucl_div_unit2, simp)

lemma Lcm_eucl_coprime:
  assumes "finite A" and "A \<noteq> {}" 
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd_eucl a b = 1"
  shows "Lcm_eucl A = \<Prod>A div normalisation_factor (\<Prod>A)"
using assms proof (induct rule: finite_ne_induct)
  case (insert a A)
  have "Lcm_eucl (insert a A) = lcm_eucl a (Lcm_eucl A)" by simp
  also from insert have "Lcm_eucl A = \<Prod>A div normalisation_factor (\<Prod>A)" by blast
  also have "lcm_eucl a \<dots> = lcm_eucl a (\<Prod>A)" by (cases "\<Prod>A = 0") (simp_all add: lcm_eucl_div_unit2)
  also from insert have "gcd_eucl a (\<Prod>A) = 1" by (subst gcd.commute, intro setprod_coprime) auto
  with insert have "lcm_eucl a (\<Prod>A) = \<Prod>(insert a A) div normalisation_factor (\<Prod>(insert a A))"
    by (simp add: lcm_eucl_coprime)
  finally show ?case .
qed simp
      
lemma Lcm_eucl_coprime':
  "card A \<noteq> 0 \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd_eucl a b = 1)
    \<Longrightarrow> Lcm_eucl A = \<Prod>A div normalisation_factor (\<Prod>A)"
  by (rule Lcm_eucl_coprime) (simp_all add: card_eq_0_iff)

lemma Gcd_eucl_Lcm_eucl:
  "Gcd_eucl A = Lcm_eucl {d. \<forall>x\<in>A. d dvd x}"
  by (simp add: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def)

lemma "Gcd_eucl A = Lcm_eucl {d. \<forall>x\<in>A. d dvd x}"
  by (simp add: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def)

lemma Gcd_eucl_dvd [simp]: "x \<in> A \<Longrightarrow> Gcd_eucl A dvd x"
  and dvd_Gcd_eucl [simp]: "(\<forall>x\<in>A. g' dvd x) \<Longrightarrow> g' dvd Gcd_eucl A"
  and normalisation_factor_Gcd_eucl [simp]: 
    "normalisation_factor (Gcd_eucl A) = (if Gcd_eucl A = 0 then 0 else 1)"
proof -
  fix x assume "x \<in> A"
  hence "Lcm_eucl {d. \<forall>x\<in>A. d dvd x} dvd x" by (intro Lcm_eucl_dvd) blast
  then show "Gcd_eucl A dvd x" by (simp add: Gcd_eucl_Lcm_eucl)
next
  fix g' assume "\<forall>x\<in>A. g' dvd x"
  hence "g' dvd Lcm_eucl {d. \<forall>x\<in>A. d dvd x}" by (intro dvd_Lcm_eucl) blast
  then show "g' dvd Gcd_eucl A" by (simp add: Gcd_eucl_Lcm_eucl)
next
  show "normalisation_factor (Gcd_eucl A) = (if Gcd_eucl A = 0 then 0 else 1)"
    by (simp add: Gcd_eucl_Lcm_eucl)
qed

lemma Gcd_euclI:
  "(\<And>x. x\<in>A \<Longrightarrow> l dvd x) \<Longrightarrow> (\<And>l'. (\<forall>x\<in>A. l' dvd x) \<Longrightarrow> l' dvd l) \<Longrightarrow>
    normalisation_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Gcd_eucl A"
  by (intro normed_associated_imp_eq)
    (auto intro: Gcd_eucl_dvd dvd_Gcd_eucl simp: associated_def)

lemma Lcm_eucl_Gcd_eucl:
  "Lcm_eucl A = Gcd_eucl {m. \<forall>x\<in>A. x dvd m}"
  by (rule Lcm_euclI[symmetric]) (auto intro: dvd_Gcd_eucl Gcd_eucl_dvd)

lemma Gcd_eucl_0_iff:
  "Gcd_eucl A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  apply (rule iffI)
  apply (rule subsetI, drule Gcd_eucl_dvd, simp)
  apply (auto intro: Gcd_euclI[symmetric])
  done

lemma Gcd_eucl_empty [simp]:
  "Gcd_eucl {} = 0"
  by (simp add: Gcd_eucl_0_iff)

lemma Gcd_eucl_1:
  "1 \<in> A \<Longrightarrow> Gcd_eucl A = 1"
  by (intro Gcd_euclI[symmetric]) (auto intro: Gcd_eucl_dvd dvd_Gcd_eucl)

lemma Gcd_eucl_insert [simp]:
  "Gcd_eucl (insert a A) = gcd_eucl a (Gcd_eucl A)"
proof (rule gcd_euclI)
  fix l assume "l dvd a" and "l dvd Gcd_eucl A"
  hence "\<forall>x\<in>A. l dvd x" by (blast intro: dvd_trans Gcd_eucl_dvd)
  with `l dvd a` show "l dvd Gcd_eucl (insert a A)" by (force intro: Gcd_eucl_dvd)
qed (auto intro: Gcd_eucl_dvd dvd_Gcd_eucl)

lemma Gcd_eucl_finite:
  assumes "finite A"
  shows "Gcd_eucl A = Finite_Set.fold gcd_eucl 0 A"
  by (induct rule: finite.induct[OF `finite A`])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd_eucl])

lemma Gcd_eucl_set [code, code_unfold]:
  "Gcd_eucl (set xs) = fold gcd_eucl xs 0"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd_eucl] Gcd_eucl_finite by (simp add: ac_simps)

lemma Gcd_eucl_singleton [simp]: "Gcd_eucl {a} = a div normalisation_factor a"
  by (simp add: gcd_eucl_0)

lemma Gcd_eucl_2 [simp]: "Gcd_eucl {a,b} = gcd_eucl a b"
  by (simp only: Gcd_eucl_insert Gcd_eucl_empty gcd_eucl_0) (cases "b = 0", simp, rule gcd_eucl_div_unit2, simp)

end


text {*
  A Euclidean ring is a Euclidean semiring with additive inverses. It provides a 
  few more lemmas; in particular, Bezout's lemma holds for any Euclidean ring.
*}

class euclidean_ring = euclidean_semiring + idom

class euclidean_ring_gcd = euclidean_semiring_gcd + idom
begin

subclass euclidean_ring ..
end

(* The following lemmas  were proven in the euclidean_ring_gcd class, 
   Now they have been proven in the euclidean_ring one*)

context euclidean_ring
begin

lemma gcd_eucl_neg1 [simp]:
  "gcd_eucl (-x) y = gcd_eucl x y"
  by (rule sym, rule gcd_euclI, simp_all add: gcd_eucl_greatest)

lemma gcd_eucl_neg2 [simp]:
  "gcd_eucl x (-y) = gcd_eucl x y"
  by (rule sym, rule gcd_euclI, simp_all add: gcd_eucl_greatest gcd_eucl_zero)

lemma gcd_eucl_neg_numeral_1 [simp]:
  "gcd_eucl (- numeral n) x = gcd_eucl (numeral n) x"
  by (fact gcd_eucl_neg1)

lemma gcd_eucl_neg_numeral_2 [simp]:
  "gcd_eucl x (- numeral n) = gcd_eucl x (numeral n)"
  by (fact gcd_eucl_neg2)

lemma gcd_eucl_diff1: "gcd_eucl (m - n) n = gcd_eucl m n"
  by (subst diff_conv_add_uminus, subst gcd_eucl_neg2[symmetric], subst gcd_eucl_add1, simp)

lemma gcd_eucl_diff2: "gcd_eucl (n - m) n = gcd_eucl m n"
  by (subst gcd_eucl_neg1[symmetric], simp only: minus_diff_eq gcd_eucl_diff1)

lemma coprime_minus_one [simp]: "gcd_eucl (n - 1) n = 1"
proof -
  have "gcd_eucl (n - 1) n = gcd_eucl n (n - 1)" by (fact gcd.commute)
  also have "\<dots> = gcd_eucl ((n - 1) + 1) (n - 1)" by simp
  also have "\<dots> = 1" by (rule coprime_plus_one)
  finally show ?thesis .
qed

lemma lcm_eucl_neg1 [simp]: "lcm_eucl (-x) y = lcm_eucl x y"
  by (rule sym, rule lcm_euclI, simp_all add: lcm_eucl_least lcm_eucl_zero)

lemma lcm_eucl_neg2 [simp]: "lcm_eucl x (-y) = lcm_eucl x y"
  by (rule sym, rule lcm_euclI, simp_all add: lcm_eucl_least lcm_eucl_zero)

lemma lcm_eucl_neg_numeral_1 [simp]: "lcm_eucl (- numeral n) x = lcm_eucl (numeral n) x"
  by (fact lcm_eucl_neg1)

lemma lcm_eucl_neg_numeral_2 [simp]: "lcm_eucl x (- numeral n) = lcm_eucl x (numeral n)"
  by (fact lcm_eucl_neg2)

function euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "euclid_ext a b = 
     (if b = 0 then 
        let x = ring_inv (normalisation_factor a) in (x, 0, a * x)
      else 
        case euclid_ext b (a mod b) of
            (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (pat_completeness, simp)
  termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

declare euclid_ext.simps [simp del]

lemma euclid_ext_0: 
  "euclid_ext a 0 = (ring_inv (normalisation_factor a), 0, a * ring_inv (normalisation_factor a))"
  by (subst euclid_ext.simps, simp add: Let_def)

lemma euclid_ext_non_0:
  "b \<noteq> 0 \<Longrightarrow> euclid_ext a b = (case euclid_ext b (a mod b) of 
    (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (subst euclid_ext.simps, simp)

definition euclid_ext' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
where
  "euclid_ext' a b = (case euclid_ext a b of (s, t, _) \<Rightarrow> (s, t))"

lemma euclid_ext_gcd_eucl [simp]:
  "(case euclid_ext a b of (_,_,t) \<Rightarrow> t) = gcd_eucl a b"
proof (induct a b rule: euclid_ext.induct)
  case (1 a b)
  then show ?case
  proof (cases "b = 0")
    case True
      then show ?thesis by (cases "a = 0") 
        (simp_all add: euclid_ext_0 unit_div mult_ac unit_simps gcd_eucl_0)
    next
    case False with 1 show ?thesis
      by (simp add: euclid_ext_non_0 ac_simps split: prod.split prod.split_asm)
    qed
qed

lemma euclid_ext_gcd_eucl' [simp]:
  "euclid_ext a b = (r, s, t) \<Longrightarrow> t = gcd_eucl a b"
  by (insert euclid_ext_gcd_eucl[of a b], drule (1) subst, simp)

lemma euclid_ext_correct:
  "case euclid_ext x y of (s,t,c) \<Rightarrow> s*x + t*y = c"
proof (induct x y rule: euclid_ext.induct)
  case (1 x y)
  show ?case
  proof (cases "y = 0")
    case True
    then show ?thesis by (simp add: euclid_ext_0 mult_ac)
  next
    case False
    obtain s t c where stc: "euclid_ext y (x mod y) = (s,t,c)"
      by (cases "euclid_ext y (x mod y)", blast)
    from 1 have "c = s * y + t * (x mod y)" by (simp add: stc False)
    also have "... = t*((x div y)*y + x mod y) + (s - t * (x div y))*y"
      by (simp add: algebra_simps) 
    also have "(x div y)*y + x mod y = x" using mod_div_equality .
    finally show ?thesis
      by (subst euclid_ext.simps, simp add: False stc)
    qed
qed

lemma euclid_ext'_correct:
  "fst (euclid_ext' a b) * a + snd (euclid_ext' a b) * b = gcd_eucl a b"
proof-
  obtain s t c where "euclid_ext a b = (s,t,c)"
    by (cases "euclid_ext a b", blast)
  with euclid_ext_correct[of a b] euclid_ext_gcd_eucl[of a b]
    show ?thesis unfolding euclid_ext'_def by simp
qed

lemma bezout: "\<exists>s t. s * x + t * y = gcd_eucl x y"
  using euclid_ext'_correct by blast

lemma euclid_ext'_0 [simp]: "euclid_ext' x 0 = (ring_inv (normalisation_factor x), 0)" 
  by (simp add: euclid_ext'_def euclid_ext_0)

lemma euclid_ext'_non_0: "y \<noteq> 0 \<Longrightarrow> euclid_ext' x y = (snd (euclid_ext' y (x mod y)),
  fst (euclid_ext' y (x mod y)) - snd (euclid_ext' y (x mod y)) * (x div y))"
  by (cases "euclid_ext y (x mod y)") 
    (simp add: euclid_ext'_def euclid_ext_non_0)
  
end

instantiation nat :: euclidean_semiring
begin

definition [simp]:
  "euclidean_size_nat = (id :: nat \<Rightarrow> nat)"

definition [simp]:
  "normalisation_factor_nat (n::nat) = (if n = 0 then 0 else 1 :: nat)"

instance
  by standard (simp_all add: is_unit_def)

end

instantiation int :: euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

definition [simp]:
  "normalisation_factor_int = (sgn :: int \<Rightarrow> int)"

instance
proof (standard, goal_cases)
  case 2
  then show ?case by (auto simp add: abs_mult nat_mult_distrib)
next
  case 3
  then show ?case by (simp add: zsgn_def is_unit_def)
next
  case 5
  then show ?case by (auto simp: zsgn_def is_unit_def)
next
  case 6
  then show ?case by (auto split: abs_split simp: zsgn_def is_unit_def) 
qed (auto simp: sgn_times split: abs_split)

end





(*Rewritings to obtain the lemmas presented in the Manuel's version*)

context euclidean_semiring_gcd
begin

lemmas gcd_red = gcd_eucl_red[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_non_0 = gcd_eucl_non_0[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_0_left = gcd_eucl_0_left[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_0 = gcd_eucl_0[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_dvd1 = gcd_eucl_dvd1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_dvd2 = gcd_eucl_dvd2[unfolded gcd_gcd_eucl[symmetric]]
lemmas dvd_gcd_D1 = dvd_gcd_eucl_D1[unfolded gcd_gcd_eucl[symmetric]]
lemmas dvd_gcd_D2 = dvd_gcd_eucl_D2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_greatest = gcd_eucl_greatest[unfolded gcd_gcd_eucl[symmetric]]
lemmas dvd_gcd_iff = dvd_gcd_eucl_iff[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_zero = gcd_eucl_zero[unfolded gcd_gcd_eucl[symmetric]]
lemmas normalisation_factor_gcd = normalisation_factor_gcd_eucl[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcdI = gcd_euclI[unfolded gcd_gcd_eucl[symmetric]]

lemmas gcd_unique = gcd_eucl_unique[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_dvd_prod = gcd_eucl_dvd_prod[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_1_left = gcd_eucl_1_left[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_1 = gcd_eucl_1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_proj2_if_dvd = gcd_eucl_proj2_if_dvd[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_proj1_if_dvd = gcd_eucl_proj1_if_dvd[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_proj1_iff = gcd_eucl_proj1_iff[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_proj2_iff = gcd_eucl_proj2_iff[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mod1 = gcd_eucl_mod1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mod2 = gcd_eucl_mod2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mult_distrib' = gcd_eucl_mult_distrib'[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mult_distrib = gcd_eucl_mult_distrib[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclidean_size_gcd_le1 = euclidean_size_gcd_eucl_le1[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclidean_size_gcd_le2 = euclidean_size_gcd_eucl_le2[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclidean_size_gcd_less1 = euclidean_size_gcd_eucl_less1[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclidean_size_gcd_less2 = euclidean_size_gcd_eucl_less2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mult_unit1 = gcd_eucl_mult_unit1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mult_unit2 = gcd_eucl_mult_unit2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_div_unit1 = gcd_eucl_div_unit1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_div_unit2 = gcd_eucl_div_unit2 [unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_idem = gcd_eucl_idem[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_right_idem = gcd_eucl_right_idem[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_left_idem = gcd_eucl_left_idem[unfolded gcd_gcd_eucl[symmetric]]
lemmas comp_fun_idem_gcd = comp_fun_idem_gcd_eucl[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_dvd_mult = coprime_dvd_mult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_dvd_mult_iff = coprime_dvd_mult_iff[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_dvd_antisym = gcd_eucl_dvd_antisym[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_mult_cancel = gcd_eucl_mult_cancel[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_crossproduct = coprime_crossproduct[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_add1 = gcd_eucl_add1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_add2 = gcd_eucl_add2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_add_mult = gcd_eucl_add_mult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprimeI = coprimeI[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime = coprime[unfolded gcd_gcd_eucl[symmetric]]
lemmas div_gcd_coprime = div_gcd_eucl_coprime[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_mult = coprime_mult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_lmult = coprime_lmult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_rmult = coprime_rmult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_mul_eq = coprime_mul_eq[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_coprime = gcd_eucl_coprime[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_power = coprime_power[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_coprime_exists = gcd_eucl_coprime_exists[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_exp = coprime_exp[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_exp2 = coprime_exp2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_exp = gcd_eucl_exp[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_common_divisor = coprime_common_divisor[unfolded gcd_gcd_eucl[symmetric]]
lemmas divides_mult = divides_mult[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_plus_one = coprime_plus_one[unfolded gcd_gcd_eucl[symmetric]]
lemmas setprod_coprime = setprod_coprime[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_divisors = coprime_divisors[unfolded gcd_gcd_eucl[symmetric]]
lemmas invertible_coprime = invertible_coprime[unfolded gcd_gcd_eucl[symmetric]]
lemmas lcm_gcd = lcm_eucl_gcd_eucl[unfolded lcm_lcm_eucl[symmetric] gcd_gcd_eucl[symmetric]]
lemmas lcm_gcd_prod = lcm_eucl_gcd_eucl_prod[unfolded lcm_lcm_eucl[symmetric] gcd_gcd_eucl[symmetric]]
lemmas lcm_dvd1 = lcm_eucl_dvd1[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcm_least = lcm_eucl_least[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcm_zero = lcm_eucl_zero[unfolded lcm_lcm_eucl[symmetric]]
lemmas gcd_lcm = gcd_eucl_lcm_eucl[unfolded lcm_lcm_eucl[symmetric] gcd_gcd_eucl[symmetric]]
lemmas normalisation_factor_lcm = normalisation_factor_lcm_eucl
lemmas lcm_dvd2 = lcm_eucl_dvd2[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcmI = lcm_euclI[unfolded lcm_lcm_eucl[symmetric]]



lemmas dvd_lcm_D1 = dvd_lcm_eucl_D1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas dvd_lcm_D2 = dvd_lcm_eucl_D2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas gcd_dvd_lcm = gcd_eucl_dvd_lcm_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_1_iff = lcm_eucl_1_iff[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_0_left = lcm_eucl_0_left[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_0 = lcm_eucl_0[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_unique = lcm_eucl_unique[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas dvd_lcm_I1 = dvd_lcm_eucl_I1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas dvd_lcm_I2 = dvd_lcm_eucl_I2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_1_left = lcm_eucl_1_left[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_1_right = lcm_eucl_1_right[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_coprime = lcm_eucl_coprime[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_proj1_if_dvd = lcm_eucl_proj1_if_dvd[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_proj2_if_dvd = lcm_eucl_proj2_if_dvd[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_proj1_iff = lcm_eucl_proj1_iff[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_proj2_iff = lcm_eucl_proj2_iff[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas euclidean_size_lcm_le1 = euclidean_size_lcm_eucl_le1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas euclidean_size_lcm_le2 = euclidean_size_lcm_eucl_le2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas euclidean_size_lcm_less1 = euclidean_size_lcm_eucl_less1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas euclidean_size_lcm_less2 = euclidean_size_lcm_eucl_less2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_mult_unit1 = lcm_eucl_mult_unit1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_mult_unit2 = lcm_eucl_mult_unit2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_div_unit1 = lcm_eucl_div_unit1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_div_unit2 = lcm_eucl_div_unit2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_left_idem = lcm_eucl_left_idem[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas lcm_right_idem = lcm_eucl_right_idem[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas comp_fun_idem_lcm = comp_fun_idem_lcm_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas dvd_Lcm = dvd_Lcm_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_dvd = Lcm_eucl_dvd[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas normalisation_factor_Lcm = normalisation_factor_Lcm_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas LcmI = Lcm_euclI[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_subset = Lcm_eucl_subset[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_Un = Lcm_eucl_Un[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_1_iff = Lcm_eucl_1_iff [unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_no_units = Lcm_eucl_no_units [unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_empty = Lcm_eucl_empty[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_eq_0 = Lcm_eucl_eq_0[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm0_iff' = Lcm_eucl0_iff'[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm0_iff = Lcm_eucl0_iff[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_no_multiple = Lcm_eucl_no_multiple[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_insert = Lcm_eucl_insert[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_finite = Lcm_eucl_finite[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_set = Lcm_eucl_set[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_singleton = Lcm_eucl_singleton[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_2 = Lcm_eucl_2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_coprime = Lcm_eucl_coprime[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_coprime' = Lcm_eucl_coprime'[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_Lcm = Gcd_eucl_Lcm_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_dvd = Gcd_eucl_dvd[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas dvd_Gcd = dvd_Gcd_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas normalisation_factor_Gcd = normalisation_factor_Gcd_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas GcdI = Gcd_euclI[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Lcm_Gcd = Lcm_eucl_Gcd_eucl[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_0_iff = Gcd_eucl_0_iff[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_empty = Gcd_eucl_empty[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_1 = Gcd_eucl_1[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_insert = Gcd_eucl_insert[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_finite = Gcd_eucl_finite[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_set = Gcd_eucl_set[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_singleton = Gcd_eucl_singleton[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
lemmas Gcd_2 = Gcd_eucl_2[unfolded gcd_gcd_eucl[symmetric] lcm_lcm_eucl[symmetric] Gcd_Gcd_eucl[symmetric] Lcm_Lcm_eucl[symmetric]]
end


context euclidean_ring_gcd
begin

lemmas gcd_neg1 = gcd_eucl_neg1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_neg2 = gcd_eucl_neg2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_neg_numeral_1 = gcd_eucl_neg_numeral_1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_neg_numeral_2 = gcd_eucl_neg_numeral_2[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_diff1 = gcd_eucl_diff1[unfolded gcd_gcd_eucl[symmetric]]
lemmas gcd_diff2 = gcd_eucl_diff2[unfolded gcd_gcd_eucl[symmetric]]
lemmas coprime_minus_one = coprime_minus_one[unfolded gcd_gcd_eucl[symmetric]]
lemmas lcm_neg1 = lcm_eucl_neg1[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcm_neg2 = lcm_eucl_neg2[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcm_neg_numeral_1 = lcm_eucl_neg_numeral_1[unfolded lcm_lcm_eucl[symmetric]]
lemmas lcm_neg_numeral_2 = lcm_eucl_neg_numeral_2[unfolded lcm_lcm_eucl[symmetric]]


lemmas euclid_ext_gcd = euclid_ext_gcd_eucl[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclid_ext_gcd' = euclid_ext_gcd_eucl'[unfolded gcd_gcd_eucl[symmetric]]
lemmas euclid_ext'_correct = euclid_ext'_correct[unfolded gcd_gcd_eucl[symmetric]]
lemmas bezout = bezout[unfolded gcd_gcd_eucl[symmetric]]

end

end
