(*  Title: Sturm_Tarski
    Author:     Wenda Li <wl302@cam.ac.uk>
*)

section "Sturm-Tarski Theorem"

theory Sturm_Tarski imports
  Complex_Main
  PolyMisc
begin

section{*Misc*}

lemma eventually_at_right:
  fixes x::real
  shows "eventually P (at_right x) \<longleftrightarrow> (\<exists>b>x. \<forall>y>x. y < b \<longrightarrow> P y)"
proof -
  obtain y where "y>x" using reals_Archimedean2 by auto
  thus ?thesis using eventually_at_right[OF `y>x`] by auto
qed

lemma eventually_neg:
  assumes "F\<noteq>bot"  and eve:"eventually (\<lambda>x. P x) F"
  shows "\<not> eventually (\<lambda>x. \<not> P x) F"
proof (rule ccontr)
  assume "\<not> \<not> eventually (\<lambda>x. \<not> P x) F"
  hence "eventually (\<lambda>x. \<not> P x) F" by auto
  hence "eventually (\<lambda>x. False) F" using eventually_conj[OF eve,of "(\<lambda>x. \<not> P x)"] by auto
  thus False using `F\<noteq>bot` eventually_False by auto
qed

lemma poly_tendsto[simp]:"(poly p \<longlongrightarrow> poly p x) (at (x::real))"
  using isCont_def[where f="poly p"] by auto

lemma not_eq_pos_or_neg_iff_1:
  fixes p::"real poly"
  shows "(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z\<noteq>0) \<longleftrightarrow>
    (\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z>0)\<or>(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z<0)" (is "?Q \<longleftrightarrow> ?P")
proof (rule,rule ccontr)
  assume "?Q" "\<not>?P"
  then obtain z1 z2 where z1:"lb<z1" "z1\<le>ub" "poly p z1\<le>0"
                      and z2:"lb<z2" "z2\<le>ub" "poly p z2\<ge>0"
    by auto
  hence "\<exists>z. lb<z\<and>z\<le>ub\<and>poly p z=0"
    proof (cases "poly p z1 = 0 \<or> poly p z2 =0 \<or> z1=z2")
      case True
      thus ?thesis using z1 z2 by auto
    next
      case False
      hence "poly p z1<0" and "poly p z2>0" and "z1\<noteq>z2" using z1(3) z2(3) by auto
      hence "(\<exists>z>z1. z < z2 \<and> poly p z = 0) \<or> (\<exists>z>z2. z < z1 \<and> poly p z = 0)"
        using poly_IVT_neg poly_IVT_pos by (subst (asm) linorder_class.neq_iff,auto)
      thus ?thesis using z1(1,2) z2(1,2) by (metis less_eq_real_def order.strict_trans2)
    qed
  thus False using `?Q` by auto
next
  assume "?P"
  thus ?Q by auto
qed

lemma not_eq_pos_or_neg_iff_2:
  fixes p::"real poly"
  shows "(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z\<noteq>0)
    \<longleftrightarrow>(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z>0)\<or>(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z<0)" (is "?Q\<longleftrightarrow>?P")
proof (rule,rule ccontr)
  assume "?Q" "\<not>?P"
  then obtain z1 z2 where z1:"lb\<le>z1" "z1<ub" "poly p z1\<le>0"
                      and z2:"lb\<le>z2" "z2<ub" "poly p z2\<ge>0"
    by auto
  hence "\<exists>z. lb\<le>z\<and>z<ub\<and>poly p z=0"
    proof (cases "poly p z1 = 0 \<or> poly p z2 =0 \<or> z1=z2")
      case True
      thus ?thesis using z1 z2 by auto
    next
      case False
      hence "poly p z1<0" and "poly p z2>0" and "z1\<noteq>z2" using z1(3) z2(3) by auto
      hence "(\<exists>z>z1. z < z2 \<and> poly p z = 0) \<or> (\<exists>z>z2. z < z1 \<and> poly p z = 0)"
        using poly_IVT_neg poly_IVT_pos by (subst (asm) linorder_class.neq_iff,auto)
      thus ?thesis using z1(1,2) z2(1,2) by (meson dual_order.strict_trans not_le)
    qed
  thus False using `?Q` by auto
next
  assume "?P"
  thus ?Q by auto
qed

lemma next_non_root_interval:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  obtains ub where "ub>lb" and "(\<forall>z. lb<z\<and>z\<le>ub\<longrightarrow>poly p z\<noteq>0)"
proof (cases "(\<exists> r. poly p r=0 \<and> r>lb)")
  case False
  thus ?thesis by (intro that[of "lb+1"],auto)
next
  case True
  def lr\<equiv>"Min {r . poly p r=0 \<and> r>lb}"
  have "\<forall>z. lb<z\<and>z<lr\<longrightarrow>poly p z\<noteq>0" and "lr>lb"
    using True lr_def poly_roots_finite[OF `p\<noteq>0`] by auto
  thus ?thesis using that[of "(lb+lr)/2"] by auto
qed

lemma last_non_root_interval:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  obtains lb where "lb<ub" and "(\<forall>z. lb\<le>z\<and>z<ub\<longrightarrow>poly p z\<noteq>0)"
proof (cases "(\<exists> r. poly p r=0 \<and> r<ub)")
  case False
  thus ?thesis by (intro that[of "ub - 1"]) auto
next
  case True
  def mr\<equiv>"Max {r . poly p r=0 \<and> r<ub}"
  have "\<forall>z. mr<z\<and>z<ub\<longrightarrow>poly p z\<noteq>0" and "mr<ub"
    using True mr_def poly_roots_finite[OF `p\<noteq>0`] by auto
  thus ?thesis using that[of "(mr+ub)/2"] `mr<ub` by auto
qed

section{*Sign*}

definition sign:: "'a::{zero,linorder} \<Rightarrow> int" where
  "sign x\<equiv>(if x>0 then 1 else if x=0 then 0 else -1)"

lemma sign_simps[simp]:
  "x>0 \<Longrightarrow>  sign x=1"
  "x=0 \<Longrightarrow>  sign x=0"
  "x<0 \<Longrightarrow> sign x=-1"
unfolding sign_def by auto


section {*Variation and cross*}

definition variation :: "real \<Rightarrow>  real \<Rightarrow> int" where
  "variation x y=(if x*y\<ge>0 then 0 else if x<y then 1 else -1)"

definition cross :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "cross p a b=variation (poly p a) (poly p b)"

lemma variation_0[simp]: "variation 0 y=0" "variation x 0=0"
  unfolding variation_def by auto

lemma variation_comm: "variation x y= - variation y x" unfolding variation_def
  by (auto simp add: mult.commute)

lemma cross_0[simp]: "cross 0 a b=0" unfolding cross_def by auto

lemma variation_cases:
  "\<lbrakk>x>0;y>0\<rbrakk>\<Longrightarrow>variation x y = 0"
  "\<lbrakk>x>0;y<0\<rbrakk>\<Longrightarrow>variation x y = -1"
  "\<lbrakk>x<0;y>0\<rbrakk>\<Longrightarrow>variation x y = 1"
  "\<lbrakk>x<0;y<0\<rbrakk>\<Longrightarrow>variation x y = 0"
proof -
  show "\<lbrakk>x>0;y>0\<rbrakk>\<Longrightarrow>variation x y = 0"  unfolding variation_def by auto
  show "\<lbrakk>x>0;y<0\<rbrakk>\<Longrightarrow>variation x y = -1" unfolding variation_def
    using mult_pos_neg by fastforce
  show "\<lbrakk>x<0;y>0\<rbrakk>\<Longrightarrow>variation x y = 1" unfolding variation_def
    using mult_neg_pos by fastforce
  show "\<lbrakk>x<0;y<0\<rbrakk>\<Longrightarrow>variation x y = 0" unfolding variation_def
    using mult_neg_neg by fastforce
qed

lemma variation_congr:
  assumes "sgn x=sgn x'" "sgn y=sgn y'"
  shows "variation x y=variation x' y'" using assms
proof -
  have " 0 \<le> x * y =  (0\<le> x' * y')" using assms by (metis sgn_times zero_le_sgn_iff)
  moreover hence "\<not> 0\<le>x * y \<Longrightarrow> x < y = (x' < y')" using assms
    by (metis less_eq_real_def mult_nonneg_nonneg mult_nonpos_nonpos not_le order.strict_trans2
      zero_le_sgn_iff)
  ultimately show ?thesis unfolding variation_def by auto
qed

lemma variation_mult_pos:
  assumes "c>0"
  shows "variation (c*x) y =variation x y" and "variation x (c*y) =variation x y"
proof -
  have "sgn (c*x) = sgn x" using `c>0`
    by (metis monoid_mult_class.mult.left_neutral sgn_pos sgn_times)
  thus "variation (c*x) y =variation x y" using variation_congr by blast
next
  have "sgn (c*y) = sgn y" using `c>0`
    by (metis monoid_mult_class.mult.left_neutral sgn_pos sgn_times)
  thus "variation x (c*y) =variation x y" using variation_congr by blast
qed

lemma variation_mult_neg_1:
  assumes "c<0"
  shows "variation (c*x) y =variation x y + (if y=0 then 0 else sign x)"
  apply (cases x  rule:linorder_cases[of 0] )
  apply (cases y  rule:linorder_cases[of 0], auto simp add:
    variation_cases mult_neg_pos[OF `c<0`,of x]  mult_neg_neg[OF `c<0`,of x])+
done

lemma variation_mult_neg_2:
  assumes "c<0"
  shows "variation x (c*y) = variation x y + (if x=0 then 0 else - sign y)"
unfolding variation_comm[of x "c*y", unfolded variation_mult_neg_1[OF `c<0`, of y x] ]
  by (auto,subst variation_comm,simp)

lemma cross_no_root:
  assumes "a<b" and no_root:"\<forall>x. a<x\<and>x<b \<longrightarrow> poly p x\<noteq>0"
  shows "cross p a b=0"
proof -
  have "\<lbrakk>poly p a>0;poly p b<0\<rbrakk> \<Longrightarrow> False" using poly_IVT_neg[OF `a<b`] no_root by auto
  moreover have "\<lbrakk>poly p a<0;poly p b>0\<rbrakk> \<Longrightarrow> False" using poly_IVT_pos[OF `a<b`] no_root by auto
  ultimately have "0 \<le> poly p a * poly p b"
    by (metis less_eq_real_def linorder_neqE_linordered_idom mult_less_0_iff)
  thus ?thesis unfolding cross_def variation_def by simp
qed

section {*Tarski query*}

definition taq :: "'a::linordered_idom set \<Rightarrow> 'a poly \<Rightarrow> int" where
  "taq s q \<equiv> \<Sum>x\<in>s. sign (poly q x)"


section {*Sign at the right*}

definition sign_r_pos :: "'a :: {linordered_idom,order_topology} poly \<Rightarrow> 'a \<Rightarrow> bool "
  where
  "sign_r_pos p x \<equiv> (eventually (\<lambda>x. poly p x>0) (at_right x))"

lemma sign_r_pos_rec:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  shows "sign_r_pos p x= (if poly p x=0 then sign_r_pos (pderiv p) x else poly p x>0 )"
proof (cases "poly p x=0")
  case True
  have "sign_r_pos (pderiv p) x \<Longrightarrow> sign_r_pos p x"
    proof (rule ccontr)
      assume "sign_r_pos (pderiv p) x" "\<not> sign_r_pos p x"
      obtain b where "b>x" and b:"\<forall>z. x < z \<and> z < b \<longrightarrow> 0 < poly (pderiv p) z"
        using `sign_r_pos (pderiv p) x` unfolding sign_r_pos_def eventually_at_right  by auto
      have "\<forall>b>x. \<exists>z>x. z < b \<and> \<not> 0 < poly p z" using `\<not> sign_r_pos p x`
        unfolding sign_r_pos_def eventually_at_right by auto
      then obtain z where "z>x" and "z<b" and "poly p z\<le>0"
        using `b>x` b by auto
      hence "\<exists>z'>x. z' < z \<and> poly p z = (z - x) * poly (pderiv p) z'"
        using poly_MVT[OF `z>x`] True by (metis diff_0_right)
      hence "\<exists>z'>x. z' < z \<and> poly (pderiv p) z' \<le>0"
        using `poly p z\<le>0``z>x` by (metis leD le_iff_diff_le_0 mult_le_0_iff)
      thus False using b by (metis `z < b` dual_order.strict_trans not_le)
    qed
  moreover have "sign_r_pos p x \<Longrightarrow> sign_r_pos (pderiv p) x"
    proof -
      assume "sign_r_pos p x"
      have "pderiv p\<noteq>0" using `poly p x=0` `p\<noteq>0`
        by (metis monoid_add_class.add.right_neutral monom_0 monom_eq_0 mult_zero_right
          pderiv_iszero poly_0 poly_pCons)
      obtain ub where "ub>x" and ub: "(\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z>0)
          \<or> (\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0)"
        using next_non_root_interval[OF `pderiv p\<noteq>0`, of x,unfolded not_eq_pos_or_neg_iff_1]
        by (metis order.strict_implies_order)
      have "\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0 \<Longrightarrow> False"
        proof -
          assume assm:"\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z<0"
          obtain ub' where "ub'>x" and ub':"\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly p z"
            using `sign_r_pos p x` unfolding sign_r_pos_def eventually_at_right by auto
          obtain z' where "x<z'" and "z' < (x+(min ub' ub))/2"
            and z':"poly p ((x+min ub' ub)/2) = ((x+min ub' ub)/2 - x) * poly (pderiv p) z'"
            using poly_MVT[of x "(x+min ub' ub)/2" p] `ub'>x` `ub>x` True by auto
          moreover have "0 < poly p ((x+min ub' ub)/2)"
            using ub'[THEN HOL.spec,of "(x+(min ub' ub))/2"] `z' < (x+min ub' ub)/2` `x<z'`
            by auto
          moreover have "(x+min ub' ub)/2 - x>0" using `ub'>x` `ub>x` by auto
          ultimately have "poly (pderiv p) z'>0" by (metis zero_less_mult_pos)
          thus False using assm[THEN spec,of z'] `x<z'` `z' < (x+(min ub' ub))/2` by auto
        qed
      hence "\<forall>z. x<z\<and>z<ub\<longrightarrow>poly (pderiv p) z>0" using ub by auto
      thus "sign_r_pos (pderiv p) x" unfolding sign_r_pos_def eventually_at_right
        using `ub>x` by auto
    qed
  ultimately show ?thesis using True by auto
next
  case False
  have "sign_r_pos p x \<Longrightarrow> poly p x>0"
    proof (rule ccontr)
      assume "sign_r_pos p x" "\<not> 0 < poly p x"
      then obtain  ub where "ub>x" and ub: "\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z"
        unfolding sign_r_pos_def eventually_at_right by auto
      hence "poly p ((ub+x)/2) > 0" by auto
      moreover have "poly p x<0" using `\<not> 0 < poly p x` False by auto
      ultimately have "\<exists>z>x. z < (ub + x) / 2 \<and> poly p z = 0"
        using poly_IVT_pos[of x "((ub + x) / 2)" p] `ub>x` by auto
      thus False using ub by auto
    qed
  moreover have "poly p x>0 \<Longrightarrow> sign_r_pos p x"
    unfolding sign_r_pos_def
    using order_tendstoD(1)[OF poly_tendsto,of 0 p x] eventually_at_split by auto
  ultimately show ?thesis using False by auto
qed

lemma sign_r_pos_0[simp]:"\<not> sign_r_pos 0 (x::real)"
  using eventually_False[of "at_right x"] unfolding sign_r_pos_def by auto

lemma sign_r_pos_minus:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  shows "sign_r_pos p x = (\<not> sign_r_pos (-p) x)"
proof -
  have "sign_r_pos p x \<or> sign_r_pos (-p) x"
    unfolding sign_r_pos_def eventually_at_right
    using next_non_root_interval[OF `p\<noteq>0`,unfolded not_eq_pos_or_neg_iff_1]
    by (metis (erased, hide_lams) le_less minus_zero neg_less_iff_less poly_minus)
  moreover have "sign_r_pos p x \<Longrightarrow> \<not> sign_r_pos (-p) x" unfolding sign_r_pos_def
    using eventually_neg[OF trivial_limit_at_right_real, of "\<lambda>x. poly p x > 0" x] poly_minus
    by (metis (lifting) eventually_mono less_asym neg_less_0_iff_less)
  ultimately show ?thesis by auto
qed

lemma sign_r_pos_smult:
  fixes p :: "real poly"
  assumes "c\<noteq>0" "p\<noteq>0"
  shows "sign_r_pos (smult c p) x= (if c>0 then sign_r_pos p x else \<not> sign_r_pos p x)"
  (is "?L=?R")
proof (cases "c>0")
  assume "c>0"
  hence "\<forall>x. (0 < poly (smult c p) x) = (0 < poly p x)"
    by (subst poly_smult,metis mult_pos_pos zero_less_mult_pos)
  thus ?thesis unfolding sign_r_pos_def using `c>0` by auto
next
  assume "\<not>(c>0)"
  hence "\<forall>x. (0 < poly (smult c p) x) = (0 < poly (-p) x)"
    by (subst poly_smult, metis assms(1) linorder_neqE_linordered_idom mult_neg_neg mult_zero_right
      neg_0_less_iff_less poly_minus zero_less_mult_pos2)
  hence "sign_r_pos (smult c p) x=sign_r_pos (-p) x"
    unfolding sign_r_pos_def using `\<not> c>0` by auto
  thus ?thesis using sign_r_pos_minus[OF `p\<noteq>0`, of x] `\<not> c>0` by auto
qed

lemma sign_r_pos_mult:
  fixes p q :: "real poly"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "sign_r_pos (p*q) x= (sign_r_pos p x \<longleftrightarrow> sign_r_pos q x)"
proof -
  obtain ub where "ub>x"
      and ub:"(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<or> (\<forall>z. x < z \<and> z < ub \<longrightarrow> poly p z < 0)"
    using next_non_root_interval[OF `p\<noteq>0`,of x,unfolded not_eq_pos_or_neg_iff_1]
    by (metis order.strict_implies_order)
  obtain ub' where "ub'>x"
      and ub':"(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z) \<or> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> poly q z < 0)"
    using next_non_root_interval[OF `q\<noteq>0`,unfolded not_eq_pos_or_neg_iff_1]
    by (metis order.strict_implies_order)
  have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z) \<Longrightarrow> ?thesis"
    proof -
      assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z)"
      hence "sign_r_pos p x" and "sign_r_pos q x" unfolding sign_r_pos_def eventually_at_right
        using `ub>x` `ub'>x` by auto
      moreover hence "eventually (\<lambda>z. poly p z>0 \<and> poly q z>0) (at_right x)"
        unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
      hence "sign_r_pos (p*q) x"
        unfolding sign_r_pos_def poly_mult
        by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
      ultimately show ?thesis by auto
    qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z)
      \<Longrightarrow> ?thesis"
    proof -
      assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 < poly q z)"
      hence "sign_r_pos (-p) x" and "sign_r_pos q x" unfolding sign_r_pos_def eventually_at_right
        using `ub>x` `ub'>x` by auto
      moreover hence "eventually (\<lambda>z. poly (-p) z>0 \<and> poly q z>0) (at_right x)"
        unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
      hence "sign_r_pos (- p*q) x"
        unfolding sign_r_pos_def poly_mult
        by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
      ultimately show ?thesis
        using sign_r_pos_minus `p\<noteq>0` `q\<noteq>0` by (metis minus_mult_left no_zero_divisors)
    qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)
      \<Longrightarrow> ?thesis"
    proof -
      assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 < poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)"
      hence "sign_r_pos p x" and "sign_r_pos (-q) x" unfolding sign_r_pos_def eventually_at_right
        using `ub>x` `ub'>x` by auto
      moreover hence "eventually (\<lambda>z. poly p z>0 \<and> poly (-q) z>0) (at_right x)"
        unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
      hence "sign_r_pos ( p * (- q)) x"
        unfolding sign_r_pos_def poly_mult
        by (metis (lifting, mono_tags) eventually_mono mult_pos_pos)
      ultimately show ?thesis
        using sign_r_pos_minus `p\<noteq>0` `q\<noteq>0`
        by (metis minus_mult_right no_zero_divisors)
    qed
  moreover have "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z) \<Longrightarrow> (\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)
      \<Longrightarrow> ?thesis"
    proof -
      assume "(\<forall>z. x < z \<and> z < ub \<longrightarrow> 0 > poly p z)" "(\<forall>z. x < z \<and> z < ub' \<longrightarrow> 0 > poly q z)"
      hence "sign_r_pos (-p) x" and "sign_r_pos (-q) x"
        unfolding sign_r_pos_def eventually_at_right using `ub>x` `ub'>x` by auto
      moreover hence "eventually (\<lambda>z. poly (-p) z>0 \<and> poly (-q) z>0) (at_right x)"
        unfolding sign_r_pos_def using eventually_conj_iff[of _ _ "at_right x"] by auto
      hence "sign_r_pos (p * q) x"
        unfolding sign_r_pos_def poly_mult poly_minus
        apply (elim eventually_mono[of _ "at_right x"])
        by (auto intro:mult_neg_neg)
      ultimately show ?thesis
        using sign_r_pos_minus `p\<noteq>0` `q\<noteq>0` by metis
    qed
  ultimately show ?thesis using ub ub' by auto
qed

lemma sign_r_pos_add:
  fixes p q :: "real poly"
  assumes "poly p x=0" "poly q x\<noteq>0"
  shows "sign_r_pos (p+q) x=sign_r_pos q x"
proof (cases "poly (p+q) x=0")
  case False
  hence "p+q\<noteq>0" by (metis poly_0)
  have "sign_r_pos (p+q) x = (poly q x > 0)"
    using sign_r_pos_rec[OF `p+q\<noteq>0`] False poly_add `poly p x=0` by auto
  moreover have "sign_r_pos q x=(poly q x > 0)"
    using sign_r_pos_rec[of q x] `poly q x\<noteq>0` poly_0 by force
  ultimately show ?thesis by auto
next
  case True
  hence False using `poly p x=0` `poly q x\<noteq>0` poly_add by auto
  thus ?thesis by auto
qed

lemma sign_r_pos_mod:
  fixes p q :: "real poly"
  assumes "poly p x=0" "poly q x\<noteq>0"
  shows "sign_r_pos (q mod p) x=sign_r_pos q x"
proof -
  have "poly (q div p * p) x=0" using `poly p x=0` poly_mult by auto
  moreover hence "poly (q mod p) x \<noteq> 0" using `poly q x\<noteq>0` mod_div_equality
    by (metis monoid_add_class.add.left_neutral poly_add)
  ultimately show ?thesis
    by (subst (2) mod_div_equality[THEN sym,of q p], auto simp add: sign_r_pos_add)
qed

lemma sign_r_pos_pderiv:
  fixes p:: "real poly"
  assumes "poly p x=0" "p\<noteq>0"
  shows "sign_r_pos (pderiv p * p) x"
proof -
  have "pderiv p \<noteq>0"
    by (metis assms(1) assms(2) monoid_add_class.add.right_neutral mult_zero_right pCons_0_0
      pderiv_iszero poly_0 poly_pCons)
  have "?thesis = (sign_r_pos (pderiv p) x \<longleftrightarrow> sign_r_pos p x)"
    using sign_r_pos_mult[OF `pderiv p \<noteq> 0` `p\<noteq>0`] by auto
  also have "...=((sign_r_pos (pderiv p) x \<longleftrightarrow> sign_r_pos (pderiv p) x))"
    using sign_r_pos_rec[OF `p\<noteq>0`] `poly p x=0` by auto
  finally show ?thesis by auto
qed

lemma sign_r_pos_power:
  fixes p:: "real poly" and a::real
  shows "sign_r_pos ([:-a,1:]^n) a"
proof (induct n)
  case 0
  thus ?case unfolding sign_r_pos_def eventually_at_right by (simp,metis gt_ex)
next
  case (Suc n)
  have "pderiv ([:-a,1:]^Suc n) = smult (Suc n) ([:-a,1:]^n)"
    proof -
      have "pderiv [:- a, 1::real:] = 1"
        by (metis monoid_add_class.add.right_neutral one_poly_def pCons_0_0 pderiv_pCons
          pderiv_singleton)
      thus ?thesis unfolding pderiv_power_Suc by (metis mult_cancel_left1)
    qed
  moreover have " poly ([:- a, 1:] ^ Suc n) a=0" by (metis old.nat.distinct(2) poly_power_n_eq)
  hence "sign_r_pos ([:- a, 1:] ^ Suc n) a = sign_r_pos (smult (Suc n) ([:-a,1:]^n)) a"
    using sign_r_pos_rec by (metis (erased, hide_lams) calculation pderiv_0)
  hence "sign_r_pos ([:- a, 1:] ^ Suc n) a = sign_r_pos  ([:-a,1:]^n) a"
    using sign_r_pos_smult by auto
  ultimately show ?case using Suc.hyps by auto
qed

section{*Jump*}

definition jump :: "'a :: {linordered_idom,order_topology} poly \<Rightarrow> 'a poly \<Rightarrow>'a \<Rightarrow> int"
 where
 "jump q p x\<equiv> ( if q\<noteq>0 \<and> odd((order x p) - (order x q) ) then
                  if sign_r_pos (q*p) x then 1 else -1
                else 0 )"

definition sjump:: "'a :: {linordered_idom,order_topology} poly  \<Rightarrow>'a \<Rightarrow> int"
  where
  "sjump p x\<equiv> ( if odd(order x p) then if sign_r_pos p x then 1 else -1 else 0 )"

lemma jump_sjump: "jump 1 p x=sjump p x" unfolding jump_def sjump_def by auto

lemma jump_not_root:"poly p x\<noteq>0\<Longrightarrow>jump q p x=0"
  unfolding jump_def by (metis even_zero order_root zero_diff)

lemma sjump_not_root:"poly p x\<noteq>0\<Longrightarrow>sjump p x=0"
  by (metis jump_not_root jump_sjump)

lemma jump0[simp]: "jump 0 p x = 0" unfolding jump_def by auto

lemma jump_smult_1:
  fixes p q::"real poly" and c::real
  assumes "p\<noteq>0"
  shows "jump (smult c q) p x= sign c * jump q p x" (is "?L=?R")
proof (cases "c=0\<or> q=0")
  case True
  thus ?thesis unfolding jump_def by auto
next
  case False
  hence "c\<noteq>0" and "q\<noteq>0" by auto
  thus ?thesis unfolding jump_def
     using order_smult[OF `c\<noteq>0`] sign_r_pos_smult[OF `c\<noteq>0`, of "q*p" x] `p\<noteq>0` `q\<noteq>0`
     by auto
qed

lemma jump_smult_2:
  fixes p q::"real poly" and c::real
  assumes "p\<noteq>0" "c\<noteq>0"
  shows "jump q (smult c p) x= sgn c * jump q p x" (is "?L=?R")
proof (cases "q=0")
  case True
  thus ?thesis unfolding jump_def by auto
next
  case False
  hence "q*p\<noteq>0" using `p\<noteq>0` by auto
  def cond\<equiv>"q \<noteq> 0 \<and> odd (order x p - order x q)"
  have "cond\<Longrightarrow>c>0\<Longrightarrow>?thesis" unfolding cond_def jump_def
    by (subst order_smult[OF `c\<noteq>0`, of x p], subst mult_smult_right[of q c p],
      subst sign_r_pos_smult[OF `c\<noteq>0` `q*p\<noteq>0`],auto)
  moreover have "cond\<Longrightarrow>c<0\<Longrightarrow>?thesis" unfolding cond_def jump_def
    by (subst order_smult[OF `c\<noteq>0`, of x p], subst mult_smult_right[of q c p],
      subst sign_r_pos_smult[OF `c\<noteq>0` `q*p\<noteq>0`],auto)
  moreover have "\<not>cond\<Longrightarrow>c>0\<Longrightarrow>?thesis" unfolding cond_def jump_def
    by (subst order_smult[OF `c\<noteq>0`, of x p], subst mult_smult_right[of q c p],
      subst sign_r_pos_smult[OF `c\<noteq>0` `q*p\<noteq>0`],auto)
  moreover have "\<not>cond\<Longrightarrow>c<0\<Longrightarrow>?thesis" unfolding cond_def jump_def
     by (subst order_smult[OF `c\<noteq>0`, of x p], subst mult_smult_right[of q c p],
      subst sign_r_pos_smult[OF `c\<noteq>0` `q*p\<noteq>0`],auto)
  ultimately show ?thesis using `c\<noteq>0` by (metis linorder_neqE_linordered_idom)
qed

lemma jump_mult:
  fixes p q p'::"real poly"
  assumes "p\<noteq>0" "p'\<noteq>0"
  shows "jump (p'*q) (p'*p) x= jump q p x"
proof (cases "q=0")
  case True
  thus ?thesis unfolding jump_def by auto
next
  case False
  have "sign_r_pos (p' * q * (p' * p)) x=sign_r_pos (q * p) x"
    proof (unfold sign_r_pos_def,rule eventually_subst,unfold eventually_at_right)
      obtain b where "b>x" and b:"\<forall>z. x < z \<and> z < b \<longrightarrow> poly (p' * p') z >0"
        proof (cases "\<exists>z. poly p' z=0 \<and> z>x")
          case True
          def lr\<equiv>"Min {r . poly p' r=0 \<and> r>x}"
          have "\<forall>z. x<z\<and>z<lr\<longrightarrow>poly p' z\<noteq>0" and "lr>x"
            using True lr_def poly_roots_finite[OF `p'\<noteq>0`] by auto
          hence "\<forall>z. x < z \<and> z < lr \<longrightarrow> 0 < poly (p' * p') z"
            by (metis not_real_square_gt_zero poly_mult)
          thus ?thesis using that[OF `lr>x`] by auto
        next
          case False
          have "\<forall>z. x<z\<and>z<x+1\<longrightarrow>poly p' z\<noteq>0" and "x+1>x"
            using False poly_roots_finite[OF `p'\<noteq>0`]  by auto
          hence "\<forall>z. x < z \<and> z < x+1 \<longrightarrow> 0 < poly (p' * p') z"
            by (metis not_real_square_gt_zero poly_mult)
          thus ?thesis using that[OF `x+1>x`] by auto
        qed
      show "\<exists>b>x. \<forall>z>x. z < b \<longrightarrow> (0 < poly (p' * q * (p' * p)) z) = (0 < poly (q * p) z)"
        proof (rule_tac x="b" in exI, rule conjI[OF `b>x`],rule allI,rule impI,rule impI)
          fix z assume "x < z"  "z < b"
          hence "0<poly (p'*p') z" using b by auto
          have " (0 < poly (p' * q * (p' * p)) z)=(0<poly (p'*p') z * poly (q*p) z)"
            by (simp add: ac_simps)
          also have "...=(0<poly (q*p) z)"
            using `0<poly (p'*p') z` by (metis mult_pos_pos zero_less_mult_pos)
          finally show "(0 < poly (p' * q * (p' * p)) z) = (0 < poly (q * p) z)" .
        qed
    qed
  moreover from False assms
    have "odd (order x (p' * p) - order x (p' * q)) = odd (order x p - order x q)"
    by (simp add: order_mult)
  moreover have " p' * q \<noteq> 0 \<longleftrightarrow> q \<noteq> 0"
    by (metis assms(2) mult_eq_0_iff)
  ultimately show "jump (p' * q) (p' * p) x = jump q p x" unfolding jump_def by auto
qed

lemma sjump_mult:
  fixes p1 p2::"real poly"
  assumes  "order x p1=0 \<or> order x p2=0" "p1\<noteq>0" "p2\<noteq>0"
  shows "sjump (p1*p2) x= sign (poly p2 x) * sjump p1 x + sign (poly p1 x) * sjump p2 x" (is "?L=?R")
proof (cases "order x p1=0")
  case True
  hence "poly p1 x\<noteq>0" by (metis assms(2) order_root)
  have "p1*p2\<noteq>0" using `p1\<noteq>0` `p2\<noteq>0` by auto
  def simpL\<equiv>"(if odd (order x p2) then if (poly p1 x>0)
    \<longleftrightarrow>  sign_r_pos p2 x then 1::int else -1 else 0)"
  have "?L=simpL"
    unfolding simpL_def sjump_def  order_mult[OF `p1*p2\<noteq>0`] True sign_r_pos_mult[OF `p1\<noteq>0` `p2\<noteq>0`]
    sign_r_pos_rec[OF `p1\<noteq>0`] using `poly p1 x \<noteq> 0` by auto
  moreover have "poly p1 x>0 \<Longrightarrow> simpL =?R"
    unfolding simpL_def sjump_not_root[OF `poly p1 x\<noteq>0`]
    by (simp, unfold sjump_def, auto)
  moreover have "poly p1 x<0 \<Longrightarrow> simpL =?R"
    unfolding simpL_def sjump_not_root[OF `poly p1 x\<noteq>0`]
    by (simp, unfold sjump_def,auto)
  ultimately show "?L=?R" using `poly p1 x\<noteq>0` by (metis linorder_neqE_linordered_idom)
next
  case False
  hence "order x p2=0" and "poly p2 x\<noteq>0"
    by (metis assms(1), metis False assms(1) assms(3) order_root)
  have "p1*p2\<noteq>0" using `p1\<noteq>0` `p2\<noteq>0` by auto
  def simpL\<equiv>" (if odd (order x p1) then if (poly p2 x>0)
    \<longleftrightarrow>  sign_r_pos p1 x then 1::int else -1 else 0)"
  have "?L=simpL"
    unfolding simpL_def sjump_def  order_mult[OF `p1*p2\<noteq>0`] `order x p2=0`
    sign_r_pos_mult[OF `p1\<noteq>0` `p2\<noteq>0`] sign_r_pos_rec[OF `p2\<noteq>0`] using `poly p2 x \<noteq> 0` by auto
  moreover have "poly p2 x>0 \<Longrightarrow> simpL =?R"
    unfolding simpL_def sjump_not_root[OF `poly p2 x\<noteq>0`]
    by (simp, unfold sjump_def, auto)
  moreover have "poly p2 x<0 \<Longrightarrow> simpL =?R"
    unfolding simpL_def sjump_not_root[OF `poly p2 x\<noteq>0`]
    by (simp, unfold sjump_def,auto)
  ultimately show "?L=?R" using `poly p2 x\<noteq>0` by (metis linorder_neqE_linordered_idom)
qed


lemma jump_mod:
  fixes p q::"real poly"
  assumes "p\<noteq>0"
  shows "jump q p x= jump (q mod p) p x"
proof (cases "q=0")
  assume "q=0"
  thus ?thesis unfolding jump_def by auto
next
  assume "q\<noteq>0"
  def n\<equiv>"min (order x q) (order x p)"
  obtain q' where q':"q=[:-x,1:]^n * q'"
    using n_def  power_le_dvd[OF order_1[of x q], of n]
    by (metis dvdE min.cobounded2 min.commute)
  obtain p' where p':"p=[:-x,1:]^n * p'"
    using n_def  power_le_dvd[OF order_1[of x p], of n]
    by (metis dvdE min.cobounded2)
  have "q'\<noteq>0" and "p'\<noteq>0" using q' p' `p\<noteq>0` `q\<noteq>0` by auto
  have "order x q'=0 \<or> order x p'=0"
    proof (rule ccontr)
      assume "\<not> (order x q' = 0 \<or> order x p' = 0)"
      hence "order x q' > 0" and "order x p' > 0" by auto
      hence "order x q>n" and "order x p>n" unfolding q' p'
        using order_mult[OF `q\<noteq>0`[unfolded q'],of x] order_mult[OF `p\<noteq>0`[unfolded p'],of x]
          order_power_n_n[of x n]
        by auto
      thus False using n_def by auto
    qed
  have cond:"q' \<noteq> 0 \<and> odd (order x p' - order x q')
    = (q' mod p' \<noteq>0 \<and> odd(order x p' - order x (q' mod p')))"
    proof (cases "order x p'=0")
      case True
      thus ?thesis by (metis `q' \<noteq> 0` even_zero zero_diff)
    next
      case False
      hence "order x q'=0" using `order x q'=0 \<or> order x p'=0` by auto
      hence "\<not> [:-x,1:] dvd q'"
        by (metis `q' \<noteq> 0` order_root poly_eq_0_iff_dvd)
      moreover have "[:-x,1:] dvd p'" using False
        by (metis order_root poly_eq_0_iff_dvd)
      ultimately have "\<not> [:-x,1:] dvd (q' mod p')"
        by (metis dvd_mod_iff)
      hence "order x (q' mod p') = 0" and "q' mod p' \<noteq>0"
        apply (metis order_root poly_eq_0_iff_dvd)
        by (metis `\<not> [:- x, 1:] dvd q' mod p'` dvd_0_right)
      thus ?thesis using `order x q'=0` by auto
    qed
  moreover have "q' mod p'\<noteq>0 \<Longrightarrow> poly p' x = 0
      \<Longrightarrow> sign_r_pos (q' * p') x= sign_r_pos (q' mod p' * p') x"
    proof -
      assume "q' mod p'\<noteq>0" "poly p' x = 0"
      hence "poly q' x\<noteq>0" using `order x q'=0 \<or> order x p'=0`
        by (metis `p' \<noteq> 0` `q' \<noteq> 0` order_root)
      hence "sign_r_pos q' x= sign_r_pos (q' mod p') x"
        using sign_r_pos_mod[OF `poly p' x=0`] by auto
      thus ?thesis
        unfolding sign_r_pos_mult[OF `q'\<noteq>0` `p'\<noteq>0`] sign_r_pos_mult[OF `q' mod p'\<noteq>0` `p'\<noteq>0`]
        by auto
    qed
  moreover have "q' mod p' = 0 \<or> poly p' x \<noteq> 0 \<Longrightarrow> jump q' p' x = jump (q' mod p') p' x"
    proof -
      assume assm:"q' mod p' = 0 \<or> poly p' x \<noteq> 0"
      have "q' mod p' = 0 \<Longrightarrow> ?thesis" unfolding jump_def
        using cond by auto
      moreover have "poly p' x \<noteq> 0
          \<Longrightarrow> \<not> odd (order x p' - order x q') \<and> \<not> odd(order x p' - order x (q' mod p'))"
        by (metis even_zero order_root zero_diff)
      hence "poly p' x \<noteq> 0 \<Longrightarrow> ?thesis" unfolding jump_def by auto
      ultimately show ?thesis using assm by auto
    qed
  ultimately have "jump q' p' x = jump (q' mod p') p' x" unfolding jump_def by force
  thus ?thesis using p' q' jump_mult[OF `p'\<noteq>0`] by auto
qed

lemma jump_coprime:
  fixes p q:: "real poly"
  assumes "p\<noteq>0" "q\<noteq>0" "poly p x=0" "coprime p q"
  shows "jump q p x= sjump (q*p) x"
proof -
  have "order x p = 0 \<or> order x q = 0"
   by (rule ccontr, metis (poly_guards_query) assms(2) assms(4) order_root poly_1 poly_all_0_iff_0
     poly_eq_0_iff_dvd poly_gcd_greatest poly_gcd_zero_iff)
  hence "order x q=0" by (metis assms(1) assms(3) order_root)
  hence "order x p - order x q=order x (q * p)"
    using `p\<noteq>0` `q\<noteq>0` order_mult [of q p x] by auto
  thus ?thesis unfolding jump_def sjump_def using `q\<noteq>0` by auto
qed

lemma jump_sgn:
  fixes p q:: "real poly"
  assumes "p\<noteq>0" "poly p x=0"
  shows "jump (pderiv p * q) p x = sign (poly q x)"
proof (cases "q=0")
  case True
  thus ?thesis by auto
next
  case False
  have "pderiv p\<noteq>0" using `p\<noteq>0` `poly p x=0`
    by (metis mult_poly_0_left sign_r_pos_0 sign_r_pos_pderiv)
  have elim_p_order: "order x p - order x (pderiv p * q)=1 - order x q"
    proof -
      have "order x p - order x (pderiv p * q)=order x p - order x (pderiv p) - order x q"
        using order_mult `pderiv p\<noteq>0` False by (metis diff_diff_left mult_eq_0_iff)
      moreover have "order x p - order x (pderiv p) = 1"
        using order_pderiv[OF `pderiv p\<noteq>0`, of x] `poly p x=0` order_root[of p x] `p\<noteq>0` by auto
      ultimately show ?thesis by auto
    qed
  have elim_p_sign_r_pos:"sign_r_pos (pderiv p * q * p) x=sign_r_pos q x"
    proof -
      have "sign_r_pos (pderiv p * q * p) x = (sign_r_pos (pderiv p* p) x \<longleftrightarrow> sign_r_pos q x)"
        by (metis `q \<noteq> 0` `pderiv p \<noteq> 0` assms(1) no_zero_divisors sign_r_pos_mult)
      thus ?thesis using sign_r_pos_pderiv[OF `poly p x=0` `p\<noteq>0`] by auto
    qed
  def simpleL\<equiv>"if pderiv p * q \<noteq> 0 \<and> odd (1 - order x q) then
      if sign_r_pos q x then 1::int else - 1 else 0"
  have "jump (pderiv p * q) p x =simpleL"
    unfolding simpleL_def jump_def by (subst elim_p_order, subst elim_p_sign_r_pos,simp)
  moreover have "poly q x=0 \<Longrightarrow> simpleL=sign (poly q x)"
    proof -
      assume "poly q x=0"
      hence "1-order x q = 0" using `q\<noteq>0` by (metis less_one not_gr0 order_root zero_less_diff)
      hence "simpleL=0" unfolding simpleL_def by auto
      moreover have "sign (poly q x)=0" using `poly q x=0` by auto
      ultimately show ?thesis by auto
    qed
  moreover have "poly q x\<noteq>0\<Longrightarrow> simpleL=sign (poly q x)"
    proof -
      assume "poly q x\<noteq>0"
      hence "odd (1 - order x q)" by (metis diff_zero odd_one order_root)
      moreover have "pderiv p * q \<noteq> 0" by (metis False `pderiv p \<noteq> 0` no_zero_divisors)
      moreover have "sign_r_pos q x = (poly q x > 0)"
        using sign_r_pos_rec[OF False] `poly q x\<noteq>0` by auto
      ultimately have "simpleL=(if poly q x>0 then 1 else - 1)" unfolding simpleL_def by auto
      thus ?thesis using `poly q x\<noteq>0` by auto
    qed
  ultimately show ?thesis by force
qed

lemma sum_sjump_cross:
  fixes p::"real poly" and a b::real
  assumes "p\<noteq>0" "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "(\<Sum>x\<in>{x.  a< x\<and> x< b \<and> poly p x=0 }. sjump p x) = cross p a b"
    using `p\<noteq>0` `poly p a\<noteq>0` `poly p b\<noteq>0`
proof (cases "{x. a< x\<and> x< b \<and> poly p x=0 }\<noteq>{}", induct "degree p" arbitrary:p rule:nat_less_induct)
  case 1
  def roots\<equiv>"{x.  a< x\<and> x< b \<and> poly p x=0 }"
  have "finite roots" unfolding roots_def using poly_roots_finite[OF `p\<noteq>0`] by auto
  def max_r\<equiv>"Max roots"
  hence "poly p max_r=0" and "a<max_r" and "max_r<b"
    using Max_in[OF `finite roots`] "1.prems"  unfolding roots_def by auto
  def max_rp\<equiv>"[:-max_r,1:]^order max_r p"
  then obtain p' where p':"p=p'*max_rp" and not_dvd:"\<not> [:-max_r,1:] dvd p'"
    by (metis "1.prems"(1) mult.commute order_decomp)
  hence "p'\<noteq>0" and "max_rp\<noteq>0" and "poly p' a\<noteq>0" and "poly p' b\<noteq>0"
      and  "poly max_rp a\<noteq>0" and "poly max_rp b\<noteq>0"
    using `p\<noteq>0` `poly p a\<noteq>0` `poly p b\<noteq>0`  by auto
  def max_r_sign\<equiv>"if odd(order max_r p) then -1 else 1::int"
  def roots'\<equiv>"{x.  a< x\<and> x< b \<and> poly p' x=0}"
  have "(\<Sum>x\<in>roots. sjump p x)= (\<Sum>x\<in>roots'. sjump p x)+ sjump p max_r"
    proof -
      have "roots=roots' \<union> {x.  a< x\<and> x< b \<and> poly max_rp x=0 }"
        unfolding roots_def roots'_def p' by auto
      moreover have "{x.  a < x \<and> x < b \<and>  poly max_rp x = 0 }={max_r}"
        unfolding max_rp_def using `poly p max_r=0`
        by (auto simp add: `a<max_r` `max_r<b`,metis "1.prems"(1) neq0_conv order_root)
      moreover hence "roots' \<inter> {x. a< x\<and> x< b \<and> poly max_rp x=0} ={}"
        unfolding roots'_def  using `\<not> [:-max_r,1:] dvd p'`
        by (metis (mono_tags) Int_insert_right_if0 inf_bot_right mem_Collect_eq poly_eq_0_iff_dvd)
      moreover have "finite roots'"
        using  p' `p\<noteq>0` by (metis `finite roots` calculation(1) calculation(2) finite_Un)
      ultimately show ?thesis using setsum.union_disjoint by auto
    qed
  moreover have "(\<Sum>x\<in>roots'. sjump p x) = max_r_sign * cross p' a b"
    proof -
      have "(\<Sum>x\<in>roots'. sjump p x) = (\<Sum>x\<in>roots'. max_r_sign * sjump p' x)"
        proof (rule setsum.cong,rule refl)
          fix x assume "x \<in> roots'"
          hence "x\<noteq>max_r" using not_dvd unfolding roots'_def
            by (metis (mono_tags, lifting) mem_Collect_eq poly_eq_0_iff_dvd )
          hence "poly max_rp x\<noteq>0" using poly_power_n_eq unfolding max_rp_def by auto
          hence "order x max_rp=0"  by (metis order_root)
          moreover have "sjump max_rp x=0"
            using `poly max_rp x\<noteq>0` by (metis sjump_not_root)
          moreover have "x\<in>roots"
            using `x \<in> roots'` unfolding roots_def roots'_def p' by auto
          hence "x<max_r"
            using Max_ge[OF `finite roots`,of x] `x\<noteq>max_r` by (fold max_r_def,auto)
          hence "sign (poly max_rp x) = max_r_sign"
            using `poly max_rp x \<noteq> 0` unfolding max_r_sign_def max_rp_def sign_def
            by (subst poly_power,simp add:linorder_class.not_less zero_less_power_eq)
          ultimately show "sjump p x = max_r_sign * sjump p' x"
            using sjump_mult[of x p' max_rp] `p\<noteq>0` unfolding p' by auto
        qed
      also have "... = max_r_sign * (\<Sum>x\<in>roots'. sjump p' x)"
        by (metis setsum_right_distrib)
      also have "... = max_r_sign * cross p' a b"
        proof (cases "roots'={}")
          case True
          hence "cross p' a b=0" unfolding roots'_def using cross_no_root[OF `a<b`] by auto
          thus ?thesis using True by simp
        next
          case False
          moreover have "degree max_rp\<noteq>0"
            unfolding max_rp_def degree_linear_power
            by (metis "1.prems"(1) `poly p max_r = 0` order_root)
          hence  "degree p' < degree p" unfolding p' degree_mult_eq[OF `p'\<noteq>0` `max_rp\<noteq>0`]
            by auto
          ultimately have "setsum (sjump p') roots' =  cross p' a b"
            unfolding roots'_def using "1.hyps" `p'\<noteq>0` `poly p' a\<noteq>0` `poly p' b\<noteq>0` by auto
          thus ?thesis by auto
        qed
      finally show ?thesis .
    qed
  moreover have "max_r_sign * cross p' a b + sjump p max_r = cross p a b" (is "?L=?R")
    proof (cases "odd (order max_r p)")
      case True
      have "poly max_rp a < 0"
        using poly_power_n_odd[OF True,of max_r a] `poly max_rp a\<noteq>0` `max_r>a`
        unfolding max_rp_def by linarith
      moreover have "poly max_rp b>0 "
        using poly_power_n_odd[OF True,of max_r b] `max_r<b`
        unfolding max_rp_def by linarith
      ultimately have "?R=cross p' a b + sign (poly p' a)"
        unfolding p' cross_def poly_mult
        using variation_mult_neg_1[of "poly max_rp a", unfolded mult.commute]
          variation_mult_pos(2)[of "poly max_rp b",unfolded mult.commute] `poly p' b\<noteq>0`
        by auto
      moreover have "?L=- cross p' a b + sign (poly p' b)"
        proof -
          have " sign_r_pos p' max_r = (poly p' max_r >0)"
            using sign_r_pos_rec[OF `p'\<noteq>0`] not_dvd by (metis poly_eq_0_iff_dvd)
          moreover have "(poly p' max_r>0) = (poly p' b>0)"
            proof (rule ccontr)
              assume "(0 < poly p' max_r) \<noteq> (0 < poly p' b)"
              hence "poly p' max_r * poly p' b <0"
                using `poly p' b\<noteq>0` not_dvd[folded poly_eq_0_iff_dvd]
                by (metis (poly_guards_query) linorder_neqE_linordered_idom mult_less_0_iff)
              then obtain r where "r>max_r" and "r<b" and "poly p' r=0"
                using poly_IVT[OF `max_r<b`] by auto
              hence "r\<in>roots" unfolding roots_def p' using `max_r>a` by auto
              thus False using `r>max_r` Max_ge[OF `finite roots`,of r] unfolding max_r_def by auto
            qed
          moreover have "sign_r_pos max_rp max_r"
            using sign_r_pos_power unfolding max_rp_def by auto
          ultimately show ?thesis
            using True `poly p' b\<noteq>0`
            unfolding max_r_sign_def sjump_def sign_r_pos_mult[OF `p'\<noteq>0` `max_rp\<noteq>0`] p' by auto
        qed
      moreover have "variation (poly p' a) (poly p' b) + sign (poly p' a)
          = - variation (poly p' a) (poly p' b) + sign (poly p' b)" unfolding cross_def
        by (cases "poly p' b" rule:linorder_cases[of 0], (cases "poly p' a" rule:linorder_cases[of 0],
          auto simp add:variation_cases `poly p' a \<noteq> 0` `poly p' b \<noteq> 0`)+)
      ultimately show ?thesis unfolding cross_def by auto
    next
      case False
      hence "poly max_rp a > 0"
        unfolding max_rp_def poly_power
        using `poly max_rp a \<noteq> 0` "1.prems" `poly p max_r = 0`
        zero_le_even_power [of _ "a - max_r"]
        by (auto simp add: le_less)
      moreover have "poly max_rp b > 0"
        unfolding max_rp_def poly_power
        using `poly max_rp b \<noteq> 0` False max_rp_def poly_power zero_le_even_power [of "order max_r p" "b - max_r"]
        by (auto simp add: le_less)
      ultimately have "?R=cross p' a b"
        unfolding p' mult.commute cross_def using variation_mult_pos
        by auto
      thus ?thesis unfolding max_r_sign_def sjump_def using False by auto
    qed
  ultimately show ?case by (fold roots_def,auto)
next
  case False
  hence "cross p a b=0" using cross_no_root[OF `a<b`] by auto
  thus ?thesis using False by (metis setsum.empty)
qed

section {*Cauchy index*}

definition cindex:: "'a:: {linordered_idom,order_topology} \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int"
  where
  "cindex a b q p\<equiv> (\<Sum>x\<in>{x. poly p x=0 \<and> a< x\<and> x< b}. jump q p x)"

lemma cindex_0: "cindex a b 0 p = 0" unfolding cindex_def by auto

lemma cindex_mult:
  fixes p q p'::"real poly"
  assumes "p \<noteq> 0" "p'\<noteq> 0"
  shows "cindex a b (p' * q ) (p' * p) = cindex a b q p"
unfolding cindex_def
proof (rule Groups_Big.comm_monoid_add_class.setsum.mono_neutral_cong_right)
  show "finite {x. poly (p' * p) x = 0 \<and> a < x \<and> x < b}"
    using poly_roots_finite assms
    by (metis (poly_guards_query) finite_Collect_conjI mult_eq_0_iff)
next
  show "{x. poly p x = 0 \<and> a < x \<and> x < b} \<subseteq> {x. poly (p' * p) x = 0 \<and> a < x \<and> x < b}" by auto
next
  show "\<forall>x\<in>{x. poly (p' * p) x = 0 \<and> a < x \<and> x < b} - {x. poly p x = 0 \<and> a < x \<and> x < b}.
      jump (p' *q) (p' * p) x = 0"
    proof
      fix x assume "x\<in>{x. poly (p' * p) x = 0 \<and> a < x \<and> x < b} - {x. poly p x = 0 \<and> a < x \<and> x < b}"
      hence "poly p x\<noteq>0" by auto
      thus "jump (p' * q) (p' * p) x = 0"
        unfolding jump_mult[OF `p \<noteq> 0` `p'\<noteq>0`] using jump_not_root by auto
    qed
next
  show "\<And>x. x \<in> {x. poly p x = 0 \<and> a < x \<and> x < b} \<Longrightarrow> jump (p' * q) (p' * p) x = jump q p x"
    using jump_mult[OF `p \<noteq> 0` `p'\<noteq>0`] by auto
qed

lemma cindex_smult_1:
  fixes p q::"real poly" and c::real
  assumes "p\<noteq>0"
  shows "cindex a b (smult c q) p =  (sign c) * cindex a b q p"
unfolding cindex_def
using setsum_right_distrib[THEN sym, of "sign c" "\<lambda>x. jump q p x"
    "{x. poly p x = (0::real) \<and> a < x \<and> x < b}"] jump_smult_1[OF `p\<noteq>0`]
  by auto

lemma cindex_smult_2:
  fixes p q::"real poly" and c::real
  assumes "p\<noteq>0" "c\<noteq> 0"
  shows "cindex a b q (smult c p) =  (sgn c) * cindex a b q p"
unfolding cindex_def of_int_setsum jump_smult_2[OF `p\<noteq>0` `c\<noteq>0`,of q]
using setsum_right_distrib[THEN sym, of "sgn c" "\<lambda>x. jump q p x"
    "{x. poly p x = (0::real) \<and> a < x \<and> x < b}"]
  by (simp add: `c\<noteq>0`)

lemma cindex_mod:
  fixes p q::"real poly"
  assumes "p\<noteq>0"
  shows "cindex a b q p =  cindex a b (q mod p) p"
unfolding cindex_def using jump_mod[OF `p\<noteq>0`] by auto

lemma cindex_sjump:
  fixes p q::"real poly"
  assumes "p\<noteq>0" "q\<noteq>0" "coprime p q"
  shows "cindex a b q p + cindex a b p q=(\<Sum>x | a<x \<and> x<b \<and> poly (p*q) x=0. sjump (p*q) x)"
    (is "?L=?R")
proof -
  def A\<equiv>"{x. poly p x = 0 \<and> a < x \<and> x < b}"
  def B\<equiv>"{x. poly q x = 0 \<and> a < x \<and> x < b}"
  have "?L = setsum (\<lambda>x. sjump (p*q) x) A + setsum (\<lambda>x. sjump (p*q) x) B"
    proof -
      have "cindex a b q p = setsum (\<lambda>x. sjump (p*q) x) A" unfolding A_def cindex_def
        using jump_coprime[OF `p\<noteq>0` `q\<noteq>0` _ `coprime p q`,folded mult.commute] by auto
      moreover have "coprime q p" using `coprime p q` by (metis poly_gcd_commute)
      hence "cindex a b p q = setsum (\<lambda>x. sjump (p*q) x) B" unfolding B_def cindex_def
        using jump_coprime[OF `q\<noteq>0` `p\<noteq>0`] by auto
      ultimately show ?thesis by auto
    qed
  moreover have "A \<union> B= {x. a<x \<and> x<b \<and> poly (p*q) x=0}" unfolding poly_mult A_def B_def by auto
  moreover have "A \<inter> B={}"
    proof (rule ccontr)
      assume "A \<inter> B\<noteq>{}"
      then obtain x where "x\<in>A" and "x\<in>B" by auto
      hence "poly p x=0" and "poly q x=0" unfolding A_def B_def by auto
      hence "gcd p q\<noteq>1" by (metis poly_1 poly_eq_0_iff_dvd poly_gcd_greatest zero_neq_one)
      thus False using `coprime p q` by auto
    qed
  moreover have "finite A" and "finite B"
    unfolding A_def B_def using poly_roots_finite assms by fast+
  ultimately show ?thesis using setsum.union_disjoint by metis
qed

lemma cindex_cross:
  fixes p q::"real poly"
  assumes "a < b" "poly (p * q) a \<noteq>0" "poly (p * q) b \<noteq>0"
  shows "cindex a b q p + cindex a b p q = cross (p * q) a b" (is "?L=?R")
proof -
  have "p\<noteq>0" and "q\<noteq>0" using `poly (p * q) a \<noteq>0` by auto
  def g\<equiv>"gcd p q"
  obtain p' q' where p':"p= p'*g" and q':"q=q'*g"
    using poly_gcd_dvd1 poly_gcd_dvd2 dvd_def[of "gcd p q", unfolded mult.commute] g_def by metis
  hence "coprime p' q'" using gcd_coprime_poly `p\<noteq>0` unfolding g_def by auto
  have "p'\<noteq>0" "q'\<noteq>0" "g \<noteq>0" using p' q' `p\<noteq>0` `q\<noteq>0` by auto
  have "?L=cindex a b q' p' + cindex a b p' q'"
    unfolding p' q' mult.commute using cindex_mult[OF `p'\<noteq>0` `g\<noteq>0`] cindex_mult[OF `q'\<noteq>0` `g\<noteq>0`]
    by auto
  also have "... =(\<Sum>x | a < x \<and> x < b \<and> poly (p' * q') x = 0. sjump (p' * q') x)"
    using  cindex_sjump[OF `p'\<noteq>0` `q'\<noteq>0` `coprime p' q'`, of a b] .
  also have "... = cross (p' * q') a b"
    using  sum_sjump_cross[OF _ `a<b`, of "p'*q'"] `p'\<noteq>0` `q'\<noteq>0`
      `poly (p * q) a \<noteq>0` `poly (p * q) b \<noteq>0`
    unfolding p' q' by auto
  also have "... = ?R"
    proof -
      have "poly (p * q) a = poly (g*g) a * poly (p' * q') a"
        and "poly (p * q) b = poly (g*g) b * poly (p' * q') b"
        unfolding p' q' by auto
      moreover have "poly g a\<noteq>0" using `poly (p * q) a \<noteq>0`
        unfolding p' by auto
      hence "poly (g*g) a>0"
        by (metis (poly_guards_query) not_real_square_gt_zero poly_mult)
      moreover have "poly g b\<noteq>0" using `poly (p * q) b \<noteq>0`
        unfolding p' by auto
      hence "poly (g*g) b>0" by (metis (poly_guards_query) not_real_square_gt_zero poly_mult)
      ultimately show ?thesis
        unfolding cross_def using variation_mult_pos by auto
    qed
  finally show "?L = ?R" .
qed

lemma cindex_rec:
  fixes p q::"real poly"
  assumes "a < b" "poly (p * q) a \<noteq>0" "poly (p * q) b \<noteq>0"
  shows "cindex a b q p  = cross (p * q) a b  +  cindex a b (- (p mod q)) q" (is "?L=?R")
proof -
  have "q\<noteq>0" using `poly (p * q) a \<noteq>0` by auto
  note cindex_cross[OF assms]
  moreover have "- cindex a b p q = cindex a b (- (p mod q)) q"
    using cindex_mod[OF `q\<noteq>0`, of a b p] cindex_smult_1[OF `q\<noteq>0`,of a b "-1"]
    by auto
  ultimately show ?thesis by auto
qed

lemma cindex_congr:
  fixes p q:: "real poly"
  assumes "a<a'" "a'<b'" "b'<b" "p\<noteq>0"
  assumes "\<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
  shows "cindex a b q p=cindex a' b' q p"
unfolding cindex_def
proof (rule setsum.mono_neutral_right)
  show "finite {x. poly p x = 0 \<and> a < x \<and> x < b}" using poly_roots_finite[OF `p\<noteq>0`] by auto
next
  show "{x. poly p x = 0 \<and> a' < x \<and> x < b'} \<subseteq> {x. poly p x = 0 \<and> a < x \<and> x < b}"
    using assms by auto
next
  show "\<forall>i\<in>{x. poly p x = 0 \<and> a < x \<and> x < b} - {x. poly p x = 0 \<and> a' < x \<and> x < b'}. jump q p i = 0"
    using assms(5) jump_not_root by auto
qed

lemma cindex_taq:
  fixes p q::"real poly"
  assumes "p\<noteq>0"
  shows "taq {x. poly p x = 0 \<and> a < x \<and> x < b} q=cindex a b (pderiv p * q) p"
unfolding cindex_def taq_def
by (rule setsum.cong,auto simp add:jump_sgn[OF `p\<noteq>0`])

section{*Signed remainder sequence*}

function smods:: "real poly \<Rightarrow> real poly \<Rightarrow> (real poly) list" where
  "smods p q= (if p=0 then [] else Cons p (smods q (-(p mod q))))"
by auto
termination
 apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 apply simp_all
 apply (metis degree_mod_less)
done

lemma smods_nil_eq:"smods p q = [] \<longleftrightarrow> (p=0)" by auto
lemma smods_singleton:"[x] = smods p q \<Longrightarrow> (p\<noteq>0 \<and> q=0 \<and> x=p)"
  by (metis list.discI list.inject smods.elims)

lemma smods_0[simp]:
  "smods 0 q = []"
  "smods p 0 = (if p=0 then [] else [p])"
by auto

lemma no_0_in_smods: "0\<notin>set (smods p q)"
  apply (induct "smods p q" arbitrary:p q)
  by (simp,metis list.inject neq_Nil_conv set_ConsD smods.elims)

fun changes:: "real list \<Rightarrow> int" where
  "changes [] = 0"|
  "changes [_] = 0" |
  "changes (x1#x2#xs) = (if x1*x2<0 then 1+changes (x2#xs)
                          else if x2=0 then changes (x1#xs)
                          else changes (x2#xs))"

lemma changes_map_sgn_eq:
  "changes xs = changes (map sgn xs)"
proof (induct xs rule:changes.induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 x1 x2 xs)
  moreover have "x1*x2<0 \<longleftrightarrow> sgn x1 * sgn x2 < 0"
    by (unfold mult_less_0_iff sgn_less sgn_greater,simp)
  moreover have "x2=0 \<longleftrightarrow> sgn x2 =0" by (rule sgn_zero_iff[symmetric])
  ultimately show ?case by auto
qed

definition changes_poly_at::"real poly list \<Rightarrow> real \<Rightarrow> int" where
  "changes_poly_at ps a= changes (map (\<lambda>p. poly p a) ps)"

definition changes_poly_pos_inf:: "real poly list \<Rightarrow> int" where
  "changes_poly_pos_inf ps = changes (map sgn_pos_inf ps)"

definition changes_poly_neg_inf:: "real poly list \<Rightarrow> int" where
  "changes_poly_neg_inf ps = changes (map sgn_neg_inf ps)"

lemma changes_poly_at_0[simp]:
  "changes_poly_at [] a =0"
  "changes_poly_at [p] a=0"
unfolding changes_poly_at_def by auto

definition changes_itv_smods:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_itv_smods a b p q= (let ps= smods p q in changes_poly_at ps a - changes_poly_at ps b)"

definition changes_gt_smods:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_gt_smods a p q= (let ps= smods p q in changes_poly_at ps a - changes_poly_pos_inf ps)"

definition changes_le_smods:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_le_smods b p q= (let ps= smods p q in changes_poly_neg_inf ps - changes_poly_at ps b)"

definition changes_R_smods:: "real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_R_smods p q= (let ps= smods p q in changes_poly_neg_inf ps - changes_poly_pos_inf ps)"

lemma changes_itv_smods_0[simp]:
  "changes_itv_smods a b 0 q = 0"
  "changes_itv_smods a b p 0 = 0"
unfolding changes_itv_smods_def
by auto

lemma changes_itv_smods_rec:
  assumes "a<b" "poly (p*q) a\<noteq>0" "poly (p*q) b\<noteq>0"
  shows "changes_itv_smods a b p q  = cross (p*q) a b + changes_itv_smods a b q (-(p mod q))"
proof (cases "p=0 \<or> q=0 \<or> p mod q = 0")
  case True
  moreover have "p=0 \<or> q=0 \<Longrightarrow> ?thesis"
    unfolding changes_itv_smods_def changes_poly_at_def by (erule HOL.disjE,auto)
  moreover have "p mod q = 0 \<Longrightarrow> ?thesis"
    unfolding changes_itv_smods_def changes_poly_at_def cross_def
    apply (insert assms(2,3))
    apply (subst (asm) (1 2) neq_iff)
    by (auto simp add: variation_cases)
  ultimately show ?thesis by auto
next
  case False
  hence "p\<noteq>0" "q\<noteq>0" "p mod q\<noteq>0" by auto
  then obtain ps where ps:"smods p q=p#q#-(p mod q)#ps" "smods q (-(p mod q)) = q#-(p mod q)#ps"
    by auto
  def changes_diff\<equiv> "\<lambda>x. changes_poly_at (p#q#-(p mod q)#ps) x
    - changes_poly_at (q#-(p mod q)#ps) x"
  have "\<And>x. poly p x*poly q x<0 \<Longrightarrow> changes_diff x=1"
    unfolding changes_diff_def changes_poly_at_def by auto
  moreover have "\<And>x. poly p x*poly q x>0 \<Longrightarrow> changes_diff x=0"
    unfolding changes_diff_def changes_poly_at_def  by auto
  ultimately have "changes_diff a - changes_diff b=cross (p*q) a b"
    unfolding cross_def
    apply (cases rule:neqE[OF `poly (p*q) a\<noteq>0`])
    by (cases rule:neqE[OF `poly (p*q) b\<noteq>0`],auto simp add:variation_cases)+
  thus ?thesis unfolding changes_itv_smods_def changes_diff_def changes_poly_at_def
    using ps by auto
qed

lemma changes_smods_congr:
  fixes p q:: "real poly"
  assumes "a\<noteq>a'" "p\<noteq>0" "poly p a\<noteq>0"
  assumes "\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (a'\<le>x \<and> x<a)) \<longrightarrow> poly p x \<noteq>0"
  shows "changes_poly_at (smods p q) a = changes_poly_at (smods p q) a'"
    using assms(2-4)
proof (induct "smods p q" arbitrary:p q rule:length_induct)
  case 1
  def r1\<equiv>"- (p mod q)"
  have a_a'_rel:"\<forall>pp\<in>set (smods p q). poly pp a * poly pp a' \<ge>0"
    proof (rule ccontr)
      assume "\<not> (\<forall>pp\<in>set (smods p q). 0 \<le> poly pp a * poly pp a')"
      then obtain pp where pp:"pp\<in>set (smods p q)" " poly pp a * poly pp a'<0"
        using `p\<noteq>0` by (metis less_eq_real_def linorder_neqE_linordered_idom)
      hence "a<a' \<Longrightarrow> False" using "1.prems"(3) poly_IVT[of a a' pp] by auto
      moreover have "a'<a\<Longrightarrow>False"
        using pp[unfolded mult.commute[of "poly pp a"]] "1.prems"(3) poly_IVT[of a' a pp] by auto
      ultimately show False using `a\<noteq>a'` by force
    qed
  have "q=0 \<Longrightarrow> ?case" by auto
  moreover have "\<lbrakk>q\<noteq>0;poly q a=0\<rbrakk> \<Longrightarrow> ?case"
    proof -
      assume "q\<noteq>0" "poly q a=0"
      def r2\<equiv>"- (q mod r1)"
      have "- poly r1 a = poly p a "
        using mod_div_equality[of p q] `poly q a=0` unfolding r1_def poly_minus minus_minus
        by (metis mod_add_self1 mod_by_0 mod_mult_self2_is_0 poly_0 poly_mult poly_add)
      hence "r1\<noteq>0" and "poly r1 a\<noteq>0" and "poly p a*poly r1 a<0" using `poly p a\<noteq>0`
        by (auto dest!: sym [of "- poly r1 a"] simp add: mult_less_0_iff)
      then obtain ps where ps:"smods p q=p#q#r1#ps" "smods r1 r2=r1#ps"
        by (metis "1.prems"(1) `q \<noteq> 0` r1_def r2_def smods.simps)
      hence "length (smods r1 r2)<length (smods p q)" by auto
      moreover have "(\<forall>p\<in>set (smods r1 r2). \<forall>x. a < x \<and> x \<le> a' \<or> a' \<le> x \<and> x < a \<longrightarrow> poly p x \<noteq> 0)"
        using "1.prems"(3) unfolding ps by auto
      ultimately have "changes_poly_at (smods r1 r2) a = changes_poly_at (smods r1 r2) a'"
        using "1.hyps" `r1\<noteq>0` `poly r1 a\<noteq>0` by metis
      moreover have "changes_poly_at (smods p q) a = 1+changes_poly_at (smods r1 r2) a"
        unfolding ps changes_poly_at_def using `poly q a=0` `poly p a*poly r1 a<0` by auto
      moreover have "changes_poly_at (smods p q) a' = 1+changes_poly_at (smods r1 r2) a'"
        proof -
          have "poly p a * poly p a' \<ge>0" and "poly r1 a*poly r1 a'\<ge>0"
            using a_a'_rel unfolding ps by auto
          moreover have "poly p a'\<noteq>0" and "poly q a'\<noteq>0" and "poly r1 a'\<noteq>0"
            using "1.prems"(3)[unfolded ps] `a\<noteq>a'` by auto
          ultimately show ?thesis using `poly p a*poly r1 a<0` unfolding ps changes_poly_at_def
            by (auto simp add: zero_le_mult_iff, auto simp add: mult_less_0_iff)
        qed
      ultimately show ?thesis by simp
    qed
  moreover have "\<lbrakk>q\<noteq>0;poly q a\<noteq>0\<rbrakk> \<Longrightarrow> ?case"
    proof -
      assume "q\<noteq>0" "poly q a\<noteq>0"
      then obtain ps where ps:"smods p q=p#q#ps" "smods q r1=q#ps"
        by (metis "1.prems"(1) r1_def smods.simps)
      hence "length (smods q r1) < length (smods p q)" by auto
      moreover have "(\<forall>p\<in>set (smods q r1). \<forall>x. a < x \<and> x \<le> a' \<or> a' \<le> x \<and> x < a \<longrightarrow> poly p x \<noteq> 0)"
        using "1.prems"(3) unfolding ps by auto
      ultimately have "changes_poly_at (smods q r1) a = changes_poly_at (smods q r1) a'"
        using "1.hyps" `q\<noteq>0` `poly q a\<noteq>0` by metis
      moreover have "poly p a'\<noteq>0" and "poly q a'\<noteq>0"
        using "1.prems"(3)[unfolded ps] `a\<noteq>a'` by auto
      moreover  have "poly p a * poly p a' \<ge>0" and "poly q a*poly q a'\<ge>0"
        using a_a'_rel unfolding ps by auto
      ultimately show ?thesis unfolding ps changes_poly_at_def using  `poly q a\<noteq>0` `poly p a\<noteq>0`
        by (auto simp add: zero_le_mult_iff,auto simp add: mult_less_0_iff)
    qed
  ultimately show ?case by blast
qed

lemma changes_itv_smods_congr:
  fixes p q:: "real poly"
  assumes "a<a'" "a'<b'" "b'<b" "p\<noteq>0" "poly p a\<noteq>0" "poly p b\<noteq>0"
  assumes no_root:"\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
  shows "changes_itv_smods a b p q=changes_itv_smods a' b' p q"
proof -
  have "changes_poly_at (smods p q) a = changes_poly_at (smods p q) a'"
    apply (rule changes_smods_congr[OF order.strict_implies_not_eq[OF `a<a'`] `p\<noteq>0` `poly p a\<noteq>0`])
    by (metis assms(1) less_eq_real_def less_irrefl less_trans no_root)
  moreover have "changes_poly_at (smods p q) b = changes_poly_at (smods p q) b'"
    apply (rule changes_smods_congr[OF order.strict_implies_not_eq[OF `b'<b`,
        symmetric] `p\<noteq>0` `poly p b\<noteq>0`])
    by (metis assms(3) less_eq_real_def less_trans no_root)
  ultimately show ?thesis unfolding changes_itv_smods_def Let_def by auto
qed

lemma changes_itv_mods_cindex:
  assumes "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "changes_itv_smods a b p q = cindex a b q p" using assms
proof (induct "smods p q" arbitrary:p q a b)
  case Nil
  hence "p=0" by (metis smods_nil_eq)
  thus ?case using `poly p a \<noteq> 0` by simp
next
  case (Cons x1 xs)
  have "p\<noteq>0" using `poly p a \<noteq> 0` by auto
  obtain a' b' where "a<a'" "a'<b'" "b'<b"
      and no_root:"\<forall>p\<in>set (smods p q). \<forall>x. ((a<x\<and>x\<le>a') \<or> (b'\<le>x \<and> x<b)) \<longrightarrow> poly p x \<noteq>0"
    proof (induct "smods p q" arbitrary:p q thesis)
      case Nil
      def a'\<equiv>"2/3 * a + 1/3 * b" and b'\<equiv>"1/3*a + 2/3*b"
      have "a < a'" and "a' < b'" and "b' < b" unfolding a'_def b'_def using `a<b` by auto
      moreover have "\<forall>p\<in>set (smods p q). \<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        unfolding `[] = smods p q`[symmetric] by auto
      ultimately show ?case using Nil by auto
    next
      case (Cons x1 xs)
      def r\<equiv>"- (p mod q)"
      hence "smods p q=p#xs" and "smods q r=xs" and "p\<noteq>0"
        using `x1 # xs = smods p q` unfolding r_def
        by (metis Cons.hyps(2) list.distinct(1) list.inject smods.simps)+
      obtain a1 b1 where
          "a < a1"  "a1 < b1"  "b1 < b" and
          a1_b1_no_root:"\<forall>p\<in>set xs. \<forall>x. a < x \<and> x \<le> a1 \<or> b1 \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        using Cons(1)[OF `smods q r=xs`[symmetric]] `smods q r=xs` by auto
      obtain a2 b2 where
          "a<a2" and a2:"\<forall>x. a<x \<and> x\<le>a2 \<longrightarrow> poly p x \<noteq> 0"
          "b2<b" and b2:"\<forall>x. b2\<le>x \<and> x<b \<longrightarrow> poly p x \<noteq> 0"
        using next_non_root_interval[OF `p\<noteq>0`] last_non_root_interval[OF `p\<noteq>0`]
        by (metis less_numeral_extra(3))
      def a'\<equiv>"if b2>a then Min{a1, b2, a2} else min a1 a2"
        and b'\<equiv>"if a2 <b then Max{ b1, a2, b2} else max b1 b2"
      have "a < a'" "a' < b'" "b' < b" unfolding a'_def b'_def
        using  `a < a1` `a1 < b1` `b1 < b` `a<a2` `b2<b` `a<b` by auto
      moreover have "\<forall>p\<in>set xs. \<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        using a1_b1_no_root unfolding a'_def b'_def by auto
      moreover have "\<forall>x. a < x \<and> x \<le> a' \<or> b' \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0"
        using a2 b2 unfolding a'_def b'_def by auto
      ultimately show ?case using Cons(3)[unfolded `smods p q=p#xs`] by auto
    qed
  have "q=0 \<Longrightarrow> ?case" by (metis changes_itv_smods_0(2) cindex_0)
  moreover have "q\<noteq>0 \<Longrightarrow> ?case"
    proof -
      assume "q\<noteq>0"
      def r\<equiv>"- (p mod q)"
      obtain ps where ps:"smods p q=p#q#ps" "smods q r=q#ps" and "xs=q#ps"
        unfolding r_def using `q\<noteq>0` `p\<noteq>0` `x1 # xs = smods p q`
        by (metis list.inject smods.simps)
      have "poly p a' \<noteq> 0" "poly p b' \<noteq> 0" "poly q a' \<noteq> 0" "poly q b' \<noteq> 0"
        using no_root[unfolded ps] `a'>a` `b'<b` by auto
      moreover hence
          "changes_itv_smods a' b' p q = cross (p * q) a' b' + changes_itv_smods a' b' q r"
          "cindex a' b' q p = cross (p * q) a' b' + cindex a' b' r q"
        using changes_itv_smods_rec[OF `a'<b'`,of p q,folded r_def]
          cindex_rec[OF `a'<b'`,of p q,folded r_def] by auto
      moreover have "changes_itv_smods a' b' q r = cindex a' b' r q"
        using  Cons.hyps(1)[of q r a' b'] `a' < b'` `q \<noteq> 0` `xs = q # ps` ps(2)
          `poly q a' \<noteq> 0` `poly q b' \<noteq> 0` by simp
      ultimately have "changes_itv_smods a' b' p q = cindex a' b' q p" by auto
      thus ?thesis using
          changes_itv_smods_congr[OF `a<a'` `a'<b'` `b'<b` `p\<noteq>0` Cons(4,5),of q]
          no_root cindex_congr[OF `a<a'` `a'<b'` `b'<b` `p\<noteq>0`] ps
        by auto
    qed
  ultimately show ?case by metis
qed

lemma root_list_ub:
  fixes ps:: "(real poly) list" and a::real
  assumes "0\<notin>set ps"
  obtains ub where "\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and "\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p" and "ub>a"
    using assms
proof (induct ps arbitrary:thesis)
  case Nil
  show ?case using Nil(1)[of "a+1"] by auto
next
  case (Cons p ps)
  hence "p\<noteq>0" and "0\<notin>set ps" by auto
  then obtain ub1 where ub1:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x < ub1" and
      ub1_sgn:"\<forall>x\<ge>ub1. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p" and "ub1>a"
    using Cons.hyps by auto
  obtain ub2 where ub2:"\<forall>x. poly p x = 0 \<longrightarrow> x < ub2"
      and ub2_sgn: "\<forall>x\<ge>ub2. sgn (poly p x) = sgn_pos_inf p"
    using root_ub[OF `p\<noteq>0`] by auto
  def ub\<equiv>"max ub1 ub2"
  have "\<forall>p\<in>set (p # ps). \<forall>x. poly p x = 0 \<longrightarrow> x < ub" using ub1 ub2 ub_def by force
  moreover have "\<forall>x\<ge>ub. \<forall>p\<in>set (p # ps). sgn (poly p x) = sgn_pos_inf p"
    using ub1_sgn ub2_sgn ub_def by auto
  ultimately show ?case using Cons(2)[of ub] `ub1>a` ub_def by auto
qed

lemma root_list_lb:
  fixes ps:: "(real poly) list" and b::real
  assumes "0\<notin>set ps"
  obtains lb where "\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and "\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p" and "lb<b"
    using assms
proof (induct ps arbitrary:thesis)
  case Nil
  show ?case using Nil(1)[of "b - 1"] by auto
next
  case (Cons p ps)
  hence "p\<noteq>0" and "0\<notin>set ps" by auto
  then obtain lb1 where lb1:"\<forall>p\<in>set ps. \<forall>x. poly p x = 0 \<longrightarrow> x > lb1" and
      lb1_sgn:"\<forall>x\<le>lb1. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p" and "lb1<b"
    using Cons.hyps by auto
  obtain lb2 where lb2:"\<forall>x. poly p x = 0 \<longrightarrow> x > lb2"
      and lb2_sgn: "\<forall>x\<le>lb2. sgn (poly p x) = sgn_neg_inf p"
    using root_lb[OF `p\<noteq>0`] by auto
  def lb\<equiv>"min lb1 lb2"
  have "\<forall>p\<in>set (p # ps). \<forall>x. poly p x = 0 \<longrightarrow> x > lb" using lb1 lb2 lb_def by force
  moreover have "\<forall>x\<le>lb. \<forall>p\<in>set (p # ps). sgn (poly p x) = sgn_neg_inf p"
    using lb1_sgn lb2_sgn lb_def by auto
  ultimately show ?case using Cons(2)[of lb] `lb1<b` lb_def by auto
qed

theorem sturm_tarski_interval:
  assumes "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "taq {x. poly p x=0 \<and> a<x \<and> x<b} q = changes_itv_smods a b p (pderiv p * q)"
proof -
  have "p\<noteq>0" using `poly p a\<noteq>0` by auto
  thus ?thesis using cindex_taq changes_itv_mods_cindex[OF assms] by auto
qed

theorem sturm_tarski_above:
  assumes "poly p a\<noteq>0"
  shows "taq {x. poly p x=0 \<and> a<x} q = changes_gt_smods a p (pderiv p * q)"
proof -
  def ps\<equiv>"smods p (pderiv p * q)"
  have "p\<noteq>0" and "p\<in>set ps" using `poly p a\<noteq>0` ps_def by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>a"
    using root_list_ub[OF no_0_in_smods,of p "pderiv p * q",folded ps_def]
    by auto
  have "taq {x. poly p x=0 \<and> a<x} q = taq {x. poly p x=0 \<and> a<x \<and> x<ub} q"
    unfolding taq_def by (rule setsum.cong,insert ub `p\<in>set ps`,auto)
  moreover have "changes_gt_smods a p (pderiv p * q) = changes_itv_smods a ub p (pderiv p * q)"
    proof -
      have "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
        using ub_sgn[THEN spec,of ub,simplified]
        by (metis (mono_tags, lifting) comp_def list.map_cong0)
      hence "changes_poly_at ps ub=changes_poly_pos_inf ps"
        unfolding changes_poly_pos_inf_def changes_poly_at_def
        by (subst changes_map_sgn_eq,metis map_map)
      thus ?thesis unfolding changes_gt_smods_def changes_itv_smods_def ps_def
        by metis
    qed
  moreover have "poly p ub\<noteq>0" using ub `p\<in>set ps` by auto
  ultimately show ?thesis using sturm_tarski_interval[OF `ub>a` assms] by auto
qed

theorem sturm_tarski_below:
  assumes "poly p b\<noteq>0"
  shows "taq {x. poly p x=0 \<and> x<b} q = changes_le_smods b p (pderiv p * q)"
proof -
  def ps\<equiv>"smods p (pderiv p * q)"
  have "p\<noteq>0" and "p\<in>set ps" using `poly p b\<noteq>0` ps_def by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<b"
    using root_list_lb[OF no_0_in_smods,of p "pderiv p * q",folded ps_def]
    by auto
  have "taq {x. poly p x=0 \<and> x<b} q = taq {x. poly p x=0 \<and> lb<x \<and> x<b} q"
    unfolding taq_def by (rule setsum.cong,insert lb `p\<in>set ps`,auto)
  moreover have "changes_le_smods b p (pderiv p * q) = changes_itv_smods lb b p (pderiv p * q)"
    proof -
      have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
        using lb_sgn[THEN spec,of lb,simplified]
        by (metis (mono_tags, lifting) comp_def list.map_cong0)
      hence "changes_poly_at ps lb=changes_poly_neg_inf ps"
        unfolding changes_poly_neg_inf_def changes_poly_at_def
        by (subst changes_map_sgn_eq,metis map_map)
      thus ?thesis unfolding changes_le_smods_def changes_itv_smods_def ps_def
        by metis
    qed
  moreover have "poly p lb\<noteq>0" using lb `p\<in>set ps` by auto
  ultimately show ?thesis using sturm_tarski_interval[OF `lb<b` _ assms] by auto
qed

theorem sturm_tarski_R:
  assumes "p\<noteq>0"
  shows "taq {x. poly p x=0} q = changes_R_smods p (pderiv p * q)"
proof -
  def ps\<equiv>"smods p (pderiv p * q)"
  have "p\<in>set ps" using ps_def `p\<noteq>0` by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<0"
    using root_list_lb[OF no_0_in_smods,of p "pderiv p * q",folded ps_def]
    by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>0"
    using root_list_ub[OF no_0_in_smods,of p "pderiv p * q",folded ps_def]
    by auto
  have "taq {x. poly p x=0} q = taq {x. poly p x=0 \<and> lb<x \<and> x<ub} q"
    unfolding taq_def by (rule setsum.cong,insert lb ub `p\<in>set ps`,auto)
  moreover have "changes_R_smods p (pderiv p * q) = changes_itv_smods lb ub p (pderiv p * q)"
    proof -
      have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
          and "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
        using lb_sgn[THEN spec,of lb,simplified] ub_sgn[THEN spec,of ub,simplified]
        by (metis (mono_tags, lifting) comp_def list.map_cong0)+
      hence "changes_poly_at ps lb=changes_poly_neg_inf ps
          \<and> changes_poly_at ps ub=changes_poly_pos_inf ps"
        unfolding changes_poly_neg_inf_def changes_poly_at_def changes_poly_pos_inf_def
        by (subst (1 3)  changes_map_sgn_eq,metis map_map)
      thus ?thesis unfolding changes_R_smods_def changes_itv_smods_def ps_def
        by metis
    qed
  moreover have "poly p lb\<noteq>0" and "poly p ub\<noteq>0" using lb ub `p\<in>set ps` by auto
  moreover have "lb<ub" using `lb<0` `0<ub` by auto
  ultimately show ?thesis using sturm_tarski_interval by auto
qed

theorem sturm_interval:
  assumes "a < b" "poly p a \<noteq> 0" "poly p b \<noteq> 0"
  shows "card {x. poly p x = 0 \<and> a < x \<and> x < b} = changes_itv_smods a b p (pderiv p)"
using sturm_tarski_interval[OF assms, unfolded taq_def,of 1] by force

theorem sturm_above:
  assumes "poly p a \<noteq> 0"
  shows "card {x. poly p x = 0 \<and> a < x} = changes_gt_smods a p (pderiv p)"
using sturm_tarski_above[OF assms, unfolded taq_def,of 1] by force

theorem sturm_below:
  assumes "poly p b \<noteq> 0"
  shows "card {x. poly p x = 0 \<and> x < b} = changes_le_smods b p (pderiv p)"
using sturm_tarski_below[OF assms, unfolded taq_def,of 1] by force

theorem sturm_R:
  assumes "p\<noteq>0"
  shows "card {x. poly p x=0} =  changes_R_smods p (pderiv p)"
using sturm_tarski_R[OF `p\<noteq>0`,of 1,unfolded taq_def] by force

end

