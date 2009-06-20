(*  ID:         $Id: PresArith.thy,v 1.11 2009-06-20 00:10:18 nipkow Exp $
    Author:     Tobias Nipkow, 2007
*)

header{* Presburger arithmetic *}

theory PresArith
imports GCD QE ListVector
begin

declare iprod_assoc[simp]

subsection{*Syntax*}

datatype atom =
  Le int "int list" | Dvd int int "int list" | NDvd int int "int list"

fun divisor :: "atom \<Rightarrow> int" where
"divisor (Le i ks) = 1" |
"divisor (Dvd d i ks) = d" |
"divisor (NDvd d i ks) = d"

fun neg\<^isub>Z :: "atom \<Rightarrow> atom fm" where
"neg\<^isub>Z (Le i ks) = Atom(Le (1-i) (-ks))" |
"neg\<^isub>Z (Dvd d i ks) = Atom(NDvd d i ks)" |
"neg\<^isub>Z (NDvd d i ks) = Atom(Dvd d i ks)"

fun hd_coeff :: "atom \<Rightarrow> int" where
"hd_coeff (Le i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)" |
"hd_coeff (Dvd d i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)" |
"hd_coeff (NDvd d i ks) = (case ks of [] \<Rightarrow> 0 | k#_ \<Rightarrow> k)"

fun decr\<^isub>Z :: "atom \<Rightarrow> atom" where
"decr\<^isub>Z (Le i ks) = Le i (tl ks)" |
"decr\<^isub>Z (Dvd d i ks) = Dvd d i (tl ks)" |
"decr\<^isub>Z (NDvd d i ks) = NDvd d i (tl ks)"

fun I\<^isub>Z :: "atom \<Rightarrow> int list \<Rightarrow> bool" where
"I\<^isub>Z (Le i ks) xs = (i \<le> \<langle>ks,xs\<rangle>)" |
"I\<^isub>Z (Dvd d i ks) xs = (d dvd i+\<langle>ks,xs\<rangle>)" |
"I\<^isub>Z (NDvd d i ks) xs = (\<not> d dvd i+\<langle>ks,xs\<rangle>)"

definition "atoms\<^isub>0 = ATOM.atoms\<^isub>0 (\<lambda>a. hd_coeff a \<noteq> 0)"
(* FIXME !!! (incl: display should hide params)*)

interpretation Z!:
  ATOM neg\<^isub>Z "(\<lambda>a. divisor a \<noteq> 0)" I\<^isub>Z "(\<lambda>a. hd_coeff a \<noteq> 0)" decr\<^isub>Z
  where "ATOM.atoms\<^isub>0 (\<lambda>a. hd_coeff a \<noteq> 0) = atoms\<^isub>0"
proof-
  case goal1
  thus ?case
apply(unfold_locales)
apply(case_tac a)
apply simp_all
apply(case_tac a)
apply simp_all
apply(case_tac a)
apply (simp_all)
apply arith
apply(case_tac a)
apply(simp_all add: split: list.splits)
apply(case_tac a)
apply simp_all
done
next
  case goal2 thus ?case by(simp add:atoms\<^isub>0_def)
qed

setup {* Sign.revert_abbrev "" @{const_name Z.I} *}
setup {* Sign.revert_abbrev "" @{const_name Z.lift_dnf_qe} *}
(* FIXME doesn't work*)
(* FIXME does not help
setup {* Sign.revert_abbrev "" @{const_name Z.normal} *}
*)

abbreviation
"hd_coeff_is1 a \<equiv>
  (case a of Le _ _ \<Rightarrow> hd_coeff a : {1,-1} | _ \<Rightarrow> hd_coeff a = 1)"


fun asubst :: "int \<Rightarrow> int list \<Rightarrow> atom \<Rightarrow> atom" where
"asubst i' ks' (Le i (k#ks)) = Le (i - k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' (Dvd d i (k#ks)) = Dvd d (i + k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' (NDvd d i (k#ks)) = NDvd d (i + k*i') (k *\<^sub>s ks' + ks)" |
"asubst i' ks' a = a"

abbreviation subst :: "int \<Rightarrow> int list \<Rightarrow> atom fm \<Rightarrow> atom fm"
where "subst i ks \<equiv> map\<^bsub>fm\<^esub> (asubst i ks)"

lemma IZ_asubst: "I\<^isub>Z (asubst i ks a) xs = I\<^isub>Z a ((i + \<langle>ks,xs\<rangle>) # xs)"
apply (cases a)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
apply (case_tac list)
apply (simp_all add:algebra_simps iprod_left_add_distrib)
done

lemma I_subst:
  "qfree \<phi> \<Longrightarrow> Z.I \<phi> ((i + \<langle>ks,xs\<rangle>) # xs) = Z.I (subst i ks \<phi>) xs"
by (induct \<phi>) (simp_all add:IZ_asubst)

lemma divisor_asubst[simp]: "divisor (asubst i ks a) = divisor a"
by(induct i ks a rule:asubst.induct) auto


definition "lbounds as = [(i,ks). Le i (k#ks) \<leftarrow> as, k>0]"
definition "ubounds as = [(i,ks). Le i (k#ks) \<leftarrow> as, k<0]"
lemma set_lbounds:
  "set(lbounds as) = {(i,ks)|i k ks. Le i (k#ks) : set as \<and> k>0}"
by(auto simp: lbounds_def split:list.splits atom.splits if_splits)
lemma set_ubounds:
  "set(ubounds as) = {(i,ks)|i k ks. Le i (k#ks) : set as \<and> k<0}"
by(auto simp: ubounds_def split:list.splits atom.splits if_splits)

lemma lbounds_append[simp]: "lbounds(as @ bs) = lbounds as @ lbounds bs"
by(simp add:lbounds_def)


subsection{*LCM and lemmas*}

(* FIXME move into Library *)

lemma zdiv_eq_0_iff:
 "(i::int) div k = 0 \<longleftrightarrow> k=0 \<or> 0\<le>i \<and> i<k \<or> i\<le>0 \<and> k<i"
apply(auto simp: div_pos_pos_trivial div_neg_neg_trivial)
  apply (metis int_0_neq_1 linorder_not_less neg_imp_zdiv_nonneg_iff zdiv_mono1 zdiv_self zero_le_one zle_anti_sym zle_refl zless_linear)
  apply (metis int_0_neq_1 linorder_not_less pos_imp_zdiv_nonneg_iff zdiv_mono1_neg zdiv_self zero_le_one zle_anti_sym zle_refl zless_linear)
apply (metis int_0_neq_1 zdiv_self zless_linear)
done

lemma pos_imp_zdiv_pos_iff:
  "0<k \<Longrightarrow> 0 < (i::int) div k \<longleftrightarrow> k \<le> i"
using pos_imp_zdiv_nonneg_iff[of k i] zdiv_eq_0_iff[of i k]
by arith

lemma zmod_le_nonneg_dividend: "(m::int) \<ge> 0 \<Longrightarrow> m mod k \<le> m"
apply(cases "k=0") apply simp
by(metis linorder_not_le mod_pos_pos_trivial neg_mod_conj pos_mod_conj zle_refl zle_trans zless_le)

fun zlcms :: "int list \<Rightarrow> int" where
"zlcms [] = 1" |
"zlcms (i#is) = lcm i (zlcms is)"

lemma dvd_zlcms: "i : set is \<Longrightarrow> i dvd zlcms is"
apply(induct "is")
 apply simp
apply(auto simp add:dvd_lcm_if_dvd2_int)
done

lemma zlcms_pos: "\<forall>i \<in> set is. i\<noteq>0 \<Longrightarrow> zlcms is > 0"
by(induct "is")(auto simp:int_lcm_pos)

lemma zlcms0_iff[simp]: "(zlcms is = 0) = (0 : set is)"
by (metis DIVISION_BY_ZERO dvd_eq_mod_eq_0 dvd_zlcms zlcms_pos zless_le)

lemma elem_le_zlcms: "\<forall>i \<in> set is. i \<noteq> 0 \<Longrightarrow> i : set is \<Longrightarrow> i \<le> zlcms is"
by (metis dvd_zlcms zdvd_imp_le zlcms_pos)


subsection{* Setting coeffiencients to 1 or -1 *}

fun hd_coeff1 :: "int \<Rightarrow> atom \<Rightarrow> atom" where
"hd_coeff1 m (Le i (k#ks)) =
   (if k=0 then Le i (k#ks)
    else let m' = m div (abs k) in Le (m'*i) (sgn k # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (Dvd d i (k#ks)) =
   (if k=0 then Dvd d i (k#ks)
    else let m' = m div k in Dvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))" |
"hd_coeff1 m (NDvd d i (k#ks)) =
   (if k=0 then NDvd d i (k#ks)
    else let m' = m div k in NDvd (m'*d) (m'*i) (1 # (m' *\<^sub>s ks)))" |
"hd_coeff1 _ a = a"

text{* The def of @{const hd_coeff1} on @{const Dvd} and @{const NDvd} is
different from the @{const Le} because it allows the resulting head
coefficient to be 1 rather than 1 or -1. We show that the other version has
the same semantics: *}

lemma "\<lbrakk> k \<noteq> 0; k dvd m \<rbrakk> \<Longrightarrow>
  I\<^isub>Z (hd_coeff1 m (Dvd d i (k#ks))) (x#e) = (let m' = m div (abs k) in
  I\<^isub>Z (Dvd (m'*d) (m'*i) (sgn k # (m' *\<^sub>s ks))) (x#e))"
apply(auto simp:algebra_simps abs_if sgn_if)
 apply(simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0[THEN iffD1] algebra_simps)
 apply (metis diff_minus comm_monoid_add.mult_left_commute dvd_minus_iff minus_add_distrib)
apply(simp add: zdiv_zminus2_eq_if dvd_eq_mod_eq_0[THEN iffD1] algebra_simps)
apply (metis diff_minus comm_monoid_add.mult_left_commute dvd_minus_iff minus_add_distrib)
done


lemma I_hd_coeff1_mult_a: assumes "m>0"
shows "hd_coeff a dvd m | hd_coeff a = 0 \<Longrightarrow> I\<^isub>Z (hd_coeff1 m a) (m*x#xs) = I\<^isub>Z a (x#xs)"
proof(induct a)
  case (Le i ks)[simp]
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case (Cons k ks')[simp]
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with Le have "\<bar>k\<bar> dvd m" by simp
      let ?m' = "m div \<bar>k\<bar>"
      have "?m' > 0" using `\<bar>k\<bar> dvd m` pos_imp_zdiv_pos_iff `m>0` `k\<noteq>0`
	by(simp add:zdvd_imp_le)
      have 1: "k*(x*?m') = sgn k * x * m"
      proof -
	have "k*(x*?m') = (sgn k * abs k) * (x * ?m')"
	  by(simp only: mult_sgn_abs)
	also have "\<dots> = sgn k * x * (abs k * ?m')" by simp
	also have "\<dots> = sgn k * x * m"
	  using zdvd_mult_div_cancel[OF `\<bar>k\<bar> dvd m`] by(simp add:algebra_simps)
	finally show ?thesis .
      qed
      have "I\<^isub>Z (hd_coeff1 m (Le i ks)) (m*x#xs) \<longleftrightarrow>
            (i*?m' \<le> sgn k * m*x + ?m' * \<langle>ks',xs\<rangle>)"
	using `k\<noteq>0` by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> ?m'*i \<le> ?m' * (k*x + \<langle>ks',xs\<rangle>)" using 1
	by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> i \<le> k*x + \<langle>ks',xs\<rangle>" using `?m'>0`
	by(simp add: mult_compare_simps)
      finally show ?thesis by(simp)
    qed
  qed
next
  case (Dvd d i ks)[simp]
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case (Cons k ks')[simp]
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with Dvd have "k dvd m" by simp
      let ?m' = "m div k"
      have "?m' \<noteq> 0" using `k dvd m` zdiv_eq_0_iff `m>0` `k\<noteq>0`
	by(simp add:linorder_not_less zdvd_imp_le)
      have 1: "k*(x*?m') = x * m"
      proof -
	have "k*(x*?m') = x*(k*?m')" by(simp add:algebra_simps)
	also have "\<dots> = x*m" using zdvd_mult_div_cancel[OF `k dvd m`]
	  by(simp add:algebra_simps)
	finally show ?thesis .
      qed
      have "I\<^isub>Z (hd_coeff1 m (Dvd d i ks)) (m*x#xs) \<longleftrightarrow>
            (?m'*d dvd ?m'*i + m*x + ?m' * \<langle>ks',xs\<rangle>)"
	using `k\<noteq>0` by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> ?m'*d dvd ?m' * (i + k*x + \<langle>ks',xs\<rangle>)" using 1
	by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> d dvd i + k*x + \<langle>ks',xs\<rangle>" using `?m'\<noteq>0` by(simp)
      finally show ?thesis by(simp add:algebra_simps)
    qed
  qed
next
  case (NDvd d i ks)[simp]
  show ?case
  proof(cases ks)
    case Nil thus ?thesis by simp
  next
    case (Cons k ks')[simp]
    show ?thesis
    proof cases
      assume "k=0" thus ?thesis by simp
    next
      assume "k\<noteq>0"
      with NDvd have "k dvd m" by simp
      let ?m' = "m div k"
      have "?m' \<noteq> 0" using `k dvd m` zdiv_eq_0_iff `m>0` `k\<noteq>0`
	by(simp add:linorder_not_less zdvd_imp_le)
      have 1: "k*(x*?m') = x * m"
      proof -
	have "k*(x*?m') = x*(k*?m')" by(simp add:algebra_simps)
	also have "\<dots> = x*m" using zdvd_mult_div_cancel[OF `k dvd m`]
	  by(simp add:algebra_simps)
	finally show ?thesis .
      qed
      have "I\<^isub>Z (hd_coeff1 m (NDvd d i ks)) (m*x#xs) \<longleftrightarrow>
            \<not>(?m'*d dvd ?m'*i + m*x + ?m' * \<langle>ks',xs\<rangle>)"
	using `k\<noteq>0` by(simp add: algebra_simps)
      also have "\<dots> \<longleftrightarrow> \<not> ?m'*d dvd ?m' * (i + k*x + \<langle>ks',xs\<rangle>)" using 1
	by(simp (no_asm_simp) add:algebra_simps)
      also have "\<dots> \<longleftrightarrow> \<not> d dvd i + k*x + \<langle>ks',xs\<rangle>" using `?m'\<noteq>0` by(simp)
      finally show ?thesis by(simp add:algebra_simps)
    qed
  qed
qed


lemma I_hd_coeff1_mult: assumes "m>0"
shows "qfree \<phi> \<Longrightarrow> \<forall> a \<in> set(Z.atoms\<^isub>0 \<phi>). hd_coeff a dvd m \<Longrightarrow>
 Z.I (map\<^bsub>fm\<^esub> (hd_coeff1 m) \<phi>) (m*x#xs) = Z.I \<phi> (x#xs)"
proof(induct \<phi>)
  case (Atom a)
  thus ?case using I_hd_coeff1_mult_a[OF `m>0`] by(simp split:split_if_asm)
qed simp_all

end
