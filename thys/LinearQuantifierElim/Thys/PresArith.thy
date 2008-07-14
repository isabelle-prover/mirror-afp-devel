(*  ID:         $Id: PresArith.thy,v 1.6 2008-07-14 09:05:06 fhaftmann Exp $
    Author:     Tobias Nipkow, 2007
*)

header{* Presburger arithmetic *}

theory PresArith
imports GCD QE ListVector
begin

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

interpretation Z:
  ATOM[neg\<^isub>Z "(\<lambda>a. divisor a \<noteq> 0)" I\<^isub>Z "(\<lambda>a. hd_coeff a \<noteq> 0)" decr\<^isub>Z]
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
apply (simp_all add:ring_simps iprod_assoc iprod_left_add_distrib)
apply (case_tac list)
apply (simp_all add:ring_simps iprod_assoc iprod_left_add_distrib)
apply (case_tac list)
apply (simp_all add:ring_simps iprod_assoc iprod_left_add_distrib)
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
"zlcms (i#is) = zlcm i (zlcms is)"

lemma dvd_zlcms: "i : set is \<Longrightarrow> i dvd zlcms is"
apply(induct "is")
 apply simp
apply(auto simp add:dvd_imp_dvd_zlcm2)
done

lemma zlcms_pos: "\<forall>i \<in> set is. i\<noteq>0 \<Longrightarrow> zlcms is > 0"
by(induct "is")(auto simp:zlcm_pos)

lemma zlcms0_iff[simp]: "(zlcms is = 0) = (0 : set is)"
by (metis DIVISION_BY_ZERO Divides.dvd_def_mod dvd_zlcms zlcms_pos zless_le)

lemma elem_le_zlcms: "\<forall>i \<in> set is. i \<noteq> 0 \<Longrightarrow> i : set is \<Longrightarrow> i \<le> zlcms is"
by (metis dvd_zlcms zdvd_imp_le zlcms_pos)

end
