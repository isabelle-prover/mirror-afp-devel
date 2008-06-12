(*  ID:         $Id: Logic.thy,v 1.5 2008-06-12 06:57:24 lsf37 Exp $
    Author:     Tobias Nipkow, 2007
*)

header{* Logic *}

theory Logic
imports Main FuncSet
begin

text{* \noindent
We start with a generic formalization of quantified logical formulae
using de Bruijn notation. The syntax is parametric in the type of atoms. *}

declare Let_def[simp]

datatype 'a fm =
  TrueF | FalseF | Atom 'a | And "'a fm" "'a fm" | Or "'a fm" "'a fm" |
  Neg "'a fm" | ExQ "'a fm"

abbreviation Imp where "Imp \<phi>\<^isub>1 \<phi>\<^isub>2 \<equiv> Or (Neg \<phi>\<^isub>1) \<phi>\<^isub>2"
abbreviation AllQ where "AllQ \<phi> \<equiv> Neg(ExQ(Neg \<phi>))"

definition neg where
"neg \<phi> = (if \<phi>=TrueF then FalseF else if \<phi>=FalseF then TrueF else Neg \<phi>)"

definition "and" :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"and \<phi>\<^isub>1 \<phi>\<^isub>2 =
 (if \<phi>\<^isub>1=TrueF then \<phi>\<^isub>2 else if \<phi>\<^isub>2=TrueF then \<phi>\<^isub>1 else
  if \<phi>\<^isub>1=FalseF \<or> \<phi>\<^isub>2=FalseF then FalseF else And \<phi>\<^isub>1 \<phi>\<^isub>2)"

definition or :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"or \<phi>\<^isub>1 \<phi>\<^isub>2 =
 (if \<phi>\<^isub>1=FalseF then \<phi>\<^isub>2 else if \<phi>\<^isub>2=FalseF then \<phi>\<^isub>1 else
  if \<phi>\<^isub>1=TrueF \<or> \<phi>\<^isub>2=TrueF then TrueF else Or \<phi>\<^isub>1 \<phi>\<^isub>2)"

definition list_conj :: "'a fm list \<Rightarrow> 'a fm" where
"list_conj fs = foldr and fs TrueF"

definition list_disj :: "'a fm list \<Rightarrow> 'a fm" where
"list_disj fs = foldr or fs FalseF"

abbreviation "Disj is f \<equiv> list_disj (map f is)"

fun atoms :: "'a fm \<Rightarrow> 'a set" where
"atoms TrueF = {}" |
"atoms FalseF = {}" |
"atoms (Atom a) = {a}" |
"atoms (And \<phi>\<^isub>1 \<phi>\<^isub>2) = atoms \<phi>\<^isub>1 \<union> atoms \<phi>\<^isub>2" |
"atoms (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = atoms \<phi>\<^isub>1 \<union> atoms \<phi>\<^isub>2" |
"atoms (Neg \<phi>) = atoms \<phi>" |
"atoms (ExQ \<phi>) = atoms \<phi>"

fun map_fm :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fm \<Rightarrow> 'b fm" ("map\<^bsub>fm\<^esub>") where
"map\<^bsub>fm\<^esub> h TrueF = TrueF" |
"map\<^bsub>fm\<^esub> h FalseF = FalseF" |
"map\<^bsub>fm\<^esub> h (Atom a) = Atom(h a)" |
"map\<^bsub>fm\<^esub> h (And \<phi>\<^isub>1 \<phi>\<^isub>2) = And (map\<^bsub>fm\<^esub> h \<phi>\<^isub>1) (map\<^bsub>fm\<^esub> h \<phi>\<^isub>2)" |
"map\<^bsub>fm\<^esub> h (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = Or (map\<^bsub>fm\<^esub> h \<phi>\<^isub>1) (map\<^bsub>fm\<^esub> h \<phi>\<^isub>2)" |
"map\<^bsub>fm\<^esub> h (Neg \<phi>) = Neg (map\<^bsub>fm\<^esub> h \<phi>)" |
"map\<^bsub>fm\<^esub> h (ExQ \<phi>) = ExQ (map\<^bsub>fm\<^esub> h \<phi>)"

lemma atoms_map_fm[simp]: "atoms(map\<^bsub>fm\<^esub> f \<phi>) = f ` atoms \<phi>"
by(induct \<phi>) auto

fun amap_fm :: "('a \<Rightarrow> 'b fm) \<Rightarrow> 'a fm \<Rightarrow> 'b fm" ("amap\<^bsub>fm\<^esub>") where
"amap\<^bsub>fm\<^esub> h TrueF = TrueF" |
"amap\<^bsub>fm\<^esub> h FalseF = FalseF" |
"amap\<^bsub>fm\<^esub> h (Atom a) = h a" |
"amap\<^bsub>fm\<^esub> h (And \<phi>\<^isub>1 \<phi>\<^isub>2) = and (amap\<^bsub>fm\<^esub> h \<phi>\<^isub>1) (amap\<^bsub>fm\<^esub> h \<phi>\<^isub>2)" |
"amap\<^bsub>fm\<^esub> h (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = or (amap\<^bsub>fm\<^esub> h \<phi>\<^isub>1) (amap\<^bsub>fm\<^esub> h \<phi>\<^isub>2)" |
"amap\<^bsub>fm\<^esub> h (Neg \<phi>) = neg (amap\<^bsub>fm\<^esub> h \<phi>)"

lemma amap_fm_list_disj:
  "amap\<^bsub>fm\<^esub> h (list_disj fs) = list_disj (map (amap\<^bsub>fm\<^esub> h) fs)"
by(induct fs) (auto simp:list_disj_def or_def)

fun qfree :: "'a fm \<Rightarrow> bool" where
"qfree(ExQ f) = False" |
"qfree(And \<phi>\<^isub>1 \<phi>\<^isub>2) = (qfree \<phi>\<^isub>1 \<and> qfree \<phi>\<^isub>2)" |
"qfree(Or \<phi>\<^isub>1 \<phi>\<^isub>2) = (qfree \<phi>\<^isub>1 \<and> qfree \<phi>\<^isub>2)" |
"qfree(Neg \<phi>) = (qfree \<phi>)" |
"qfree \<phi> = True"

lemma qfree_and[simp]: "\<lbrakk> qfree \<phi>\<^isub>1; qfree \<phi>\<^isub>2 \<rbrakk> \<Longrightarrow> qfree(and \<phi>\<^isub>1 \<phi>\<^isub>2)"
by(simp add:and_def)

lemma qfree_or[simp]: "\<lbrakk> qfree \<phi>\<^isub>1; qfree \<phi>\<^isub>2 \<rbrakk> \<Longrightarrow> qfree(or \<phi>\<^isub>1 \<phi>\<^isub>2)"
by(simp add:or_def)

lemma qfree_neg[simp]: "qfree(neg \<phi>) = qfree \<phi>"
by(simp add:neg_def)

lemma qfree_foldr_Or[simp]:
 "qfree(foldr Or fs \<phi>) = (qfree \<phi> \<and> (\<forall>\<phi> \<in> set fs. qfree \<phi>))"
by (induct fs) auto

lemma qfree_list_conj[simp]:
assumes "\<forall>\<phi> \<in> set fs. qfree \<phi>" shows "qfree(list_conj fs)"
proof -
  { fix fs \<phi>
    have "\<lbrakk> \<forall>\<phi> \<in> set fs. qfree \<phi>; qfree \<phi> \<rbrakk> \<Longrightarrow> qfree(foldr and fs \<phi>)"
      by (induct fs) auto
  } thus ?thesis using assms by (fastsimp simp add:list_conj_def)
qed

lemma qfree_list_disj[simp]:
assumes "\<forall>\<phi> \<in> set fs. qfree \<phi>" shows "qfree(list_disj fs)"
proof -
  { fix fs \<phi>
    have "\<lbrakk> \<forall>\<phi> \<in> set fs. qfree \<phi>; qfree \<phi> \<rbrakk> \<Longrightarrow> qfree(foldr or fs \<phi>)"
      by (induct fs) auto
  } thus ?thesis using assms by (fastsimp simp add:list_disj_def)
qed

lemma qfree_map_fm: "qfree (map\<^bsub>fm\<^esub> f \<phi>) = qfree \<phi>"
by (induct \<phi>) simp_all

lemma atoms_list_disjE:
  "a : atoms(list_disj fs) \<Longrightarrow> a : (\<Union>\<phi> \<in> set fs. atoms \<phi>)"
apply(induct fs)
 apply (simp add:list_disj_def)
apply (auto simp add:list_disj_def Logic.or_def split:split_if_asm)
done

lemma atoms_list_conjE:
  "a : atoms(list_conj fs) \<Longrightarrow> a : (\<Union>\<phi> \<in> set fs. atoms \<phi>)"
apply(induct fs)
 apply (simp add:list_conj_def)
apply (auto simp add:list_conj_def Logic.and_def split:split_if_asm)
done


fun dnf :: "'a fm \<Rightarrow> 'a list list" where
"dnf TrueF = [[]]" |
"dnf FalseF = []" |
"dnf (Atom \<phi>) = [[\<phi>]]" |
"dnf (And \<phi>\<^isub>1 \<phi>\<^isub>2) = [d1 @ d2. d1 \<leftarrow> dnf \<phi>\<^isub>1, d2 \<leftarrow> dnf \<phi>\<^isub>2]" |
"dnf (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = dnf \<phi>\<^isub>1 @ dnf \<phi>\<^isub>2"

fun nqfree :: "'a fm \<Rightarrow> bool" where
"nqfree(Atom a) = True" |
"nqfree TrueF = True" |
"nqfree FalseF = True" |
"nqfree (And \<phi>\<^isub>1 \<phi>\<^isub>2) = (nqfree \<phi>\<^isub>1 \<and> nqfree \<phi>\<^isub>2)" |
"nqfree (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = (nqfree \<phi>\<^isub>1 \<and> nqfree \<phi>\<^isub>2)" |
"nqfree \<phi> = False"

lemma nqfree_qfree[simp]: "nqfree \<phi> \<Longrightarrow> qfree \<phi>"
by (induct \<phi>) simp_all

lemma nqfree_map_fm: "nqfree (map\<^bsub>fm\<^esub> f \<phi>) = nqfree \<phi>"
by (induct \<phi>) simp_all


fun "interpret" :: "('a \<Rightarrow> 'b list \<Rightarrow> bool) \<Rightarrow> 'a fm \<Rightarrow> 'b list \<Rightarrow> bool" where
"interpret h TrueF xs = True" |
"interpret h FalseF xs = False" |
"interpret h (Atom a) xs = h a xs" |
"interpret h (And \<phi>\<^isub>1 \<phi>\<^isub>2) xs = (interpret h \<phi>\<^isub>1 xs \<and> interpret h \<phi>\<^isub>2 xs)" |
"interpret h (Or \<phi>\<^isub>1 \<phi>\<^isub>2) xs = (interpret h \<phi>\<^isub>1 xs | interpret h \<phi>\<^isub>2 xs)" |
"interpret h (Neg \<phi>) xs = (\<not> interpret h \<phi> xs)" |
"interpret h (ExQ \<phi>) xs = (\<exists>x. interpret h \<phi> (x#xs))"

subsection{*Atoms*}

text{* The locale ATOM of atoms provides a minimal framework for the
generic formulation of theory-independent algorithms, in particular
quantifier elimination. *}

locale ATOM =
fixes aneg :: "'a \<Rightarrow> 'a fm"
fixes anormal :: "'a \<Rightarrow> bool"
assumes nqfree_aneg: "nqfree(aneg a)"
assumes anormal_aneg: "anormal a \<Longrightarrow> \<forall>b\<in>atoms(aneg a). anormal b"

fixes I\<^isub>a :: "'a \<Rightarrow> 'b list \<Rightarrow> bool"
assumes I\<^isub>a_aneg: "interpret I\<^isub>a (aneg a) xs = (\<not> I\<^isub>a a xs)"

fixes depends\<^isub>0 :: "'a \<Rightarrow> bool"
and decr :: "'a \<Rightarrow> 'a" 
assumes not_dep_decr: "\<not>depends\<^isub>0 a \<Longrightarrow> I\<^isub>a a (x#xs) = I\<^isub>a (decr a) xs"
assumes anormal_decr: "\<not> depends\<^isub>0 a \<Longrightarrow> anormal a \<Longrightarrow> anormal(decr a)"

begin

fun atoms\<^isub>0 :: "'a fm \<Rightarrow> 'a list" where
"atoms\<^isub>0 TrueF = []" |
"atoms\<^isub>0 FalseF = []" |
"atoms\<^isub>0 (Atom a) = (if depends\<^isub>0 a then [a] else [])" |
"atoms\<^isub>0 (And \<phi>\<^isub>1 \<phi>\<^isub>2) = atoms\<^isub>0 \<phi>\<^isub>1 @ atoms\<^isub>0 \<phi>\<^isub>2" |
"atoms\<^isub>0 (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = atoms\<^isub>0 \<phi>\<^isub>1 @ atoms\<^isub>0 \<phi>\<^isub>2" |
"atoms\<^isub>0 (Neg \<phi>) = atoms\<^isub>0 \<phi>"

abbreviation I where "I \<equiv> interpret I\<^isub>a"

fun nnf :: "'a fm \<Rightarrow> 'a fm" where
"nnf (And \<phi>\<^isub>1 \<phi>\<^isub>2) = And (nnf \<phi>\<^isub>1) (nnf \<phi>\<^isub>2)" |
"nnf (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = Or (nnf \<phi>\<^isub>1) (nnf \<phi>\<^isub>2)" |
"nnf (Neg TrueF) = FalseF" |
"nnf (Neg FalseF) = TrueF" |
"nnf (Neg (Neg \<phi>)) = (nnf \<phi>)" |
"nnf (Neg (And \<phi>\<^isub>1 \<phi>\<^isub>2)) = (Or (nnf (Neg \<phi>\<^isub>1)) (nnf (Neg \<phi>\<^isub>2)))" |
"nnf (Neg (Or \<phi>\<^isub>1 \<phi>\<^isub>2)) = (And (nnf (Neg \<phi>\<^isub>1)) (nnf (Neg \<phi>\<^isub>2)))" |
"nnf (Neg (Atom a)) = aneg a" |
"nnf \<phi> = \<phi>"

lemma nqfree_nnf: "qfree \<phi> \<Longrightarrow> nqfree(nnf \<phi>)"
by(induct \<phi> rule:nnf.induct)
  (simp_all add: nqfree_aneg and_def or_def)

lemma qfree_nnf[simp]: "qfree(nnf \<phi>) = qfree \<phi>"
by (induct \<phi> rule:nnf.induct)(simp_all add: nqfree_aneg)


lemma I_neg[simp]: "I (neg \<phi>) xs = I (Neg \<phi>) xs"
by(simp add:neg_def)

lemma I_and[simp]: "I (and \<phi>\<^isub>1 \<phi>\<^isub>2) xs = I (And \<phi>\<^isub>1 \<phi>\<^isub>2) xs"
by(simp add:and_def)

lemma I_list_conj[simp]:
 "I (list_conj fs) xs = (\<forall>\<phi> \<in> set fs. I \<phi> xs)"
proof -
  { fix fs \<phi>
    have "I (foldr and fs \<phi>) xs = (I \<phi> xs \<and> (\<forall>\<phi> \<in> set fs. I \<phi> xs))"
      by (induct fs) auto
  } thus ?thesis by(simp add:list_conj_def)
qed

lemma I_or[simp]: "I (or \<phi>\<^isub>1 \<phi>\<^isub>2) xs = I (Or \<phi>\<^isub>1 \<phi>\<^isub>2) xs"
by(simp add:or_def)

lemma I_list_disj[simp]:
 "I (list_disj fs) xs = (\<exists>\<phi> \<in> set fs. I \<phi> xs)"
proof -
  { fix fs \<phi>
    have "I (foldr or fs \<phi>) xs = (I \<phi> xs \<or> (\<exists>\<phi> \<in> set fs. I \<phi> xs))"
      by (induct fs) auto
  } thus ?thesis by(simp add:list_disj_def)
qed

lemma I_nnf: "I (nnf \<phi>) xs = I \<phi> xs"
by(induct rule:nnf.induct)(simp_all add: I\<^isub>a_aneg)

lemma I_dnf:
"nqfree \<phi> \<Longrightarrow> (\<exists>as\<in>set (dnf \<phi>). \<forall>a\<in>set as. I\<^isub>a a xs) = I \<phi> xs"
by (induct \<phi>) (fastsimp)+

definition "normal \<phi> = (\<forall>a \<in> atoms \<phi>. anormal a)"

lemma normal_simps[simp]:
"normal TrueF"
"normal FalseF"
"normal (Atom a) \<longleftrightarrow> anormal a"
"normal (And \<phi>\<^isub>1 \<phi>\<^isub>2) \<longleftrightarrow> normal \<phi>\<^isub>1 \<and> normal \<phi>\<^isub>2"
"normal (Or \<phi>\<^isub>1 \<phi>\<^isub>2) \<longleftrightarrow> normal \<phi>\<^isub>1 \<and> normal \<phi>\<^isub>2"
"normal (Neg \<phi>) \<longleftrightarrow> normal \<phi>"
"normal (ExQ \<phi>) \<longleftrightarrow> normal \<phi>"
by(auto simp:normal_def)

lemma normal_aneg[simp]: "anormal a \<Longrightarrow> normal (aneg a)"
by (simp add:anormal_aneg normal_def)

lemma normal_and[simp]:
  "normal \<phi>\<^isub>1 \<Longrightarrow> normal \<phi>\<^isub>2 \<Longrightarrow> normal (and \<phi>\<^isub>1 \<phi>\<^isub>2)"
by (simp add:Logic.and_def)

lemma normal_or[simp]:
  "normal \<phi>\<^isub>1 \<Longrightarrow> normal \<phi>\<^isub>2 \<Longrightarrow> normal (or \<phi>\<^isub>1 \<phi>\<^isub>2)"
by (simp add:Logic.or_def)

lemma normal_list_disj[simp]:
  "\<forall>\<phi>\<in>set fs. normal \<phi> \<Longrightarrow> normal (list_disj fs)"
apply(induct fs)
 apply (simp add:list_disj_def normal_simps)
apply (simp add:list_disj_def normal_simps)
done

lemma normal_nnf: "normal \<phi> \<Longrightarrow> normal(nnf \<phi>)"
by(induct \<phi> rule:nnf.induct) simp_all

lemma normal_map_fm:
  "\<forall>a. anormal(f a) = anormal(a) \<Longrightarrow> normal (map\<^bsub>fm\<^esub> f \<phi>) = normal \<phi>"
by(induct \<phi>) auto


lemma anormal_nnf:
  "qfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> \<forall>a\<in>atoms(nnf \<phi>). anormal a"
apply(induct \<phi> rule:nnf.induct)
apply(unfold normal_def)
apply(simp_all)
apply (blast dest:anormal_aneg)+
done

lemma atoms_dnf: "nqfree \<phi> \<Longrightarrow> as : set(dnf \<phi>) \<Longrightarrow> a : set as \<Longrightarrow> a : atoms \<phi>"
by(induct \<phi> arbitrary: as a rule:nqfree.induct)(auto)

lemma anormal_dnf_nnf:
  "as : set(dnf(nnf \<phi>)) \<Longrightarrow> qfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> a : set as \<Longrightarrow> anormal a"
apply(induct \<phi> arbitrary: a as rule:nnf.induct)
            apply(simp_all add: normal_def)
    apply clarify
    apply (metis UnE set_append)
   apply metis
  apply metis
 apply fastsimp
apply (metis anormal_aneg atoms_dnf nqfree_aneg)
done

end

end