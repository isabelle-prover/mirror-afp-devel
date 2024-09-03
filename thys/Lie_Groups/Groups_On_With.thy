(*  Title:       Groups_On_With
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Groups_On_With
imports
  "HOL-Types_To_Sets.Group_On_With"
  Complex_Main
begin


section \<open>Locales for non-abelian groups\<close>
text \<open>Extends the approach used for smooth manifolds in \<^session>\<open>HOL-Types_To_Sets\<close>
  (under Examples) to also include non-commutative groups.
  We can use the \<^locale>\<open>semigroup_add_on_with\<close> as it is defined in the theory above.
  Notice "add" is merely a name for the group operation, we will want to apply this to groups under
  (matrix) multiplication too.\<close>

subsection \<open>Locale definitions leading to non-abelian groups\<close>


locale monoid_on_with = semigroup_add_on_with +
  fixes z
  assumes add_zero: "a \<in> S \<Longrightarrow> pls z a = a \<and> pls a z = a"
  assumes zero_mem: "z \<in> S"
begin

lemma carrier_ne: "S \<noteq> {}" using zero_mem by auto

lemma
  assumes "a \<in> S"
  shows add_zeroL: "pls z a = a"
    and add_zeroR: "pls a z = a"
  by (simp_all add: add_zero assms)

end

locale group_on_with = monoid_on_with +
  fixes mns um
  assumes left_minus: "a \<in> S \<Longrightarrow> pls (um a) a = z"
    and diff_conv_add_uminus: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> mns a b = pls a (um b)"
    and uminus_mem: "a \<in> S \<Longrightarrow> um a \<in> S"
begin

text \<open>Axiom @{thm diff_conv_add_uminus} ensures division/subtraction agrees with inverse/unary-minus,
  while leaving the flexibility to provide any fitting implementation of the operations
  (since they are constrained only on the carrier set).\<close>

lemma right_minus: "a \<in> S \<Longrightarrow> pls a (um a) = z"
  by (metis (full_types) add_assoc add_zero add_zeroR local.left_minus uminus_mem)

lemma add_uminus: "a \<in> S \<Longrightarrow> pls a (um a) = z \<and> pls (um a) a = z"
  by (simp add: left_minus right_minus)

text \<open>A group's identity is unique: we show this both inside and outside \<^locale>\<open>group_on_with\<close>.
  The in-locale version is mildly more powerful, requiring invariance only on one side.
  The non-locale lemma is used later to prove there is a canonical instantiation of the group
  inverse and division, and to provide the sublocale \<open>grp_on\<close> of \<^locale>\<open>group_on_with\<close>,
  which requires fewer parameters.\<close>

lemma id_is_unique:
  assumes "\<And>x. x\<in>S \<Longrightarrow> pls x other_id = x \<or> pls other_id x = x" "other_id\<in>S"
  shows "other_id = z"
  using assms zero_mem add_zero add_zeroR
  by metis

lemma uminus_uminus: "x\<in>S \<Longrightarrow> um (um x) = x"
  by (metis (full_types) add_assoc add_zeroL add_zeroR local.right_minus uminus_mem)

end

lemma id_is_unique:
  fixes G::"'a set" and mult::"'a\<Rightarrow>'a\<Rightarrow>'a" and e::'a
  defines "is_id \<equiv> \<lambda>e. e\<in>G \<and> (\<forall>a\<in>G. mult e a = a \<and> mult a e = a)"
  assumes ident: "is_id e"
  shows "e = (THE e. is_id e)" "is_id e' \<longrightarrow> e'=e"
  using the_equality apply (metis assms) by (metis assms)

text \<open>Inverses are unique too, and we show this in several lemmas both inside and outside the locale
  \<open>group_on_with\<close>, as above.\<close>

lemma inv_is_uniqueL:
  fixes G::"'a set" and mult::"'a\<Rightarrow>'a\<Rightarrow>'a" and e::'a
  defines "is_id \<equiv> \<lambda>e. e\<in>G \<and> (\<forall>a\<in>G. mult e a = a)"
  assumes assoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mult (mult a b) c = mult a (mult b c)"
    and ident: "is_id e"
    and inver: "\<forall>x\<in>G. \<exists>y\<in>G. mult x y = e"
    and "x\<in>G" "y\<in>G" "z\<in>G" "mult x y = e" "mult x z = e"
  shows "y=z"
  by (metis assms)

lemma inv_is_uniqueR:
  fixes G::"'a set" and mult::"'a\<Rightarrow>'a\<Rightarrow>'a" and e::'a
  defines "is_id \<equiv> \<lambda>e. e\<in>G \<and> (\<forall>a\<in>G. mult a e = a)"
  assumes assoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mult (mult a b) c = mult a (mult b c)"
    and ident: "is_id e"
    and inver: "\<forall>x\<in>G. \<exists>y\<in>G. mult x y = e"
    and "x\<in>G" "y\<in>G" "z\<in>G" "mult y x = e" "mult z x = e"
  shows "y=z"
  by (metis assms)

lemma inv_is_unique:
  fixes G::"'a set" and mult::"'a\<Rightarrow>'a\<Rightarrow>'a" and e::'a
  defines "is_id \<equiv> \<lambda>e. e\<in>G \<and> (\<forall>a\<in>G. mult e a = a \<and> mult a e = a)"
  assumes assoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mult (mult a b) c = mult a (mult b c)"
    and ident: "is_id e"
    and "x\<in>G" "y\<in>G" "z\<in>G" "mult y x = e" "mult x z = e"
  shows "y=z"
  by (metis assms)

lemma (in group_on_with) inv_is_unique:
  fixes other_inv
  assumes "\<forall>x\<in>S. pls x (other_inv x) = z \<or> pls (other_inv x) x = z"
    and "\<forall>x\<in>S. other_inv x \<in> S"
  shows "\<forall>x\<in>S. other_inv x = um x"
   (*by (metis (full_types) add_assoc add_zeroL add_zeroR assms right_minus uminus_mem)*) 
proof
  fix x assume "x\<in>S"
  consider "pls x (other_inv x) = z" | "pls (other_inv x) x = z" using assms \<open>x \<in> S\<close> by auto
  thus "other_inv x = um x"
  proof (cases)
    case 1
    hence "um x = pls (um x) (pls x (other_inv x))" by (simp add: \<open>x\<in>S\<close> add_zeroR uminus_mem)
    also have "\<dots> = pls (pls (um x) x) (other_inv x)" by (simp add: \<open>x\<in>S\<close> add_assoc assms(2) uminus_mem)
    finally show "other_inv x = um x" by (simp add: \<open>x\<in>S\<close> add_zero assms(2) left_minus)
  next
    case 2
    hence "um x = pls (pls (other_inv x) x) (um x)" using add_zero[OF uminus_mem[OF \<open>x\<in>S\<close>]] by simp
    also have "\<dots> = pls (other_inv x) (pls x (um x))" by (simp add: \<open>x\<in>S\<close> add_assoc assms(2) uminus_mem)
    finally show "other_inv x = um x" by (simp add: \<open>x\<in>S\<close> add_zeroR assms(2) right_minus)
  qed
qed


lemma group_on_with_alt_intro:
  fixes G::"'a set" and mult::"'a\<Rightarrow>'a\<Rightarrow>'a" and e::'a
    and is_id is_inv
  defines "is_id \<equiv> \<lambda>e. e\<in>G \<and> (\<forall>a\<in>G. mult e a = a \<and> mult a e = a)"
      and "is_inv \<equiv> \<lambda>x y. y\<in>G \<and> mult x y = e \<and> mult y x = e"
  assumes closed: "\<forall>a\<in>G. \<forall>b\<in>G. mult a b \<in> G"
      and assoc: "\<forall>a\<in>G. \<forall>b\<in>G. \<forall>c\<in>G. mult (mult a b) c = mult a (mult b c)"
      and ident: "is_id e" (* no need for uniqueness, which is implied *)
      and inver: "\<forall>x\<in>G. \<exists>y. is_inv x y" (* no need for uniqueness, which is implied *)
  shows "group_on_with G mult e (\<lambda>x z. mult x (THE y. is_inv z y)) (\<lambda>x. THE y. is_inv x y)"
    (is "group_on_with G mult e ?div ?inv")
proof (unfold_locales)
  show "e\<in>G"
    using ident is_id_def by auto
  have inv: "\<forall>x\<in>G. mult x (?inv x) = e" "\<forall>x\<in>G. ?inv x \<in> G" "\<forall>x\<in>G. mult (?inv x) x = e"
  proof (safe)
    fix x assume "x\<in>G"
    have 1: "e\<in>G \<and> (\<forall>a\<in>G. mult e a = a)" "\<forall>x\<in>G. \<exists>y\<in>G. mult x y = e"
      using ident is_id_def inver is_inv_def by auto
    obtain y where y: "is_inv x y"
      using inver \<open>x\<in>G\<close> by blast
    have y_Uniq: "y = ?inv x"
      using y inv_is_uniqueL[OF assoc 1 \<open>x\<in>G\<close>] unfolding is_inv_def by (simp add: the_equality)
    thus 2: "mult x (?inv x) = e"
      using is_inv_def y by blast
    show "?inv x \<in> G"
      using y y_Uniq is_inv_def by simp
    show "mult (?inv x) x = e"
      using 2 is_id_def by (metis is_inv_def y y_Uniq)
  qed
  fix x assume "x \<in> G"
  show "mult e x = x \<and> mult x e = x"
    using \<open>x \<in> G\<close> ident is_id_def by auto
  show "mult (?inv x) x = e"
    using inv(3) by (simp add: \<open>x \<in> G\<close>)
  show "?inv x \<in> G"
    by (simp add: \<open>x \<in> G\<close> inv(2))
qed (simp add: assoc closed)+

locale grp_on = monoid_on_with +
  assumes inv_ex: "\<forall>x\<in>S. \<exists>y\<in>S. pls x y = z \<and> pls y x = z"
begin

definition "is_invs x y \<equiv> y\<in>S \<and> pls x y = z \<and> pls y x = z"
definition "invs \<equiv> (\<lambda>x. THE y. is_invs x y)"
definition "mns \<equiv> (\<lambda>x y. pls x (invs y))"

lemma is_group_on_with:
  shows "group_on_with S pls z mns invs"
  apply (unfold mns_def invs_def is_invs_def, intro group_on_with_alt_intro)
  using inv_ex by (auto simp: add_mem add_assoc add_zero zero_mem)

lemma grp_on_cong:
  assumes "\<And>x y. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> pls x y = pls' x y"
  shows "grp_on S pls' z"
  using assms add_assoc add_mem add_zeroR inv_ex zero_mem by (unfold_locales, auto)

sublocale group_on_with S pls z mns invs
  using is_group_on_with by simp

end


lemma (in group_on_with) is_grp_on:
  shows "grp_on S pls z"
  using add_uminus uminus_mem by (unfold_locales, blast)


subsection \<open>(Homo)morphism of groups\<close>

locale group_on_with_pair =
  G1: group_on_with G1 pls1 z1 mns1 um1 +
  G2: group_on_with G2 pls2 z2 mns2 um2
  for G1 G2 pls1 pls2 z1 z2 mns1 mns2 um1 um2

locale group_hom_betw =
  group_on_with_pair +
  fixes f
  assumes group_hom: "x\<in>G1 \<Longrightarrow> y\<in>G1 \<Longrightarrow> f (pls1 x y) =  pls2 (f x) (f y)"
    and closure: "x \<in> G1 \<Longrightarrow> f x \<in> G2"
begin

lemma maps_id: "f z1 = z2"
  using G2.id_is_unique closure group_hom
  by (metis (full_types) G1.add_zeroR G1.zero_mem G2.add_assoc G2.add_zeroR G2.right_minus G2.uminus_mem)

lemma maps_inv: "f (um1 x) = um2 (f x)" if "x\<in>G1" for x
  using G2.inv_is_unique G1.uminus_mem closure group_hom that maps_id
  by (smt (z3) G1.left_minus G2.add_assoc G2.add_zeroL G2.add_zeroR G2.right_minus G2.uminus_mem)

end

end
