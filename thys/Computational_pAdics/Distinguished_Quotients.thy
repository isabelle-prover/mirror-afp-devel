(*  Title:       Computational p-Adics: Distinguished Quotients
    Author:      Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>, 2025
    Maintainer:  Jeremy Sylvestre <jeremy.sylvestre at ualberta.ca>
*)


theory Distinguished_Quotients

imports Main

begin

section \<open>Distinguished Algebraic Quotients\<close>

text \<open>
  We define quotient groups and quotient rings modulo distinguished normal subgroups and ideals,
  respectively, leading to the construction of a field as a commutative ring with 1 modulo a
  maximal ideal.
\<close>

class distinguished_subset =
  fixes distinguished_subset :: "'a set" ("\<N>")

hide_const distinguished_subset

subsection \<open>Quotient groups\<close>

subsubsection \<open>Class definitions\<close>

text \<open>Here we set up subclasses of @{class group_add} with a distinguished subgroup.\<close>

class group_add_with_distinguished_subgroup = group_add + distinguished_subset +
  assumes distset_nonempty: "\<N> \<noteq> {}"
    and   distset_diff_closed:
    "g \<in> \<N> \<Longrightarrow> h \<in> \<N> \<Longrightarrow> g - h \<in> \<N>"
begin

lemma distset_zero_closed : "0 \<in> \<N>"
proof-
  from distset_nonempty obtain g::'a where "g \<in> \<N>" by fast
  hence "g - g \<in> \<N>" using distset_diff_closed by fast
  thus ?thesis by simp
qed

lemma distset_uminus_closed: "a \<in> \<N> \<Longrightarrow> -a \<in> \<N>"
  using distset_zero_closed distset_diff_closed by force

lemma distset_add_closed:
  "a \<in> \<N> \<Longrightarrow>  b \<in> \<N> \<Longrightarrow> a + b \<in> \<N>"
  using distset_uminus_closed[of b] distset_diff_closed[of a "-b"] by simp

lemma distset_uminus_plus_closed:
  "a \<in> \<N> \<Longrightarrow> b \<in> \<N> \<Longrightarrow> -a + b \<in> \<N>"
  using distset_uminus_closed distset_add_closed by simp

lemma distset_lcoset_closed1:
  "a \<in> \<N> \<Longrightarrow> -a + b \<in> \<N> \<Longrightarrow> b \<in> \<N>"
  using add.assoc[of a "-a" b] distset_add_closed by fastforce

lemma distset_lcoset_closed2:
  "b \<in> \<N> \<Longrightarrow> -a + b \<in> \<N> \<Longrightarrow> a \<in> \<N>"
proof-
  assume ab: "b \<in> \<N>" "-a + b \<in> \<N>"
  from ab(2) obtain z where z: "z \<in> \<N>" "-a + b = z" by fast
  from z(2) have "a = -(z - b)" using add.assoc[of "-a" b "-b"] by simp
  with ab(1) z(1) show "a \<in> \<N>" using distset_diff_closed by simp
qed

lemma reflp_lcosetrel: "- x + x \<in> \<N>"
  using distset_zero_closed by simp

lemma symp_lcosetrel: "- a + b \<in> \<N> \<Longrightarrow> - b + a \<in> \<N>"
  using distset_uminus_closed by (fastforce simp add: minus_add)

lemma transp_lcosetrel:
  "-x + z \<in> \<N>" if "-x + y \<in> \<N>" and "-y + z \<in> \<N>"
proof-
  from that obtain a a' :: 'a
    where "a \<in> \<N>" "-x + y = a" "a' \<in> \<N>" "-y + z = a'" by fast
  thus ?thesis using add.assoc[of a "-y" z] distset_add_closed by fastforce
qed

end (* class group_add_with_distinguished_subgroup *)

class group_add_with_distinguished_normal_subgroup = group_add_with_distinguished_subgroup +
  assumes distset_normal: "((+) g) ` \<N> = (\<lambda>x. x + g) ` \<N>"

class ab_group_add_with_distinguished_subgroup =
  ab_group_add + group_add_with_distinguished_subgroup
begin

subclass group_add_with_distinguished_normal_subgroup
proof (unfold_locales, rule distset_nonempty, rule distset_diff_closed)
  show "\<And>g. ((+) g) ` \<N> = (\<lambda>x. x + g) ` \<N>" by (force simp add: add.commute)
qed

end (* class ab_group_add_with_distinguished_subgroup *)

subsubsection \<open>The quotient group type\<close>

text \<open>
  Here we define a quotient type relative to the left-coset relation, and instantiate it as a
  @{class group_add}.
\<close>

quotient_type (overloaded) 'a coset_by_dist_sbgrp =
  "'a::group_add_with_distinguished_subgroup" / "\<lambda>g h :: 'a. -g + h \<in> (\<N>::'a set)"
  morphisms distinguished_quotient_coset_rep distinguished_quotient_coset
proof (rule equivpI)
  show "reflp (\<lambda>g h :: 'a. -g + h \<in> \<N>)" using reflp_lcosetrel by (fast intro: reflpI)
  show "symp (\<lambda>g h :: 'a. -g + h \<in> \<N>)" using symp_lcosetrel by (fast intro: sympI)
  show "transp (\<lambda>g h :: 'a. -g + h \<in> \<N>)" using transp_lcosetrel
    by (fast intro: transpI)
qed

lemmas distinguished_quotient_coset_rep_inverse =
        Quotient_abs_rep[OF Quotient_coset_by_dist_sbgrp]
   and coset_by_dist_sbgrp_eq_iff =
        Quotient_rel_rep[OF Quotient_coset_by_dist_sbgrp]
   and distinguished_quotient_coset_eqI =
        Quotient_rel_abs[OF Quotient_coset_by_dist_sbgrp]
   and eq_to_distinguished_quotient_cosetI =
        Quotient_rel_abs2[OF Quotient_coset_by_dist_sbgrp]

lemma coset_coset_by_dist_sbgrp_cases
  [case_names coset, cases type: coset_by_dist_sbgrp]:
  "(\<And>y. z = distinguished_quotient_coset y \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct z) auto

lemmas distinguished_quotient_coset_eq_iff = coset_by_dist_sbgrp.abs_eq_iff

lemma distinguished_quotient_coset_rep_coset_equiv:
  "- distinguished_quotient_coset_rep (distinguished_quotient_coset r) + r \<in> \<N>"
  using Quotient_rep_abs[OF Quotient_coset_by_dist_sbgrp]
  by    (simp add: distset_zero_closed)

instantiation coset_by_dist_sbgrp ::
  (group_add_with_distinguished_normal_subgroup) group_add
begin

lift_definition zero_coset_by_dist_sbgrp :: "'a coset_by_dist_sbgrp"
  is "0::'a" .

lemmas zero_distinguished_quotient [simp] = zero_coset_by_dist_sbgrp.abs_eq[symmetric]

lemma zero_distinguished_quotient_eq_iffs:
  "(distinguished_quotient_coset x = 0) = (x \<in> \<N>)"
  "(X = 0) = (distinguished_quotient_coset_rep X \<in> \<N>)"
proof-
  have "distinguished_quotient_coset x = 0 \<Longrightarrow> x \<in> \<N>"
  proof transfer
    fix x::'a show "- x + 0 \<in> \<N> \<Longrightarrow> x \<in> \<N>"
      using distset_uminus_closed[of "-x"] by simp
  qed
  moreover have "x \<in> \<N> \<Longrightarrow> distinguished_quotient_coset x = 0"
    by transfer (simp add: distset_uminus_closed)
  ultimately show "(distinguished_quotient_coset x = 0) = (x \<in> \<N>)" by fast
  have "distinguished_quotient_coset_rep 0 \<in> \<N>"
    using distinguished_quotient_coset_rep_coset_equiv[of "0::'a"] distset_uminus_closed
    by    fastforce
  moreover have "distinguished_quotient_coset_rep X \<in> \<N> \<Longrightarrow> X = 0"
    using eq_to_distinguished_quotient_cosetI[of X 0] by (simp add: distset_uminus_closed)
  ultimately show "(X = 0) = (distinguished_quotient_coset_rep X \<in> \<N>)" by fast
qed

lift_definition plus_coset_by_dist_sbgrp ::
  "'a coset_by_dist_sbgrp \<Rightarrow> 'a coset_by_dist_sbgrp \<Rightarrow>
      'a coset_by_dist_sbgrp"
  is "\<lambda>x y::'a. x + y"
proof-
  fix w x y z :: 'a assume wx: "-w+x \<in> \<N>" and yz: "-y+z \<in> \<N>"
  from this obtain a1 a2
    where a1: "a1 \<in> \<N>" "-w + x = a1"
    and   a2: "a2 \<in> \<N>" "-y + z = a2"
    by    fast
  from a1(1) obtain a3 where a3: "a3 \<in> \<N>" "-y + a1 = a3 + -y" using distset_normal by fast
  from a1(2) a2(2) a3(2) have "-(w + y) + (x + z) = a3 + a2"
    using minus_add add.assoc[of "-y + -w" x z] add.assoc[of "-y" "-w" x] add.assoc[of a3 "-y" z]
    by    simp
  with a2(1) a3(1) show "-(w + y) + (x + z) \<in> \<N>" using distset_add_closed by simp
qed

lemmas plus_coset_by_dist_sbgrp [simp] = plus_coset_by_dist_sbgrp.abs_eq

lift_definition uminus_coset_by_dist_sbgrp ::
  "'a coset_by_dist_sbgrp \<Rightarrow> 'a coset_by_dist_sbgrp"
  is "\<lambda>x::'a. -x"
proof-
  fix x y :: 'a assume xy: "-x + y \<in> \<N>"
  from this obtain a where a: "a \<in> \<N>" "-x + y = a" by fast
  from a(1) obtain a' where a': "a'\<in>\<N>" "a + -y = -y + a'" using distset_normal by fast
  from a(2) a'(2) have "- (-x) + -y = -(- y + a') + -y"
    using add.assoc[of "-x" y "-y"] by simp
  hence "- (-x) + -y = -a'" by (simp add: minus_add)
  with a'(1) show "- (-x) + -y \<in> \<N>" using distset_uminus_closed by simp
qed

lemmas uminus_coset_by_dist_sbgrp [simp] =
  uminus_coset_by_dist_sbgrp.abs_eq

lift_definition minus_coset_by_dist_sbgrp ::
  "'a coset_by_dist_sbgrp \<Rightarrow> 'a coset_by_dist_sbgrp \<Rightarrow>
      'a coset_by_dist_sbgrp"
  is "\<lambda>x y::'a. x - y"
proof-
  fix w x y z :: 'a assume wx: "-w + x \<in> \<N>" and yz: "-y + z \<in> \<N>"
  from this obtain a1 a2
    where a1: "a1 \<in> \<N>" "x = w + a1"
    and   a2: "a2 \<in> \<N>" "z = y + a2"
    by    simp
  from a1(1) obtain a3 where a3: "a3 \<in> \<N>" "y + a1 = a3 + y" using distset_normal by auto
  from a2(1) obtain a4 where a4: "a4 \<in> \<N>" "y + a2 = a4 + y" using distset_normal by auto
  from a3(2) a4(2) a1(2) a2(2) have "x - z = w - y + a3 + y - y - a4"
    using add.assoc[of "w - y" y a1] add.assoc[of "w - y" a3 y]
          add.assoc[of "w - y + a3" y "-y"]
    by (simp add: algebra_simps)
  hence "x - z = (w - y) + (a3 - a4)"
    using add.assoc[of "w - y + a3" y "-y"] add.assoc[of "w - y" a3 "-a4"] by simp
  hence "-(w - y) + (x - z) = a3 - a4"
    using add.assoc[of "-(w - y)" "w - y" "a3 - a4", symmetric]
          left_minus[of "w - y"]
    by    simp
  with a3(1) a4(1) show "-(w - y) + (x - z) \<in> \<N>" using distset_diff_closed by auto
qed

lemmas minus_coset_by_dist_sbgrp [simp] = minus_coset_by_dist_sbgrp.abs_eq

instance proof
  fix x y z :: "'a coset_by_dist_sbgrp"
  show "x + y + z = x + (y + z)" by transfer (simp add: distset_zero_closed algebra_simps)
  show " 0 + x = x" by transfer (simp add: distset_zero_closed)
  show " x + 0 = x" by transfer (simp add: distset_zero_closed)
  show "-x + x = 0" by transfer (simp add: distset_zero_closed)
  show "x + - y = x - y" by transfer (simp add: distset_zero_closed algebra_simps)
qed

end (* instantiation *)

instance coset_by_dist_sbgrp ::
  (ab_group_add_with_distinguished_subgroup) ab_group_add
proof
  show "\<And>x y :: 'a coset_by_dist_sbgrp. x + y = y + x"
    by transfer (simp add: distset_zero_closed)
qed auto

subsection \<open>Quotient rings\<close>

subsubsection \<open>Class definitions\<close>

text \<open>Now we set up subclasses of @{class ring} with a distinguished ideal.\<close>

class ring_with_distinguished_ideal = ring + ab_group_add_with_distinguished_subgroup +
  assumes distset_leftideal : "a \<in> \<N> \<Longrightarrow> r * a \<in> \<N>"
  and     distset_rightideal: "a \<in> \<N> \<Longrightarrow> a * r \<in> \<N>"

class ring_1_with_distinguished_ideal = ring_1 + ring_with_distinguished_ideal +
  assumes distset_no1: "1\<notin>\<N>"
  \<comment> \<open>
    For unitary rings we do not allow the quotient to be trivial to ensure that @{term 0} and
    @{term 1} will be different.
  \<close>

subsubsection \<open>The quotient ring type\<close>

text \<open>
  We just reuse the @{typ "'a coset_by_dist_sbgrp"} type to define a quotient ring, and
  instantiate it as a @{class ring}.
\<close>

type_synonym 'a distinguished_quotient_ring = "'a coset_by_dist_sbgrp"
\<comment> \<open>
  This is intended to be used with @{class ring_with_distinguished_ideal} or one of its subclasses.
\<close>

instantiation coset_by_dist_sbgrp :: (ring_with_distinguished_ideal) ring
begin

lift_definition times_coset_by_dist_sbgrp ::
  "'a distinguished_quotient_ring \<Rightarrow> 'a distinguished_quotient_ring \<Rightarrow>
    'a distinguished_quotient_ring"
  is "\<lambda>x y::'a. x * y"
proof-
  fix w x y z :: 'a assume wx: "-w + x \<in> \<N>" and yz: "-y + z \<in> \<N>"
  from this obtain a1 a2
    where a1: "a1 \<in> \<N>" "-w + x = a1"
    and   a2: "a2 \<in> \<N>" "-y + z = a2"
    by    fast
  from a1(2) a2(2) have "-(w * y) + (x * z) = w * a2 + a1 * z"
    by (simp add: algebra_simps)
  with a1(1) a2(1) show "-(w * y) + (x * z) \<in> \<N>"
    using distset_leftideal[of _ w] distset_rightideal[of _ z] distset_add_closed by auto
qed

lemmas times_coset_by_dist_sbgrp [simp] = times_coset_by_dist_sbgrp.abs_eq

instance proof
  fix x y z :: "'a distinguished_quotient_ring"
  show "x * y * z = x * (y * z)"      by transfer (simp add: distset_zero_closed algebra_simps)
  show "(x + y) * z = x * z + y * z"  by transfer (simp add: distset_zero_closed algebra_simps)
  show "x * (y + z) = x * y + x * z"  by transfer (simp add: distset_zero_closed algebra_simps)
qed

end (* instantiation *)

instantiation coset_by_dist_sbgrp :: (ring_1_with_distinguished_ideal) ring_1
begin

lift_definition one_coset_by_dist_sbgrp :: "'a distinguished_quotient_ring"
  is "1::'a" .

lemmas one_coset_by_dist_sbgrp [simp] = one_coset_by_dist_sbgrp.abs_eq[symmetric]

instance proof
  show "(0::'a distinguished_quotient_ring) \<noteq> (1::'a distinguished_quotient_ring)"
  proof transfer qed (simp add: distset_no1)
next
  fix x :: "'a distinguished_quotient_ring"
  show "1 * x = x" by transfer (simp add: distset_zero_closed algebra_simps)
  show "x * 1 = x" by transfer (simp add: distset_zero_closed algebra_simps)
qed

end (* instantiation *)

subsection \<open>Quotients of commutative rings\<close>

text \<open>
  For a commutative ring, the quotient modulo a prime ideal is an integral domain, and the quotient
  modulo a maximal ideal is a field.
\<close>

subsubsection \<open>Class definitions\<close>

class comm_ring_with_distinguished_ideal = comm_ring + ab_group_add_with_distinguished_subgroup +
  assumes distset_ideal : "a \<in> \<N> \<Longrightarrow> r * a \<in> \<N>"
begin

subclass ring_with_distinguished_ideal
  using distset_ideal by unfold_locales (auto simp add: mult.commute)

definition distideal_extension :: "'a \<Rightarrow> 'a set"
  where "distideal_extension a \<equiv> {x. \<exists>r z. z \<in> \<N> \<and> x = r * a + z}"

lemma distideal_extension: "\<N> \<subseteq> distideal_extension a"
  unfolding distideal_extension_def
proof clarify
  fix x assume "x\<in>\<N>"
  hence "x\<in>\<N> \<and> x = 0*a + x" by simp
  thus "\<exists>r z. z \<in> \<N> \<and> x = r*a + z" by fast
qed

lemma distideal_extension_diff_closed:
  "r \<in> distideal_extension a \<Longrightarrow> s \<in> distideal_extension a \<Longrightarrow>
    r - s \<in> distideal_extension a"
  unfolding distideal_extension_def
proof clarify
  fix r r' z z'
  assume "z \<in> \<N>" "z' \<in> \<N>"
  moreover have "r * a + z - (r' * a + z') = (r - r') * a + (z - z')"
    by (simp add: algebra_simps)
  ultimately show
    "\<exists>r'' z''. z'' \<in> \<N> \<and> r * a + z - (r' * a + z') = r'' * a + z''"
    using distset_diff_closed by fast
qed

lemma distideal_extension_ideal:
  "x \<in> distideal_extension a \<Longrightarrow> r * x \<in> distideal_extension a"
  unfolding distideal_extension_def
proof clarify
  fix s r z assume "z \<in> \<N>"
  thus "\<exists>r' z'. z' \<in> \<N> \<and> s * (r * a + z) = r' * a + z'"
    using distset_ideal by (fastforce simp add: algebra_simps)
qed

end (* class comm_ring_with_distinguished_ideal *)

class comm_ring_1_with_distinguished_ideal = ring_1 + comm_ring_with_distinguished_ideal +
  assumes distset_no1:
    "1\<notin>\<N>"
  \<comment> \<open>Don't allow the quotient to be trivial.\<close>
begin

subclass ring_1_with_distinguished_ideal using distset_no1 by unfold_locales

lemma distideal_extension_by: "a \<in> distideal_extension a"
  unfolding distideal_extension_def
proof
  have "0 \<in> \<N> \<and> a = 1 * a + 0" using distset_zero_closed by simp
  thus "\<exists>r z. z \<in> \<N> \<and> a = r * a + z" by fastforce
qed

end (* class comm_ring_1_with_distinguished_ideal *)

class comm_ring_1_with_distinguished_pideal = comm_ring_1_with_distinguished_ideal +
  assumes distset_pideal: "r * s \<in> \<N> \<Longrightarrow> r \<in> \<N> \<or> s \<in> \<N>"

class comm_ring_1_with_distinguished_maxideal = comm_ring_1_with_distinguished_ideal +
  assumes distset_maxideal:
    "\<lbrakk>
      \<N> \<subseteq> I; 1\<notin>I;
      \<forall>r s. r \<in> I \<and> s \<in> I \<longrightarrow> r - s \<in> I;
      \<forall>a r. a \<in> I \<longrightarrow> r * a \<in> I
    \<rbrakk> \<Longrightarrow> I = \<N>"
begin

lemma distset_maxideal_vs_distideal_extension:
  "1 \<notin> distideal_extension a \<Longrightarrow> distideal_extension a = \<N>"
  using distideal_extension distideal_extension_diff_closed distideal_extension_ideal
        distset_maxideal
  by    force

subclass comm_ring_1_with_distinguished_pideal
proof
  fix a b :: 'a
  assume ab: "a * b \<in> \<N>"
  have "\<not> (a \<notin> \<N> \<and> b \<notin> \<N>)"
  proof clarify
    assume a: "a \<notin> \<N>" and b: "b \<notin> \<N>"
    define I where "I \<equiv> distideal_extension b"
    have "1 \<notin> I"
      unfolding distideal_extension_def I_def
    proof clarify
      fix r z assume rz: "z \<in> \<N>" "1 = r * b + z"
      from rz(2) have "a = r * (a * b) + a * z" using mult_1_right by (simp add: algebra_simps)
      moreover from ab rz(1) have "r * (a * b) \<in> \<N>" and "a * z \<in> \<N>"
        using distset_ideal by auto
      ultimately show False using a distset_add_closed by fastforce
    qed
    with I_def b show False
      using distset_maxideal_vs_distideal_extension distideal_extension_by by fast
  qed
  thus "a \<in> \<N> \<or> b \<in> \<N>" by fast
qed

end (* class comm_ring_1_with_distinguished_maxideal *)

subsubsection \<open>Instances and instantiations\<close>

instance coset_by_dist_sbgrp :: (comm_ring_with_distinguished_ideal) comm_ring
proof
  fix x y :: "'a distinguished_quotient_ring"
  show "x * y = y * x" by transfer (simp add: distset_zero_closed algebra_simps)
qed (simp add: algebra_simps)

instance coset_by_dist_sbgrp :: (comm_ring_1_with_distinguished_ideal) comm_ring_1
 by standard (auto simp add: algebra_simps)

instance coset_by_dist_sbgrp :: (comm_ring_1_with_distinguished_pideal) idom
proof (standard, transfer)
  fix a b :: 'a show
    "-a + 0 \<notin> \<N> \<Longrightarrow> -b + 0 \<notin> \<N> \<Longrightarrow>
      -(a * b) + 0 \<notin> \<N>"
    using distset_pideal distset_uminus_closed by fastforce
qed

lemma inverse_in_quotient_mod_maxideal:
  "\<exists>y. -(y * x) + 1 \<in> \<N>" if "x \<notin> \<N>"
  for x :: "'a::comm_ring_1_with_distinguished_maxideal"
proof-
  from that have "1 \<notin> distideal_extension x \<Longrightarrow> False"
    using distset_uminus_closed distset_maxideal_vs_distideal_extension distideal_extension_by
    by    auto
  from this obtain y z where yz: "z \<in> \<N>" "1 = y * x + z"
    using distideal_extension_def by fast
  from yz(2) have "- (y * x) + 1 = z" by (simp add: algebra_simps)
  with yz(1) show "\<exists>y. -(y * x) + 1 \<in> \<N>" by fast
qed

instantiation coset_by_dist_sbgrp :: (comm_ring_1_with_distinguished_maxideal) field
begin

lift_definition inverse_coset_by_dist_sbgrp ::
  "'a distinguished_quotient_ring \<Rightarrow> 'a distinguished_quotient_ring"
  is "\<lambda>x::'a. if x\<in>\<N> then 0 else (SOME y::'a. -(y*x) + 1 \<in> \<N>)"
proof-
  fix x x' :: 'a
  assume xx': "-x + x' \<in> \<N>"
  define ix ix'
    where "ix  \<equiv> if  x \<in> \<N> then 0 else (SOME y::'a. -(y * x ) + 1 \<in> \<N>)"
    and   "ix' \<equiv> if x' \<in> \<N> then 0 else (SOME y::'a. -(y * x') + 1 \<in> \<N>)"
  show "-ix + ix' \<in> \<N>"
  proof (cases "x\<in>\<N>")
    case True with xx' ix_def ix'_def show ?thesis
      using distset_lcoset_closed1[of x] distset_zero_closed by auto
  next
    case False
    with xx' have "x' \<notin> \<N>" using distset_lcoset_closed2 by fast
    with ix_def ix'_def False have "-((-ix + ix') * x) + ix' * (x + - x') \<in> \<N>"
      using someI_ex[OF inverse_in_quotient_mod_maxideal]
            distset_uminus_plus_closed[of "-(ix * x) + 1" "-(ix' * x') + 1"]
      by    (force simp add: algebra_simps)
    moreover have "ix' * (x + -x') \<in> \<N>"
      using distset_uminus_closed[OF xx'] distset_ideal by auto
    ultimately have "(-ix + ix') * x \<in> \<N>" using distset_lcoset_closed2 by force
    with False show ?thesis using distset_pideal by fast
  qed
qed

lemma inverse_coset_by_dist_sbgrp_eq0 [simp]:
  "x \<in> \<N> \<Longrightarrow> inverse (distinguished_quotient_coset x) = 0"
  by transfer (simp add: distset_zero_closed)

lemma coset_by_dist_sbgrp_inverse_rep:
  "x \<notin> \<N> \<Longrightarrow> -(y * x) + 1 \<in> \<N> \<Longrightarrow>
    inverse (distinguished_quotient_coset x) = distinguished_quotient_coset y"
proof transfer
  fix x y :: 'a
  assume xy: "x \<notin> \<N>" "-(y * x) + 1 \<in> \<N>"
  define z :: 'a where "z \<equiv> (SOME y. - (y * x) + 1 \<in> \<N>)"
  with xy have "(-z + y) * x \<in> \<N>"
    using someI_ex[OF inverse_in_quotient_mod_maxideal]
          distset_diff_closed[of "-(z * x) + 1" "-(y * x) + 1"]
    by    (fastforce simp add: algebra_simps)
  with xy(1) show "- (if x \<in> \<N> then 0 else z) + y \<in> \<N>"
    using distset_pideal by auto
qed

definition divide_coset_by_dist_sbgrp_def [simp]:
  "x div y = (x::'a distinguished_quotient_ring) * inverse y"

lemma coset_by_dist_sbgrp_divide_rep:
  "y \<notin> \<N> \<Longrightarrow> -(z * y) + 1 \<in> \<N> \<Longrightarrow>
    distinguished_quotient_coset x div distinguished_quotient_coset y
      = distinguished_quotient_coset (x * z)"
  by (simp add: coset_by_dist_sbgrp_inverse_rep)

instance proof
  show "inverse (0::'a distinguished_quotient_ring) = 0"
    by transfer (simp add: distset_zero_closed)
next
  fix x :: "'a distinguished_quotient_ring"
  show "x \<noteq> 0 \<Longrightarrow> inverse x * x = 1"
  proof transfer
    fix a::'a
    assume "-a + 0 \<notin> \<N>"
    moreover define ia
      where "ia \<equiv> if a \<in> \<N> then 0 else (SOME b. - (b * a) + 1 \<in> \<N>)"
    ultimately show "-(ia * a) + 1 \<in> \<N>"
      using distset_uminus_closed someI_ex[OF inverse_in_quotient_mod_maxideal] by auto
  qed
qed (rule divide_coset_by_dist_sbgrp_def)

end (* instantiation *)


end (* theory *)
