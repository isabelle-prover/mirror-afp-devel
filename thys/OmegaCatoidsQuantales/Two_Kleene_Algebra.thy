(* 
Title: 2-Kleene Algebras
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>2-Kleene algebras\<close>

theory "Two_Kleene_Algebra"
  imports Quantales_Converse.Modal_Kleene_Algebra_Var

begin

text \<open>Here we develop (globular) 2-semigroups and (globular) 2-Kleene algebras. These should eventually
be extended to n-structures and omega-structures.\<close>

subsection \<open>Copies for 0-structures\<close>

class comp0_op =
  fixes comp0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>0" 70)

class id0_op =
  fixes id0 :: "'a" ("1\<^sub>0")

class star0_op =
  fixes star0 :: "'a \<Rightarrow> 'a"

class dom0_op =
  fixes dom\<^sub>0 :: "'a \<Rightarrow> 'a"

class cod0_op =
  fixes cod\<^sub>0 :: "'a \<Rightarrow> 'a"

class monoid_mult0 = comp0_op + id0_op +
  assumes par_assoc0: "x \<cdot>\<^sub>0 (y \<cdot>\<^sub>0 z) = (x \<cdot>\<^sub>0 y) \<cdot>\<^sub>0 z"
  and comp0_unl: "1\<^sub>0 \<cdot>\<^sub>0 x = x" 
  and comp0_unr: "x \<cdot>\<^sub>0 1\<^sub>0 = x" 

class dioid0 = monoid_mult0 + join_semilattice_zero +
  assumes distl0: "x \<cdot>\<^sub>0 (y + z) = x \<cdot>\<^sub>0 y + x \<cdot>\<^sub>0 z"
  and distr0: "(x + y) \<cdot>\<^sub>0 z = x \<cdot>\<^sub>0 z + y \<cdot>\<^sub>0 z"
  and annil0: "0 \<cdot>\<^sub>0 x = 0"
  and annir0: "x \<cdot>\<^sub>0 0 = 0"

class kleene_algebra0 = dioid0 + star0_op +
  assumes star0_unfoldl: "1\<^sub>0 + x \<cdot>\<^sub>0 star0 x \<le> star0 x"  
  and star0_unfoldr: "1\<^sub>0 + star0 x \<cdot>\<^sub>0 x \<le> star0 x"
  and star0_inductl: "z + x \<cdot>\<^sub>0 y \<le> y \<Longrightarrow> star0 x \<cdot>\<^sub>0 z \<le> y"
  and star0_inductr: "z + y \<cdot>\<^sub>0 x \<le> y \<Longrightarrow> z \<cdot>\<^sub>0 star0 x \<le> y"

class domain_semiring0 = dioid0 + dom0_op +
  assumes d0_absorb: "x \<le> dom\<^sub>0 x \<cdot>\<^sub>0 x"
  and d0_local: "dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and d0_add: "dom\<^sub>0 (x + y) = dom\<^sub>0 x + dom\<^sub>0 y"
  and d0_subid: "dom\<^sub>0 x \<le> 1\<^sub>0"
  and d0_zero: "dom\<^sub>0 0 = 0"

class codomain_semiring0 = dioid0 + cod0_op +
  assumes cod0_absorb: "x \<le> x \<cdot>\<^sub>0 cod\<^sub>0 x" 
  and cod0_local: "cod\<^sub>0 (cod\<^sub>0 x \<cdot>\<^sub>0 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and cod0_add: "cod\<^sub>0 (x + y) = cod\<^sub>0 x + cod\<^sub>0 y"
  and cod0_subid: "cod\<^sub>0 x \<le> 1\<^sub>0"
  and cod0_zero: "cod\<^sub>0 0 = 0"

class modal_semiring0 = domain_semiring0 + codomain_semiring0 +
  assumes dc_compat0: "dom\<^sub>0 (cod\<^sub>0 x) = cod\<^sub>0 x" 
  and cd_compat0:  "cod\<^sub>0 (dom\<^sub>0 x) = dom\<^sub>0 x" 

class modal_kleene_algebra0 = modal_semiring0 + kleene_algebra0

sublocale monoid_mult0 \<subseteq> mm0: monoid_mult "1\<^sub>0" "(\<cdot>\<^sub>0)"
  by (unfold_locales, simp_all add: local.par_assoc0 local.comp0_unl local.comp0_unr)

sublocale dioid0 \<subseteq> d0: dioid_one_zero _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _ _ _
  by (unfold_locales, simp_all add: local.distl0 local.distr0 annil0 annir0)

sublocale dioid0 \<subseteq> dd0: dioid0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _
  by unfold_locales (simp_all add: local.mm0.mult_assoc local.d0.distrib_left)

sublocale kleene_algebra0 \<subseteq> k0: kleene_algebra _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _ _ _ star0
  apply unfold_locales
  using local.star0_unfoldl apply blast
  by (simp_all add: local.star0_inductl local.star0_inductr local.star0_unfoldl)

sublocale kleene_algebra0 \<subseteq> dk0: kleene_algebra0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ _
  by (unfold_locales, simp_all add: local.star0_inductr local.star0_inductl)

sublocale domain_semiring0 \<subseteq> dsr0: domain_semiring _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _ "dom\<^sub>0" _ _
  apply unfold_locales
      apply (simp add: local.d0_absorb local.join.sup_absorb2)
     apply (simp add: local.d0_local)
    apply (simp add: local.d0_subid local.join.sup_absorb2)
  apply (simp add: local.d0_zero)
  by (simp add: local.d0_add)

sublocale codomain_semiring0 \<subseteq> csr0: range_semiring  _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _ "cod\<^sub>0" _ _
  apply unfold_locales
      apply (simp add: local.cod0_absorb local.join.sup_absorb2)
     apply (simp add: local.cod0_local)
    apply (simp add: local.cod0_subid local.join.sup_absorb2)
   apply (simp add: local.cod0_zero)
  by (simp add: local.cod0_add)

sublocale codomain_semiring0 \<subseteq> ds0dual: domain_semiring0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ cod\<^sub>0
  by unfold_locales simp_all

sublocale modal_semiring0 \<subseteq> msr0: dr_modal_semiring _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _  "dom\<^sub>0" _ _ "cod\<^sub>0"
  by (unfold_locales, simp_all add: local.dc_compat0 local.cd_compat0)

sublocale modal_semiring0 \<subseteq> msr0dual: modal_semiring0 "dom\<^sub>0" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"
  by unfold_locales simp_all

sublocale modal_kleene_algebra0 \<subseteq> mka0: dr_modal_kleene_algebra _ "(\<cdot>\<^sub>0)" "1\<^sub>0" _ _ _ star0  "dom\<^sub>0" "cod\<^sub>0"..

sublocale modal_kleene_algebra0 \<subseteq> mka0dual: modal_kleene_algebra0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ _ "dom\<^sub>0" "cod\<^sub>0"..


subsection \<open>Copies for 1-structures\<close>

class comp1_op =
  fixes comp1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>1" 70)

class id1_op =
  fixes id1 :: "'a" ("1\<^sub>1")

class star1_op =
  fixes star1 :: "'a \<Rightarrow> 'a"

class dom1_op =
  fixes dom\<^sub>1 :: "'a \<Rightarrow> 'a"

class cod1_op =
  fixes cod\<^sub>1 :: "'a \<Rightarrow> 'a"

class monoid_mult1 = comp1_op + id1_op +
  assumes par_assoc1: "x \<cdot>\<^sub>1 (y \<cdot>\<^sub>1 z) = (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>1 z"
  and comp1_unl: "1\<^sub>1 \<cdot>\<^sub>1 x = x" 
  and comp1_unr: "x \<cdot>\<^sub>1 1\<^sub>1 = x"

class dioid1 = monoid_mult1 + join_semilattice_zero +
  assumes distl1: "x \<cdot>\<^sub>1 (y + z) = x \<cdot>\<^sub>1 y + x \<cdot>\<^sub>1 z"
  and distr1: "(x + y) \<cdot>\<^sub>1 z = x \<cdot>\<^sub>1 z + y \<cdot>\<^sub>1 z"
  and annil1: "0 \<cdot>\<^sub>1 x = 0"
  and annir1: "x \<cdot>\<^sub>1 0 = 0"

class kleene_algebra1 = dioid1 + star1_op +
  assumes star1_unfoldl: "1\<^sub>1 + x \<cdot>\<^sub>1 star1 x \<le> star1 x"  
  and star1_unfoldr: "1\<^sub>1 + star1 x \<cdot>\<^sub>1 x \<le> star1 x"
  and star1_inductl: "z + x \<cdot>\<^sub>1 y \<le> y \<Longrightarrow> star1 x \<cdot>\<^sub>1 z \<le> y"
  and star1_inductr: "z + y \<cdot>\<^sub>1 x \<le> y \<Longrightarrow> z \<cdot>\<^sub>1 star1 x \<le> y"

class domain_semiring1 = dioid1 + dom1_op +
  assumes d1_absorb: "x \<le> dom\<^sub>1 x \<cdot>\<^sub>1 x"
  and d1_local: " dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = dom\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and d1_add: "dom\<^sub>1 (x + y) = dom\<^sub>1 x + dom\<^sub>1 y"
  and d1_subid: "dom\<^sub>1 x \<le> 1\<^sub>1"
  and d1_zero: "dom\<^sub>1 0 = 0"

class codomain_semiring1 = dioid1 + cod1_op +
  assumes cod1_absorb: "x \<le> x \<cdot>\<^sub>1 cod\<^sub>1 x" 
  and cod1_local: "cod\<^sub>1 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = cod\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and cod1_add: "cod\<^sub>1 (x + y) = cod\<^sub>1 x + cod\<^sub>1 y"
  and cod1_subid: "cod\<^sub>1 x \<le> 1\<^sub>1"
  and cod1_zero: "cod\<^sub>1 0 = 0"

class modal_semiring1 = domain_semiring1 + codomain_semiring1 +
  assumes dc_compat1: "dom\<^sub>1 (cod\<^sub>1 x) = cod\<^sub>1 x" 
  and cd_compat1:  "cod\<^sub>1 (dom\<^sub>1 x) = dom\<^sub>1 x" 

class modal_kleene_algebra1 = modal_semiring1 + kleene_algebra1

sublocale  monoid_mult1 \<subseteq> mm1: monoid_mult "1\<^sub>1" "(\<cdot>\<^sub>1)"
  by (unfold_locales, simp_all add: local.par_assoc1 comp1_unl comp1_unr) 

sublocale  dioid1 \<subseteq>d1: dioid_one_zero  _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _ _ _ 
  by (unfold_locales, simp_all add: local.distl1 local.distr1 local.annil1 local.annir1)

sublocale  dioid1 \<subseteq> dd1: dioid1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x"  "1\<^sub>1"
  apply unfold_locales
        apply simp_all
   apply (simp add: local.mm1.mult_assoc)
  by (simp add: local.d1.distrib_left)

sublocale kleene_algebra1 \<subseteq> k1: kleene_algebra _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _ _ _ star1
  apply unfold_locales
  using local.star1_unfoldl apply blast
   apply (simp add: local.star1_inductl)
  by (simp add: local.star1_inductr)

sublocale kleene_algebra1 \<subseteq> dk1: kleene_algebra1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" "1\<^sub>1" star1
  by (unfold_locales, simp_all add: local.star1_inductr local.star1_inductl)

sublocale domain_semiring1 \<subseteq> dsr1: domain_semiring _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _ "dom\<^sub>1" _ _ 
  apply unfold_locales
  using local.d1_absorb local.join.sup_absorb2 apply force
     apply (simp add: local.d1_local)
  using local.d1_subid local.join.sup_absorb2 apply force
  using local.d1_zero apply fastforce
  by (simp add: local.d1_add)

sublocale codomain_semiring1 \<subseteq> csr1: range_semiring _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _ cod\<^sub>1 _ _
  apply unfold_locales
      apply (simp add: local.cod1_absorb local.join.sup_absorb2)
     apply (simp add: local.cod1_local)
    apply (simp add: local.cod1_subid local.join.sup_absorb2)
  using local.cod1_zero apply fastforce
  by (simp add: local.cod1_add)

sublocale codomain_semiring1 \<subseteq> ds1dual: domain_semiring1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ cod\<^sub>1
  by (unfold_locales, simp_all add: local.cod1_absorb local.cod1_local local.cod1_add local.cod1_subid)

sublocale modal_semiring1 \<subseteq> msr1: dr_modal_semiring _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _   "dom\<^sub>1" _ _ "cod\<^sub>1"
  apply unfold_locales
   apply (simp add: local.dc_compat1)
  by (simp add: local.cd_compat1)

sublocale modal_semiring1 \<subseteq> msr1dual: modal_semiring1 "dom\<^sub>1" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  by unfold_locales simp_all

sublocale modal_kleene_algebra1 \<subseteq> mka1: dr_modal_kleene_algebra _ "(\<cdot>\<^sub>1)" "1\<^sub>1" _ _ _ star1 "dom\<^sub>1" "cod\<^sub>1"..

sublocale modal_kleene_algebra1 \<subseteq> mka1dual: modal_kleene_algebra1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ _ "dom\<^sub>1" "cod\<^sub>1"..

subsection \<open>Globular 2-semirings\<close>

class two_semiring = modal_semiring0 + modal_semiring1 +
  assumes interchange: "(w \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (w \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 z)"
  and d1_hom: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) \<le> dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_hom: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) \<le> cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"
  and d0_hom: "dom\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
  and c0_hom: "cod\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  and d1d0 [simp]: "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"

class strong_two_semiring = two_semiring + 
  assumes d1_strong_hom [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) = dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_strong_hom: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"

sublocale two_semiring \<subseteq> tgsdual: two_semiring "dom\<^sub>0" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"  "dom\<^sub>1" "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  apply unfold_locales
       apply (simp_all add: local.interchange local.d0_hom local.c0_hom local.c1_hom local.d1_hom)
  by (metis local.cd_compat1 local.d1d0 local.dc_compat0)

sublocale strong_two_semiring \<subseteq> stgsdual: strong_two_semiring "dom\<^sub>0" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"  "dom\<^sub>1" "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  apply unfold_locales by (simp_all add: local.c1_strong_hom)

context two_semiring
begin
  
lemma c1d0 [simp]: "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
proof-
  have "cod\<^sub>1 (dom\<^sub>0 x) = cod\<^sub>1 (dom\<^sub>1 (dom\<^sub>0 x))"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 x)"
    using local.cd_compat1 by presburger
  also have "\<dots> = dom\<^sub>0 x"
    by simp
  finally show ?thesis.
qed

lemma d1c0 [simp]: "dom\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  by (simp add: msr1.d_cod_fix)

lemma c1c0 [simp]: "cod\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  by simp

lemma "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 \<le> 1\<^sub>1"
  (*nitpick [expect=genuine]*)
  oops

lemma id1_comp0_var: "1\<^sub>1 \<le> 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
proof-
  have "1\<^sub>1 = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0"
    by simp
  also have "\<dots> = (1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>1) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>1)"
    by simp
  also have "\<dots> \<le> (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    using local.interchange by presburger
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    by simp
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
    by simp
  finally show ?thesis.
qed

lemma "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 = 1\<^sub>1"
  (*nitpick*)
  oops

lemma id0_le_id1: "1\<^sub>0 \<le> 1\<^sub>1"
proof-
  have "1\<^sub>0 = 1\<^sub>0 \<cdot>\<^sub>0 1\<^sub>0"
    by simp
  also have "... = (1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>0) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>1)"
    by simp
  also have "... \<le> (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>0 \<cdot>\<^sub>0 1\<^sub>1)"
    using local.interchange by blast
  also have "... = 1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>1"
    by simp
  also have "... = 1\<^sub>1"
    by simp
  finally show ?thesis.
qed

lemma id0_comp1_eq [simp]: "1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>0 = 1\<^sub>0"
proof-
  have "1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>0 = dom\<^sub>0 1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 1\<^sub>0"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 dom\<^sub>0 1\<^sub>0"
    using local.d1d0 by presburger
  also have "\<dots> = dom\<^sub>0 1\<^sub>0"
    by simp
  finally show ?thesis
    by simp
qed

lemma d1_id0 [simp]: "dom\<^sub>1 1\<^sub>0 = 1\<^sub>0"
proof-
  have "dom\<^sub>1 1\<^sub>0 = dom\<^sub>1 (dom\<^sub>0 1\<^sub>0)"
    by simp
  also have "\<dots> = dom\<^sub>0 1\<^sub>0"
    using local.d1d0 by blast
  also have "\<dots> = 1\<^sub>0"
    by simp
  finally show ?thesis.
qed

lemma d0_id1 [simp]: "dom\<^sub>0 1\<^sub>1 = 1\<^sub>0"
proof-
  have a: "dom\<^sub>0 1\<^sub>1 \<le> 1\<^sub>0"
    by simp
  have "1\<^sub>0 \<le> 1\<^sub>1"
    by (simp add: local.id0_le_id1)
  hence "1\<^sub>0 \<le> dom\<^sub>0 1\<^sub>1"
    using local.dsr0.d_iso by fastforce
  thus ?thesis
    by (simp add: local.dual_order.antisym)
qed

lemma c0_id1: "cod\<^sub>0 1\<^sub>1 = 1\<^sub>0"
  using id0_le_id1 local.csr0.rdual.dom_iso local.dual_order.antisym by fastforce

lemma c0_id0: "cod\<^sub>1 1\<^sub>0 = 1\<^sub>0"
  using c1d0 d0_id1 by blast

lemma comm_d0d1: "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>1 (dom\<^sub>0 x)"
proof-
  have "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 (dom\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 x))"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>1 x)"
    using local.d1_hom local.dsr0.d_iso by blast
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 1\<^sub>0"
    using d0.mult_isol local.d0_subid by blast
  finally have a: "dom\<^sub>0 (dom\<^sub>1 x) \<le> dom\<^sub>1 (dom\<^sub>0 x)"
    by simp
  have "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
    by simp
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 dom\<^sub>0 x"
    using local.d0_hom by blast 
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 1\<^sub>0"
    by (simp add: d1.mult_isol)
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 1\<^sub>1"
    using d1.mult_isol local.id0_le_id1 by presburger
  finally have "dom\<^sub>1 (dom\<^sub>0 x) \<le> dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  thus ?thesis
    using a by auto
qed

lemma comm_d0c1: "dom\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>1 (dom\<^sub>0 x)"
proof-
 have "dom\<^sub>0 (cod\<^sub>1 x) = dom\<^sub>0 (cod\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 x))"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 cod\<^sub>1 x)"
    using local.c1_hom local.dsr0.d_iso by blast
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 cod\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  also have "\<dots> = cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 1\<^sub>0"
    using d0.mult_isol local.d0_subid by blast
  finally have a: "dom\<^sub>0 (cod\<^sub>1 x) \<le> cod\<^sub>1 (dom\<^sub>0 x)"
    by simp
  have "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>1 cod\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    using local.d0_hom by blast
  also have  "\<dots> \<le> 1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    by (simp add: d1.mult_isor)
  also have  "\<dots> \<le> 1\<^sub>1 \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    using d1.mult_isor local.id0_le_id1 by blast
  finally have "cod\<^sub>1 (dom\<^sub>0 x) \<le> dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  thus ?thesis
    using a by auto
qed

lemma comm_c0c1: "cod\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>1 (cod\<^sub>0 x)"
  by (metis c1c0 local.csr0.rdual.dom_llp local.csr0.rdual.dom_ord local.csr0.rdual.dsg1 local.csr0.rdual.dsg4 local.csr1.rdual.dom_llp local.csr1.rdual.dsg1 local.tgsdual.d0_hom local.tgsdual.d1_hom)

lemma comm_c0d1: "cod\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>1 (cod\<^sub>0 x)"
  by (metis d1c0 local.c0_hom local.csr0.rdual.dom_subid_aux2 local.csr0.rdual.domain_1'' local.csr0.rdual.domain_invol local.csr0.rdual.dsg1 local.d1_hom local.dsr1.dom_subid_aux2 local.dsr1.dom_subid_aux2'' local.dsr1.dsg1 local.dual_order.antisym)

text \<open>We prove further lemmas that are not related to the globular structure.\<close>

lemma d0_comp1_idem [simp]: "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x = dom\<^sub>0 x"
proof-
  have "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x = dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>1 dom\<^sub>1 (dom\<^sub>0 x)"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 x)"
    using local.dsr1.dom_el_idem by blast
  also have "\<dots> =  dom\<^sub>0 x"
    by simp
  finally show ?thesis.
qed

lemma cod0_comp1_idem: "cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 x = cod\<^sub>0 x"
  by (metis d1c0 local.dsr1.dsg1)

lemma  dom01_loc [simp]: "dom\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>1 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>1 y) = dom\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 y))"
    by (simp add: local.comm_d0d1)
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>1 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y)"
    using local.comm_d0d1 local.d1d0 by presburger
  finally show ?thesis..
qed

lemma cod01_locl: "cod\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>1 y)"
  by (metis c1c0 comm_c0c1 local.cod1_local)

lemma dom01_exp [simp]: "dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>1 y)"
  by (metis local.c1d0 local.cod1_local local.comm_d0c1)

lemma cod01_exo: "cod\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>1 y)"
  by (metis comm_c0d1 d1c0 local.d1_local)

lemma dom01_loc_var [simp]: "dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 (dom\<^sub>0 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 y))"
    by (simp add: local.comm_d0d1)
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y)"
    by simp
    finally show ?thesis..
  qed

lemma cod01_loc_var: "cod\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  by (metis c1c0 comm_c0c1 local.cod0_local)

lemma dom0cod1_exp: "dom\<^sub>0 (x \<cdot>\<^sub>0 y) \<le> dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>0 y) = dom\<^sub>0 (cod\<^sub>1 (x \<cdot>\<^sub>0 y))"
    by (simp add: local.comm_d0c1)
  also have "\<dots> \<le> dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y)"
    by (simp add: local.c1_hom local.dsr0.d_iso)
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by (simp add: local.comm_d0c1)
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y)"
    by simp
  finally show ?thesis.
qed

lemma cod0dom1_exp: " cod\<^sub>0 (x \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y)"
  by (metis comm_c0d1 d1c0 local.cod0_local local.csr0.rdual.dom_iso local.d1_hom)

lemma (in two_semiring) d0_comp1: "dom\<^sub>0 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 z)"
proof-
  have "dom\<^sub>0 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) = (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 z)"
    using local.interchange by presburger
  finally show ?thesis.
qed

lemma d1_comp1: "dom\<^sub>1 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (dom\<^sub>1 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>1 x \<cdot>\<^sub>0 z)"
  by (metis local.dsr1.dom_el_idem local.tgsdual.interchange)

lemma d01_export: "dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
proof-
  have "dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 dom\<^sub>0 y"
    by (simp add: local.d0_hom)
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
    by (simp add: local.comm_d0d1)
  finally show ?thesis.
qed

lemma cod01_export: "cod\<^sub>0 (x \<cdot>\<^sub>1 cod\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  by (metis local.c0_hom local.c1c0 local.comm_c0c1)

lemma d10_export [simp]: "dom\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>1 y) = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>1 y"
  by (metis local.d1d0 local.dsr1.dsg3)

lemma cod10_export: "cod\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  by (metis local.c1c0 local.csr1.rdual.dsg3)

lemma d0_comp10: "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y"
proof (rule order.antisym)
  have "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y \<le> dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 (dom\<^sub>0 x) \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>0 y)) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y)"
    using d0.mult_isor local.tgsdual.c0_hom by blast
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>1 1\<^sub>0) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by (simp add: local.d0.mult_isol_var local.d1.mult_isol_var)
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>1 1\<^sub>1) \<cdot>\<^sub>0 (1\<^sub>1 \<cdot>\<^sub>1 dom\<^sub>0 y)"
    using local.d0.mult_isol_var local.dd1.d1.mult_isol local.dd1.d1.mult_isor local.id0_le_id1 by presburger
  also have "\<dots> \<le> dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y"
    by simp
  finally show "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y \<le> dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y".
next
  have "dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y = (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    using local.interchange by blast
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>0 \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by (simp add: local.d1.mult_isol_var local.dsr0.dom_subid_aux2 local.dsr0.dom_subid_aux2'')
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
    by simp
  finally show "dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y".
qed

lemma dom_exchange_strong: "(dom\<^sub>0 w \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 z) = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
proof-
  have  "(dom\<^sub>0 w \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 z) = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by (simp add: local.d0_comp10)
  also have "\<dots> = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by (metis local.dd0.mm0.mult_assoc local.dsr0.dsg4)
  also have  "\<dots> = dom\<^sub>0 (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by simp
  also have  "\<dots> = dom\<^sub>0 (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    using local.d0_comp10 by presburger
  also have  "\<dots> = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by simp
  finally show ?thesis.
qed

end

context strong_two_semiring
begin

lemma id1_comp0: "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 \<le> 1\<^sub>1"
proof-
  have "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 = dom\<^sub>1 1\<^sub>1 \<cdot>\<^sub>0 dom\<^sub>1 1\<^sub>1"
    by simp
  also have "\<dots> = dom\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    by simp
  also have "\<dots> \<le> 1\<^sub>1"
    using local.d1_subid by blast
  finally show ?thesis.
qed

lemma id1_comp0_eq [simp]: "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 = 1\<^sub>1"
proof-
  have "1\<^sub>1 = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0"
    by simp
  also have "\<dots> = (1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>1) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>1)"
    by simp
  also have "\<dots> \<le> (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    using local.interchange by presburger
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    by simp
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
    by simp
  finally have "1\<^sub>1 \<le> 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1".
  thus ?thesis
    by (simp add: local.antisym_conv local.id1_comp0)
qed

lemma  "1\<^sub>0 = 1\<^sub>1"
  (*nitpick  *)
  oops

lemma dom0cod1_exp: "dom\<^sub>0 (x \<cdot>\<^sub>0 y) = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>0 y) = dom\<^sub>0 (cod\<^sub>1 (x \<cdot>\<^sub>0 y))"
    using local.c1d0 local.comm_d0c1 by presburger
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y)"
    by (simp add: local.c1_hom local.dsr0.d_iso)
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by (simp add: local.comm_d0c1)
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y)"
    by simp
  finally show ?thesis.
qed

lemma cod0dom1_exp: "cod\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  by (metis local.comm_c0d1 local.d1c0 local.ds0dual.d0_local local.stgsdual.c1_strong_hom)

end

text \<open>The following laws are diamond laws. It remains to define diamonds for them.\<close>

context two_semiring
begin

lemma fdia0fdia1_prop: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 z))"
  by simp

lemma bdia0fdia1_prop [simp]: "cod\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) = cod\<^sub>0 ((x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y)"
  by (metis local.comm_c0d1 local.d1c0 local.ds0dual.d0_local)

lemma fdia0bdia1_prop: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 z))"
  by (metis local.c1d0 local.comm_d0c1 local.d0_local)

lemma bdia0bdia1_prop: "cod\<^sub>0 (cod\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) = cod\<^sub>0 ((x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y)"
  by simp

lemma fdia0fdia1_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
proof-
  have "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>0 (x \<cdot>\<^sub>1 z))"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
    using d0.mult_isol local.dsr0.d_iso local.tgsdual.c0_hom by presburger
  finally show ?thesis.
qed

lemma fdia00_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>0 (x \<cdot>\<^sub>1 z)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
  using local.fdia0fdia1_prop2 by auto
 
lemma bdia0dom1_prop2: "cod\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using local.c0_hom local.csr0.rdual.fd_def local.csr0.rdual.fd_iso1 local.tgsdual.d0_comp10 by auto

lemma bdia0dom0_prop2: "cod\<^sub>0 (dom\<^sub>0 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z) \<cdot>\<^sub>0 y)"
  by (simp add: local.csr0.rdual.dom_iso local.dd0.d0.mult_isol local.tgsdual.c0_hom)

lemma fdia0bdia1_prop_2: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>1 (z \<cdot>\<^sub>1 x)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
  by (metis fdia00_prop2 local.c1d0 local.csr1.rdual.dsg1 local.csr1.rdual.dsg4 local.dom01_exp local.msr0dual.cod0_local)

lemma fdia0bdiao_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>0 (z \<cdot>\<^sub>1 x)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (cod\<^sub>0 z \<cdot>\<^sub>1 cod\<^sub>0 x))"
  by (simp add: local.c0_hom local.dd0.d0.mult_isor local.dsr0.dom_iso)

lemma bdia0bdia1_prop2: "cod\<^sub>0 (cod\<^sub>1 (z \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using bdia0dom1_prop2 local.csr0.rdual.dsg4 local.tgsdual.d0_comp10 by fastforce

lemma bdia0bdia0_prop2: "cod\<^sub>0 (cod\<^sub>0 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using bdia0dom1_prop2 by force

lemma fdia1fdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (y \<cdot>\<^sub>0 z)) \<le> dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>1 y \<cdot>\<^sub>0 z))"
  by (metis d1.mult_isol local.comm_d0d1 local.d1_hom local.d1d0 local.dsr0.d_iso local.dsr1.d_iso local.tgsdual.cod01_loc_var)

lemma fdia1bdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 y)) \<le> dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 dom\<^sub>1 y))"
  by (simp add: d1.mult_isol local.dsr1.d_iso local.tgsdual.dom0cod1_exp)

lemma bdia1fdia0_prop3: "cod\<^sub>1 (dom\<^sub>0 (y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x) \<le> cod\<^sub>1 (dom\<^sub>0 (cod\<^sub>1 y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x)"
  by (simp add: local.csr1.rdual.dom_iso local.dd1.d1.mult_isol local.tgsdual.cod0dom1_exp)

lemma bdia1bdia0_prop3: "cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 x) \<le> cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 cod\<^sub>1 y) \<cdot>\<^sub>1 x)"
  by (metis local.c1_hom local.c1c0 local.comm_c0c1 local.csr0.rdual.dom_iso local.csr1.rdual.dom_iso local.dd1.d1.mult_isol local.tgsdual.dom01_loc_var)

end

context strong_two_semiring
begin

lemma fdia1fdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>1 y \<cdot>\<^sub>0 z)) = dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (y \<cdot>\<^sub>0 z))"
  by (metis local.comm_d0d1 local.d1_strong_hom local.d1d0 local.dom01_loc_var)

lemma fdia1bdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 dom\<^sub>1 y)) = dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 y))"
  by (simp add: local.cod0dom1_exp)

lemma bdia1fdia0_prop3: "cod\<^sub>1 (dom\<^sub>0 (cod\<^sub>1 y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x) = cod\<^sub>1 (dom\<^sub>0 (y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x)"
  by (simp add: local.stgsdual.cod0dom1_exp)

lemma bdia1bdia0_prop3: " cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 cod\<^sub>1 y) \<cdot>\<^sub>1 x) = cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 x)"
  by (metis local.c1_strong_hom local.c1c0 local.cod01_loc_var local.comm_c0c1)

lemma fdia0fdia1_prop4: "dom\<^sub>0 z \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 y))"
 proof-
  have  "dom\<^sub>0 z \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y) = dom\<^sub>1 (dom\<^sub>0 z) \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y)"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y))"
    by simp
  also have "\<dots> \<le> dom\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (dom\<^sub>0 z  \<cdot>\<^sub>0 y))"
    using local.d0_comp1 local.dsr1.d_iso by presburger
  finally show ?thesis.
qed

lemma fdia0bdia1_prop4: "dom\<^sub>0 z \<cdot>\<^sub>0 cod\<^sub>1 (y \<cdot>\<^sub>1 x) \<le> cod\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 x))"
  by (metis local.c1d0 local.csr1.rdual.dom_iso local.d0_comp1 local.stgsdual.d1_strong_hom)

lemma fdia1fdia1_prop4: "dom\<^sub>1 (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 dom\<^sub>0 z \<le> dom\<^sub>1 ((x \<cdot>\<^sub>0 dom\<^sub>0 z) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 dom\<^sub>0 z))"
  by (metis local.d0_comp1_idem local.d1_strong_hom local.d1d0 local.dsr1.d_iso local.tgsdual.interchange)

lemma bdia1bdia1_prop4:  "cod\<^sub>1 (y \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 dom\<^sub>0 z \<le> cod\<^sub>1 ((y \<cdot>\<^sub>0 dom\<^sub>0 z) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 dom\<^sub>0 z))"
  by (metis local.c1d0 local.csr1.rdual.dom_iso local.stgsdual.d1_strong_hom local.tgsdual.d1_comp1)

end

subsection \<open>Globular 2-Kleene algebras\<close>

class two_kleene_algebra = two_semiring + kleene_algebra0 + kleene_algebra1 

class strong_two_kleene_algebra = strong_two_semiring + kleene_algebra0 + kleene_algebra1 

lemma (in strong_two_kleene_algebra) "star1 x \<cdot>\<^sub>0 star1 y \<le> star0 (x \<cdot>\<^sub>1 y)"
  (*nitpick *)
  oops

lemma (in strong_two_kleene_algebra) "star1 x \<cdot>\<^sub>0 star1 y \<le> star1 (x \<cdot>\<^sub>1 y)"
  (*nitpick *)
  oops

context two_kleene_algebra
begin

lemma interchange_var1: "(x \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (z \<cdot>\<^sub>1 z) \<le> (x \<cdot>\<^sub>0 y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 y \<cdot>\<^sub>0 z)"
  by (meson local.dd0.d0.mult_isol local.dual_order.trans local.tgsdual.interchange)

lemma interchange_var2: "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> (x \<cdot>\<^sub>0 x \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 y \<cdot>\<^sub>0 y)"
  by (meson local.dd0.d0.mult_isol local.dual_order.trans local.tgsdual.interchange)

lemma star0_comp1: "star0 (x \<cdot>\<^sub>1 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
proof-
  have a: "1\<^sub>0 \<le> star0 x \<cdot>\<^sub>1 star0 y"
    by (metis local.d1.mult_isol_var local.id0_comp1_eq local.k0.star_ref)
  have "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> (x \<cdot>\<^sub>0 star0 x ) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 star0 y)"
    by (simp add: local.interchange)
  also have "\<dots> \<le> star0 x \<cdot>\<^sub>1 star0 y"
    by (simp add: local.dd1.d1.mult_isol_var)
  finally have "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y".
  hence "1\<^sub>0 + (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
    by (simp add: a)
  thus ?thesis
    using local.star0_inductl by force
qed

end

context strong_two_kleene_algebra
begin

lemma " star1 (x \<cdot>\<^sub>1 y) \<le> star1 x \<cdot>\<^sub>0 star1 y"
  (*nitpick *)
  oops

lemma "star1 x \<cdot>\<^sub>0 star1 y \<le> star1 (x \<cdot>\<^sub>0 y)"
   (*nitpick *)
  oops

lemma "star1 (x \<cdot>\<^sub>0 y) \<le> star1 x \<cdot>\<^sub>0 star1 y"
   (*nitpick *)
  oops

lemma "star0 x \<cdot>\<^sub>1 star0 y \<le> star0 (x \<cdot>\<^sub>0 y)"
   (*nitpick *)
  oops

lemma " star0 (x \<cdot>\<^sub>0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
   (*nitpick *)
  oops

lemma "star0 x \<cdot>\<^sub>1 star0 y \<le> star0 (x \<cdot>\<^sub>1 y)"
   (*nitpick *)
  oops

lemma (in strong_two_kleene_algebra) "dom\<^sub>0 x \<cdot>\<^sub>0 star1 y \<le> star1 (dom\<^sub>0 x \<cdot>\<^sub>0 y)" 
  oops (* no proof no counterexample *)

end
 
class two_quantale_lmcs = modal_semiring0 + modal_semiring1 +
  assumes interchange: "(w \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (w \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 z)"
  and d1_hom: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) = dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_hom: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"
  and d1d0 [simp]: "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
 and c1d0 [simp]: "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
 and d1c0 [simp]: "dom\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
 and c1c0 [simp]: "cod\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  and d0d1 [simp]: "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 x"
 and c0d1 [simp]: "cod\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 x"
 and d0c1 [simp]: "dom\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>0 x"
 and c0c1 [simp]: "cod\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>0 x"

begin

lemma "dom\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
  (* no proof no counterexample *)
  oops

lemma  "cod\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  (* no proof no counterexample *)
  oops

end

end