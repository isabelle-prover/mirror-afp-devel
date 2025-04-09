theory TarskiIsomorphism
  imports Poincare_Disc.Tarski
begin

locale TarskiAbsoluteIso = TarskiAbsolute + 
  fixes \<phi> :: "'a \<Rightarrow> 'b"
  fixes cong' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes betw' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes \<phi>bij: "bij \<phi>"
  assumes \<phi>cong: "\<And> x y z w. cong' (\<phi> x) (\<phi> y) (\<phi> z) (\<phi> w) \<longleftrightarrow> cong x y z w"
  assumes \<phi>betw: "\<And> x y z. betw' (\<phi> x) (\<phi> y) (\<phi> z) \<longleftrightarrow> betw x y z"

sublocale TarskiAbsoluteIso \<subseteq> TA: TarskiAbsolute cong' betw'
proof
  fix x y
  show "cong' x y y x"
    by (smt (verit) \<phi>cong  \<phi>bij bij_iff cong_reflexive)
next
  fix x y z u v w
  show "cong' x y z u \<and> cong' x y v w \<longrightarrow> cong' z u v w"
    by (smt (verit) \<phi>cong \<phi>bij bij_iff cong_transitive)
next
  fix x y z
  show "cong' x y z z \<longrightarrow> x = y"
    by (smt (verit) \<phi>cong \<phi>bij bij_iff cong_identity)
next
  fix x y a b
  show "\<exists> z. betw' x y z \<and> cong' y z a b"
    by (smt (verit) \<phi>cong \<phi>betw \<phi>bij bij_iff segment_construction)
next
  fix x y z x' y' z' u u'
  show "x \<noteq> y \<and> betw' x y z \<and> betw' x' y' z' \<and> cong' x y x' y' \<and> cong' y z y' z' \<and> cong' x u x' u' \<and> cong' y u y' u' \<longrightarrow>
        cong' z u z' u'"
    by (smt (verit) \<phi>cong \<phi>betw \<phi>bij bij_iff five_segment)
next
  fix x y 
  show "betw' x y x \<longrightarrow> x = y"
    by (metis \<phi>betw \<phi>bij betw_identity bij_pointE)
next
  fix x u z y v
  show "betw' x u z \<and> betw' y v z \<longrightarrow> (\<exists>a. betw' u a y \<and> betw' x a v)"
    by (smt (verit) \<phi>betw \<phi>bij Pasch bij_pointE)
next
  show "\<exists> a b c. \<not> betw' a b c \<and> \<not> betw' b c a \<and> \<not> betw' c a b"
    by (smt (verit) \<phi>betw \<phi>bij lower_dimension bij_pointE)
next
  fix x u v y z
  show "cong' x u x v \<and> cong' y u y v \<and> cong' z u z v \<and> u \<noteq> v \<longrightarrow> betw' x y z \<or> betw' y z x \<or> betw' z x y"
    by (smt (verit) \<phi>cong \<phi>betw \<phi>bij upper_dimension bij_pointE)
qed

context TarskiAbsoluteIso
begin
lemma \<phi>on_line: 
  shows "TA.on_line (\<phi> p) (\<phi> a) (\<phi> b) \<longleftrightarrow> on_line p a b"
  using TA.on_line_def \<phi>betw on_line_def 
  by presburger

lemma \<phi>on_ray: 
  shows "TA.on_ray (\<phi> p) (\<phi> a) (\<phi> b) \<longleftrightarrow> on_ray p a b"
  using TA.on_ray_def \<phi>betw on_ray_def 
  by presburger

lemma \<phi>in_angle: 
  shows "TA.in_angle (\<phi> p) (\<phi> a) (\<phi> b) (\<phi> c) \<longleftrightarrow> in_angle p a b c"
proof
  assume "in_angle p a b c"
  then show "TA.in_angle (\<phi> p) (\<phi> a) (\<phi> b) (\<phi> c)"
    by (smt (verit, best) TA.in_angle_def in_angle_def \<phi>betw \<phi>bij \<phi>on_ray bij_is_inj inj_eq)
next
  assume "TA.in_angle (\<phi> p) (\<phi> a) (\<phi> b) (\<phi> c)"
  then obtain x where "\<phi> b \<noteq> \<phi> a \<and> \<phi> b \<noteq> \<phi> c \<and> \<phi> p \<noteq> \<phi> b" "betw' (\<phi> a) (\<phi> x) (\<phi> c) \<and> \<phi> x \<noteq> \<phi> a \<and> \<phi> x \<noteq> \<phi> c" "TA.on_ray (\<phi> p) (\<phi> b) (\<phi> x)"
    by (smt (verit, ccfv_threshold) TA.in_angle_def \<phi>bij bij_pointE)
  then show "in_angle p a b c"
    unfolding in_angle_def
    using \<phi>betw \<phi>on_ray by auto
qed

lemma \<phi>ray_meets_line: 
  shows "TA.ray_meets_line (\<phi> ra) (\<phi> rb) (\<phi> la) (\<phi> lb) \<longleftrightarrow>
         ray_meets_line ra rb la lb"
  unfolding TA.ray_meets_line_def ray_meets_line_def
  by (metis \<phi>bij \<phi>on_line \<phi>on_ray bij_pointE)

end

locale TarskiHyperbolicIso = TarskiHyperbolic + 
  fixes \<phi> :: "'a \<Rightarrow> 'b"
  fixes cong' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes betw' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes \<phi>bij: "bij \<phi>"
  assumes \<phi>cong: "\<And> x y z w. cong' (\<phi> x) (\<phi> y) (\<phi> z) (\<phi> w) \<longleftrightarrow> cong x y z w"
  assumes \<phi>betw: "\<And> x y z. betw' (\<phi> x) (\<phi> y) (\<phi> z) \<longleftrightarrow> betw x y z"

sublocale TarskiHyperbolicIso \<subseteq> TAI: TarskiAbsoluteIso
  by (simp add: TarskiAbsoluteIso.intro TarskiAbsoluteIso_axioms_def TarskiAbsolute_axioms \<phi>betw \<phi>bij \<phi>cong)

sublocale TarskiHyperbolicIso \<subseteq> TarskiHyperbolic cong' betw'
proof
  show "\<exists>a b c d t. betw' a d t \<and> betw' b d c \<and> a \<noteq> d \<and> (\<forall>x y. betw' a b x \<and> betw' a c y \<longrightarrow> \<not> betw' x t y)"
    by (smt (verit) \<phi>betw \<phi>bij euclid_negation bij_pointE)
next
  fix a x1 x2
  assume "\<not> TAI.TA.on_line a x1 x2"
  then have *: "\<not> on_line (inv \<phi> a) (inv \<phi> x1) (inv \<phi> x2)"
    by (metis \<phi>bij TAI.\<phi>on_line bij_inv_eq_iff)
  obtain a1 a2 where *: 
    "\<not> on_line (inv \<phi> a) (inv \<phi> a1) (inv \<phi> a2)"
    "\<not> ray_meets_line (inv \<phi> a) (inv \<phi> a1) (inv \<phi> x1) (inv \<phi> x2)"
    "\<not> ray_meets_line (inv \<phi> a) (inv \<phi> a2) (inv \<phi> x1) (inv \<phi> x2)"
    "(\<forall>a'. in_angle a' (inv \<phi> a1) (inv \<phi> a) (inv \<phi> a2) \<longrightarrow> ray_meets_line (inv \<phi> a) a' (inv \<phi> x1) (inv \<phi> x2))"
    using limiting_parallels[OF *] 
    by (smt (verit, ccfv_threshold) \<phi>bij bij_inv_eq_iff)
  then have "\<not> TAI.TA.on_line a a1 a2 \<and> \<not> TAI.TA.ray_meets_line a a1 x1 x2 \<and> \<not> TAI.TA.ray_meets_line a a2 x1 x2"
    by (metis \<phi>bij TAI.\<phi>on_line TAI.\<phi>ray_meets_line bij_is_surj surj_f_inv_f)
  moreover
  have "\<forall>a'. TAI.TA.in_angle a' a1 a a2 \<longrightarrow> TAI.TA.ray_meets_line a a' x1 x2"
  proof safe
    fix a'
    assume "TAI.TA.in_angle a' a1 a a2"
    then have "ray_meets_line (inv \<phi> a) (inv \<phi> a') (inv \<phi> x1) (inv \<phi> x2)"
      using *(4) TAI.\<phi>ray_meets_line TAI.\<phi>in_angle \<phi>bij bij_pointE
      by (smt (verit, ccfv_SIG) bij_is_surj surj_f_inv_f)
    then show "TAI.TA.ray_meets_line a a' x1 x2"
      by (metis \<phi>bij TAI.\<phi>ray_meets_line bij_is_surj surj_f_inv_f)
  qed
  ultimately show "\<exists>a1 a2.
          \<not> TAI.TA.on_line a a1 a2 \<and>
          \<not> TAI.TA.ray_meets_line a a1 x1 x2 \<and>
          \<not> TAI.TA.ray_meets_line a a2 x1 x2 \<and>
          (\<forall>a'. TAI.TA.in_angle a' a1 a a2 \<longrightarrow> TAI.TA.ray_meets_line a a' x1 x2)"
    by blast
qed

locale ElementaryTarskiHyperbolicIso = ElementaryTarskiHyperbolic + 
  fixes \<phi> :: "'a \<Rightarrow> 'b"
  fixes cong' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes betw' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes \<phi>bij: "bij \<phi>"
  assumes \<phi>cong: "\<And> x y z w. cong' (\<phi> x) (\<phi> y) (\<phi> z) (\<phi> w) \<longleftrightarrow> cong x y z w"
  assumes \<phi>betw: "\<And> x y z. betw' (\<phi> x) (\<phi> y) (\<phi> z) \<longleftrightarrow> betw x y z"

sublocale ElementaryTarskiHyperbolicIso \<subseteq> THI: TarskiHyperbolicIso
  by (simp add: TarskiHyperbolicIso.intro TarskiHyperbolicIso_axioms_def TarskiHyperbolic_axioms \<phi>betw \<phi>bij \<phi>cong)

sublocale ElementaryTarskiHyperbolicIso \<subseteq> ElementaryTarskiHyperbolic cong' betw'
proof
  fix \<Phi> \<Psi>
  assume "\<exists>a. \<forall>x y. \<Phi> x \<and> \<Psi> y \<longrightarrow> betw' a x y"
  then have "\<exists>a. \<forall>x y. (\<Phi> \<circ> \<phi>) x \<and> (\<Psi> \<circ> \<phi>) y \<longrightarrow> betw a x y"
    by (metis (no_types, opaque_lifting) \<phi>betw \<phi>bij bij_pointE comp_eq_dest_lhs)
  then have "\<exists>b. \<forall>x y. (\<Phi> \<circ> \<phi>) x \<and> (\<Psi> \<circ> \<phi>) y \<longrightarrow> betw x b y"
    using continuity
    by simp
  then show "\<exists>b. \<forall>x y. \<Phi> x \<and> \<Psi> y \<longrightarrow> betw' x b y"
    by (metis (no_types, opaque_lifting) \<phi>betw \<phi>bij bij_pointE comp_eq_dest_lhs)    
qed


end