\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport for Dependent Function Relator with Non-Dependent Functions\<close>
theory Transport_Rel_If
  imports
    Transport
begin

paragraph \<open>Summary\<close>
text \<open>We introduce a special case of @{locale transport_Dep_Fun_Rel}.
The derived theorem is easier to apply and supported by the current prototype.\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma reflexive_on_rel_if_if_reflexive_onI [intro]:
  assumes "B \<Longrightarrow> reflexive_on P R"
  shows "reflexive_on P (rel_if B R)"
  using assms by (intro reflexive_onI) blast

lemma transitive_on_rel_if_if_transitive_onI [intro]:
  assumes "B \<Longrightarrow> transitive_on P R"
  shows "transitive_on P (rel_if B R)"
  using assms by (intro transitive_onI) (blast dest: transitive_onD)

lemma preorder_on_rel_if_if_preorder_onI [intro]:
  assumes "B \<Longrightarrow> preorder_on P R"
  shows "preorder_on P (rel_if B R)"
  using assms by (intro preorder_onI) auto

lemma symmetric_on_rel_if_if_symmetric_onI [intro]:
  assumes "B \<Longrightarrow> symmetric_on P R"
  shows "symmetric_on P (rel_if B R)"
  using assms by (intro symmetric_onI) (blast dest: symmetric_onD)

lemma partial_equivalence_rel_on_rel_if_if_partial_equivalence_rel_onI [intro]:
  assumes "B \<Longrightarrow> partial_equivalence_rel_on P R"
  shows "partial_equivalence_rel_on P (rel_if B R)"
  using assms by (intro partial_equivalence_rel_onI)
  auto

lemma rel_if_dep_mono_wrt_rel_if_iff_if_dep_mono_wrt_relI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ([x y \<Colon> R] \<Rrightarrow>\<^sub>m S x y) f"
  and "B \<longleftrightarrow> B'"
  shows "([x y \<Colon> (rel_if B R)] \<Rrightarrow>\<^sub>m (rel_if B' (S x y))) f"
  using assms by (intro dep_mono_wrt_relI) auto

end

corollary reflexive_rel_if_if_reflexiveI [intro]:
  assumes "B \<Longrightarrow> reflexive R"
  shows "reflexive (rel_if B R)"
  using assms unfolding reflexive_eq_reflexive_on by blast

corollary transitive_rel_if_if_transitiveI [intro]:
  assumes "B \<Longrightarrow> transitive R"
  shows "transitive (rel_if B R)"
  using assms unfolding transitive_eq_transitive_on by blast

corollary preorder_rel_if_if_preorderI [intro]:
  assumes "B \<Longrightarrow> preorder R"
  shows "preorder (rel_if B R)"
  using assms unfolding preorder_eq_preorder_on by blast

corollary symmetric_rel_if_if_symmetricI [intro]:
  assumes "B \<Longrightarrow> symmetric R"
  shows "symmetric (rel_if B R)"
  using assms unfolding symmetric_eq_symmetric_on by blast

corollary partial_equivalence_rel_rel_if_if_partial_equivalence_relI [intro]:
  assumes "B \<Longrightarrow> partial_equivalence_rel R"
  shows "partial_equivalence_rel (rel_if B R)"
  using assms unfolding partial_equivalence_rel_eq_partial_equivalence_rel_on
  by blast

context galois_prop
begin

interpretation rel_if : galois_prop "rel_if B (\<le>\<^bsub>L\<^esub>)" "rel_if B' (\<le>\<^bsub>R\<^esub>)" l r .
interpretation flip_inv : galois_prop "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l .

lemma rel_if_half_galois_prop_left_if_iff_if_half_galois_prop_leftI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<^sub>h\<unlhd> (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.half_galois_prop_leftI) auto

lemma rel_if_half_galois_prop_right_if_iff_if_half_galois_prop_rightI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<unlhd>\<^sub>h (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.half_galois_prop_rightI) fastforce

lemma rel_if_galois_prop_if_iff_if_galois_propI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<unlhd> (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.galois_propI
    rel_if_half_galois_prop_left_if_iff_if_half_galois_prop_leftI
    rel_if_half_galois_prop_right_if_iff_if_half_galois_prop_rightI)
  auto

end

context galois
begin

interpretation rel_if : galois "rel_if B (\<le>\<^bsub>L\<^esub>)" "rel_if B' (\<le>\<^bsub>R\<^esub>)" l r .

lemma rel_if_galois_connection_if_iff_if_galois_connectionI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<stileturn> (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.galois_connectionI
    rel_if_dep_mono_wrt_rel_if_iff_if_dep_mono_wrt_relI
    rel_if_galois_prop_if_iff_if_galois_propI)
  auto

lemma rel_if_galois_equivalence_if_iff_if_galois_equivalenceI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^sub>G (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.galois_equivalenceI
    rel_if_galois_connection_if_iff_if_galois_connectionI
    galois_prop.rel_if_galois_prop_if_iff_if_galois_propI)
  (auto elim: galois.galois_connectionE)

end

context transport
begin

interpretation rel_if : transport "rel_if B (\<le>\<^bsub>L\<^esub>)" "rel_if B' (\<le>\<^bsub>R\<^esub>)" l r .

lemma rel_if_preorder_equivalence_if_iff_if_preorder_equivalenceI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^bsub>pre\<^esub> (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro rel_if.preorder_equivalence_if_galois_equivalenceI
    rel_if_galois_equivalence_if_iff_if_galois_equivalenceI
    preorder_on_rel_if_if_preorder_onI)
  blast+

lemma rel_if_partial_equivalence_rel_equivalence_if_iff_if_partial_equivalence_rel_equivalenceI:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((rel_if B (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^bsub>PER\<^esub> (rel_if B' (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro
    rel_if.partial_equivalence_rel_equivalence_if_galois_equivalenceI
    rel_if_galois_equivalence_if_iff_if_galois_equivalenceI)
  blast+

end

locale transport_Dep_Fun_Rel_no_dep_fun =
  transport_Dep_Fun_Rel_syntax L1 R1 l1 r1 L2 R2 "\<lambda>_ _. l2" "\<lambda>_ _. r2" +
  tdfr : transport_Dep_Fun_Rel L1 R1 l1 r1 L2 R2 "\<lambda>_ _. l2" "\<lambda>_ _. r2"
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'a2"
  and r1 :: "'a2 \<Rightarrow> 'a1"
  and L2 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and R2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'b1 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'b1"
begin

notation t2.unit ("\<eta>\<^sub>2")
notation t2.counit ("\<epsilon>\<^sub>2")

abbreviation "L \<equiv> tdfr.L"
abbreviation "R \<equiv> tdfr.R"

abbreviation "l \<equiv> tdfr.l"
abbreviation "r \<equiv> tdfr.r"

notation tdfr.L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation tdfr.R (infix "\<le>\<^bsub>R\<^esub>" 50)

notation tdfr.ge_left (infix "\<ge>\<^bsub>L\<^esub>" 50)
notation tdfr.ge_right (infix "\<ge>\<^bsub>R\<^esub>" 50)

notation tdfr.unit ("\<eta>")
notation tdfr.counit ("\<epsilon>")

theorem partial_equivalence_rel_equivalenceI:
  assumes per_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and per_equiv2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2 r2"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  have per2I: "((\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) l2 r2"
    if hyps: "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<^bsub>L1\<^esub>\<lessapprox> x1'" "x1' \<le>\<^bsub>R1\<^esub> x2'" for x1 x2 x1' x2'
  proof -
    from hyps have "x1 \<^bsub>L1\<^esub>\<lessapprox> x2'"
      using per_equiv1 t1.left_Galois_if_left_Galois_if_left_relI
        t1.left_Galois_if_right_rel_if_left_GaloisI
      by fast
    with per_equiv2 show ?thesis by blast
  qed
  have "([x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)) (\<lambda>_ _. l2)"
    by (intro dep_mono_wrt_relI Dep_Fun_Rel_relI Dep_Fun_Rel_predI rel_if_if_impI)
    (auto 8 0 dest!: per2I)
  moreover have
    "([x1 x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2 \<^bsub>L1\<^esub>\<lessapprox> x1'] \<Rrightarrow>
    [in_field (\<le>\<^bsub>R2 (l1 x1) x2'\<^esub>)] \<Rrightarrow> (\<le>\<^bsub>L2 x1 (r1 x2')\<^esub>)) (\<lambda>_ _. r2)"
    by (intro dep_mono_wrt_relI Dep_Fun_Rel_relI Dep_Fun_Rel_predI rel_if_if_impI)
    (auto 8 0 dest!: per2I)
  ultimately show ?thesis
    using assms by (intro tdfr.partial_equivalence_rel_equivalenceI) auto
qed

end


end